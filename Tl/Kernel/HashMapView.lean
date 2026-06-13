/-
`Tl.Kernel.HashMapView` — O(1)-amortized hash views of the kernel's list-backed
collections, with proved bridges back to the list/`AMap` forms.

The kernel's semantic collections stay lists/`AMap`s (so the join laws and the
spec theorems are stated over them), but `AMap.find` is a linear assoc-list
scan: read once per issue across N issues and a command path is Θ(N²). These
views — a `HashSet` of a list, a `HashMap` copy of an assoc list, and an
adjacency bucketing — give O(1)-amortized probes, each carrying the lemma that
makes it pointwise EQUAL to the list form (`mem_hashSetOf`,
`getElem?_hashAssoc_amap`, `getD_bucketBy`). This module sits upstream of the
ready queue and the diagnostics so both the kernel fast paths and the CLI's
per-row projections can read through it.
-/
import Tl.Kernel.State
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

namespace Tl.Kernel

open Tl.Crdt

/-! ## A list's membership, as a hash set -/

def hashSetOf (l : List IssueId) : Std.HashSet IssueId :=
  l.foldl (fun s x => s.insert x) ∅

theorem mem_foldl_insert (l : List IssueId) (s0 : Std.HashSet IssueId) (x : IssueId) :
    x ∈ l.foldl (fun s y => s.insert y) s0 ↔ x ∈ l ∨ x ∈ s0 := by
  induction l generalizing s0 with
  | nil =>
    rw [List.foldl_nil]
    exact ⟨Or.inr, fun h => h.elim (fun h => nomatch h) id⟩
  | cons a as ih =>
    rw [List.foldl_cons, ih, Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem mem_hashSetOf {l : List IssueId} {x : IssueId} : x ∈ hashSetOf l ↔ x ∈ l := by
  unfold hashSetOf
  rw [mem_foldl_insert]
  exact ⟨fun h => h.elim id (fun h => absurd h (Std.HashSet.not_mem_empty)), Or.inl⟩

/-! ## A hash copy of an association list (e.g. the rollup `AMap`'s `toList`) -/

def hashAssoc {V : Type _} (l : List (IssueId × V)) : Std.HashMap IssueId V :=
  l.foldl (fun m p => m.insert p.1 p.2) ∅

theorem lookup_eq_none_of_not_fst {V : Type _} {k : IssueId} :
    (l : List (IssueId × V)) → k ∉ l.map Prod.fst → AssocList.lookup k l = none
  | [], _ => rfl
  | p :: ps, h => by
    have hne : k ≠ p.1 := fun he => by
      rw [List.map_cons] at h
      exact h (he ▸ List.mem_cons_self ..)
    show (if k = p.1 then some p.2 else AssocList.lookup k ps) = none
    rw [if_neg hne]
    exact lookup_eq_none_of_not_fst ps (fun hm => by
      rw [List.map_cons] at h
      exact h (List.mem_cons_of_mem _ hm))

theorem getElem?_foldl_insert {V : Type _} (l : List (IssueId × V))
    (m0 : Std.HashMap IssueId V) (hnd : (l.map Prod.fst).Nodup) (k : IssueId) :
    (l.foldl (fun m p => m.insert p.1 p.2) m0)[k]?
      = match AssocList.lookup k l with
        | some v => some v
        | none => m0[k]? := by
  induction l generalizing m0 with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hp, hps⟩ := hnd
    rw [List.foldl_cons, ih _ hps]
    by_cases hk : k = p.1
    · have hnone : AssocList.lookup k ps = none :=
        lookup_eq_none_of_not_fst ps (hk ▸ hp)
      have hlk : AssocList.lookup k (p :: ps) = some p.2 := by
        show (if k = p.1 then some p.2 else AssocList.lookup k ps) = some p.2
        rw [if_pos hk]
      rw [hnone, hlk]
      show (m0.insert p.1 p.2)[k]? = some p.2
      rw [Std.HashMap.getElem?_insert, if_pos (beq_iff_eq.mpr hk.symm)]
    · have hlk : AssocList.lookup k (p :: ps) = AssocList.lookup k ps := by
        show (if k = p.1 then some p.2 else AssocList.lookup k ps) = _
        rw [if_neg hk]
      rw [hlk]
      cases hcase : AssocList.lookup k ps with
      | some v => rfl
      | none =>
        show (m0.insert p.1 p.2)[k]? = m0[k]?
        rw [Std.HashMap.getElem?_insert,
          if_neg (fun h => hk (beq_iff_eq.mp h).symm)]

theorem getElem?_hashAssoc {V : Type _} (l : List (IssueId × V))
    (hnd : (l.map Prod.fst).Nodup) (k : IssueId) :
    (hashAssoc l)[k]? = AssocList.lookup k l := by
  unfold hashAssoc
  rw [getElem?_foldl_insert l ∅ hnd k]
  cases AssocList.lookup k l with
  | some v => rfl
  | none => exact Std.HashMap.getElem?_empty

/-- The `AMap` instance of the bridge: the hash copy looks up exactly `find`. -/
theorem getElem?_hashAssoc_amap {V : Type _} (m : AMap IssueId V) (k : IssueId) :
    (hashAssoc m.toList)[k]? = m.find k :=
  getElem?_hashAssoc m.toList (AMap.keys_nodup m) k

/-! ## Adjacency bucketing -/

/-- Bucket `(key, value)` pairs by key; each bucket carries its values in
    reverse input order (cons-accumulated — callers reverse once on read). -/
def bucketBy (l : List (IssueId × IssueId)) : Std.HashMap IssueId (List IssueId) :=
  l.foldl (fun m p => m.insert p.1 (p.2 :: m[p.1]?.getD [])) ∅

theorem getElem?_foldl_bucket (l : List (IssueId × IssueId))
    (m0 : Std.HashMap IssueId (List IssueId)) (k : IssueId) :
    ((l.foldl (fun m p => m.insert p.1 (p.2 :: m[p.1]?.getD [])) m0)[k]?.getD [])
      = ((l.filter (fun p => p.1 == k)).map (·.2)).reverse ++ (m0[k]?.getD []) := by
  induction l generalizing m0 with
  | nil =>
    rw [List.foldl_nil, List.filter_nil, List.map_nil, List.reverse_nil, List.nil_append]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    rw [List.foldl_cons]
    dsimp only
    rw [ih]
    by_cases hk : a = k
    · subst hk
      rw [List.filter_cons_of_pos (p := fun q : IssueId × IssueId => q.1 == a)
          (beq_iff_eq.mpr rfl),
        List.map_cons, List.reverse_cons, Std.HashMap.getElem?_insert,
        if_pos (beq_iff_eq.mpr rfl), Option.getD_some,
        List.append_assoc, List.singleton_append]
    · rw [List.filter_cons_of_neg (p := fun q : IssueId × IssueId => q.1 == k)
          (fun h => hk (beq_iff_eq.mp h)),
        Std.HashMap.getElem?_insert, if_neg (fun h => hk (beq_iff_eq.mp h))]

theorem getD_bucketBy (l : List (IssueId × IssueId)) (k : IssueId) :
    ((bucketBy l)[k]?.getD []).reverse = (l.filter (fun p => p.1 == k)).map (·.2) := by
  unfold bucketBy
  rw [getElem?_foldl_bucket l ∅ k, Std.HashMap.getElem?_empty, Option.getD_none,
    List.append_nil, List.reverse_reverse]

theorem mem_bucketBy {l : List (IssueId × IssueId)} {k y : IssueId}
    (h : y ∈ (bucketBy l)[k]?.getD []) : (k, y) ∈ l := by
  have h' : y ∈ ((bucketBy l)[k]?.getD []).reverse := List.mem_reverse.mpr h
  rw [getD_bucketBy] at h'
  obtain ⟨p, hp, hpy⟩ := List.mem_map.mp h'
  have hpf := List.mem_filter.mp hp
  obtain ⟨a, b⟩ := p
  have hak : a = k := beq_iff_eq.mp hpf.2
  have hby : b = y := hpy
  rw [← hak, ← hby]
  exact hpf.1

end Tl.Kernel
