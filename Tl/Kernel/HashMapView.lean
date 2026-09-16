/-
`Tl.Kernel.HashMapView` — O(1)-amortized hash views of the kernel's list-backed
collections, with proved bridges back to the list/`AMap` forms.

The kernel's semantic collections stay lists/`AMap`s (so the join laws and the
spec theorems are stated over them), but `AMap.find` is a linear assoc-list
scan: read once per issue across N issues and a command path is Θ(N²). These
views — a `HashSet` of a list, a `HashMap` copy of an assoc list, and an
adjacency bucketing — give O(1)-amortized probes, each carrying the lemma that
makes it pointwise equal to the list form (`mem_hashSetOf`,
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

/-- The presence probe over the present-issue hash set agrees with the spec's
    `hasIssue` (used by the ready queue and the diagnostics). -/
theorem contains_hashSetOf_present (s : State) (j : IssueId) :
    (hashSetOf s.presentIssues).contains j = decide (s.hasIssue j) := by
  apply Bool.eq_iff_iff.mpr
  rw [Std.HashSet.contains_iff_mem, decide_eq_true_iff, mem_hashSetOf]
  exact OrSet.mem_presentElements s.issues j

/-! ## A hash copy of an association list (e.g. the rollup `AMap`'s `toList`)

Generic in the key `K` (any lawful-`BEq`/`Hashable`/`TotalOrd` type). The
`IssueId`-keyed views (`dataH`/`rollupH`/`provH`, `CyclesFast`/`ReadyFast`) are
the `K := IssueId` instantiation; the canonical-parent tie-break
(`Tl.Kernel.CanonParent`) is the `K := Edge` one — one probe, no per-key copy,
so a fix cannot split the two. -/

def hashAssoc {K V : Type _} [BEq K] [Hashable K] (l : List (K × V)) : Std.HashMap K V :=
  l.foldl (fun m p => m.insert p.1 p.2) ∅

theorem lookup_eq_none_of_not_fst {K V : Type _} [TotalOrd K] {k : K} :
    (l : List (K × V)) → k ∉ l.map Prod.fst → AssocList.lookup k l = none
  | [], _ => rfl
  | p :: ps, h => by
    have hne : k ≠ p.1 := fun he => by
      rw [List.map_cons] at h
      exact h (he ▸ List.mem_cons_self ..)
    show (if k = p.1 then some p.2 else AssocList.lookup k ps) = none
    rw [ite_eq_right hne]
    exact lookup_eq_none_of_not_fst ps (fun hm => by
      rw [List.map_cons] at h
      exact h (List.mem_cons_of_mem _ hm))

theorem getElem?_foldl_insert {K V : Type _} [TotalOrd K] [BEq K] [LawfulBEq K]
    [Hashable K] [LawfulHashable K] (l : List (K × V))
    (m0 : Std.HashMap K V) (hnd : (l.map Prod.fst).Nodup) (k : K) :
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
        rw [ite_eq_left hk]
      rw [hnone, hlk]
      show (m0.insert p.1 p.2)[k]? = some p.2
      rw [Std.HashMap.getElem?_insert, ite_eq_left (beq_iff_eq.mpr hk.symm)]
    · have hlk : AssocList.lookup k (p :: ps) = AssocList.lookup k ps := by
        show (if k = p.1 then some p.2 else AssocList.lookup k ps) = _
        rw [ite_eq_right hk]
      rw [hlk]
      cases hcase : AssocList.lookup k ps with
      | some v => rfl
      | none =>
        show (m0.insert p.1 p.2)[k]? = m0[k]?
        rw [Std.HashMap.getElem?_insert,
          ite_eq_right (fun h => hk (beq_iff_eq.mp h).symm)]

theorem getElem?_hashAssoc {K V : Type _} [TotalOrd K] [BEq K] [LawfulBEq K]
    [Hashable K] [LawfulHashable K] (l : List (K × V))
    (hnd : (l.map Prod.fst).Nodup) (k : K) :
    (hashAssoc l)[k]? = AssocList.lookup k l := by
  unfold hashAssoc
  rw [getElem?_foldl_insert l ∅ hnd k]
  cases AssocList.lookup k l with
  | some v => rfl
  | none => exact Std.HashMap.getElem?_empty

/-- The `AMap` instance of the bridge: the hash copy looks up exactly `find`.
    Instantiated at `K := IssueId` (the row-view probes) and `K := Edge` (the
    canonical-parent tag/tombstone hashes). -/
theorem getElem?_hashAssoc_amap {K V : Type _} [TotalOrd K] [BEq K] [LawfulBEq K]
    [Hashable K] [LawfulHashable K] (m : AMap K V) (k : K) :
    (hashAssoc m.toList)[k]? = m.find k :=
  getElem?_hashAssoc m.toList (AMap.keys_nodup m) k

/-- `lookup` distributes over a value-map that preserves keys: looking up `k` in
    `l.map (fun p => (p.1, g p.2))` is the lookup in `l` with `g` applied. -/
theorem lookup_map_val {V W : Type _} (g : V → W) (k : IssueId) :
    (l : List (IssueId × V)) →
      AssocList.lookup k (l.map (fun p => (p.1, g p.2))) = (AssocList.lookup k l).map g
  | [] => rfl
  | p :: ps => by
    show (if k = p.1 then some (g p.2) else AssocList.lookup k (ps.map (fun q => (q.1, g q.2))))
       = (if k = p.1 then some p.2 else AssocList.lookup k ps).map g
    by_cases hk : k = p.1
    · rw [ite_eq_left hk, ite_eq_left hk]; rfl
    · rw [ite_eq_right hk, ite_eq_right hk, lookup_map_val g k ps]

/-- The mapped-list instance of the bridge: a hash copy of an `AMap` whose values
    have been mapped by `g` looks up exactly `find`, with `g` applied — the
    `hashAssoc`-over-mapped-list companion of `getElem?_hashAssoc_amap` (which is
    value-copy only). Lets a *derived* per-issue view (e.g. the min-create-HLC
    ranking key) hoist into a hash while staying provably equal to its `find`. -/
theorem getElem?_hashAssoc_map_amap {V W : Type _} (g : V → W) (m : AMap IssueId V) (k : IssueId) :
    (hashAssoc (m.toList.map (fun p => (p.1, g p.2))))[k]? = (m.find k).map g := by
  have hnd : ((m.toList.map (fun p => (p.1, g p.2))).map Prod.fst).Nodup := by
    have hkeys : (m.toList.map (fun p => (p.1, g p.2))).map Prod.fst = m.toList.map Prod.fst := by
      rw [List.map_map]; rfl
    rw [hkeys]
    exact AMap.keys_nodup m
  rw [getElem?_hashAssoc _ hnd k, lookup_map_val g k m.toList]; rfl

/-- `getElem?` after folding a batch of `insert k (val k)` over a key list: a key
    in the batch reads its `val`, anything else falls through to the starting map.
    The `val` is a function of the key, so duplicate keys in the batch are harmless
    (the `Std.HashMap` twin of `AMap`'s `find_foldl_insert`). -/
theorem getElem?_foldl_insert_keys {V : Type _} (val : IssueId → V) :
    ∀ (l : List IssueId) (m0 : Std.HashMap IssueId V) (z : IssueId),
      (l.foldl (fun m k => m.insert k (val k)) m0)[z]? = if z ∈ l then some (val z) else m0[z]?
  | [], m0, z => by rw [List.foldl_nil, ite_eq_right List.not_mem_nil]
  | a :: rest, m0, z => by
    show (rest.foldl (fun m k => m.insert k (val k)) (m0.insert a (val a)))[z]? = _
    rw [getElem?_foldl_insert_keys val rest (m0.insert a (val a)) z, Std.HashMap.getElem?_insert]
    by_cases hz : z ∈ rest
    · rw [ite_eq_left hz, ite_eq_left (List.mem_cons.mpr (Or.inr hz))]
    · rw [ite_eq_right hz]
      by_cases hza : z = a
      · rw [ite_eq_left (beq_iff_eq.mpr hza.symm), ite_eq_left (List.mem_cons.mpr (Or.inl hza)), hza]
      · rw [ite_eq_right (fun h => hza (beq_iff_eq.mp h).symm),
          ite_eq_right (fun h => (List.mem_cons.mp h).elim hza hz)]

/-! ## The inverse: an `AMap` materialized from a `HashMap`

The rollup builds its memo in a `Std.HashMap` (O(1)-amortized), then materializes
the canonical `AMap` once at the end — O(N log N): sort the entries by key
(`mergeSort`) and wrap with the proved strict sort (`sorted_mergeSort_keys`), not
an O(N) `AMap.insert` per entry (which would be O(N²)). So `effStatusAll`'s type
and every downstream bridge stay unchanged. `find_amapOfHashMap` is the bridge:
the materialized map looks up exactly the hash map's `getElem?`. -/

/-- A member of a key-nodup assoc list is found by `lookup`. -/
theorem lookup_of_mem_nodup {V : Type _} {k : IssueId} {v : V} :
    (l : List (IssueId × V)) → (l.map Prod.fst).Nodup → (k, v) ∈ l →
    AssocList.lookup k l = some v
  | [], _, hmem => absurd hmem (List.not_mem_nil)
  | p :: ps, hnd, hmem => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hp, hps⟩ := hnd
    rcases List.mem_cons.mp hmem with heq | hmem'
    · subst heq
      show (if k = (k, v).1 then some (k, v).2 else AssocList.lookup k ps) = some v
      rw [ite_eq_left rfl]
    · have hkfst : k ∈ ps.map Prod.fst := List.mem_map.mpr ⟨(k, v), hmem', rfl⟩
      have hkp : k ≠ p.1 := fun he => hp (he ▸ hkfst)
      show (if k = p.1 then some p.2 else AssocList.lookup k ps) = some v
      rw [ite_eq_right hkp]
      exact lookup_of_mem_nodup ps hps hmem'

/-- The hash map's `toList` keys are nodup. -/
theorem nodup_keys_toList {V : Type _} (m : Std.HashMap IssueId V) :
    (m.toList.map Prod.fst).Nodup :=
  List.pairwise_map.mpr
    ((Std.HashMap.distinct_keys_toList (m := m)).imp (fun hab => ne_of_beq_false hab))

/-- `lookup` over the hash map's `toList` is exactly its `getElem?`. -/
theorem lookup_toList_eq_getElem? {V : Type _} (m : Std.HashMap IssueId V) (k : IssueId) :
    AssocList.lookup k m.toList = m[k]? := by
  cases h : m[k]? with
  | some v =>
    exact lookup_of_mem_nodup m.toList (nodup_keys_toList m)
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h)
  | none =>
    cases hl : AssocList.lookup k m.toList with
    | none => rfl
    | some v =>
      have hmem : m[k]? = some v :=
        Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (AssocList.lookup_mem hl)
      rw [h] at hmem
      nomatch hmem

/-- Bool key order for `mergeSort` (which wants a `Bool` comparator). -/
def keyLe {V : Type _} (a b : IssueId × V) : Bool := decide (TotalOrd.le a.1 b.1)

theorem keyLe_trans {V : Type _} (a b c : IssueId × V)
    (hab : keyLe a b = true) (hbc : keyLe b c = true) : keyLe a c = true :=
  decide_eq_true (TotalOrd.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))

theorem keyLe_total {V : Type _} (a b : IssueId × V) :
    (keyLe a b || keyLe b a) = true := by
  rcases TotalOrd.le_total a.1 b.1 with h | h
  · rw [show keyLe a b = true from decide_eq_true h, Bool.true_or]
  · rw [show keyLe b a = true from decide_eq_true h, Bool.or_true]

/-- `Pairwise` of the strict key order is exactly `AssocList.Sorted`. -/
theorem sorted_of_pairwise_ltKey {V : Type _} :
    (l : List (IssueId × V)) →
    l.Pairwise (fun a b => TotalOrd.lt a.1 b.1) → AssocList.Sorted l
  | [], _ => trivial
  | _ :: ps, h => by
    rw [List.pairwise_cons] at h
    exact ⟨fun q hq => h.1 q hq, sorted_of_pairwise_ltKey ps h.2⟩

/-- The mergeSorted entries are strictly key-sorted: `mergeSort` gives `≤`-pairwise,
    and the hash map's distinct keys upgrade `≤` to `<`. -/
theorem sorted_mergeSort_keys {V : Type _} (m : Std.HashMap IssueId V) :
    AssocList.Sorted (m.toList.mergeSort keyLe) := by
  have hle : (m.toList.mergeSort keyLe).Pairwise (fun a b => keyLe a b = true) :=
    List.pairwise_mergeSort (fun a b c => keyLe_trans a b c) (fun a b => keyLe_total a b) m.toList
  have hnd : (m.toList.mergeSort keyLe).Pairwise (fun a b => a.1 ≠ b.1) :=
    List.pairwise_map.mp
      (((List.mergeSort_perm m.toList keyLe).map Prod.fst).nodup_iff.mpr (nodup_keys_toList m))
  refine sorted_of_pairwise_ltKey _ ((hle.and hnd).imp (fun {a b} h => ?_))
  exact ⟨of_decide_eq_true h.1, fun hba => h.2 (TotalOrd.le_antisymm (of_decide_eq_true h.1) hba)⟩

/-- Materialize an `AMap` from a hash map in O(N log N): sort the entries by key,
    wrap with the proved strict sort. -/
def amapOfHashMap {V : Type _} (m : Std.HashMap IssueId V) : AMap IssueId V :=
  ⟨m.toList.mergeSort keyLe, sorted_mergeSort_keys m⟩

/-- **The inverse bridge.** The materialized `AMap` looks up exactly the hash
    map's `getElem?` — so a rollup that threads a `HashMap` memo and materializes
    once keeps `effStatusAll.find` pointwise equal to the in-flight memo. -/
theorem find_amapOfHashMap {V : Type _} (m : Std.HashMap IssueId V) (k : IssueId) :
    (amapOfHashMap m).find k = m[k]? := by
  show AssocList.lookup k (m.toList.mergeSort keyLe) = m[k]?
  have hnd : ((m.toList.mergeSort keyLe).map Prod.fst).Nodup :=
    ((List.mergeSort_perm m.toList keyLe).map Prod.fst).nodup_iff.mpr (nodup_keys_toList m)
  cases h : m[k]? with
  | some v =>
    exact lookup_of_mem_nodup _ hnd
      (List.mem_mergeSort.mpr (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h))
  | none =>
    cases hl : AssocList.lookup k (m.toList.mergeSort keyLe) with
    | none => rfl
    | some v =>
      have hmem : m[k]? = some v :=
        Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_mergeSort.mp (AssocList.lookup_mem hl))
      rw [h] at hmem
      nomatch hmem

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
        ite_eq_left (beq_iff_eq.mpr rfl), Option.getD_some,
        List.append_assoc, List.singleton_append]
    · rw [List.filter_cons_of_neg (p := fun q : IssueId × IssueId => q.1 == k)
          (fun h => hk (beq_iff_eq.mp h)),
        Std.HashMap.getElem?_insert, ite_eq_right (fun h => hk (beq_iff_eq.mp h))]

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
