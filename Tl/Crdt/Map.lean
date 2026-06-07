/-
`Tl.Crdt.Map` — canonical finite maps and sets with semilattice joins.

The CRDT state (ADR-0002) is built from per-id register maps, the per-key-LWW
`meta` map, and OR-Sets of issues / edges / labels. To make the convergence laws
(ADR-0004 thm 1–2) genuine *equalities* rather than setoid reasoning, every
collection is kept in a canonical form: a list strictly sorted by key (hence
duplicate-free). Two canonical maps with the same lookups are then *equal*
(`AMap.ext`), and a merge whose value-combiner is a join-semilattice is itself a
join-semilattice — commutative, associative, idempotent (`AMap.merge_comm` etc.).

`FinSet` is the degenerate map-to-`Unit`; its `union` is that merge with the
trivial combiner, so the OR-Set built on it (ADR-0002) inherits the same laws.

No Mathlib (ADR-0009): the order is `Tl.Crdt.TotalOrd`, all proofs explicit.
-/
import Tl.Crdt.Order

namespace Tl.Crdt

open TotalOrd

universe u v w

/-! ## `optCombine` — the outer-join of two optional values

`merge`'s per-key behaviour: present on both sides ⇒ combine; present on one ⇒
keep it; absent on both ⇒ absent. When the combiner is a semilattice so is this. -/

/-- Outer-join two options with `f` on the overlap. -/
def optCombine (f : α → α → α) : Option α → Option α → Option α
  | none, x => x
  | some a, none => some a
  | some a, some b => some (f a b)

@[simp] theorem optCombine_none_left (f : α → α → α) (x : Option α) :
    optCombine f none x = x := rfl

@[simp] theorem optCombine_none_right (f : α → α → α) : (x : Option α) →
    optCombine f x none = x
  | none => rfl
  | some _ => rfl

theorem optCombine_comm {f : α → α → α} (hf : ∀ a b, f a b = f b a) :
    (x y : Option α) → optCombine f x y = optCombine f y x
  | none, y => by rw [optCombine_none_left, optCombine_none_right]
  | some _, none => rfl
  | some a, some b => by simp only [optCombine, hf a b]

theorem optCombine_idem {f : α → α → α} (hf : ∀ a, f a a = a) :
    (x : Option α) → optCombine f x x = x
  | none => rfl
  | some a => by simp only [optCombine, hf a]

theorem optCombine_assoc {f : α → α → α} (hf : ∀ a b c, f (f a b) c = f a (f b c)) :
    (x y z : Option α) → optCombine f (optCombine f x y) z = optCombine f x (optCombine f y z)
  | none, _, _ => rfl
  | some _, none, _ => rfl
  | some _, some _, none => rfl
  | some a, some b, some c => by simp only [optCombine, hf a b c]

/-! ## `AssocList` — list-level sorted maps -/

namespace AssocList

variable {K : Type u} {V : Type v} [TotalOrd K]

/-- `k` is strictly below every key in `l`. -/
def lbKey (k : K) (l : List (K × V)) : Prop := ∀ q ∈ l, lt k q.1

/-- Strictly sorted by key (so keys are unique). -/
def Sorted : List (K × V) → Prop
  | [] => True
  | p :: ps => lbKey p.1 ps ∧ Sorted ps

/-- First value stored under `k`, or `none`. -/
def lookup (k : K) : List (K × V) → Option V
  | [] => none
  | p :: ps => if k = p.1 then some p.2 else lookup k ps

theorem lbKey_of_lt {k k' : K} {l : List (K × V)} (h : lt k k') (hk' : lbKey k' l) :
    lbKey k l := fun q hq => lt_trans h (hk' q hq)

theorem lookup_eq_none_of_lbKey {k : K} : {l : List (K × V)} → lbKey k l → lookup k l = none
  | [], _ => rfl
  | p :: ps, hlb => by
    unfold lookup
    rw [if_neg (ne_of_lt (hlb p (List.mem_cons_self ..)))]
    exact lookup_eq_none_of_lbKey (fun q hq => hlb q (List.mem_cons_of_mem p hq))

/-- Insert `(k, v)`, combining with an existing value at `k` via `f` (existing
    first), preserving the sort. -/
def insertWith (f : V → V → V) (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | p :: ps =>
    if lt k p.1 then (k, v) :: p :: ps
    else if k = p.1 then (k, f p.2 v) :: ps
    else p :: insertWith f k v ps

theorem lbKey_insertWith {f : V → V → V} {b k : K} {v : V} (hbk : lt b k) :
    {l : List (K × V)} → lbKey b l → lbKey b (insertWith f k v l)
  | [], _ => by intro q hq; cases List.mem_singleton.mp hq; exact hbk
  | p :: ps, hlb => by
    unfold insertWith
    have hbp : lt b p.1 := hlb p (List.mem_cons_self ..)
    have hlbps : lbKey b ps := fun q hq => hlb q (List.mem_cons_of_mem p hq)
    split
    · intro q hq
      rcases List.mem_cons.mp hq with h | h
      · cases h; exact hbk
      · exact hlb q h
    · split
      · intro q hq
        rcases List.mem_cons.mp hq with h | h
        · cases h; exact hbk
        · exact hlbps q h
      · intro q hq
        rcases List.mem_cons.mp hq with h | h
        · cases h; exact hbp
        · exact lbKey_insertWith hbk hlbps q h

theorem sorted_insertWith {f : V → V → V} {k : K} {v : V} :
    {l : List (K × V)} → Sorted l → Sorted (insertWith f k v l)
  | [], _ => ⟨nofun, trivial⟩
  | p :: ps, ⟨hlb, hsp⟩ => by
    unfold insertWith
    split
    · rename_i hlt
      refine ⟨?_, hlb, hsp⟩
      intro q hq
      rcases List.mem_cons.mp hq with h | h
      · cases h; exact hlt
      · exact lt_trans hlt (hlb q h)
    · split
      · rename_i hkp
        refine ⟨?_, hsp⟩
        show lbKey k ps
        rw [hkp]; exact hlb
      · rename_i hnlt hne
        have hlt : lt p.1 k := by
          rcases trichotomy k p.1 with h | h | h
          · exact absurd h hnlt
          · exact absurd h hne
          · exact h
        exact ⟨lbKey_insertWith hlt hlb, sorted_insertWith hsp⟩

/-! Clean lookup-rewriting lemmas — preferred over inline `unfold lookup`. -/

@[simp] theorem lookup_nil (k : K) : lookup k ([] : List (K × V)) = none := rfl

theorem lookup_cons_self (p : K × V) (ps : List (K × V)) :
    lookup p.1 (p :: ps) = some p.2 := by unfold lookup; rw [if_pos rfl]

theorem lookup_cons_eq (k : K) (v : V) (ps : List (K × V)) :
    lookup k ((k, v) :: ps) = some v := by unfold lookup; rw [if_pos rfl]

theorem lookup_cons_ne {k : K} {p : K × V} (h : k ≠ p.1) (ps : List (K × V)) :
    lookup k (p :: ps) = lookup k ps := by
  show (if k = p.1 then some p.2 else lookup k ps) = lookup k ps
  rw [if_neg h]

theorem lookup_insertWith_ne {f : V → V → V} {j k : K} (hjk : j ≠ k) (v : V) :
    (l : List (K × V)) → lookup j (insertWith f k v l) = lookup j l
  | [] => by unfold insertWith; rw [lookup_cons_ne (show j ≠ (k, v).1 from hjk)]
  | p :: ps => by
    unfold insertWith
    by_cases h1 : lt k p.1
    · rw [if_pos h1, lookup_cons_ne (show j ≠ (k, v).1 from hjk)]
    · rw [if_neg h1]
      by_cases h2 : k = p.1
      · rw [if_pos h2, lookup_cons_ne (show j ≠ (k, f p.2 v).1 from hjk),
          lookup_cons_ne (show j ≠ p.1 from h2 ▸ hjk)]
      · rw [if_neg h2]
        by_cases hjp : j = p.1
        · rw [hjp, lookup_cons_self p (insertWith f k v ps), lookup_cons_self p ps]
        · rw [lookup_cons_ne hjp, lookup_cons_ne hjp]
          exact lookup_insertWith_ne hjk v ps

theorem lookup_insertWith_self {f : V → V → V} {k : K} {v : V} :
    {l : List (K × V)} → Sorted l →
    lookup k (insertWith f k v l)
      = some (match lookup k l with | some a => f a v | none => v)
  | [], _ => by unfold insertWith; rw [lookup_cons_eq, lookup_nil]
  | p :: ps, ⟨hlb, _⟩ => by
    unfold insertWith
    by_cases h1 : lt k p.1
    · rw [if_pos h1, lookup_cons_eq, lookup_cons_ne (ne_of_lt h1),
        lookup_eq_none_of_lbKey (lbKey_of_lt h1 hlb)]
    · rw [if_neg h1]
      by_cases h2 : k = p.1
      · rw [if_pos h2, lookup_cons_eq,
          show lookup k (p :: ps) = some p.2 by rw [h2]; exact lookup_cons_self p ps]
      · rename_i hsp
        rw [if_neg h2, lookup_cons_ne h2, lookup_cons_ne h2]
        exact lookup_insertWith_self hsp

/-- Outer-join two sorted maps, combining overlapping keys with `f`. -/
def merge (f : V → V → V) (l1 l2 : List (K × V)) : List (K × V) :=
  l2.foldr (fun p acc => insertWith f p.1 p.2 acc) l1

theorem sorted_merge {f : V → V → V} {l1 : List (K × V)} (s1 : Sorted l1) :
    (l2 : List (K × V)) → Sorted (merge f l1 l2)
  | [] => s1
  | _ :: qs => sorted_insertWith (sorted_merge s1 qs)

theorem lookup_merge {f : V → V → V} {l1 : List (K × V)} (s1 : Sorted l1) :
    {l2 : List (K × V)} → Sorted l2 → (k : K) →
    lookup k (merge f l1 l2) = optCombine f (lookup k l1) (lookup k l2)
  | [], _, k => by
    show lookup k l1 = optCombine f (lookup k l1) (lookup k [])
    rw [lookup_nil, optCombine_none_right]
  | q :: qs, ⟨hlb, hsq⟩, k => by
    show lookup k (insertWith f q.1 q.2 (merge f l1 qs))
       = optCombine f (lookup k l1) (lookup k (q :: qs))
    have hacc : Sorted (merge f l1 qs) := sorted_merge s1 qs
    by_cases hk : k = q.1
    · rw [hk, lookup_insertWith_self hacc, lookup_merge s1 hsq q.1,
        lookup_eq_none_of_lbKey hlb, optCombine_none_right, lookup_cons_self q qs]
      cases lookup q.1 l1 <;> rfl
    · rw [lookup_insertWith_ne hk, lookup_merge s1 hsq k, lookup_cons_ne hk]

/-- Two sorted maps with equal lookups are equal (extensionality / uniqueness of
    canonical form). The keystone that makes the merge laws equalities. -/
theorem ext : {l1 l2 : List (K × V)} → Sorted l1 → Sorted l2 →
    (∀ k, lookup k l1 = lookup k l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], q :: qs, _, _, h => by
    have hc := h q.1
    rw [lookup_nil, lookup_cons_self q qs] at hc
    nomatch hc
  | p :: ps, [], _, _, h => by
    have hc := h p.1
    rw [lookup_nil, lookup_cons_self p ps] at hc
    nomatch hc
  | p :: ps, q :: qs, ⟨hlbp, hsp⟩, ⟨hlbq, hsq⟩, h => by
    have hkey : p.1 = q.1 := by
      rcases trichotomy p.1 q.1 with hlt | heq | hlt
      · have hc := h p.1
        rw [lookup_cons_self p ps, lookup_cons_ne (ne_of_lt hlt),
          lookup_eq_none_of_lbKey (lbKey_of_lt hlt hlbq)] at hc
        nomatch hc
      · exact heq
      · have hc := h q.1
        rw [lookup_cons_self q qs, lookup_cons_ne (ne_of_lt hlt),
          lookup_eq_none_of_lbKey (lbKey_of_lt hlt hlbp)] at hc
        nomatch hc
    have hval : p.2 = q.2 := by
      have hc := h p.1
      rw [lookup_cons_self p ps,
        show lookup p.1 (q :: qs) = some q.2 by rw [hkey]; exact lookup_cons_self q qs] at hc
      exact Option.some.inj hc
    have hp : p = q := Prod.ext hkey hval
    have htail : ps = qs := by
      apply ext hsp hsq
      intro k
      by_cases hk : k = p.1
      · rw [hk, lookup_eq_none_of_lbKey hlbp,
          lookup_eq_none_of_lbKey (show lbKey p.1 qs by rw [hkey]; exact hlbq)]
      · have hc := h k
        rw [lookup_cons_ne hk, lookup_cons_ne (hkey ▸ hk)] at hc
        exact hc
    rw [hp, htail]

end AssocList

/-! ## `AMap` — a canonical finite map -/

/-- A finite map kept canonical (strictly sorted by key). -/
structure AMap (K : Type u) (V : Type v) [TotalOrd K] where
  toList : List (K × V)
  sorted : AssocList.Sorted toList

namespace AMap

variable {K : Type u} {V : Type v} [TotalOrd K]

/-- The empty map. -/
def empty : AMap K V := ⟨[], trivial⟩

/-- The single-entry map `{k ↦ v}`. -/
def singleton (k : K) (v : V) : AMap K V := ⟨[(k, v)], ⟨nofun, trivial⟩⟩

/-- Look up a key. -/
def find (m : AMap K V) (k : K) : Option V := AssocList.lookup k m.toList

/-- Merge two maps, combining overlapping keys with `f`. -/
def merge (f : V → V → V) (m1 m2 : AMap K V) : AMap K V :=
  ⟨AssocList.merge f m1.toList m2.toList, AssocList.sorted_merge m1.sorted m2.toList⟩

/-- Maps with equal lookups are equal — proof-irrelevant in the `sorted` field. -/
theorem ext {m1 m2 : AMap K V} (h : ∀ k, m1.find k = m2.find k) : m1 = m2 := by
  obtain ⟨l1, s1⟩ := m1
  obtain ⟨l2, s2⟩ := m2
  have : l1 = l2 := AssocList.ext s1 s2 h
  subst this; rfl

theorem find_merge (f : V → V → V) (m1 m2 : AMap K V) (k : K) :
    (merge f m1 m2).find k = optCombine f (m1.find k) (m2.find k) :=
  AssocList.lookup_merge m1.sorted m2.sorted k

theorem merge_comm {f : V → V → V} (hf : ∀ a b, f a b = f b a) (m1 m2 : AMap K V) :
    merge f m1 m2 = merge f m2 m1 := by
  apply ext; intro k
  rw [find_merge, find_merge, optCombine_comm hf]

theorem merge_idem {f : V → V → V} (hf : ∀ a, f a a = a) (m : AMap K V) :
    merge f m m = m := by
  apply ext; intro k
  rw [find_merge, optCombine_idem hf]

theorem merge_assoc {f : V → V → V} (hf : ∀ a b c, f (f a b) c = f a (f b c))
    (m1 m2 m3 : AMap K V) :
    merge f (merge f m1 m2) m3 = merge f m1 (merge f m2 m3) := by
  apply ext; intro k
  rw [find_merge, find_merge, find_merge, find_merge, optCombine_assoc hf]

@[simp] theorem find_empty (k : K) : (empty : AMap K V).find k = none := rfl

end AMap

/-! ## `FinSet` — a canonical finite set (the map to `Unit`) -/

/-- A finite set: the degenerate `AMap … Unit`. `union` is its merge with the
    trivial combiner, hence a commutative/associative/idempotent join — the OR-Set
    add-tag and label sets (ADR-0002) ride on it. -/
def FinSet (α : Type u) [TotalOrd α] := AMap α Unit

namespace FinSet

variable {α : Type u} [TotalOrd α]

/-- Membership: the key is present. Phrased on `isSome` (a `Bool`), so it is
    `rfl`-decidable regardless of the `Unit` payload. -/
def Mem (s : FinSet α) (a : α) : Prop := (AMap.find s a).isSome = true

instance : Membership α (FinSet α) where
  mem s a := s.Mem a

instance (s : FinSet α) (a : α) : Decidable (a ∈ s) :=
  inferInstanceAs (Decidable ((AMap.find s a).isSome = true))

/-- The empty set. -/
def empty : FinSet α := AMap.empty

/-- The singleton `{a}`. -/
def singleton (a : α) : FinSet α := ⟨[(a, ())], ⟨nofun, trivial⟩⟩

/-- Set union. -/
def union (s t : FinSet α) : FinSet α := AMap.merge (fun _ _ => ()) s t

theorem mem_def (s : FinSet α) (a : α) : a ∈ s ↔ (AMap.find s a).isSome = true := Iff.rfl

theorem find_singleton (a b : α) :
    AMap.find (singleton b) a = (if a = b then some () else none) := rfl

theorem isSome_optCombine (f : Unit → Unit → Unit) (x y : Option Unit) :
    (optCombine f x y).isSome = (x.isSome || y.isSome) := by
  cases x <;> cases y <;> rfl

theorem not_mem_empty (a : α) : a ∉ (empty : FinSet α) := by
  show ¬ ((AMap.find AMap.empty a).isSome = true)
  rw [AMap.find_empty]; exact fun hh => Bool.noConfusion hh

theorem mem_singleton (a b : α) : a ∈ singleton b ↔ a = b := by
  rw [mem_def, find_singleton]
  by_cases h : a = b
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun hh => Bool.noConfusion hh, fun hh => absurd hh h⟩

theorem mem_union (s t : FinSet α) (a : α) : a ∈ union s t ↔ a ∈ s ∨ a ∈ t := by
  rw [mem_def, mem_def, mem_def, union,
    show AMap.find (AMap.merge (fun _ _ => ()) s t) a
       = optCombine (fun _ _ => ()) (AMap.find s a) (AMap.find t a)
       from AMap.find_merge _ s t a,
    isSome_optCombine, Bool.or_eq_true]

theorem union_comm (s t : FinSet α) : union s t = union t s :=
  AMap.merge_comm (fun _ _ => rfl) s t

theorem union_idem (s : FinSet α) : union s s = s :=
  AMap.merge_idem (fun a => by cases a; rfl) s

theorem union_assoc (s t u : FinSet α) : union (union s t) u = union s (union t u) :=
  AMap.merge_assoc (fun _ _ _ => rfl) s t u

end FinSet

end Tl.Crdt
