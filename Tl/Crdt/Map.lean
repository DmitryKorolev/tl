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

/-- Boolean strict-ascending check over adjacent keys — the executable face of
    `Sorted` for input that arrives *without* a proof (a deserialized list, e.g.
    the store's fold cache). `sorted_of_ascending` re-establishes the canonical
    invariant; a `false` is the caller's corrupt-input signal. -/
def ascending : List (K × V) → Bool
  | [] => true
  | [_] => true
  | p :: q :: ps => decide (lt p.1 q.1) && ascending (q :: ps)

/-- Adjacent strict ascent implies the full sorted invariant (transitivity
    closes the gap from each head to the whole tail). -/
theorem sorted_of_ascending : {l : List (K × V)} → ascending l = true → Sorted l
  | [], _ => trivial
  | [_], _ => ⟨nofun, trivial⟩
  | p :: q :: ps, h => by
    unfold ascending at h
    rw [Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨hpq, hrest⟩ := h
    have hs : Sorted (q :: ps) := sorted_of_ascending hrest
    refine ⟨?_, hs⟩
    intro r hr
    rcases List.mem_cons.mp hr with he | hm
    · rw [he]; exact hpq
    · exact lt_trans hpq (hs.1 r hm)

/-- The converse: a `Sorted` list always passes the boolean check, so an
    encode of a canonical map is never rejected on decode. -/
theorem ascending_of_sorted : {l : List (K × V)} → Sorted l → ascending l = true
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: q :: _, ⟨hlb, hs⟩ => by
    unfold ascending
    rw [Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨hlb q (List.mem_cons_self ..), ascending_of_sorted hs⟩

/-- Outer-join two sorted maps, combining overlapping keys with `f`. Generic and
    O(|l2|·|result|) (a fold of `insertWith`); the WARM CRDT path merges a singleton
    and the COLD path is bridged to the linear merge-join `joinFast` (ADR-0023). BATCH
    callers should route through `joinFast`, not this directly. -/
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

/-- A successful lookup's entry is in the list. -/
theorem lookup_mem {k : K} {v : V} : {l : List (K × V)} → lookup k l = some v → (k, v) ∈ l
  | [], h => by rw [lookup_nil] at h; exact nomatch h
  | p :: ps, h => by
    unfold lookup at h
    by_cases hk : k = p.1
    · rw [if_pos hk] at h
      have hp : p = (k, v) := Prod.ext hk.symm (Option.some.inj h)
      rw [hp]; exact List.mem_cons_self ..
    · rw [if_neg hk] at h
      exact List.mem_cons_of_mem p (lookup_mem h)

/-- An entry's key looks up to some value. -/
theorem isSome_lookup_of_mem {k : K} {v : V} :
    {l : List (K × V)} → (k, v) ∈ l → (lookup k l).isSome = true
  | [], h => nomatch h
  | p :: ps, h => by
    unfold lookup
    by_cases hk : k = p.1
    · rw [if_pos hk]; rfl
    · rw [if_neg hk]
      rcases List.mem_cons.mp h with he | he
      · exact absurd (congrArg Prod.fst he) hk
      · exact isSome_lookup_of_mem he

/-- In a `Sorted` list (unique keys), a member entry IS its key's lookup — the
    converse of `lookup_mem`, needed to read an entry's value without re-scanning
    for it (the `presentElements` one-pass enumeration). -/
theorem lookup_of_mem {k : K} {v : V} :
    {l : List (K × V)} → Sorted l → (k, v) ∈ l → lookup k l = some v
  | [], _, h => nomatch h
  | p :: ps, ⟨hlb, hps⟩, hmem => by
    rcases List.mem_cons.mp hmem with he | hmem'
    · rw [← he]; exact lookup_cons_eq k v ps
    · have hlt : lt p.1 k := hlb (k, v) hmem'
      rw [lookup_cons_ne (Ne.symm (ne_of_lt hlt)), lookup_of_mem hps hmem']

/-- Keys of a `Sorted` list are duplicate-free — the strict sort gives the finite,
    NoDup node set the tracker layer's well-founded recursion measures over. -/
theorem sorted_map_fst_nodup : {l : List (K × V)} → Sorted l → (l.map Prod.fst).Nodup
  | [], _ => by rw [List.map_nil]; exact List.nodup_nil
  | p :: ps, ⟨hlb, hsp⟩ => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, sorted_map_fst_nodup hsp⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨q, hq, hqk⟩ := hmem
    exact absurd hqk.symm (ne_of_lt (hlb q hq))

/-- Filtering the keys of `insertWith f e0 v l` by a predicate that *rejects* `e0`
    yields the same list as filtering `l`'s keys: `insertWith` either merges into an
    existing `e0` entry (keys unchanged) or inserts `e0` (dropped by the filter),
    and touches no other key's position. The frame-lemma workhorse for a `related`
    edge add — it changes the edge OR-Set's add-map only at the `related` key. -/
theorem mapfst_insertWith_filter {f : V → V → V} {e0 : K} {v : V} {P : K → Bool}
    (hP : P e0 = false) : (l : List (K × V)) →
    ((insertWith f e0 v l).map Prod.fst).filter P = (l.map Prod.fst).filter P
  | [] => by
    show (List.map Prod.fst [(e0, v)]).filter P = (List.map Prod.fst ([] : List (K × V))).filter P
    rw [List.map_cons, List.map_nil,
      List.filter_cons_of_neg (a := Prod.fst (e0, v))
        (show ¬ P e0 = true by rw [hP]; exact Bool.false_ne_true)]
  | p :: ps => by
    unfold insertWith
    by_cases h1 : lt e0 p.1
    · rw [if_pos h1, List.map_cons,
        List.filter_cons_of_neg (a := Prod.fst (e0, v))
          (show ¬ P e0 = true by rw [hP]; exact Bool.false_ne_true)]
    · rw [if_neg h1]
      by_cases h2 : e0 = p.1
      · rw [if_pos h2, List.map_cons, List.map_cons,
          List.filter_cons_of_neg (a := Prod.fst (e0, f p.2 v))
            (show ¬ P e0 = true by rw [hP]; exact Bool.false_ne_true),
          List.filter_cons_of_neg (a := Prod.fst p)
            (show ¬ P p.1 = true by rw [← h2, hP]; exact Bool.false_ne_true)]
      · rw [if_neg h2, List.map_cons, List.map_cons]
        by_cases h3 : P p.1 = true
        · rw [List.filter_cons_of_pos (a := Prod.fst p) h3,
            List.filter_cons_of_pos (a := Prod.fst p) h3, mapfst_insertWith_filter hP ps]
        · rw [List.filter_cons_of_neg (a := Prod.fst p) h3,
            List.filter_cons_of_neg (a := Prod.fst p) h3, mapfst_insertWith_filter hP ps]

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

@[simp] theorem find_singleton (k j : K) (v : V) :
    (singleton k v).find j = if j = k then some v else none := by
  show AssocList.lookup j [(k, v)] = _
  unfold AssocList.lookup
  rfl

/-- Replace (or add) the value at `k`, preserving the canonical sort. Unlike `merge`,
    this *overrides* the existing entry rather than joining it — used for read-only
    state projections (the `unblocks` force-closed diagnostic), never the CRDT fold. -/
def insert (m : AMap K V) (k : K) (v : V) : AMap K V :=
  ⟨AssocList.insertWith (fun _ n => n) k v m.toList, AssocList.sorted_insertWith m.sorted⟩

@[simp] theorem find_insert (m : AMap K V) (k j : K) (v : V) :
    (m.insert k v).find j = if j = k then some v else m.find j := by
  unfold AMap.insert AMap.find
  by_cases h : j = k
  · subst h
    rw [if_pos rfl, AssocList.lookup_insertWith_self m.sorted]
    cases AssocList.lookup j m.toList <;> rfl
  · rw [if_neg h, AssocList.lookup_insertWith_ne h v m.toList]

/-- The keys, in sorted order — the finite, duplicate-free enumeration the OR-Set
    and the tracker layer iterate over. -/
def keys (m : AMap K V) : List K := m.toList.map Prod.fst

theorem mem_keys {m : AMap K V} {k : K} : k ∈ m.keys ↔ (m.find k).isSome = true := by
  unfold keys find
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact AssocList.isSome_lookup_of_mem hp
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    exact ⟨(k, v), AssocList.lookup_mem hv, rfl⟩

theorem keys_nodup (m : AMap K V) : m.keys.Nodup :=
  AssocList.sorted_map_fst_nodup m.sorted

/-- A member entry's value IS its key's `find` — read an entry in `toList`
    without a separate O(N) lookup for it. -/
theorem find_eq_some_of_mem {m : AMap K V} {k : K} {v : V}
    (h : (k, v) ∈ m.toList) : m.find k = some v :=
  AssocList.lookup_of_mem m.sorted h

/-- A successful `find`'s entry is in `toList` (the converse direction). -/
theorem mem_toList_of_find {m : AMap K V} {k : K} {v : V}
    (h : m.find k = some v) : (k, v) ∈ m.toList :=
  AssocList.lookup_mem h

/-- Rebuild a canonical map from an untrusted (deserialized) list: accepted iff
    strictly ascending by key, with the `Sorted` proof re-established; `none` is
    the corrupt-input signal. By `ascending_of_sorted`, a list that came out of
    an `AMap` (an encode of `toList`) is always accepted. -/
def ofAscList? (l : List (K × V)) : Option (AMap K V) :=
  if h : AssocList.ascending l = true then some ⟨l, AssocList.sorted_of_ascending h⟩
  else none

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

/-- Merging a single-key map `{e0 ↦ v}` into `m` and filtering the keys by a
    predicate that *rejects* `e0` leaves the filtered key list unchanged — the frame
    workhorse for a `related` edge add (lifts `AssocList.mapfst_insertWith_filter`). -/
theorem keys_merge_singleton_filter {f : V → V → V} (m : AMap K V) (e0 : K) (v : V)
    {P : K → Bool} (hP : P e0 = false) :
    ((merge f m (singleton e0 v)).keys).filter P = (m.keys).filter P := by
  show ((AssocList.insertWith f e0 v m.toList).map Prod.fst).filter P
     = (m.toList.map Prod.fst).filter P
  exact AssocList.mapfst_insertWith_filter hP m.toList

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

theorem merge_empty_left (f : V → V → V) (m : AMap K V) : merge f empty m = m := by
  apply ext; intro k; rw [find_merge, find_empty, optCombine_none_left]

theorem merge_empty_right (f : V → V → V) (m : AMap K V) : merge f m empty = m := by
  apply ext; intro k; rw [find_merge, find_empty, optCombine_none_right]

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

theorem union_empty_left (s : FinSet α) : union empty s = s := AMap.merge_empty_left _ s

theorem union_empty_right (s : FinSet α) : union s empty = s := AMap.merge_empty_right _ s

end FinSet

end Tl.Crdt
