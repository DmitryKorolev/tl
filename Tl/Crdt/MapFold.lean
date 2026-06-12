/-
`Tl.Crdt.MapFold` — the batched canonical `AMap` join and its bridge to the
iterated `merge` fold.

The cold materialization fold (`Tl.Kernel.fold`) joins one delta at a time, and
each join is a positional `AssocList.insertWith` — Θ(ops × keys) overall. This
module builds the *same* canonical map from all entries in one sorted pass
(`mergeSort` then an adjacent group-combine), so a cold rebuild is O(N log N).

The bridge is `find`-pointwise (`AMap.ext`): both the iterated merge and the
batched build reduce, at each key, to the `f`-combine of that key's values. The
combiners here are join-semilattices (`optCombine_comm`/`_assoc`), so the
combine *order* is irrelevant — `mergeSort`'s permutation (`mergeSort_perm`)
suffices and no sort *stability* is needed.
-/
import Tl.Crdt.Map

namespace Tl.Crdt

open TotalOrd

/-! ## Per-key combine fold infrastructure (the bridge's two sides) -/

namespace AMap

variable {K : Type u} {V : Type v} [TotalOrd K]

/-- `find` distributes over the iterated `merge`: the value at `k` after joining a
    list of maps left-to-right is the running `optCombine` of each map's value at
    `k`. This is the merge fold's per-key reduction, made explicit — the RHS of
    the batched-construction bridge. -/
theorem find_foldl_merge (f : V → V → V) (k : K) :
    (ms : List (AMap K V)) → (acc : AMap K V) →
    (ms.foldl (AMap.merge f) acc).find k
      = (ms.map (fun m => m.find k)).foldl (optCombine f) (acc.find k)
  | [], _ => rfl
  | m :: ms, acc => by
    simp only [List.foldl_cons, List.map_cons]
    rw [find_foldl_merge f k ms (AMap.merge f acc m), find_merge]

/-- The `optCombine` swap law: from `f`'s commutativity and associativity, two
    accumulated combines may be reordered. This is the `Perm.foldl_eq'` premise. -/
theorem optCombine_right_comm {f : V → V → V}
    (hcomm : ∀ a b, f a b = f b a) (hassoc : ∀ a b c, f (f a b) c = f a (f b c))
    (z x y : Option V) :
    optCombine f (optCombine f z x) y = optCombine f (optCombine f z y) x := by
  rw [optCombine_assoc hassoc z x y, optCombine_comm hcomm x y,
    ← optCombine_assoc hassoc z y x]

/-- The per-key `optCombine` fold is permutation-invariant when `f` is a
    commutative-associative combiner — so the order in which a key's values are
    gathered (original delta order vs. sorted) does not change the result. -/
theorem foldl_optCombine_perm {f : V → V → V}
    (hcomm : ∀ a b, f a b = f b a) (hassoc : ∀ a b c, f (f a b) c = f a (f b c))
    {l1 l2 : List (Option V)} (hp : l1.Perm l2) (init : Option V) :
    l1.foldl (optCombine f) init = l2.foldl (optCombine f) init :=
  hp.foldl_eq' (fun x _ y _ z => optCombine_right_comm hcomm hassoc z x y) init

end AMap

/-! ## The near-linear canonical builder — `mergeSort` then an adjacent collapse -/

namespace AssocList

variable {K : Type u} {V : Type v} [TotalOrd K]

/-- A strict order from `≤` and `≠` — the collapsed list has strictly ascending
    keys because equal keys are merged away. -/
theorem lt_of_le_of_ne {a b : K} (hle : le a b) (hne : a ≠ b) : lt a b :=
  ⟨hle, fun hba => hne (le_antisymm hle hba)⟩

/-- `lt` absorbs a `≤` on the right — used to push the emitted head's strict
    bound through the rest of the collapsed tail. -/
theorem lt_of_lt_of_le {a b c : K} (h1 : lt a b) (h2 : le b c) : lt a c :=
  ⟨le_trans h1.1 h2, fun hca => h1.2 (le_trans h2 hca)⟩

/-- The key comparator `mergeSort` uses before the collapse. -/
def keyLe (p q : K × V) : Bool := decide (le p.1 q.1)

theorem keyLe_trans (a b c : K × V) : keyLe a b → keyLe b c → keyLe a c := by
  unfold keyLe
  intro h1 h2
  rw [decide_eq_true_iff] at h1 h2 ⊢
  exact le_trans h1 h2

theorem keyLe_total (a b : K × V) : keyLe a b || keyLe b a := by
  unfold keyLe
  rcases le_total a.1 b.1 with h | h
  · rw [decide_eq_true_iff.mpr h]; rfl
  · rw [decide_eq_true_iff.mpr h, Bool.or_true]

/-- Combine adjacent equal-key entries on a key-sorted list, folding values
    left-to-right with `f`. On a `keyLe`-sorted input every key's entries are
    adjacent, so this groups each key exactly once. -/
def collapseGo (f : V → V → V) (k : K) (acc : V) : List (K × V) → List (K × V)
  | [] => [(k, acc)]
  | (k', v') :: rest =>
    if k = k' then collapseGo f k (f acc v') rest
    else (k, acc) :: collapseGo f k' v' rest

/-- Collapse a key-sorted entry list to a canonical (unique-key) one. -/
def collapse (f : V → V → V) : List (K × V) → List (K × V)
  | [] => []
  | (k, v) :: rest => collapseGo f k v rest

/-- Every key in a collapse run is `≥` the run's lower bound `b` (≤ the run key
    and ≤ every input key). The frame lemma for the strict `Sorted` invariant. -/
theorem collapseGo_keys_bound {f : V → V → V} (b : K) :
    {rest : List (K × V)} → {k : K} → {acc : V} →
    le b k → (∀ q ∈ rest, le b q.1) →
    ∀ p ∈ collapseGo f k acc rest, le b p.1
  | [], k, acc, hbk, _ => by
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact hbk
  | (k', v') :: rest', k, acc, hbk, hrest => by
    intro p hp
    have hbk' : le b k' := hrest (k', v') (List.mem_cons_self ..)
    have hrest' : ∀ q ∈ rest', le b q.1 := fun q hq => hrest q (List.mem_cons_of_mem _ hq)
    unfold collapseGo at hp
    split at hp
    · exact collapseGo_keys_bound b hbk hrest' p hp
    · rcases List.mem_cons.mp hp with rfl | hp'
      · exact hbk
      · exact collapseGo_keys_bound b hbk' hrest' p hp'

/-- A collapse run is strictly key-sorted, given the run key bounds the rest and
    the rest is `le`-pairwise (what `mergeSort` delivers). -/
theorem collapseGo_sorted {f : V → V → V} :
    {rest : List (K × V)} → {k : K} → {acc : V} →
    (∀ q ∈ rest, le k q.1) → rest.Pairwise (fun a b => le a.1 b.1) →
    Sorted (collapseGo f k acc rest)
  | [], k, acc, _, _ => ⟨nofun, trivial⟩
  | (k', v') :: rest', k, acc, hk, hp => by
    have hkk' : le k k' := hk (k', v') (List.mem_cons_self ..)
    have hp' : rest'.Pairwise (fun a b => le a.1 b.1) := (List.pairwise_cons.mp hp).2
    have hk'rest' : ∀ q ∈ rest', le k' q.1 :=
      fun q hq => (List.pairwise_cons.mp hp).1 q hq
    unfold collapseGo
    split
    · rename_i hkeq
      -- k = k': same run continues; rest' bounded by k = k'
      exact collapseGo_sorted (hkeq ▸ hk'rest') hp'
    · rename_i hkne
      -- k < k': emit (k, acc), then the k' run
      refine ⟨?_, collapseGo_sorted hk'rest' hp'⟩
      have hltkk' : lt k k' := lt_of_le_of_ne hkk' hkne
      intro p hp''
      exact lt_of_lt_of_le hltkk'
        (collapseGo_keys_bound k' (le_refl k') hk'rest' p hp'')

theorem collapse_sorted {f : V → V → V} :
    {entries : List (K × V)} → entries.Pairwise (fun a b => le a.1 b.1) →
    Sorted (collapse f entries)
  | [], _ => trivial
  | (k, v) :: rest, hp => by
    have hkrest : ∀ q ∈ rest, le k q.1 := fun q hq => (List.pairwise_cons.mp hp).1 q hq
    exact collapseGo_sorted hkrest (List.pairwise_cons.mp hp).2

/-- `mergeSort` by key produces a `le`-pairwise list (its `keyLe`-pairwise output
    re-read as the `Prop` key order). -/
theorem pairwise_le_mergeSort (entries : List (K × V)) :
    (entries.mergeSort keyLe).Pairwise (fun a b => le a.1 b.1) := by
  have h := List.pairwise_mergeSort (le := keyLe)
    (fun a b c => keyLe_trans a b c) (fun a b => keyLe_total a b) entries
  refine h.imp ?_
  intro a b hab
  exact of_decide_eq_true hab

end AssocList

namespace AMap

variable {K : Type u} {V : Type v} [TotalOrd K]

/-- Build a canonical map from raw entries by sorting on key and collapsing
    adjacent equal keys with `f` (one O(N log N) pass — the batched cold fold). -/
def ofEntries (f : V → V → V) (entries : List (K × V)) : AMap K V :=
  ⟨AssocList.collapse f (entries.mergeSort AssocList.keyLe),
   AssocList.collapse_sorted (AssocList.pairwise_le_mergeSort entries)⟩

end AMap

end Tl.Crdt
