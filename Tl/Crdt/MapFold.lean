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

end Tl.Crdt
