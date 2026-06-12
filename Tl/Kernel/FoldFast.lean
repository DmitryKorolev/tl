/-
`Tl.Kernel.FoldFast` — the near-linear cold materialization fold.

`fold` joins the per-op deltas one at a time (`fold_eq_joinAll`), each a
positional `insertWith` — Θ(ops × keys) on a cold rebuild. `foldFast` builds the
same state by joining every delta's component maps in one batched pass
(`AMap.joinFast`: `mergeSort` + adjacent collapse, O(N log N)). The bridge
`foldFast_eq_fold` makes them EQUAL, so every `fold` theorem (ADR-0004 thm 1/2/8)
transfers to the shipped cold path with no re-proof.

The lift is componentwise: `State.merge`/`OrSet.merge` are componentwise joins,
so the left-folded merge of the deltas equals the per-component batched join,
each combiner a semilattice (`IssueData.merge`, `FinSet.union`, the trivial
`Unit` join). Pure; no I/O. No Mathlib (ADR-0009).
-/
import Tl.Kernel.Theorems
import Tl.Crdt.MapFold

namespace Tl.Crdt

open TotalOrd

/-! ## OR-Set batched join -/

namespace OrSet

variable {α : Type u} [TotalOrd α]

theorem foldl_merge_adds : (os : List (OrSet α)) → (acc : OrSet α) →
    (os.foldl merge acc).adds
      = (os.map (fun o => o.adds)).foldl (AMap.merge FinSet.union) acc.adds
  | [], _ => rfl
  | o :: os, acc => by
    simp only [List.foldl_cons, List.map_cons]
    exact foldl_merge_adds os (merge acc o)

theorem foldl_merge_removed : (os : List (OrSet α)) → (acc : OrSet α) →
    (os.foldl merge acc).removed
      = (os.map (fun o => o.removed)).foldl FinSet.union acc.removed
  | [], _ => rfl
  | o :: os, acc => by
    simp only [List.foldl_cons, List.map_cons]
    exact foldl_merge_removed os (merge acc o)

/-- The batched OR-Set join: combine all add-maps and all tombstone sets at once. -/
def joinFast (os : List (OrSet α)) : OrSet α :=
  ⟨AMap.joinFast FinSet.union (os.map (fun o => o.adds)),
   AMap.joinFast (fun _ _ => ()) (os.map (fun o => o.removed))⟩

theorem joinFast_eq (os : List (OrSet α)) : joinFast os = os.foldl merge OrSet.empty := by
  apply OrSet.ext
  · show AMap.joinFast FinSet.union (os.map (fun o => o.adds)) = (os.foldl merge OrSet.empty).adds
    rw [AMap.joinFast_eq (fun a b => FinSet.union_comm a b)
        (fun a b c => FinSet.union_assoc a b c), foldl_merge_adds os OrSet.empty]
    rfl
  · show AMap.joinFast (fun _ _ => ()) (os.map (fun o => o.removed))
        = (os.foldl merge OrSet.empty).removed
    rw [AMap.joinFast_eq (f := fun _ _ => ()) (fun _ _ => rfl) (fun _ _ _ => rfl),
      foldl_merge_removed os OrSet.empty]
    rfl

end OrSet

end Tl.Crdt

/-! ## The state-level batched fold -/

namespace Tl.Kernel

open Tl.Crdt

namespace State

theorem foldl_merge_issues : (ss : List State) → (acc : State) →
    (ss.foldl State.merge acc).issues
      = (ss.map (fun s => s.issues)).foldl OrSet.merge acc.issues
  | [], _ => rfl
  | s :: ss, acc => by
    simp only [List.foldl_cons, List.map_cons]
    exact foldl_merge_issues ss (State.merge acc s)

theorem foldl_merge_data : (ss : List State) → (acc : State) →
    (ss.foldl State.merge acc).data
      = (ss.map (fun s => s.data)).foldl (AMap.merge IssueData.merge) acc.data
  | [], _ => rfl
  | s :: ss, acc => by
    simp only [List.foldl_cons, List.map_cons]
    exact foldl_merge_data ss (State.merge acc s)

theorem foldl_merge_edges : (ss : List State) → (acc : State) →
    (ss.foldl State.merge acc).edges
      = (ss.map (fun s => s.edges)).foldl OrSet.merge acc.edges
  | [], _ => rfl
  | s :: ss, acc => by
    simp only [List.foldl_cons, List.map_cons]
    exact foldl_merge_edges ss (State.merge acc s)

end State

/-- The near-linear cold fold: join every per-op delta's component maps in one
    batched (`mergeSort` + collapse) pass per component. -/
def foldFast (ops : List Op) : State :=
  let ds := ops.map Op.delta
  ⟨OrSet.joinFast (ds.map (fun s => s.issues)),
   AMap.joinFast IssueData.merge (ds.map (fun s => s.data)),
   OrSet.joinFast (ds.map (fun s => s.edges))⟩

/-- **The bridge.** The batched cold fold IS `fold` — every fold theorem transfers. -/
theorem foldFast_eq_fold (ops : List Op) : foldFast ops = fold ops := by
  rw [fold_eq_joinAll]
  apply State.ext
  · show OrSet.joinFast ((ops.map Op.delta).map (fun s => s.issues))
        = (joinAll (ops.map Op.delta)).issues
    rw [OrSet.joinFast_eq]
    exact (State.foldl_merge_issues (ops.map Op.delta) State.empty).symm
  · show AMap.joinFast IssueData.merge ((ops.map Op.delta).map (fun s => s.data))
        = (joinAll (ops.map Op.delta)).data
    rw [AMap.joinFast_eq (fun a b => IssueData.merge_comm a b)
        (fun a b c => IssueData.merge_assoc a b c)]
    exact (State.foldl_merge_data (ops.map Op.delta) State.empty).symm
  · show OrSet.joinFast ((ops.map Op.delta).map (fun s => s.edges))
        = (joinAll (ops.map Op.delta)).edges
    rw [OrSet.joinFast_eq]
    exact (State.foldl_merge_edges (ops.map Op.delta) State.empty).symm

end Tl.Kernel
