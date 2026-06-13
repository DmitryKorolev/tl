/-
`Tl.Kernel.Apply` — the single total reducer and the fold (ADR-0004).

`apply s op = State.merge s op.delta`: there is exactly one mutation path, and it
is a join with the op's delta. So the two convergence properties fall straight out
of the state semilattice (ADR-0004 thm 1):

* operations **commute** (`apply_left_comm`) — the seed of fold order-insensitivity
  (thm 2);
* operations are **idempotent on re-delivery** (`apply_idem`) — at-least-once
  delivery is safe (thm 8).

The full fold theorems are assembled in `Tl.Kernel.Theorems`; the per-op laws live
here next to the definition they characterize.
-/
import Tl.Kernel.Op

namespace Tl.Kernel

open Tl.Crdt

/-- The single reducer: join the op's delta into the state (total). A change to
    how an `Op` maps to its delta (here or in `Op.delta`) must bump
    `Tl.Store.cacheVersion` — the cache persists folded state (Cache.lean header). -/
def apply (s : State) (op : Op) : State := State.merge s op.delta

/-- Materialization: fold the ops over the empty state (ADR-0001). -/
def fold (ops : List Op) : State := ops.foldl apply State.empty

@[simp] theorem apply_def (s : State) (op : Op) : apply s op = State.merge s op.delta := rfl

/-- Operations commute — the per-op core of fold order-insensitivity (thm 2). -/
theorem apply_left_comm (s : State) (o1 o2 : Op) :
    apply (apply s o1) o2 = apply (apply s o2) o1 := by
  show State.merge (State.merge s o1.delta) o2.delta
     = State.merge (State.merge s o2.delta) o1.delta
  rw [State.merge_assoc, State.merge_assoc, State.merge_comm o1.delta o2.delta]

/-- Re-applying the same op changes nothing — at-least-once delivery is safe (thm
    8); the segment union / worktree local-leg may re-deliver a line (ADR-0001/0016). -/
theorem apply_idem (s : State) (o : Op) : apply (apply s o) o = apply s o := by
  show State.merge (State.merge s o.delta) o.delta = State.merge s o.delta
  rw [State.merge_assoc, State.merge_idem]

end Tl.Kernel
