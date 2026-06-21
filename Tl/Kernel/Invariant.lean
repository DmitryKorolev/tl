/-
`Tl.Kernel.Invariant` — the kernel invariant (ADR-0004 thm 3).

`Invariant` asserts exactly one thing: every status is a valid enum value (plus
the intra-issue type-level invariants). Because `status : Reg Status` and
`priority : Reg (Fin 5)` make illegal values *unrepresentable*, the invariant has
no dynamic content — it holds by construction and `apply` preserves it for free.
That is the *stronger* guarantee the ADR intends: not "we check status is valid"
but "an invalid status cannot be built." So `Invariant := True` is the faithful
encoding, and theorem 3 (`Invariant s → Invariant (apply s op)`) is discharged by
the type system, inherited by every op (there is one reducer).

Three things are deliberately not invariants, each because an order-insensitive
fold cannot maintain them and a CRDT merge cannot reject a write (ADR-0003/0004):
acyclicity (reported via `dep cycles`), endpoint-existence of `blocks`/`parent`
edges (dangling edges tolerated as inert at read time), and status-transition
legality (a local courtesy guard only).
-/
import Tl.Kernel.Apply

namespace Tl.Kernel

/-- The kernel invariant: valid status (type-level, hence trivially true). -/
def Invariant (_ : State) : Prop := True

theorem invariant_empty : Invariant State.empty := trivial

/-- Invariant preservation (ADR-0004 thm 3), proved once over `apply`, inherited
    by every op — the type system does the work. -/
theorem invariant_apply (s : State) (op : Op) : Invariant s → Invariant (apply s op) :=
  fun _ => trivial

end Tl.Kernel
