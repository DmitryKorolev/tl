/-
`Tl.Kernel.ClaimWrites` — the write-set a `claim` lowers to.

Its own leaf (imports only `Tl.Kernel.Op`) so one definition is shared by two
callers without dragging either's dependencies onto the other: the codec's
`claim → setFields` lowering (`Tl.Format.WireOp.toOp`) and the kernel's
claim-outcome proofs (`Tl.Kernel.ClaimWon`, Tl/Kernel/Claim.lean). It does not
live in `Tl.Kernel.Op`, whose deltas are verb-agnostic by design ("the kernel
never sees a verb"), nor in `Tl.Kernel.Claim`, whose proof cone the codec must
not import.
-/
import Tl.Kernel.Op

namespace Tl.Kernel

/-- The write-set a `claim` lowers to: `status := InProgress` and
    `assignee := actor`, both at the op's one stamp. Shared verbatim by the
    codec's `claim → setFields` lowering (`Tl.Format.WireOp.toOp`) and the
    kernel's claim-outcome proofs (`ClaimWon`/`claimWonB`, Tl/Kernel/Claim.lean),
    so the lowering and the property proved about the resulting registers cannot
    drift.

    Cache-keyed op projection: what a `claim` writes is part of the ADR-0008
    verb→delta table the fold cache is keyed on, so any change to the written
    fields here must bump `Tl.Store.cacheVersion` (ADR-0022 §3) — the obligation
    stated in `WireOp.toOp`'s header, carried to the shared definition. -/
def claimWrites (actor : String) : ScalarWrites :=
  { status := some Status.InProgress, assignee := some (some actor) }

end Tl.Kernel
