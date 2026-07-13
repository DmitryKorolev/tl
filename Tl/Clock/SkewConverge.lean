/-
`Tl.Clock.SkewConverge` — the convergence-safety corollary of the HLC skew
window (ADR-0007 skew window), composing the pure admission lemmas
(`Tl.Clock.Skew`) with the kernel's set-insensitive fold (`fold_eq_of_mem_iff`).

Split from `Tl.Clock.Skew` so the predicate + monotonicity stay kernel-free
(the shell's `Tl/Store/Materialize` imports only those); this file is the one
place the skew filter meets the verified fold. Pure; no I/O.
-/
import Tl.Clock.Skew
import Tl.Kernel.Theorems

namespace Tl.Clock.Skew

open Tl.Kernel

/-- **Convergence-safety of the skew window.** Two replicas that have observed
    the same op *set* and whose clocks have both passed every op's physical time
    materialize identical state — the deferral changed nothing in the limit.
    The filter is the identity past the threshold (`filter_admittedB_eq_self`),
    so this reduces to the kernel's set-insensitive fold (`fold_eq_of_mem_iff`).

    Instantiate at `α := ParsedOp`, `phys := (·.stamp.hlc)`, `toOp :=
    ParsedOp.kernelOp` for the real `(filter ∘ map ∘ fold)` pipeline
    (`Tl/Store/Materialize`). Holds for any window `W` — convergence is
    window-independent — and regardless of clock accuracy: a wrong clock changes
    only *when* an op appears, never the eventual state. -/
theorem skew_converges {α} (phys : α → Nat) (toOp : α → Op)
    (la lb : List α) (nowA nowB W : Nat)
    (hset : ∀ o, o ∈ la.map toOp ↔ o ∈ lb.map toOp)
    (hA : ∀ a ∈ la, phys a / 2 ^ 16 ≤ nowA)
    (hB : ∀ a ∈ lb, phys a / 2 ^ 16 ≤ nowB) :
    fold ((la.filter (fun a => admittedB (phys a) (nowA + W))).map toOp)
      = fold ((lb.filter (fun a => admittedB (phys a) (nowB + W))).map toOp) := by
  rw [filter_admittedB_eq_self phys la nowA W hA,
      filter_admittedB_eq_self phys lb nowB W hB]
  exact fold_eq_of_mem_iff hset

end Tl.Clock.Skew
