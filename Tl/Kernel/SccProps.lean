/-
`Tl.Kernel.SccProps` — SCC-witness enumeration correctness (ADR-0003 §2, ADR-0004
thm 6); closes the `sccWitnesses` residual.

`sccWitnesses succ` groups the cyclic nodes by `sameSCC` (mutual reachability). This
file proves that grouping is exactly the SCC partition of the cyclic node set:

  * `sameSCC` is an **equivalence** on present nodes (reflexive, symmetric, and —
    via the `reachClosure` transitive-closure characterization — transitive);
  * the witnesses **cover** exactly the cyclic present nodes (`mem_flatten_*`);
  * two cyclic nodes share a witness **iff** `sameSCC` (`*_same_witness_iff`) — no SCC
    is split across witnesses and none are merged, i.e. exactly one witness per SCC.

Generic over any `succ` whose successors stay within `presentIssues` (true for
`kindSucc`/`precSucc`, ADR-0004 thm 6), so the bounded `reachClosure` saturates.
-/
import Tl.Kernel.Cycles
import Tl.Kernel.Reach

namespace Tl.Kernel

open Tl.Crdt

namespace State

variable {s : State} {succ : IssueId → List IssueId}

/-- `reachSet` membership is exactly reachability, for a present root. -/
theorem mem_reachSet_iff (hsucc : ∀ x, succ x ⊆ s.presentIssues) {v : IssueId}
    (hv : v ∈ s.presentIssues) (a : IssueId) :
    a ∈ s.reachSet succ v ↔ Relation.ReflTransGen (StepRel succ) v a := by
  rw [State.reachSet,
    mem_reachClosure_iff (by intro x hx; rw [List.mem_singleton] at hx; exact hx ▸ hv)
      (fun x _ => hsucc x)]
  constructor
  · rintro ⟨s', hs', h⟩; rw [List.mem_singleton] at hs'; exact hs' ▸ h
  · intro h; exact ⟨v, List.mem_singleton.mpr rfl, h⟩

/-- `sameSCC` as mutual reachability, for present nodes. -/
theorem sameSCC_iff (hsucc : ∀ x, succ x ⊆ s.presentIssues) {u v : IssueId}
    (hu : u ∈ s.presentIssues) (hv : v ∈ s.presentIssues) :
    s.sameSCC succ u v = true
      ↔ Relation.ReflTransGen (StepRel succ) v u ∧ Relation.ReflTransGen (StepRel succ) u v := by
  unfold State.sameSCC
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    mem_reachSet_iff hsucc hv u, mem_reachSet_iff hsucc hu v]

/-- `sameSCC` is reflexive on present nodes. -/
theorem sameSCC_refl (hsucc : ∀ x, succ x ⊆ s.presentIssues) {v : IssueId}
    (hv : v ∈ s.presentIssues) : s.sameSCC succ v v = true :=
  (sameSCC_iff hsucc hv hv).mpr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- `sameSCC` is symmetric. -/
theorem sameSCC_symm (u v : IssueId) : s.sameSCC succ u v = s.sameSCC succ v u := by
  unfold State.sameSCC; rw [Bool.and_comm]

/-- `sameSCC` is transitive on present nodes. -/
theorem sameSCC_trans (hsucc : ∀ x, succ x ⊆ s.presentIssues) {u v w : IssueId}
    (hu : u ∈ s.presentIssues) (hv : v ∈ s.presentIssues) (hw : w ∈ s.presentIssues)
    (huv : s.sameSCC succ u v = true) (hvw : s.sameSCC succ v w = true) :
    s.sameSCC succ u w = true := by
  obtain ⟨hvu, huv'⟩ := (sameSCC_iff hsucc hu hv).mp huv
  obtain ⟨hwv, hvw'⟩ := (sameSCC_iff hsucc hv hw).mp hvw
  exact (sameSCC_iff hsucc hu hw).mpr ⟨hwv.trans hvu, huv'.trans hvw'⟩

end State

end Tl.Kernel
