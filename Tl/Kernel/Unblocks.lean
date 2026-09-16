/-
`Tl.Kernel.Unblocks` — `unblocks` correctness, exact and unconditional (ADR-0004 thm 10).

`unblocks s now i` is now *defined* as the true set difference
`ready (withClosed s i) \ ready s` — the issues that closing `i` newly makes ready —
where `withClosed s i` forces `i`'s materialized status to `Cancelled` (the full effect
of closing `i`, rollup ripple included). So both soundness *and* completeness are
unconditional and fall straight out of the definition (`mem_unblocks_iff`): there is no
"blocked only by `i`" heuristic to under-report indirect unblocks through epic rollup.

The earlier *local* definition was a sound under-approximation: it only credited `i`
for blockers literally equal to `i`, so it missed cases where closing `i` rolls up an
epic *ancestor* of `i` that itself blocks `j` (the epic-ripple gap — see ADR-0003 §3 /
ADR-0004 thm 10). The diff definition is exact because it re-derives readiness in the
closed world. `ready_withClosed_eq_cancel` grounds the projection in the real op: the
force-closed state agrees with `apply s (cancelOp i st)` on `ready` whenever that close
actually takes effect (its stamp wins LWW).
-/
import Tl.Kernel.CloseMono
import Tl.Kernel.RollupSpec

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ## The force-closed projection `withClosed` -/

/-- `withClosed` overrides exactly `i`'s data entry (to its old record with the status
    register forced closed). -/
theorem withClosed_issueData_i (s : State) (i : IssueId) :
    (s.withClosed i).issueData i
      = { s.issueData i with status := Reg.write ⟨0, 0, 0⟩ Status.Cancelled } := by
  show (((s.data.insert i { s.issueData i with status := Reg.write ⟨0, 0, 0⟩ Status.Cancelled }).find i).getD
      IssueData.empty) = { s.issueData i with status := Reg.write ⟨0, 0, 0⟩ Status.Cancelled }
  rw [AMap.find_insert, ite_eq_left rfl, Option.getD_some]

/-- Off `i`, `withClosed` changes nothing. -/
theorem withClosed_issueData_ne (s : State) (i j : IssueId) (h : j ≠ i) :
    (s.withClosed i).issueData j = s.issueData j := by
  show (((s.data.insert i { s.issueData i with status := Reg.write ⟨0, 0, 0⟩ Status.Cancelled }).find j).getD
      IssueData.empty) = (s.data.find j).getD IssueData.empty
  rw [AMap.find_insert, ite_eq_right h]

theorem withClosed_issues (s : State) (i : IssueId) : (s.withClosed i).issues = s.issues := rfl
theorem withClosed_edges (s : State) (i : IssueId) : (s.withClosed i).edges = s.edges := rfl

/-- `i`'s forced status materializes as `Cancelled`. -/
theorem withClosed_statusOf_i (s : State) (i : IssueId) :
    ((s.withClosed i).issueData i).statusOf = Status.Cancelled := by
  rw [withClosed_issueData_i]; rfl

/-- `withClosed` leaves `i`'s priority/defer registers untouched (only status changes). -/
theorem withClosed_priorityOf_i (s : State) (i : IssueId) :
    ((s.withClosed i).issueData i).priorityOf = (s.issueData i).priorityOf := by
  rw [withClosed_issueData_i]; rfl

theorem withClosed_deferUntilOf_i (s : State) (i : IssueId) :
    ((s.withClosed i).issueData i).deferUntilOf = (s.issueData i).deferUntilOf := by
  rw [withClosed_issueData_i]; rfl

/-- Closing `i` discharges `i` in the projected state (manual-cancel precedence). -/
theorem effClosed_withClosed_i (s : State) (i : IssueId) : (s.withClosed i).effClosed i = true := by
  unfold State.effClosed
  rw [effectiveStatus_cancelled (s.withClosed i) i (withClosed_statusOf_i s i)]; rfl

/-! ## Exact, unconditional characterization -/

/-- **`unblocks` correctness (exact, unconditional).** `j` is reported iff closing `i`
    newly makes `j` ready — ready in the force-closed projection but not in `s`. Both
    soundness and completeness, by definition; the epic-rollup ripple is captured. -/
theorem mem_unblocks_iff (s : State) (now : Instant) (i j : IssueId) :
    j ∈ s.unblocks now i ↔ j ∈ (s.withClosed i).ready now ∧ j ∉ s.ready now := by
  simp only [State.unblocks, List.mem_filter, decide_eq_true_eq]

/-- Soundness: a reported issue is genuinely not ready now. -/
theorem unblocks_not_ready (s : State) (now : Instant) (i j : IssueId)
    (hj : j ∈ s.unblocks now i) : j ∉ s.ready now :=
  ((mem_unblocks_iff s now i j).mp hj).2

/-- Soundness: a reported issue is ready in the force-closed projection. -/
theorem unblocks_mem_readyClosed (s : State) (now : Instant) (i j : IssueId)
    (hj : j ∈ s.unblocks now i) : j ∈ (s.withClosed i).ready now :=
  ((mem_unblocks_iff s now i j).mp hj).1

/-! ## Operational grounding: the projection equals a winning close -/

/-- The force-closed projection agrees with the real cancel on `ready`, whenever the
    cancel actually discharges `i` (its stamp wins LWW). The two states then have the
    same materialized status everywhere and the same priority/defer registers (the
    cancel writes only `i`'s status, the projection forces only `i`'s status), so the
    frame congruence `ready_congr` applies. -/
theorem ready_withClosed_eq_cancel (s : State) (i : IssueId) (st : Stamp) (now : Instant)
    (hwin : ((apply s (cancelOp i st)).issueData i).statusOf = Status.Cancelled) :
    (s.withClosed i).ready now = (apply s (cancelOp i st)).ready now := by
  have hdata_ne : ∀ k, k ≠ i → (apply s (cancelOp i st)).issueData k = s.issueData k := by
    intro k hk; unfold cancelOp; exact setFields_issueData_ne s i st _ hk
  have hprio_i : ((apply s (cancelOp i st)).issueData i).priorityOf = (s.issueData i).priorityOf :=
    congrArg (fun r => r.value.getD (2 : Fin 5))
      (reg_mergeSingleton IssueData.priority (fun _ _ => rfl) rfl s.data i
        (Op.scalarData st { status := some Status.Cancelled }) rfl i)
  have hdefer_i : ((apply s (cancelOp i st)).issueData i).deferUntilOf = (s.issueData i).deferUntilOf :=
    congrArg (fun r => r.value.getD none)
      (reg_mergeSingleton IssueData.deferUntil (fun _ _ => rfl) rfl s.data i
        (Op.scalarData st { status := some Status.Cancelled }) rfl i)
  refine ready_congr ?_ ?_ ?_ ?_ ?_ now
  · rw [withClosed_issues]; exact (OrSet.merge_empty_right s.issues).symm
  · rw [withClosed_edges]; exact (OrSet.merge_empty_right s.edges).symm
  · intro k
    by_cases hk : k = i
    · subst hk; rw [withClosed_statusOf_i, hwin]
    · rw [withClosed_issueData_ne s i k hk, hdata_ne k hk]
  · intro k
    by_cases hk : k = i
    · subst hk; rw [withClosed_priorityOf_i, hprio_i]
    · rw [withClosed_issueData_ne s i k hk, hdata_ne k hk]
  · intro k
    by_cases hk : k = i
    · subst hk; rw [withClosed_deferUntilOf_i, hdefer_i]
    · rw [withClosed_issueData_ne s i k hk, hdata_ne k hk]

/-- **Operationally grounded characterization**: when closing `i` takes effect (the
    cancel stamp wins LWW), `j` is reported iff `j` becomes ready under the real op
    `apply s (cancelOp i st)` and was not ready before — exact, unconditional. -/
theorem mem_unblocks_iff_cancel (s : State) (now : Instant) (i j : IssueId) (st : Stamp)
    (hwin : ((apply s (cancelOp i st)).issueData i).statusOf = Status.Cancelled) :
    j ∈ s.unblocks now i ↔ j ∈ (apply s (cancelOp i st)).ready now ∧ j ∉ s.ready now := by
  rw [mem_unblocks_iff, ready_withClosed_eq_cancel s i st now hwin]

end State

end Tl.Kernel
