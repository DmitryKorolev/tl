/-
`Tl.Kernel.CloseMono` — close-monotonicity (ADR-0004 thm 7).

Closing an issue only ever *unblocks*: `ready (apply s close_i) ⊇ ready s \ {i}`.
We prove it for `close --as cancelled` (`setFields i {status := Cancelled}`), which
is monotone for *any* issue — a `cancelled` write moves the stored status toward
closed and, by manual-cancel precedence, an epic too (the `--as done` case is the
same argument but restricted to non-epics, since an epic's `done` is derived).

The crux is that closing is monotone on `effectiveStatus`: a status moving toward
closed only moves any ancestor epic's rollup toward done. This is an induction on
the rollup fuel; everything else (issues, edges, other issues' status) is fixed by
the `setFields` delta, so no blocked dependent can be newly blocked.
-/
import Tl.Kernel.Frame

namespace Tl.Kernel

open Tl.Crdt

/-- The cancel op. -/
def cancelOp (i : IssueId) (st : Stamp) : Op :=
  Op.setFields i st { status := some Status.Cancelled }

/-! ## Data preservation -/

/-- A `setFields i` leaves every *other* issue's data untouched. -/
theorem setFields_issueData_ne (s : State) (i : IssueId) (st : Stamp) (w : ScalarWrites)
    {k : IssueId} (hk : k ≠ i) :
    (apply s (Op.setFields i st w)).issueData k = s.issueData k := by
  show ((AMap.merge IssueData.merge s.data (AMap.singleton i (Op.scalarData st w))).find k).getD
      IssueData.empty = (s.data.find k).getD IssueData.empty
  rw [AMap.find_merge, AMap.find_singleton, ite_eq_right hk, optCombine_none_right]

/-- A `setFields i` sets each of `i`'s registers to the merge of the old
    register and the written value — stated once for any register projection
    that distributes over `IssueData.merge` (every field of the fieldwise merge
    does, by `rfl`), so per-register instances need no per-field proof clone. -/
theorem setFields_reg_i (s : State) (i : IssueId) (st : Stamp) (w : ScalarWrites)
    {V : Type} [TotalOrd V] (f : IssueData → Reg V)
    (hmerge : ∀ a b, f (IssueData.merge a b) = Reg.merge (f a) (f b))
    (hempty : f IssueData.empty = none) :
    f ((apply s (Op.setFields i st w)).issueData i)
      = Reg.merge (f (s.issueData i)) (f (Op.scalarData st w)) := by
  show f (((AMap.merge IssueData.merge s.data (AMap.singleton i (Op.scalarData st w))).find i).getD
      IssueData.empty)
    = Reg.merge (f ((s.data.find i).getD IssueData.empty)) (f (Op.scalarData st w))
  rw [AMap.find_merge, AMap.find_singleton, ite_eq_left rfl]
  cases s.data.find i with
  | none =>
    rw [Option.getD_none, hempty, Reg.merge_none_left]
    rfl
  | some d0 =>
    exact hmerge d0 (Op.scalarData st w)

/-- A `setFields i` sets `i`'s status register to the merge of the old register and
    the written value. -/
theorem setFields_status_i (s : State) (i : IssueId) (st : Stamp) (w : ScalarWrites) :
    ((apply s (Op.setFields i st w)).issueData i).status
      = Reg.merge (s.issueData i).status (Op.scalarData st w).status :=
  setFields_reg_i s i st w (fun d => d.status) (fun _ _ => rfl) rfl

/-! ## Status monotonicity under cancel -/

/-- After a cancel, `i`'s materialized status is either unchanged or `Cancelled`. -/
theorem cancel_statusOf_i (s : State) (i : IssueId) (st : Stamp) :
    ((apply s (cancelOp i st)).issueData i).statusOf = (s.issueData i).statusOf
    ∨ ((apply s (cancelOp i st)).issueData i).statusOf = Status.Cancelled := by
  unfold cancelOp
  unfold IssueData.statusOf
  rw [setFields_status_i s i st { status := some Status.Cancelled }]
  rcases Reg.merge_value_cases (s.issueData i).status
      (Op.scalarData st { status := some Status.Cancelled }).status with hc | hc
  · exact Or.inl (by rw [hc])
  · exact Or.inr (by rw [hc]; rfl)

/-- Cancel is monotone on materialized status: closed stays closed. -/
theorem cancel_statusOf_mono (s : State) (i : IssueId) (st : Stamp) (k : IssueId) :
    Status.closed ((s.issueData k).statusOf) →
    Status.closed (((apply s (cancelOp i st)).issueData k).statusOf) := by
  by_cases hk : k = i
  · subst hk
    rcases cancel_statusOf_i s k st with h | h
    · rw [h]; exact id
    · rw [h]; exact fun _ => rfl
  · unfold cancelOp; rw [setFields_issueData_ne s i st _ hk]; exact id

/-- Cancel preserves a manual `Cancelled`. -/
theorem cancel_statusOf_cancelled (s : State) (i : IssueId) (st : Stamp) (k : IssueId) :
    (s.issueData k).statusOf = Status.Cancelled →
    ((apply s (cancelOp i st)).issueData k).statusOf = Status.Cancelled := by
  by_cases hk : k = i
  · subst hk
    rcases cancel_statusOf_i s k st with h | h
    · rw [h]; exact id
    · rw [h]; exact fun _ => rfl
  · unfold cancelOp; rw [setFields_issueData_ne s i st _ hk]; exact id

/-! ## effectiveStatus monotonicity (the rollup) -/

/-- If status moves only toward closed (and `Cancelled` is preserved, children
    fixed), the rollup moves only toward done — closed stays closed. -/
theorem effStatusAux_mono {s s' : State}
    (hpc : ∀ b, s'.presentChildren b = s.presentChildren b)
    (hmono : ∀ k, Status.closed ((s.issueData k).statusOf) → Status.closed ((s'.issueData k).statusOf))
    (hcanc : ∀ k, (s.issueData k).statusOf = Status.Cancelled →
      (s'.issueData k).statusOf = Status.Cancelled) :
    (fuel : Nat) → (b : IssueId) →
    Status.closed (s.effStatusAux fuel b) = true → Status.closed (s'.effStatusAux fuel b) = true
  | 0, b => by
    intro hcl
    simp only [State.effStatusAux] at hcl ⊢
    by_cases hB : (s.issueData b).statusOf = Status.Cancelled
    · rw [ite_eq_left (hcanc b hB)]; rfl
    · rw [ite_eq_right hB] at hcl
      by_cases hB' : (s'.issueData b).statusOf = Status.Cancelled
      · rw [ite_eq_left hB']; rfl
      · rw [ite_eq_right hB', hpc b]
        by_cases hemp : (s.presentChildren b).isEmpty = true
        · rw [ite_eq_left hemp] at hcl ⊢; exact hmono b hcl
        · rw [ite_eq_right hemp] at hcl
          simp only [Status.closed] at hcl
          exact Bool.noConfusion hcl
  | fuel + 1, b => by
    intro hcl
    simp only [State.effStatusAux] at hcl ⊢
    by_cases hB : (s.issueData b).statusOf = Status.Cancelled
    · rw [ite_eq_left (hcanc b hB)]; rfl
    · rw [ite_eq_right hB] at hcl
      by_cases hB' : (s'.issueData b).statusOf = Status.Cancelled
      · rw [ite_eq_left hB']; rfl
      · rw [ite_eq_right hB', hpc b]
        by_cases hemp : (s.presentChildren b).isEmpty = true
        · rw [ite_eq_left hemp] at hcl ⊢; exact hmono b hcl
        · rw [ite_eq_right hemp] at hcl ⊢
          by_cases hall :
              (s.presentChildren b).all (fun c => Status.closed (s.effStatusAux fuel c)) = true
          · have hall' : (s.presentChildren b).all
                (fun c => Status.closed (s'.effStatusAux fuel c)) = true := by
              rw [List.all_eq_true] at hall ⊢
              exact fun c hc => effStatusAux_mono hpc hmono hcanc fuel c (hall c hc)
            rw [ite_eq_left hall']; rfl
          · rw [ite_eq_right hall] at hcl
            simp only [Status.closed] at hcl
            exact Bool.noConfusion hcl

/-- A cancel is monotone on `effClosed`: a discharged blocker stays discharged. -/
theorem cancel_effClosed_mono (s : State) (i : IssueId) (st : Stamp) (b : IssueId) :
    s.effClosed b = true → (apply s (cancelOp i st)).effClosed b = true := by
  have hi : (apply s (cancelOp i st)).issues = s.issues := OrSet.merge_empty_right s.issues
  have he : (apply s (cancelOp i st)).edges = s.edges := OrSet.merge_empty_right s.edges
  have hpi : (apply s (cancelOp i st)).presentIssues = s.presentIssues := by
    unfold State.presentIssues; rw [hi]
  unfold State.effClosed State.effectiveStatus
  rw [hpi]
  exact effStatusAux_mono (fun b => presentChildren_congr hi he b)
    (cancel_statusOf_mono s i st) (cancel_statusOf_cancelled s i st) _ b

/-! ## Close-monotonicity (ADR-0004 thm 7) -/

/-- **Thm 7** (close-monotonicity, cancel case): closing `i` never removes any
    *other* ready item — `ready (apply s close_i) ⊇ ready s \ {i}`. The only state
    change is `i`'s status moving toward closed, which can only *discharge*
    blockers, never create them. -/
theorem close_cancel_monotone (s : State) (i : IssueId) (st : Stamp) (now : Instant)
    {j : IssueId} (hj : j ≠ i) (hr : j ∈ s.ready now) :
    j ∈ (apply s (cancelOp i st)).ready now := by
  have hi : (apply s (cancelOp i st)).issues = s.issues := OrSet.merge_empty_right s.issues
  have he : (apply s (cancelOp i st)).edges = s.edges := OrSet.merge_empty_right s.edges
  have hdataj : (apply s (cancelOp i st)).issueData j = s.issueData j := by
    unfold cancelOp; exact setFields_issueData_ne s i st _ hj
  have hbd : ∀ b, s.blockerDischarged b = true →
      (apply s (cancelOp i st)).blockerDischarged b = true := by
    intro b hb
    unfold State.blockerDischarged at hb ⊢
    rw [Bool.or_eq_true] at hb ⊢
    rcases hb with hb | hb
    · left; rw [decide_hasIssue_congr hi b]; exact hb
    · right; exact cancel_effClosed_mono s i st b hb
  rw [mem_ready_iff] at hr ⊢
  obtain ⟨hjp, hjr⟩ := hr
  refine ⟨?_, ?_⟩
  · rw [show (apply s (cancelOp i st)).presentIssues = s.presentIssues by
      unfold State.presentIssues; rw [hi]]
    exact hjp
  · simp only [State.isReady, Bool.and_eq_true] at hjr ⊢
    obtain ⟨⟨⟨⟨hHas, hStat⟩, hEpic⟩, hDef⟩, hBlk⟩ := hjr
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [decide_hasIssue_congr hi j]; exact hHas
    · rw [hdataj]; exact hStat
    · rw [isEpic_congr hi he j]; exact hEpic
    · rw [hdataj]; exact hDef
    · rw [blockersOf_congr he j, List.all_eq_true]
      rw [List.all_eq_true] at hBlk
      exact fun b hb => hbd b (hBlk b hb)

end Tl.Kernel
