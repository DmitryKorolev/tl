/-
`Tl.Kernel.Unblocks` — `unblocks` soundness (ADR-0004 thm 10).

`unblocks s now i` lists `i`'s live dependents that, in the current state, are blocked
*only* by `i`. This file proves the **safe** half of its correctness:

  * `unblocks_not_ready` — every reported issue is genuinely not-yet-ready
    (unconditional);
  * `unblocks_sound` — every reported issue *does* become ready once `i` is closed,
    given the close actually discharges `i` (its cancel stamp wins LWW —
    `(apply s (cancelOp i st)).effClosed i`) and the reported issue is not `i` itself.

Both hypotheses are necessary, not incidental: a cancel whose stamp loses leaves `i`
open (so nothing it "unblocks" becomes ready), and a self-blocking `i` cannot ready
itself by closing. The matching **completeness** (`newly ready ⇒ reported`) is the
remaining residual — it fails when a *different* blocker is an epic ancestor of `i`
that rolls up to done as `i` closes, so it holds only under a no-epic-ancestor-blocker
side condition (overview Proof status). Reuses the close-monotonicity machinery
(`cancel_effClosed_mono`) and the frame congruences.
-/
import Tl.Kernel.CloseMono

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-- Every reported unblock is genuinely not ready in the current state (the filter's
    `!isReady` conjunct); unconditional. -/
theorem unblocks_not_ready (s : State) (now : Instant) (i j : IssueId)
    (hj : j ∈ s.unblocks now i) : j ∉ s.ready now := by
  unfold State.unblocks at hj
  rw [List.mem_filter] at hj
  have hfilt : (decide (i ∈ s.blockersOf j) && !s.isReady now j
      && s.wouldReadyOnClose now i j) = true := hj.2
  rw [Bool.and_eq_true, Bool.and_eq_true] at hfilt
  have hnr : (!s.isReady now j) = true := hfilt.1.2
  rw [mem_ready_iff]
  rintro ⟨_, hr⟩
  rw [hr, Bool.not_true] at hnr
  exact Bool.noConfusion hnr

/-- **Soundness**: a reported unblock `j ≠ i` becomes ready once closing `i` actually
    discharges it (the cancel stamp wins LWW). The only state change is `i`'s status,
    so every conjunct of `j`'s readiness is preserved or newly satisfied: `i`-blockers
    discharge by `hdis`, other blockers by close-monotonicity. -/
theorem unblocks_sound (s : State) (now : Instant) (i j : IssueId) (st : Stamp)
    (hj : j ∈ s.unblocks now i) (hji : j ≠ i)
    (hdis : (apply s (cancelOp i st)).effClosed i = true) :
    j ∈ (apply s (cancelOp i st)).ready now := by
  unfold State.unblocks at hj
  rw [List.mem_filter] at hj
  have hjp : j ∈ s.presentIssues := hj.1
  have hfilt : (decide (i ∈ s.blockersOf j) && !s.isReady now j
      && s.wouldReadyOnClose now i j) = true := hj.2
  rw [Bool.and_eq_true, Bool.and_eq_true] at hfilt
  have hwr : s.wouldReadyOnClose now i j = true := hfilt.2
  unfold State.wouldReadyOnClose at hwr
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hwr
  obtain ⟨⟨⟨⟨hHas, hStat⟩, hEpic⟩, hDef⟩, hBlk⟩ := hwr
  -- frame facts: the cancel touches only `i`'s data
  have hi : (apply s (cancelOp i st)).issues = s.issues := OrSet.merge_empty_right s.issues
  have he : (apply s (cancelOp i st)).edges = s.edges := OrSet.merge_empty_right s.edges
  have hdataj : (apply s (cancelOp i st)).issueData j = s.issueData j := by
    unfold cancelOp; exact setFields_issueData_ne s i st _ hji
  have hbd : ∀ b, s.blockerDischarged b = true →
      (apply s (cancelOp i st)).blockerDischarged b = true := by
    intro b hb
    unfold State.blockerDischarged at hb ⊢
    rw [Bool.or_eq_true] at hb ⊢
    rcases hb with hb | hb
    · left; rw [decide_hasIssue_congr hi b]; exact hb
    · right; exact cancel_effClosed_mono s i st b hb
  have hbi : (apply s (cancelOp i st)).blockerDischarged i = true := by
    unfold State.blockerDischarged; rw [Bool.or_eq_true]; right; exact hdis
  rw [mem_ready_iff]
  refine ⟨?_, ?_⟩
  · rw [show (apply s (cancelOp i st)).presentIssues = s.presentIssues by
      unfold State.presentIssues; rw [hi]]
    exact hjp
  · simp only [State.isReady, Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [decide_hasIssue_congr hi j]; exact hHas
    · rw [hdataj]; exact hStat
    · rw [isEpic_congr hi he j]; exact hEpic
    · rw [hdataj]; exact hDef
    · rw [blockersOf_congr he j, List.all_eq_true]
      intro b hb
      rw [List.all_eq_true] at hBlk
      have hbor : (decide (b = i) || s.blockerDischarged b) = true := hBlk b hb
      rw [Bool.or_eq_true] at hbor
      rcases hbor with hbeq | hbd'
      · rw [of_decide_eq_true hbeq]; exact hbi
      · exact hbd b hbd'

end State

end Tl.Kernel
