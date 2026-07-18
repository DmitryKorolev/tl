/-
`Tl.Kernel.Claim` — the claim-outcome predicate (ADR-0013).

A `claim` lowers to one `setFields` writing `status := InProgress` and
`assignee := actor` at a single stamp (ADR-0008). Whether the claim *holds* in
a materialized state is therefore a property of BOTH registers: the claim won
exactly when each register's winning entry is this claim's own write —
stamp-exact and value-exact. Deriving the outcome from the assignee register
alone misreports a concurrent close (which outstamps `status` but never writes
`assignee`) as a win — ADR-0013's independent-register anomaly, seen from the
other side.

`ClaimWon` is the propositional form; `claimWonB` the executable form the CLI
branches on (kernel proved, CLI branch tested — the ADR-0004 tiering).
`ClaimPartial` distinguishes the partial win (assignee kept, status lost) so
the shell can explain what happened; it never satisfies `ClaimWon`
(`ClaimPartial.not_won`).
-/
import Tl.Kernel.CloseMono

namespace Tl.Kernel

open Tl.Crdt
open Tl.Crdt.TotalOrd

/-! ## The claim op and its write-set -/

/-- The write-set a `claim` lowers to (the codec's `claim → setFields` row). -/
def claimWrites (actor : String) : ScalarWrites :=
  { status := some Status.InProgress, assignee := some (some actor) }

/-- The claim op: one `setFields` carrying both writes at one stamp. -/
def claimOp (i : IssueId) (st : Stamp) (actor : String) : Op :=
  Op.setFields i st (claimWrites actor)

/-! ## The outcome predicates -/

/-- Full win: both winning register entries are this claim's exact stamped
    writes — `status = (st, InProgress)` and `assignee = (st, actor)`. Any
    partial survival (one register kept, the other outstamped) fails this. -/
def ClaimWon (d : IssueData) (st : Stamp) (actor : String) : Prop :=
  d.status = Reg.write st Status.InProgress ∧ d.assignee = Reg.write st (some actor)

instance (d : IssueData) (st : Stamp) (actor : String) : Decidable (ClaimWon d st actor) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Executable form of `ClaimWon` — what `tl claim` and `show`'s claim block
    branch on. -/
def claimWonB (d : IssueData) (st : Stamp) (actor : String) : Bool :=
  decide (ClaimWon d st actor)

theorem claimWonB_iff (d : IssueData) (st : Stamp) (actor : String) :
    claimWonB d st actor = true ↔ ClaimWon d st actor :=
  ⟨of_decide_eq_true, decide_eq_true⟩

/-- Partial win: the assignee write survived but the status write lost —
    reachable when a concurrent status-only write (a close, or a skewed
    `create`'s status seed) outstamps the claim. Classified `superseded`; the
    shell uses this form to explain the outcome instead of a bare verdict. -/
def ClaimPartial (d : IssueData) (st : Stamp) (actor : String) : Prop :=
  d.assignee = Reg.write st (some actor) ∧ d.status ≠ Reg.write st Status.InProgress

instance (d : IssueData) (st : Stamp) (actor : String) : Decidable (ClaimPartial d st actor) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Executable form of `ClaimPartial`. -/
def claimPartialB (d : IssueData) (st : Stamp) (actor : String) : Bool :=
  decide (ClaimPartial d st actor)

theorem claimPartialB_iff (d : IssueData) (st : Stamp) (actor : String) :
    claimPartialB d st actor = true ↔ ClaimPartial d st actor :=
  ⟨of_decide_eq_true, decide_eq_true⟩

/-- A partial win never satisfies the full-win predicate. -/
theorem ClaimPartial.not_won {d : IssueData} {st : Stamp} {actor : String}
    (h : ClaimPartial d st actor) : ¬ ClaimWon d st actor :=
  fun hw => h.2 hw.1

/-! ## The claim delta on the issue's registers

`setFields_status_i` (CloseMono) gives the status leg; the assignee leg is its
mirror. -/

/-- A `setFields i` sets `i`'s assignee register to the merge of the old
    register and the written value (the `setFields_status_i` mirror). -/
theorem setFields_assignee_i (s : State) (i : IssueId) (st : Stamp) (w : ScalarWrites) :
    ((apply s (Op.setFields i st w)).issueData i).assignee
      = Reg.merge (s.issueData i).assignee (Op.scalarData st w).assignee := by
  show (((AMap.merge IssueData.merge s.data (AMap.singleton i (Op.scalarData st w))).find i).getD
      IssueData.empty).assignee
    = Reg.merge ((s.data.find i).getD IssueData.empty).assignee (Op.scalarData st w).assignee
  rw [AMap.find_merge, AMap.find_singleton, if_pos rfl]
  cases s.data.find i <;> rfl

/-- The claim delta's status leg is the claim's own stamped write. -/
theorem claim_scalarData_status (st : Stamp) (actor : String) :
    (Op.scalarData st (claimWrites actor)).status = Reg.write st Status.InProgress := rfl

/-- The claim delta's assignee leg is the claim's own stamped write. -/
theorem claim_scalarData_assignee (st : Stamp) (actor : String) :
    (Op.scalarData st (claimWrites actor)).assignee = Reg.write st (some actor) := rfl

/-- Merging a write that no existing entry exceeds installs that write. -/
theorem reg_merge_write_right {V : Type _} [TotalOrd V] {R : Reg V} {st : Stamp} {v : V}
    (h : ∀ e, R = some e → le e (st, v)) :
    Reg.merge R (Reg.write st v) = Reg.write st v := by
  match R with
  | none => rfl
  | some e =>
    show some (tmax e (st, v)) = some (st, v)
    unfold tmax
    rw [if_pos (h e rfl)]

/-- Establishment: folding the claim op wins when its stamp strictly dominates
    every existing entry of both registers — the fresh-write case (the HLC
    ticked past everything this replica had folded). -/
theorem claimWon_apply_of_fresh (s : State) (i : IssueId) (st : Stamp) (actor : String)
    (hs : ∀ e, (s.issueData i).status = some e → lt e.1 st)
    (ha : ∀ e, (s.issueData i).assignee = some e → lt e.1 st) :
    ClaimWon ((apply s (claimOp i st actor)).issueData i) st actor := by
  constructor
  · show ((apply s (Op.setFields i st (claimWrites actor))).issueData i).status = _
    rw [setFields_status_i, claim_scalarData_status]
    exact reg_merge_write_right (fun e he => Or.inl (hs e he))
  · show ((apply s (Op.setFields i st (claimWrites actor))).issueData i).assignee = _
    rw [setFields_assignee_i, claim_scalarData_assignee]
    exact reg_merge_write_right (fun e he => Or.inl (ha e he))

/-! ## Merge-exactness -/

/-- The merged register holds exactly the write `(st, v)` iff one side holds it
    and neither side exceeds it — the join arbitrates a write's survival
    exactly. -/
theorem reg_merge_eq_write_iff {V : Type _} [TotalOrd V] (R W : Reg V) (st : Stamp) (v : V) :
    Reg.merge R W = Reg.write st v ↔
      ((R = Reg.write st v ∨ W = Reg.write st v)
        ∧ (∀ e, R = some e → le e (st, v))
        ∧ (∀ e, W = some e → le e (st, v))) := by
  constructor
  · intro h
    match R, W with
    | none, none =>
      exact nomatch h
    | none, some w =>
      cases Option.some.inj h
      refine ⟨Or.inr rfl, ⟨fun e he => ?_, fun e he => ?_⟩⟩
      · exact nomatch he
      · cases Option.some.inj he
        exact le_refl _
    | some r, none =>
      cases Option.some.inj h
      refine ⟨Or.inl rfl, ⟨fun e he => ?_, fun e he => ?_⟩⟩
      · cases Option.some.inj he
        exact le_refl _
      · exact nomatch he
    | some r, some w =>
      have hm : tmax r w = (st, v) := Option.some.inj h
      have hler : le r (st, v) := by rw [← hm]; exact le_tmax_left r w
      have hlew : le w (st, v) := by rw [← hm]; exact le_tmax_right r w
      have hside : r = (st, v) ∨ w = (st, v) := by
        rcases tmax_eq r w with he | he
        · rw [he] at hm
          exact Or.inl hm
        · rw [he] at hm
          exact Or.inr hm
      refine ⟨?_, ⟨fun e he => ?_, fun e he => ?_⟩⟩
      · rcases hside with he | he
        · exact Or.inl (congrArg some he)
        · exact Or.inr (congrArg some he)
      · cases Option.some.inj he
        exact hler
      · cases Option.some.inj he
        exact hlew
  · intro h
    obtain ⟨hor, hR, hW⟩ := h
    match R, W with
    | none, none =>
      rcases hor with h' | h' <;>
        exact nomatch h'
    | none, some w =>
      have hw : w = (st, v) := by
        rcases hor with h' | h'
        · exact nomatch h'
        · exact Option.some.inj h'
      cases hw
      rfl
    | some r, none =>
      have hr : r = (st, v) := by
        rcases hor with h' | h'
        · exact Option.some.inj h'
        · exact nomatch h'
      cases hr
      rfl
    | some r, some w =>
      show some (tmax r w) = some (st, v)
      have h1 : le r (st, v) := hR r rfl
      have h2 : le w (st, v) := hW w rfl
      rcases hor with h' | h'
      · cases Option.some.inj h'
        unfold tmax
        by_cases hc : le (st, v) w
        · rw [if_pos hc, le_antisymm h2 hc]
        · rw [if_neg hc]
      · cases Option.some.inj h'
        unfold tmax
        rw [if_pos h1]

/-- Merge-exactness at the claim level: after any merge the claim reads won iff
    its own write is the winning entry of both registers — one side carries
    each write and nothing on either side exceeds it. Merges arbitrate the
    outcome exactly; they never blur won into superseded or back. -/
theorem claimWon_merge_iff (d f : IssueData) (st : Stamp) (actor : String) :
    ClaimWon (IssueData.merge d f) st actor ↔
      ((d.status = Reg.write st Status.InProgress ∨ f.status = Reg.write st Status.InProgress)
        ∧ (∀ e, d.status = some e → le e (st, Status.InProgress))
        ∧ (∀ e, f.status = some e → le e (st, Status.InProgress)))
      ∧ ((d.assignee = Reg.write st (some actor) ∨ f.assignee = Reg.write st (some actor))
        ∧ (∀ e, d.assignee = some e → le e (st, some actor))
        ∧ (∀ e, f.assignee = some e → le e (st, some actor))) :=
  and_congr (reg_merge_eq_write_iff d.status f.status st Status.InProgress)
    (reg_merge_eq_write_iff d.assignee f.assignee st (some actor))

/-- Preservation: a won claim stays won across a merge that brings nothing
    exceeding either of its writes. -/
theorem claimWon_merge_of_le {d : IssueData} (f : IssueData) {st : Stamp} {actor : String}
    (hw : ClaimWon d st actor)
    (hs : ∀ e, f.status = some e → le e (st, Status.InProgress))
    (ha : ∀ e, f.assignee = some e → le e (st, some actor)) :
    ClaimWon (IssueData.merge d f) st actor := by
  apply (claimWon_merge_iff d f st actor).mpr
  refine ⟨⟨Or.inl hw.1, fun e he => ?_, hs⟩, ⟨Or.inl hw.2, fun e he => ?_, ha⟩⟩
  · rw [hw.1] at he
    cases Option.some.inj he
    exact le_refl _
  · rw [hw.2] at he
    cases Option.some.inj he
    exact le_refl _

/-- Supersession is stable: once either register holds an entry strictly above
    the claim's write — a concurrent close, reopen, or steal that outstamped
    it — no further merge restores the win, because registers only move up the
    order. -/
theorem not_claimWon_merge_of_superseded (d f : IssueData) (st : Stamp) (actor : String)
    (h : (∃ e, d.status = some e ∧ lt (st, Status.InProgress) e)
       ∨ (∃ e, d.assignee = some e ∧ lt (st, some actor) e)) :
    ¬ ClaimWon (IssueData.merge d f) st actor := by
  intro hw
  obtain ⟨⟨_, hsd, _⟩, ⟨_, had, _⟩⟩ := (claimWon_merge_iff d f st actor).mp hw
  rcases h with ⟨e, he, hlt⟩ | ⟨e, he, hlt⟩
  · exact hlt.2 (hsd e he)
  · exact hlt.2 (had e he)

end Tl.Kernel
