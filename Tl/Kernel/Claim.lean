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
import Tl.Kernel.ClaimWrites

namespace Tl.Kernel

open Tl.Crdt
open Tl.Crdt.TotalOrd

/-! ## The claim op -/

/-- The claim op: one `setFields` carrying both writes at one stamp. Its
    write-set is `Tl.Kernel.claimWrites` (Tl/Kernel/ClaimWrites.lean), shared
    with the codec's `claim → setFields` lowering so the two cannot drift. -/
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

`setFields_reg_i` (CloseMono) gives any register leg; `setFields_status_i` is
its status instance, and the assignee instance is here. -/

/-- A `setFields i` sets `i`'s assignee register to the merge of the old
    register and the written value (the `setFields_reg_i` assignee instance). -/
theorem setFields_assignee_i (s : State) (i : IssueId) (st : Stamp) (w : ScalarWrites) :
    ((apply s (Op.setFields i st w)).issueData i).assignee
      = Reg.merge (s.issueData i).assignee (Op.scalarData st w).assignee :=
  setFields_reg_i s i st w (fun d => d.assignee) (fun _ _ => rfl) rfl

/-- The claim delta's status leg is the claim's own stamped write. -/
theorem claim_scalarData_status (st : Stamp) (actor : String) :
    (Op.scalarData st (claimWrites actor)).status = Reg.write st Status.InProgress := rfl

/-- The claim delta's assignee leg is the claim's own stamped write. -/
theorem claim_scalarData_assignee (st : Stamp) (actor : String) :
    (Op.scalarData st (claimWrites actor)).assignee = Reg.write st (some actor) := rfl

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
    exact Reg.merge_write_right (fun e he => Or.inl (hs e he))
  · show ((apply s (Op.setFields i st (claimWrites actor))).issueData i).assignee = _
    rw [setFields_assignee_i, claim_scalarData_assignee]
    exact Reg.merge_write_right (fun e he => Or.inl (ha e he))

/-! ## Merge-exactness

`Reg.merge_eq_write_iff` (Lww) arbitrates a single register; the claim-level
form conjoins its two instances. -/

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
  and_congr (Reg.merge_eq_write_iff d.status f.status st Status.InProgress)
    (Reg.merge_eq_write_iff d.assignee f.assignee st (some actor))

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
