/-
`Tl.Kernel.NotesInvariant` — the journal state invariants, discharged for
every folded state (ADR-0027).

The journal hiding theorems (`Tl.Crdt.Journal`) carry two structural
hypotheses: `SelfTagged` (an element's tag set is `⊆` its own stamp — what
makes a tombstone by tag value final) and `PayloadTotal` (every visible entry
has a payload — what makes `visibleEntries`'s skip case unreachable). Both are
invariants of the op fold: every `Op.delta` contributes one of the three
journal shapes (`empty` / `addDelta` / `removeDelta`), each closed under the
predicate, and the join composes closure through `IssueData.merge` pointwise.
So `selfTagged_fold` / `payloadTotal_fold` discharge the hypotheses for every
state a replica actually materializes — `fold`, and via `foldFast_eq_fold`
the shipped cold path too. Pure; no I/O; no Mathlib (ADR-0009).
-/
import Tl.Kernel.Apply

namespace Tl.Kernel

open Tl.Crdt

/-- A merged state's per-issue journal is the join of the sides' journals
    (the `getD empty` base is absorbed by the journal's empty laws). -/
theorem issueData_merge_notes (s t : State) (id : IssueId) :
    ((State.merge s t).issueData id).notes
      = Journal.merge ((s.issueData id).notes) ((t.issueData id).notes) := by
  unfold State.issueData
  show (((AMap.merge IssueData.merge s.data t.data).find id).getD IssueData.empty).notes = _
  rw [AMap.find_merge]
  cases hs : s.data.find id with
  | none =>
    cases ht : t.data.find id with
    | none =>
      show Journal.empty = Journal.merge Journal.empty Journal.empty
      exact (Journal.merge_empty_left Journal.empty).symm
    | some dt =>
      show dt.notes = Journal.merge Journal.empty dt.notes
      exact (Journal.merge_empty_left dt.notes).symm
  | some ds =>
    cases ht : t.data.find id with
    | none =>
      show ds.notes = Journal.merge ds.notes Journal.empty
      exact (Journal.merge_empty_right ds.notes).symm
    | some dt => rfl

/-- Every op delta's per-issue journal satisfies any predicate that holds of
    the three delta shapes — the per-op leg of the fold invariants. -/
private theorem notes_invariant_delta {P : Journal → Prop}
    (hempty : P Journal.empty)
    (hadd : ∀ st p, P (Journal.addDelta st p))
    (hrem : ∀ obs, P (Journal.removeDelta obs))
    (op : Op) (id : IssueId) : P ((op.delta.issueData id).notes) := by
  have hsing : ∀ (tid : IssueId) (D : IssueData), P D.notes →
      P ((((AMap.singleton tid D).find id).getD IssueData.empty).notes) := by
    intro tid D hD
    rw [AMap.find_singleton]
    by_cases hid : id = tid
    · rw [ite_eq_left hid]; exact hD
    · rw [ite_eq_right hid]; exact hempty
  cases op with
  | create cid st w => exact hsing cid (Op.createData st w) hempty
  | setFields cid st w => exact hsing cid (Op.scalarData st w) hempty
  | metaSet cid st k v => exact hsing cid (Op.metaData st k v) hempty
  | edgeAdd e st => exact hempty
  | edgeRemove e obs => exact hempty
  | labelAdd cid l st => exact hsing cid (Op.labelData st l) hempty
  | labelRemove cid l obs => exact hsing cid (Op.labelRemoveData l obs) hempty
  | noteAdd cid st note text actor =>
    exact hsing cid (Op.noteData st note text actor) (hadd st ⟨note, text, actor⟩)
  | noteRemove cid obs => exact hsing cid (Op.noteRemoveData obs) (hrem obs)

/-- The foldl invariant: a predicate closed under the three delta shapes and
    the join holds of every issue's journal along the whole fold. -/
private theorem notes_invariant_foldl {P : Journal → Prop}
    (hempty : P Journal.empty)
    (hadd : ∀ st p, P (Journal.addDelta st p))
    (hrem : ∀ obs, P (Journal.removeDelta obs))
    (hmerge : ∀ a b, P a → P b → P (Journal.merge a b)) :
    (ops : List Op) → (s : State) → (∀ id, P ((s.issueData id).notes)) →
    ∀ id, P (((ops.foldl apply s).issueData id).notes)
  | [], _, hs => hs
  | op :: ops, s, hs => by
    intro id
    refine notes_invariant_foldl hempty hadd hrem hmerge ops (apply s op) (fun j => ?_) id
    show P (((State.merge s op.delta).issueData j).notes)
    rw [issueData_merge_notes]
    exact hmerge _ _ (hs j) (notes_invariant_delta hempty hadd hrem op j)

private theorem notes_invariant_fold {P : Journal → Prop}
    (hempty : P Journal.empty)
    (hadd : ∀ st p, P (Journal.addDelta st p))
    (hrem : ∀ obs, P (Journal.removeDelta obs))
    (hmerge : ∀ a b, P a → P b → P (Journal.merge a b))
    (ops : List Op) (id : IssueId) : P (((fold ops).issueData id).notes) :=
  notes_invariant_foldl hempty hadd hrem hmerge ops State.empty
    (fun _ => hempty) id

/-- **Fold-level `SelfTagged` discharge (ADR-0027).** Every issue's journal in
    every folded state carries only self-tags — the `SelfTagged`/`htags`
    hypotheses of the hiding and no-resurrection theorems hold for every state
    a replica materializes (and for the shipped cold path via
    `foldFast_eq_fold`). -/
theorem selfTagged_fold (ops : List Op) (id : IssueId) :
    Journal.SelfTagged (((fold ops).issueData id).notes) :=
  notes_invariant_fold Journal.selfTagged_empty Journal.selfTagged_addDelta
    Journal.selfTagged_removeDelta (fun _ _ ha hb => Journal.selfTagged_merge ha hb) ops id

/-- **Fold-level `PayloadTotal` discharge (ADR-0027).** Every visible entry in
    every folded state has a payload — `visibleEntries` never exercises its
    skip case on a real state, so retention is rendering
    (`exists_mem_visibleEntries_of_visible` with a free hypothesis). -/
theorem payloadTotal_fold (ops : List Op) (id : IssueId) :
    Journal.PayloadTotal (((fold ops).issueData id).notes) :=
  notes_invariant_fold Journal.payloadTotal_empty Journal.payloadTotal_addDelta
    Journal.payloadTotal_removeDelta (fun _ _ ha hb => Journal.payloadTotal_merge ha hb) ops id

end Tl.Kernel
