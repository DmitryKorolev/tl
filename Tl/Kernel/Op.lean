/-
`Tl.Kernel.Op` — the seven state-deltas (ADR-0004).

One constructor per distinct state-delta, *not* per CLI verb: `create`,
`setFields`, `metaSet`, `edgeAdd`, `edgeRemove`, `labelAdd`, `labelRemove`. The
readable wire verbs (`claim`, `close`, `reopen`, `defer`, `dep add`, …) are
mapped onto these by the tested shell (ADR-0008); the kernel never sees a verb.

Every op's effect is captured by `Op.delta : Op → State` — the op's *contribution*
as a standalone state — so `apply` is just `State.merge s (delta op)` (ADR-0001:
"apply = a join with the op's delta"). This is what collapses convergence (thm
2/8) onto the state semilattice laws.
-/
import Tl.Kernel.State

namespace Tl.Kernel

open Tl.Crdt

/-- The scalar fields a `create`/`setFields` op writes — each `none` means "this
    op does not touch this field", `some v` means "write `v` at the op's stamp".
    Nullable fields carry `Option (Option _)` so a clear (a written `none`) is
    distinct from no-write (ADR-0002/0008). -/
structure ScalarWrites where
  title : Option String := none
  status : Option Status := none
  priority : Option (Fin 5) := none
  assignee : Option (Option String) := none
  description : Option (Option String) := none
  slug : Option (Option String) := none
  deferUntil : Option (Option Instant) := none
  closeResolution : Option (Option CloseResolution) := none

/-- A stamped write of an optional field value into a register (no-write ⇒ `none`). -/
def writeIf {V : Type _} (st : Stamp) : Option V → Reg V
  | some v => Reg.write st v
  | none => none

/-- The nine kernel deltas (ADR-0004/0027). The `Stamp` is the op's `(hlc,
    replica, nonce)` (ADR-0007); on add-ops it is the OR-Set add-tag and the LWW
    write stamp; `observed` on remove-ops is the tombstoned add-tag set, scoped
    in the delta to the element the op carries (the edge / the label / the
    note's own tag). `noteAdd` carries the minted handle, text, and envelope
    actor as journal *payload* (ADR-0027 — actor becomes tag-keyed payload and
    a join-tuple component here; convergence and identity stay actor-free). -/
inductive Op where
  | create (id : IssueId) (st : Stamp) (writes : ScalarWrites)
  | setFields (id : IssueId) (st : Stamp) (writes : ScalarWrites)
  | metaSet (id : IssueId) (st : Stamp) (key : String) (val : Option String)
  | edgeAdd (e : Edge) (st : Stamp)
  | edgeRemove (e : Edge) (observed : FinSet Stamp)
  | labelAdd (id : IssueId) (label : Label) (st : Stamp)
  | labelRemove (id : IssueId) (label : Label) (observed : FinSet Stamp)
  | noteAdd (id : IssueId) (st : Stamp) (note : String) (text : String) (actor : Option String)
  | noteRemove (id : IssueId) (observed : FinSet Stamp)

namespace Op

/-- The per-issue data delta of a scalar write set, stamped `st`. -/
def scalarData (st : Stamp) (w : ScalarWrites) : IssueData where
  title := writeIf st w.title
  status := writeIf st w.status
  priority := writeIf st w.priority
  assignee := writeIf st w.assignee
  description := writeIf st w.description
  notes := Journal.empty
  slug := writeIf st w.slug
  deferUntil := writeIf st w.deferUntil
  closeResolution := writeIf st w.closeResolution
  labels := OrSet.empty
  metadata := AMap.empty

/-- The data delta of a `create` — like `scalarData`, but the two total fields
    are seeded as *ordinary LWW writes at the create stamp* when not carried:
    `status := Open`, `priority := 2` (ADR-0002 §2 / ADR-0008 `create` row). These
    are not privileged — a pre-`create` `update` at a later HLC still wins by LWW —
    so reads never fall through to the materialization default for a created issue
    (`statusOf`/`priorityOf`'s `getD` only fires for an orphan, pre-`create` id). -/
def createData (st : Stamp) (w : ScalarWrites) : IssueData :=
  scalarData st { w with
    status := some (w.status.getD Status.Open)
    priority := some (w.priority.getD (2 : Fin 5)) }

/-- The data delta of a `metaSet`. -/
def metaData (st : Stamp) (key : String) (val : Option String) : IssueData :=
  { IssueData.empty with metadata := AMap.singleton key (Reg.write st val) }

/-- The data delta of a `labelAdd`. -/
def labelData (st : Stamp) (label : Label) : IssueData :=
  { IssueData.empty with labels := OrSet.singletonAdd label st }

/-- The data delta of a `labelRemove` (tombstone the observed tags at the
    removed label — element-scoped, so it cannot touch any other label). -/
def labelRemoveData (label : Label) (obs : FinSet Stamp) : IssueData :=
  { IssueData.empty with labels := OrSet.tombstonesAt label obs }

/-- The data delta of a `noteAdd`: one journal entry, keyed by the op's own
    stamp, carrying the minted handle, the text, and the envelope actor as
    payload (ADR-0027). -/
def noteData (st : Stamp) (note text : String) (actor : Option String) : IssueData :=
  { IssueData.empty with notes := Journal.addDelta st ⟨note, text, actor⟩ }

/-- The data delta of a `noteRemove`: tombstone each observed tag at itself
    (the journal element *is* the tag). The remove op's own stamp is never
    materialized (ADR-0027 — `noteRemove` does not bump `updatedAt`). -/
def noteRemoveData (obs : FinSet Stamp) : IssueData :=
  { IssueData.empty with notes := Journal.removeDelta obs }

/-- The op's contribution as a standalone state; `apply` joins it in. -/
def delta : Op → State
  | create id st w => ⟨OrSet.singletonAdd id st, AMap.singleton id (createData st w), OrSet.empty⟩
  | setFields id st w => ⟨OrSet.empty, AMap.singleton id (scalarData st w), OrSet.empty⟩
  | metaSet id st key val => ⟨OrSet.empty, AMap.singleton id (metaData st key val), OrSet.empty⟩
  | edgeAdd e st => ⟨OrSet.empty, AMap.empty, OrSet.singletonAdd e st⟩
  | edgeRemove e obs => ⟨OrSet.empty, AMap.empty, OrSet.tombstonesAt e obs⟩
  | labelAdd id label st => ⟨OrSet.empty, AMap.singleton id (labelData st label), OrSet.empty⟩
  | labelRemove id label obs =>
    ⟨OrSet.empty, AMap.singleton id (labelRemoveData label obs), OrSet.empty⟩
  | noteAdd id st note text actor =>
    ⟨OrSet.empty, AMap.singleton id (noteData st note text actor), OrSet.empty⟩
  | noteRemove id obs => ⟨OrSet.empty, AMap.singleton id (noteRemoveData obs), OrSet.empty⟩

end Op

end Tl.Kernel
