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
  notes : Option (Option String) := none
  slug : Option (Option String) := none
  deferUntil : Option (Option Instant) := none
  closeResolution : Option (Option CloseResolution) := none

/-- A stamped write of an optional field value into a register (no-write ⇒ `none`). -/
def writeIf {V : Type _} (st : Stamp) : Option V → Reg V
  | some v => Reg.write st v
  | none => none

/-- The seven kernel deltas (ADR-0004). The `Stamp` is the op's `(hlc, replica,
    nonce)` (ADR-0007); on add-ops it is the OR-Set add-tag and the LWW write
    stamp; `observed` on remove-ops is the tombstoned add-tag set. -/
inductive Op where
  | create (id : IssueId) (st : Stamp) (writes : ScalarWrites)
  | setFields (id : IssueId) (st : Stamp) (writes : ScalarWrites)
  | metaSet (id : IssueId) (st : Stamp) (key : String) (val : Option String)
  | edgeAdd (e : Edge) (st : Stamp)
  | edgeRemove (e : Edge) (observed : FinSet Stamp)
  | labelAdd (id : IssueId) (label : Label) (st : Stamp)
  | labelRemove (id : IssueId) (label : Label) (observed : FinSet Stamp)

namespace Op

/-- The per-issue data delta of a scalar write set, stamped `st`. -/
def scalarData (st : Stamp) (w : ScalarWrites) : IssueData where
  title := writeIf st w.title
  status := writeIf st w.status
  priority := writeIf st w.priority
  assignee := writeIf st w.assignee
  description := writeIf st w.description
  notes := writeIf st w.notes
  slug := writeIf st w.slug
  deferUntil := writeIf st w.deferUntil
  closeResolution := writeIf st w.closeResolution
  labels := OrSet.empty
  metadata := AMap.empty

/-- The data delta of a `metaSet`. -/
def metaData (st : Stamp) (key : String) (val : Option String) : IssueData :=
  { IssueData.empty with metadata := AMap.singleton key (Reg.write st val) }

/-- The data delta of a `labelAdd`. -/
def labelData (st : Stamp) (label : Label) : IssueData :=
  { IssueData.empty with labels := OrSet.singletonAdd label st }

/-- The data delta of a `labelRemove` (tombstone the observed tags). -/
def labelRemoveData (obs : FinSet Stamp) : IssueData :=
  { IssueData.empty with labels := OrSet.tombstones obs }

/-- The op's contribution as a standalone state; `apply` joins it in. -/
def delta : Op → State
  | create id st w => ⟨OrSet.singletonAdd id st, AMap.singleton id (scalarData st w), OrSet.empty⟩
  | setFields id st w => ⟨OrSet.empty, AMap.singleton id (scalarData st w), OrSet.empty⟩
  | metaSet id st key val => ⟨OrSet.empty, AMap.singleton id (metaData st key val), OrSet.empty⟩
  | edgeAdd e st => ⟨OrSet.empty, AMap.empty, OrSet.singletonAdd e st⟩
  | edgeRemove _ obs => ⟨OrSet.empty, AMap.empty, OrSet.tombstones obs⟩
  | labelAdd id label st => ⟨OrSet.empty, AMap.singleton id (labelData st label), OrSet.empty⟩
  | labelRemove id _ obs => ⟨OrSet.empty, AMap.singleton id (labelRemoveData obs), OrSet.empty⟩

end Op

end Tl.Kernel
