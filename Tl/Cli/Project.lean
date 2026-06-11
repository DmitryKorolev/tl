/-
`Tl.Cli.Project` — the read view and the `--json` issue projections
(ADR-0003 §json, ADR-0008 §provenance, ADR-0020).

`View` is what every command works from: located dirs, the materialized log,
the injected `now`, and this working copy's replica when known. The issue
object is built here once — scalars by their field-table names, the derived
projections (`effectiveStatus`, `isEpic`/`ready`/`blocked`/`deferred`), the
fold-time provenance timestamps (`createdAt` = the create op's HLC;
`updatedAt` = max over the issue's own scalar writes; `closedAt` absent once
reopened; `claimedAt` = the latest claim later than any close/reopen), the
`dependencies` edge array with the canonical `parent`, and the `provenance`
trust block. Omit-empty throughout (ADR-0020), with `provenance.createdBy`
and `claim.currentAssignee` as the pinned `|null` exceptions.
-/
import Tl.Store.Lock
import Tl.Format.Ids
import Tl.Cli.Envelope
import Tl.Cli.Sanitize
import Tl.Kernel.Rollup
import Tl.Kernel.Ready
import Tl.Kernel.Cycles

namespace Tl.Cli

open Tl.Store
open Tl.Kernel
open Tl.Format
open Tl.Crdt
open Lean (Json)

/-- A command's read view. -/
structure View where
  dirs : Dirs
  loaded : Loaded
  now : Nat
  replica : Option Tl.Clock.Replica

def View.state (v : View) : State := v.loaded.state

def jnum (n : Nat) : Json := Json.num ⟨n, 0⟩

/-- HLC → ISO-8601 UTC with forced millisecond precision (the ADR-0020
    timestamp form; the HLC's physical component is the instant). -/
def hlcIso (hlc : Nat) : String :=
  let s := Time.isoOfEpochMs (hlc / 2 ^ 16)
  if s.toList.contains '.' then s else (s.dropEnd 1).toString ++ ".000Z"

/-! ## Fold-time provenance (ADR-0008) -/

structure Prov where
  createdAt : Option Nat := none
  updatedAt : Option Nat := none
  lastClose : Nat := 0
  lastReopen : Nat := 0
  lastClaim : Nat := 0
  createdBy : Option String := none
  createdReplica : Option Nat := none

/-- One pass over the log for one issue's provenance projections. -/
def provenanceOf (ops : List ParsedOp) (id : IssueId) : Prov := Id.run do
  let mut pr : Prov := {}
  for p in ops do
    let h := p.stamp.hlc
    let bump (pr : Prov) : Prov :=
      { pr with updatedAt := some (max (pr.updatedAt.getD 0) h) }
    match p.op with
    | .create i _ =>
      if i == id then
        if pr.createdAt.all (h < ·) then
          pr := { pr with createdAt := some h, createdBy := p.actor,
                          createdReplica := some p.stamp.replica }
        pr := bump pr
    | .update i _ => if i == id then pr := bump pr
    | .claim i _ =>
      if i == id then pr := { bump pr with lastClaim := max pr.lastClaim h }
    | .close i _ =>
      if i == id then pr := { bump pr with lastClose := max pr.lastClose h }
    | .reopen i =>
      if i == id then pr := { bump pr with lastReopen := max pr.lastReopen h }
    | .defer i _ => if i == id then pr := bump pr
    | .undefer i => if i == id then pr := bump pr
    | _ => pure ()
  return pr

/-- `closedAt` — absent once reopened (ADR-0008). -/
def Prov.closedAt (pr : Prov) : Option Nat :=
  if pr.lastClose > pr.lastReopen && pr.lastClose > 0 then some pr.lastClose else none

/-- `claimedAt` — the latest claim later than any close/reopen (ADR-0008). -/
def Prov.claimedAt (pr : Prov) : Option Nat :=
  if pr.lastClaim > max pr.lastClose pr.lastReopen && pr.lastClaim > 0 then
    some pr.lastClaim
  else none

/-! ## Derived booleans (vision §states) -/

def blockedOf (s : State) (i : IssueId) : Bool :=
  (s.issueData i).statusOf == .Open
    && (s.blockersOf i).any (fun b => !s.blockerDischarged b)

def deferredOf (s : State) (now : Nat) (i : IssueId) : Bool :=
  (s.issueData i).statusOf == .Open
    && match (s.issueData i).deferUntilOf with
       | some t => now < t
       | none => false

/-! ## Edges, canonical parent, labels, meta -/

/-- The greatest surviving add-tag of an edge (for the canonical parent). -/
private def maxTagOf (s : State) (e : Edge) : Option Stamp :=
  (AMap.keys (s.edges.tagsOf e)).foldl
    (fun acc st => match acc with
      | none => some st
      | some m => some (if TotalOrd.le m st then st else m))
    none

/-- The canonical display parent: the surviving `parent` edge greatest in
    `(hlc, replica, nonce)` (ADR-0003 §4). -/
def canonicalParent (s : State) (i : IssueId) : Option IssueId := Id.run do
  let mut best : Option (IssueId × Stamp) := none
  for p in s.parentsOf i do
    if let some tag := maxTagOf s (p, i, EdgeKind.Parent) then
      best := match best with
        | none => some (p, tag)
        | some (bp, bt) => if TotalOrd.le bt tag then some (p, tag) else some (bp, bt)
  return best.map (·.1)

def dependenciesJson (s : State) (i : IssueId) : Json :=
  let rows := s.presentEdges.filter (fun (f, t, _) => f == i || t == i)
  Json.arr (rows.map (fun (f, t, k) =>
    Json.mkObj [("type", Json.str (edgeKindWire k)),
                ("from", Json.str (displayId f)),
                ("to", Json.str (displayId t))])).toArray

private def labelsJson (d : IssueData) : Json :=
  Json.arr (d.labels.presentElements.map (Json.str ∘ sanitizeSingle)).toArray

private def metaJson (d : IssueData) : Json :=
  Json.mkObj ((AMap.keys d.metadata).filterMap (fun k =>
    match (d.metadata.find k).bind (·.value) with
    | some (some v) =>
      -- duplicate-of holds an id: render display form when well-formed (ADR-0008)
      if k == "duplicate-of" && validId v then some (sanitizeSingle k, Json.str (displayId v))
      else some (sanitizeSingle k, Json.str (sanitizeSingle v))
    | _ => none))

/-- The stored `duplicate-of` target (bare), if any. -/
def duplicateOf (s : State) (i : IssueId) : Option IssueId :=
  match ((s.issueData i).metadata.find "duplicate-of").bind (·.value) with
  | some (some v) => if validId v then some v else none
  | _ => none

/-! ## The issue objects (ADR-0003/0020) -/

private def optField (k : String) (v : Option Json) : List (String × Json) :=
  match v with
  | some j => [(k, j)]
  | none => []

/-- The full issue object (`show`, mutation echoes). -/
def issueObj (v : View) (i : IssueId) : Json :=
  let s := v.state
  let d := s.issueData i
  let pr := provenanceOf v.loaded.ops i
  Json.mkObj <|
    [("id", Json.str (displayId i)),
     ("status", Json.str (statusWire d.statusOf)),
     ("effectiveStatus", Json.str (statusWire (s.effectiveStatus i))),
     ("priority", jnum d.priorityOf.val),
     ("isEpic", Json.bool (s.isEpic i)),
     ("ready", Json.bool (s.isReady v.now i)),
     ("blocked", Json.bool (blockedOf s i)),
     ("deferred", Json.bool (deferredOf s v.now i)),
     ("labels", labelsJson d),
     ("meta", metaJson d),
     ("dependencies", dependenciesJson s i)]
    ++ optField "title" ((d.title.value).map (Json.str ∘ sanitizeSingle))
    ++ optField "assignee" ((d.assignee.value.getD none).map (Json.str ∘ sanitizeSingle))
    ++ optField "slug" ((d.slug.value.getD none).map (Json.str ∘ sanitizeSingle))
    ++ optField "description" ((d.description.value.getD none).map (Json.str ∘ sanitizeMulti))
    ++ optField "notes" ((d.notes.value.getD none).map (Json.str ∘ sanitizeMulti))
    ++ optField "deferUntil" ((d.deferUntilOf).map (Json.str ∘ Time.isoOfEpochMs))
    ++ optField "closeResolution"
        ((d.closeResolution.value.getD none).map (Json.str ∘ resolutionWire))
    ++ optField "parent" ((canonicalParent s i).map (Json.str ∘ displayId))
    ++ optField "createdAt" (pr.createdAt.map (Json.str ∘ hlcIso))
    ++ optField "updatedAt" (pr.updatedAt.map (Json.str ∘ hlcIso))
    ++ optField "closedAt" (pr.closedAt.map (Json.str ∘ hlcIso))
    ++ optField "claimedAt" (pr.claimedAt.map (Json.str ∘ hlcIso))
    ++ [("provenance", Json.mkObj <|
          [("source", Json.str "native"),
           ("createdBy", pr.createdBy.elim Json.null (Json.str ∘ sanitizeSingle))]
          ++ optField "replica" (pr.createdReplica.map (Json.str ∘ (toCrockford · 13))))]

/-- The trimmed list/ready row (ADR-0020): selection-driving scalars +
    derived booleans + the two graph counts. -/
def issueRow (v : View) (i : IssueId) : Json :=
  let s := v.state
  let d := s.issueData i
  let pr := provenanceOf v.loaded.ops i
  Json.mkObj <|
    [("id", Json.str (displayId i)),
     ("status", Json.str (statusWire d.statusOf)),
     ("effectiveStatus", Json.str (statusWire (s.effectiveStatus i))),
     ("priority", jnum d.priorityOf.val),
     ("isEpic", Json.bool (s.isEpic i)),
     ("ready", Json.bool (s.isReady v.now i)),
     ("blocked", Json.bool (blockedOf s i)),
     ("deferred", Json.bool (deferredOf s v.now i)),
     ("dependencyCount", jnum (s.blockersOf i).length),
     ("dependentCount", jnum (s.dependentsOf i).length)]
    ++ optField "title" ((d.title.value).map (Json.str ∘ sanitizeSingle))
    ++ optField "assignee" ((d.assignee.value.getD none).map (Json.str ∘ sanitizeSingle))
    ++ optField "createdAt" (pr.createdAt.map (Json.str ∘ hlcIso))
    ++ optField "updatedAt" (pr.updatedAt.map (Json.str ∘ hlcIso))

/-- One human line per issue (plain stage-1 output). -/
def issueLine (v : View) (i : IssueId) : String :=
  let d := v.state.issueData i
  let title := sanitizeSingle ((d.title.value).getD "(untitled)")
  let flags := String.intercalate ""
    [if v.state.isEpic i then " [epic]" else "",
     if blockedOf v.state i then " [blocked]" else "",
     if deferredOf v.state v.now i then " [deferred]" else ""]
  s!"{displayId i}  p{d.priorityOf.val}  {statusWire (v.state.effectiveStatus i)}  {title}{flags}"

end Tl.Cli
