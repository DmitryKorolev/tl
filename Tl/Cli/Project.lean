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
import Tl.Kernel.RollupFast
import Tl.Kernel.Ready
import Tl.Kernel.ReadyFast
import Tl.Kernel.Cycles
import Tl.Kernel.CyclesFast

namespace Tl.Cli

open Tl.Store
open Tl.Kernel
open Tl.Format
open Tl.Crdt
open Lean (Json)

def jnum (n : Nat) : Json := Json.num ⟨n, 0⟩

/-- HLC → ISO-8601 UTC with forced millisecond precision (the ADR-0020
    timestamp form; the HLC's physical component is the instant). -/
def hlcIso (hlc : Nat) : String :=
  let s := Time.isoOfEpochMs (hlc / 2 ^ 16)
  if s.toList.contains '.' then s else (s.dropEnd 1).toString ++ ".000Z"

/-! ## Fold-time provenance (ADR-0008)

Rule: every cross-op recency comparison uses the FULL `Stamp` order — the
LWW order on `(hlc, replica, nonce)` — never the bare HLC. Two replicas can
write lifecycle ops at the same HLC; the materialized state is decided by
the full triple, and a projection comparing bare HLCs would disagree with it
(a closed issue rendered without `closedAt`). Rendered timestamps then take
the *winning stamp's* HLC. -/

/-- The later of an optional stamp and a new one, by the LWW order. -/
private def laterStamp : Option Stamp → Stamp → Option Stamp
  | none, s => some s
  | some m, s => some (if TotalOrd.le m s then s else m)

structure Prov where
  /-- The earliest `create` (by stamp order) and its actor. -/
  created : Option (Stamp × Option String) := none
  updated : Option Stamp := none
  lastClose : Option Stamp := none
  lastReopen : Option Stamp := none
  lastClaim : Option Stamp := none

/-- One pass over the log for one issue's provenance projections. -/
def provenanceOf (ops : List ParsedOp) (id : IssueId) : Prov := Id.run do
  let mut pr : Prov := {}
  for p in ops do
    let st := p.stamp
    let bump (pr : Prov) : Prov := { pr with updated := laterStamp pr.updated st }
    match p.op with
    | .create i _ =>
      if i == id then
        if pr.created.all (fun (c, _) => decide (TotalOrd.lt st c)) then
          pr := { pr with created := some (st, p.actor) }
        pr := bump pr
    | .update i _ => if i == id then pr := bump pr
    | .claim i _ =>
      if i == id then pr := { bump pr with lastClaim := laterStamp pr.lastClaim st }
    | .close i _ =>
      if i == id then pr := { bump pr with lastClose := laterStamp pr.lastClose st }
    | .reopen i =>
      if i == id then pr := { bump pr with lastReopen := laterStamp pr.lastReopen st }
    | .defer i _ => if i == id then pr := bump pr
    | .undefer i => if i == id then pr := bump pr
    | _ => pure ()
  return pr

/-- One pass over the whole log: every issue's provenance at once. The
    per-id `provenanceOf` rescans the full log per rendered row — O(rows × ops)
    across a `list`; this map costs one pass and each row one lookup. The
    per-op arms mirror `provenanceOf` exactly (the property test pins
    agreement per id). -/
def provenanceMap (ops : List ParsedOp) : AMap IssueId Prov := Id.run do
  -- near-linear build: tag each provenance-bearing op with its target, sort
  -- stably by target (within-target original order preserved — the per-id
  -- fold below then matches provenanceOf's left-to-right walk exactly), fold
  -- each adjacent group, and assemble the already-sorted entries. A per-op
  -- positional map insert would be Θ(ops × issues).
  let step (pr : Prov) (p : ParsedOp) : Prov :=
    let st := p.stamp
    let bump (pr : Prov) : Prov := { pr with updated := laterStamp pr.updated st }
    match p.op with
    | .create _ _ =>
      let pr := if pr.created.all (fun (c, _) => decide (TotalOrd.lt st c))
                then { pr with created := some (st, p.actor) } else pr
      bump pr
    | .update _ _ => bump pr
    | .claim _ _ => { bump pr with lastClaim := laterStamp pr.lastClaim st }
    | .close _ _ => { bump pr with lastClose := laterStamp pr.lastClose st }
    | .reopen _ => { bump pr with lastReopen := laterStamp pr.lastReopen st }
    | .defer _ _ => bump pr
    | .undefer _ => bump pr
    | _ => pr
  let target (p : ParsedOp) : Option IssueId :=
    match p.op with
    | .create i _ | .update i _ | .claim i _ | .close i _
    | .reopen i | .defer i _ | .undefer i => some i
    | _ => none
  let tagged := ops.filterMap (fun p => (target p).map (·, p))
  let sorted := tagged.mergeSort (fun a b => decide (TotalOrd.le a.1 b.1))
  -- one fold over the sorted pairs: accumulate the current group's Prov,
  -- emit it when the target changes (completed groups in ascending order)
  let folded := sorted.foldl (fun acc (j, q) =>
    match acc with
    | none => some (j, step {} q, ([] : List (IssueId × Prov)))
    | some (i, pr, done) =>
      if j == i then some (i, step pr q, done)
      else some (j, step {} q, (i, pr) :: done)) none
  let entries := match folded with
    | none => []
    | some (i, pr, done) => ((i, pr) :: done).reverse
  match AMap.ofAscList? entries with
  | some m => m
  | none =>
    -- unreachable (the entries come out of a sort, grouped to distinct keys);
    -- the fallback is the slow-but-correct per-op build, never a wrong map
    entries.foldl (fun m (i, pr) => m.insert i pr) AMap.empty

/-- One issue's provenance from the batched map (absent ⇒ no ops touched it). -/
def provOf (m : AMap IssueId Prov) (i : IssueId) : Prov := (m.find i).getD {}

/-- A command's read view. -/
structure View where
  dirs : Dirs
  loaded : Loaded
  now : Nat
  replica : Option Tl.Clock.Replica
  /-- The batched rollup map (ADR-0003 §3 amendment), computed once per view:
      every per-row effectiveStatus/readiness read goes through it
      (`effStatusWith_eq` — pointwise the spec, so nothing observable moves). -/
  rollup : AMap IssueId Status
  /-- The present edges, hoisted once per view — the spec re-derives them
      inside every `blockersOf`/`isEpic` call, O(E²) per row (the profile's
      whole remaining `list` cost). Row helpers read `blockersOfE`-style
      views, each rfl-equal to the spec at this list. -/
  edges : List Edge
  /-- The hoisted `(parent, child)` view (`parentEdges`), for per-row
      epic-ness (`kidsOfEdges_parentEdges`). -/
  pedges : List (IssueId × IssueId)
  /-- The batched provenance map — one log pass per view instead of one per
      rendered row (`provenanceMap` mirrors `provenanceOf` arm-for-arm). -/
  prov : AMap IssueId Prov

/- View-construction note (an accepted cost): every command builds all four
   hoisted views eagerly, including single-issue reads and write echoes —
   each build is one pass with linear-find constants, milliseconds at the
   thousands-of-ops scale target, and `tl close` pays it three times (the
   pre-state view and `unblocksFast`'s two queues). Revisiting laziness or
   sharing rides the tracked comparison-constant follow-up work. -/

def View.state (v : View) : State := v.loaded.state


def Prov.createdAt (pr : Prov) : Option Nat := pr.created.map (·.1.hlc)
def Prov.updatedAt (pr : Prov) : Option Nat := pr.updated.map (·.hlc)
def Prov.createdBy (pr : Prov) : Option String := pr.created.bind (·.2)
def Prov.createdReplica (pr : Prov) : Option Nat := pr.created.map (·.1.replica)

/-- `closedAt` — absent once reopened (ADR-0008); the close wins exactly when
    it beats every reopen in the stamp order, mirroring the LWW state. -/
def Prov.closedAt (pr : Prov) : Option Nat := do
  let c ← pr.lastClose
  if pr.lastReopen.all (fun r => decide (TotalOrd.lt r c)) then some c.hlc else none

/-- `claimedAt` — the latest claim later (in stamp order) than any
    close/reopen (ADR-0008). -/
def Prov.claimedAt (pr : Prov) : Option Nat := do
  let c ← pr.lastClaim
  if pr.lastClose.all (fun x => decide (TotalOrd.lt x c))
      && pr.lastReopen.all (fun x => decide (TotalOrd.lt x c)) then
    some c.hlc
  else none

/-! ## Derived booleans (vision §states) -/

def blockedOf (m : AMap IssueId Status) (edges : List Edge) (s : State) (i : IssueId) : Bool :=
  (s.issueData i).statusOf == .Open
    && (State.blockersOfE edges i).any (fun b => !State.blockerDischargedWith m s b)

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

/-- `canonicalParent` over the hoisted `(parent, child)` view — the spec
    re-derives `presentEdges` inside `parentsOf` per call (the tree render's
    profile cost). For a present `i` the candidate set is identical: the
    hoisted view only additionally filters child presence, and `i` is the
    child. -/
def canonicalParentE (v : View) (i : IssueId) : Option IssueId := Id.run do
  let mut best : Option (IssueId × Stamp) := none
  for (p, c) in v.pedges do
    if c == i then
      if let some tag := maxTagOf v.state (p, i, EdgeKind.Parent) then
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
  -- Meta KEYS are emitted as-is (not control-stripped): the `--json` encoder
  -- escapes control bytes safely, and stripping keys would silently collapse
  -- two distinct stored keys that differ only in control chars into one
  -- mkObj member — silent data loss the loud-never-silent rule forbids
  -- (ADR-0014, amended: keys are escaped-not-stripped on the JSON path; the
  -- human path does not render meta in stage 1). VALUES are still sanitized.
  Json.mkObj ((AMap.keys d.metadata).filterMap (fun k =>
    match (d.metadata.find k).bind (·.value) with
    | some (some v) =>
      -- duplicate-of holds an id: render display form when well-formed (ADR-0008)
      if k == "duplicate-of" && validId v then some (k, Json.str (displayId v))
      else some (k, Json.str (sanitizeSingle v))
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
  let pr := provOf v.prov i
  Json.mkObj <|
    [("id", Json.str (displayId i)),
     ("status", Json.str (statusWire d.statusOf)),
     ("effectiveStatus", Json.str (statusWire (State.effStatusWith v.rollup s i))),
     ("priority", jnum d.priorityOf.val),
     ("isEpic", Json.bool (!(State.kidsOfEdges v.pedges i).isEmpty)),
     ("ready", Json.bool (State.isReadyFast v.rollup v.edges v.pedges s v.now i)),
     ("blocked", Json.bool (blockedOf v.rollup v.edges s i)),
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
  let pr := provOf v.prov i
  Json.mkObj <|
    [("id", Json.str (displayId i)),
     ("status", Json.str (statusWire d.statusOf)),
     ("effectiveStatus", Json.str (statusWire (State.effStatusWith v.rollup s i))),
     ("priority", jnum d.priorityOf.val),
     ("isEpic", Json.bool (!(State.kidsOfEdges v.pedges i).isEmpty)),
     ("ready", Json.bool (State.isReadyFast v.rollup v.edges v.pedges s v.now i)),
     ("blocked", Json.bool (blockedOf v.rollup v.edges s i)),
     ("deferred", Json.bool (deferredOf s v.now i)),
     ("dependencyCount", jnum (State.blockersOfE v.edges i).length),
     ("dependentCount", jnum (State.dependentsOfE v.edges i).length)]
    ++ optField "title" ((d.title.value).map (Json.str ∘ sanitizeSingle))
    ++ optField "assignee" ((d.assignee.value.getD none).map (Json.str ∘ sanitizeSingle))
    ++ optField "createdAt" (pr.createdAt.map (Json.str ∘ hlcIso))
    ++ optField "updatedAt" (pr.updatedAt.map (Json.str ∘ hlcIso))

/-- One human line per issue (plain stage-1 output). -/
def issueLine (v : View) (i : IssueId) : String :=
  let d := v.state.issueData i
  let title := sanitizeSingle ((d.title.value).getD "(untitled)")
  let flags := String.intercalate ""
    [if !(State.kidsOfEdges v.pedges i).isEmpty then " [epic]" else "",
     if blockedOf v.rollup v.edges v.state i then " [blocked]" else "",
     if deferredOf v.state v.now i then " [deferred]" else ""]
  s!"{displayId i}  p{d.priorityOf.val}  {statusWire (State.effStatusWith v.rollup v.state i)}  {title}{flags}"

end Tl.Cli
