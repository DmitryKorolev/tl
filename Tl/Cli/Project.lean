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

/-- `State.parentEdges` with the child-present check through a hash set built
    once, not an O(N) `hasIssue` (`OrSet.Present`) find per edge — `parentEdges`
    is Θ(E·N) and `loadView` builds it for every command. The result is the same
    list: `(hashSetOf present).contains t = decide (hasIssue t)`
    (`contains_hashSetOf_present`), so `v.pedges = s.parentEdges` (pinned by a
    test), and every kernel function taking `pe = s.parentEdges` stays correct. -/
def parentEdgesFast (s : State) : List (IssueId × IssueId) :=
  let pset := Tl.Kernel.hashSetOf s.presentIssues
  s.presentEdges.filterMap (fun e =>
    let (f, t, k) := e
    if decide (k = EdgeKind.Parent) && pset.contains t then some (f, t) else none)

/-- The per-query indexed views (ADR-0024): O(1)-amortized hash/bucket copies of
    the view's list-backed collections, built once per command and discarded.
    Each probe is proved pointwise-equal to the spec accessor it replaces
    (`getElem?_hashAssoc_amap` / `getD_bucketBy` / `contains_hashSetOf_present`,
    plus the `ReadyFast` bridges), so routing a per-issue read through it leaves
    every rendered value byte-identical while turning the O(N)-find / O(E)-filter
    per issue into an O(1)/O(deg) lookup — the per-row Θ(N²)/Θ(N·E) command-path
    cost class (ADR-0023 §3). -/
structure ViewIndex where
  /-- `state.data` as a hash map (`issueDataH_eq` ⇒ `issueData`). -/
  dataH : Std.HashMap IssueId IssueData
  /-- The rollup map as a hash map (`getElem?_hashAssoc_amap` ⇒
      `effStatusWith`/`effClosedWith`). -/
  rollupH : Std.HashMap IssueId Status
  /-- The present issues as a hash set (`contains_hashSetOf_present` ⇒ `hasIssue`). -/
  presentH : Std.HashSet IssueId
  /-- `Blocks` edges bucketed by target — each issue's blockers
      (`blocksByTarget_eq` ⇒ `blockersOfE`). -/
  btgt : Std.HashMap IssueId (List IssueId)
  /-- `Blocks` edges bucketed by source — each issue's dependents
      (`blocksBySource_eq` ⇒ `dependentsOfE`). -/
  bsrc : Std.HashMap IssueId (List IssueId)
  /-- Parent edges bucketed by parent — each issue's children
      (`getD_bucketBy` ⇒ `kidsOfEdges`). -/
  pbk : Std.HashMap IssueId (List IssueId)
  /-- Parent edges bucketed by child — each issue's parents (the canonical-parent
      candidates and the multi-parent count; `getD_bucketBy` over swapped pairs). -/
  pbc : Std.HashMap IssueId (List IssueId)
  /-- The provenance map as a hash map (`getElem?_hashAssoc_amap` ⇒ `provOf`). -/
  provH : Std.HashMap IssueId Prov
  /-- The edge OR-Set's add-tags, keyed by edge — a hash copy of
      `state.edges.adds`, so `edgeTags[e]?.getD ∅ = state.edges.tagsOf e`. The
      canonical-parent tie-break (`canonicalParentE`'s `maxTag`) reads it per
      candidate; the spec `tagsOf` is an O(E) `AMap.find`, and the tree's
      `isRoot` runs it per visible issue (Θ(N·E)). -/
  edgeTags : Std.HashMap Edge (FinSet Stamp)
  /-- Each present id's shortest unambiguous display-prefix length (`shortIdLens`
      over `present`) — `View.shortId` renders `tl-` + that many chars. Display
      only; JSON keeps the full id (ADR-0020). -/
  shortLen : Std.HashMap IssueId Nat

/-- The display floor for a short id: at least this many id chars after `tl-`
    (git-short-hash style — keeps ids visually stable and typable; collisions
    extend past it). -/
def shortIdFloor : Nat := 4

/-- Each id's shortest unambiguous prefix length over `ids` (the present set —
    what input resolution disambiguates against, `resolveToken`). Sorted
    lexicographically (`TotalOrd.le`), the longest prefix any id shares with
    another is shared with a sorted neighbor, so one char past the max neighbor
    LCP is unique; floored at `shortIdFloor`, capped at the id length. Built once
    per view (O(N log N)); `View.shortId` reads it O(1). -/
def shortIdLens (ids : List IssueId) : Std.HashMap IssueId Nat := Id.run do
  let arr := (ids.mergeSort (fun a b => decide (TotalOrd.le a b))).toArray
  let n := arr.size
  let getAt := fun k => (arr[k]?).getD ""
  let lcp := fun (a b : String) =>
    ((a.toList.zip b.toList).takeWhile (fun p => p.1 == p.2)).length
  let mut m : Std.HashMap IssueId Nat := ∅
  for k in [0:n] do
    let id := getAt k
    let prev := if k == 0 then 0 else lcp id (getAt (k - 1))
    let next := if k + 1 == n then 0 else lcp id (getAt (k + 1))
    let need := Nat.max (Nat.max prev next + 1) shortIdFloor
    m := m.insert id (Nat.min need id.length)
  return m

/-- Build the indexed views once from a view's already-materialized collections
    (ADR-0024 "build once, read many"). Pass the SAME `rollup`/`present`/`edges`/
    `pedges`/`prov` the base `View` fields hold, so each hashed probe equals its
    spec accessor over those lists. -/
def ViewIndex.of (data : AMap IssueId IssueData) (rollup : AMap IssueId Status)
    (present : List IssueId) (edges : List Edge) (pedges : List (IssueId × IssueId))
    (prov : AMap IssueId Prov) (edgeAdds : List (Edge × FinSet Stamp)) : ViewIndex :=
  { dataH := Tl.Kernel.hashAssoc data.toList
    rollupH := Tl.Kernel.hashAssoc rollup.toList
    presentH := Tl.Kernel.hashSetOf present
    btgt := State.blocksByTarget edges
    bsrc := State.blocksBySource edges
    pbk := Tl.Kernel.bucketBy pedges
    pbc := Tl.Kernel.bucketBy (pedges.map (fun p => (p.2, p.1)))
    provH := Tl.Kernel.hashAssoc prov.toList
    edgeTags := edgeAdds.foldl (fun m p => m.insert p.1 p.2) ∅
    shortLen := shortIdLens present }

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
  /-- The present issues, hoisted once per view — `presentElements` is a single
      O(N) pass for the issue OR-Set (no tombstones; `b0f3ff5` retired the old
      Θ(N²) re-`find`-per-key form), and the diagnostics (`cyclesFast`/
      `precCyclesFast`) and `stats`/`doctor` each re-derived it independently.
      Shared here so a command pays it once (`cyclesFastWith`/`precCyclesFastWith`
      consume it). -/
  present : List IssueId
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
  /-- The indexed views (ADR-0024): hash/bucket copies of `data`/`rollup`/
      `present`/`edges`/`pedges`/`prov`, built once per command so the per-row
      projections read each issue O(1)/O(deg) instead of O(N)/O(E). Built by
      `ViewIndex.of` from the same lists the fields above hold. -/
  idx : ViewIndex
  /-- A read-time refresh that could not run (no git, read-only FS): the read
      still served — a moment stale — and this carries the disclosure
      (ADR-0008 loud-not-silent; ADR-0016 §3 `RefreshOutcome.degraded`). `none`
      on the steady-state path. Write echoes leave it `none` (the write path
      surfaces its own pre-transact refresh degrade inline). -/
  refreshNote : Option String := none

/- View-construction note (an accepted cost): every command builds all the
   hoisted views eagerly, including single-issue reads and write echoes —
   each build is one pass, and `tl close` pays it three times (the
   pre-state view and `unblocksFast`'s two queues). The `present`/`edges`
   scans are now one-pass O(N + Σtags·|removed|) OR-Set enumerations
   (`presentElements` linearized in `b0f3ff5`; the issue OR-Set has no removes, so
   `present` is O(N); `edges` carries the dep/label tombstones); hoisting them here
   means a command pays each ONCE rather than per diagnostic/per row. -/

def View.state (v : View) : State := v.loaded.state

/-! ## Indexed-view row accessors (ADR-0024)

Each reads the once-built `ViewIndex` and equals — pointwise — the spec accessor
it replaces (the bridge named in each comment), so every routed render stays
byte-identical while the per-issue read drops from O(N)/O(E) to O(1)/O(deg).
Routed through by `issueRow`/`issueObj`/`issueLine`, `Render`'s
`displayState`/`styledLine`/`styledShow`/`treeLines`, and the `list`/`stats`/
`doctor` aggregates — the per-row Θ(N²)/Θ(N·E) cost class (ADR-0023). -/

/-- `s.issueData i` via the data hash (`issueDataH_eq`). -/
def View.issueData (v : View) (i : IssueId) : IssueData := (v.idx.dataH[i]?).getD IssueData.empty
/-- The short display id (ADR-0017 human surface; ADR-0018 ids): `tl-` + the
    shortest id prefix unambiguous over the present set, floored at
    `shortIdFloor`. Directly typable as a command argument — input resolution
    matches a prefix over the same present set (`resolveToken`). `--json` keeps
    the full id (the ADR-0020 contract): never depend on prefix length, which
    grows as issues are added. -/
def View.shortId (v : View) (i : IssueId) : String :=
  displayId (String.ofList (i.toList.take ((v.idx.shortLen[i]?).getD i.length)))
/-- `decide (s.hasIssue i)` via the present-issue set (`contains_hashSetOf_present`). -/
def View.has (v : View) (i : IssueId) : Bool := v.idx.presentH.contains i
/-- `effStatusWith v.rollup s i` via the rollup hash (`getElem?_hashAssoc_amap`); the
    `effectiveStatus` fallback is reached only for an id absent from the rollup. -/
def View.effStatus (v : View) (i : IssueId) : Status := (v.idx.rollupH[i]?).getD (v.state.effectiveStatus i)
/-- `effClosedWith v.rollup s i`. -/
def View.effClosed (v : View) (i : IssueId) : Bool := Status.closed (v.effStatus i)
/-- `provOf v.prov i` via the provenance hash. -/
def View.provFor (v : View) (i : IssueId) : Prov := (v.idx.provH[i]?).getD {}
/-- `kidsOfEdges v.pedges i` via the parent bucket (`getD_bucketBy`). -/
def View.kids (v : View) (i : IssueId) : List IssueId := (v.idx.pbk[i]?.getD []).reverse
/-- Is an epic (`!(kidsOfEdges …).isEmpty`). -/
def View.isEpic (v : View) (i : IssueId) : Bool := !(v.kids i).isEmpty
/-- `blockersOfE v.edges i` via the blocks-by-target bucket (`blocksByTarget_eq`). -/
def View.blockers (v : View) (i : IssueId) : List IssueId := (v.idx.btgt[i]?.getD []).reverse
/-- `dependentsOfE v.edges i` via the blocks-by-source bucket (`blocksBySource_eq`). -/
def View.dependents (v : View) (i : IssueId) : List IssueId := (v.idx.bsrc[i]?.getD []).reverse
/-- The issues symmetrically related to `i` — the other endpoint of every present
    `Related` edge touching it (the link drives nothing; it is filter/display only). -/
def View.relatedOf (v : View) (i : IssueId) : List IssueId :=
  v.edges.filterMap (fun (f, t, k) =>
    if k == EdgeKind.Related then (if f == i then some t else if t == i then some f else none) else none)
/-- The parents of `i` via the parent-by-child bucket (the canonical-parent
    candidates / the multi-parent count) — the swapped-pair `getD_bucketBy`. -/
def View.parents (v : View) (i : IssueId) : List IssueId := (v.idx.pbc[i]?.getD []).reverse
/-- `isReady`/`isReadyFast` via the hash/bucket views (`isReadyFastH_eq`). -/
def View.ready (v : View) (i : IssueId) : Bool :=
  State.isReadyFastH v.idx.presentH v.idx.rollupH v.idx.dataH v.idx.btgt v.idx.pbk v.state v.now i
/-- `blockedOf v.rollup v.edges s i` — open with an undischarged blocker, every
    read hashed (`blockerDischargedH_eq`; `.any` is order-independent). -/
def View.blocked (v : View) (i : IssueId) : Bool :=
  (v.issueData i).statusOf == .Open
    && (v.blockers i).any (fun b => !State.blockerDischargedH v.idx.presentH v.idx.rollupH v.state b)
/-- `deferredOf s v.now i` — open with a future `deferUntil`, status/defer hashed. -/
def View.deferred (v : View) (i : IssueId) : Bool :=
  (v.issueData i).statusOf == .Open
    && match (v.issueData i).deferUntilOf with | some t => v.now < t | none => false
/-- `duplicateOf s i` via the data hash — the stored `duplicate-of` target. -/
def View.duplicateOf (v : View) (i : IssueId) : Option IssueId :=
  match ((v.issueData i).metadata.find "duplicate-of").bind (·.value) with
  | some (some val) => if validId val then some val else none
  | _ => none
/-- The greatest surviving add-tag of an edge, via the edge-tag hash (=
    `maxTagOf v.state e`: `edgeTags[e]?.getD ∅ = v.state.edges.tagsOf e`, and the
    fold is identical). O(1) lookup vs the spec's O(E) `AMap.find`. -/
def View.maxTag (v : View) (e : Edge) : Option Stamp :=
  (AMap.keys (v.idx.edgeTags[e]?.getD FinSet.empty)).foldl
    (fun acc st => match acc with
      | none => some st
      | some m => some (if TotalOrd.le m st then st else m))
    none

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

/-- The canonical-parent LWW pick: among the candidate parents, the one whose
    greatest surviving `parent` add-tag is `(hlc, replica, nonce)`-greatest
    (ADR-0003 §4). The ONE canonicalization fold — both the spec `canonicalParent`
    and the view-hoisted `canonicalParentE` are a candidate source + a per-parent
    max-tag lookup over this core, so the logic cannot silently drift between them
    (the two sources are pinned equal by `canonicalParentTieTests` /
    `rowAccessorAgreementTests`). -/
def canonicalParentCore (parents : List IssueId)
    (maxTag : IssueId → Option Stamp) : Option IssueId := Id.run do
  let mut best : Option (IssueId × Stamp) := none
  for p in parents do
    if let some tag := maxTag p then
      best := match best with
        | none => some (p, tag)
        | some (bp, bt) => if TotalOrd.le bt tag then some (p, tag) else some (bp, bt)
  return best.map (·.1)

/-- The canonical display parent — the spec/reference: candidates from
    `parentsOf` (re-derives `presentEdges`), tags from `maxTagOf`. Production
    reads the hoisted `canonicalParentE`; this is the form tests compare to. -/
def canonicalParent (s : State) (i : IssueId) : Option IssueId :=
  canonicalParentCore (s.parentsOf i) (fun p => maxTagOf s (p, i, EdgeKind.Parent))

/-- The production canonical parent — the same `canonicalParentCore` fold over
    the hoisted views: candidates from the parent-by-child bucket (vs `parentsOf`
    re-deriving `presentEdges`) and tags from the edge-tag hash `v.maxTag` (vs an
    O(E) `tagsOf` find), so the tree's `isRoot` runs it O(deg)/row, not O(E)/row.
    Both inputs are pinned equal to the spec's, so the result is identical. -/
def canonicalParentE (v : View) (i : IssueId) : Option IssueId :=
  canonicalParentCore (v.parents i) (fun p => v.maxTag (p, i, EdgeKind.Parent))

def dependenciesJson (edges : List Edge) (i : IssueId) : Json :=
  let rows := edges.filter (fun (f, t, _) => f == i || t == i)
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
  let d := v.issueData i
  let pr := v.provFor i
  Json.mkObj <|
    [("id", Json.str (displayId i)),
     ("status", Json.str (statusWire d.statusOf)),
     ("effectiveStatus", Json.str (statusWire (v.effStatus i))),
     ("priority", jnum d.priorityOf.val),
     ("isEpic", Json.bool (v.isEpic i)),
     ("ready", Json.bool (v.ready i)),
     ("blocked", Json.bool (v.blocked i)),
     ("deferred", Json.bool (v.deferred i)),
     ("labels", labelsJson d),
     ("meta", metaJson d),
     ("dependencies", dependenciesJson v.edges i)]
    ++ optField "title" ((d.title.value).map (Json.str ∘ sanitizeSingle))
    ++ optField "assignee" ((d.assignee.value.getD none).map (Json.str ∘ sanitizeSingle))
    ++ optField "slug" ((d.slug.value.getD none).map (Json.str ∘ sanitizeSingle))
    ++ optField "description" ((d.description.value.getD none).map (Json.str ∘ sanitizeMulti))
    ++ optField "notes" ((d.notes.value.getD none).map (Json.str ∘ sanitizeMulti))
    ++ optField "deferUntil" ((d.deferUntilOf).map (Json.str ∘ Time.isoOfEpochMs))
    ++ optField "closeResolution"
        ((d.closeResolution.value.getD none).map (Json.str ∘ resolutionWire))
    ++ optField "parent" ((canonicalParentE v i).map (Json.str ∘ displayId))
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
  let d := v.issueData i
  let pr := v.provFor i
  Json.mkObj <|
    [("id", Json.str (displayId i)),
     ("status", Json.str (statusWire d.statusOf)),
     ("effectiveStatus", Json.str (statusWire (v.effStatus i))),
     ("priority", jnum d.priorityOf.val),
     ("isEpic", Json.bool (v.isEpic i)),
     ("ready", Json.bool (v.ready i)),
     ("blocked", Json.bool (v.blocked i)),
     ("deferred", Json.bool (v.deferred i)),
     ("dependencyCount", jnum (v.blockers i).length),
     ("dependentCount", jnum (v.dependents i).length)]
    ++ optField "title" ((d.title.value).map (Json.str ∘ sanitizeSingle))
    ++ optField "assignee" ((d.assignee.value.getD none).map (Json.str ∘ sanitizeSingle))
    ++ optField "createdAt" (pr.createdAt.map (Json.str ∘ hlcIso))
    ++ optField "updatedAt" (pr.updatedAt.map (Json.str ∘ hlcIso))

/-- One human line per issue (plain stage-1 output). -/
def issueLine (v : View) (i : IssueId) : String :=
  let d := v.issueData i
  let title := sanitizeSingle ((d.title.value).getD "(untitled)")
  let flags := String.intercalate ""
    [if v.isEpic i then " [epic]" else "",
     if v.blocked i then " [blocked]" else "",
     if v.deferred i then " [deferred]" else ""]
  s!"{displayId i}  p{d.priorityOf.val}  {statusWire (v.effStatus i)}  {title}{flags}"

end Tl.Cli
