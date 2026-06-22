/-
`Tl.Cli.Commands` — the stage-1 verbs (vision §stage 1, ADR-0020 shapes).

Every command returns `CmdOut` — the `--json` `data`, the human text, and
stderr notes (foreign-segment refusal disclosures, clamp warnings). Errors
travel as structured `Tl.Error`s; the dispatch layer owns streams and exit
codes. Write verbs run their guards *inside* the locked `transact` build
(against the under-lock state), so a refusal happens before any byte is
written; the pinned guard inventory (ADR-0008 §write-time guards) is exactly
`not-claimable` (claim of a non-ready target), and `not-closeable` (epic
`--as done`, self-duplicate). Re-closing with the same resolution (and, for
duplicate, the same canonical target) appends nothing and succeeds.
-/
import Tl.Cli.Project
import Tl.Cli.Render
import Tl.Cli.Resolve
import Tl.Cli.Init
import Tl.Kernel.Path
import Tl.Sync.Local
import Tl.Sync.Remote
import Tl.Sync.AutoSync

namespace Tl.Cli

open Tl.Store
open Tl.Kernel
open Tl.Format
open Tl.Crdt
open Lean (Json)

structure CmdOut where
  data : Json
  human : String
  notes : List String := []
  /-- Style-parameterized human rendering (ADR-0017). When present, `run`
      resolves the `Style` from flags/env/TTY and uses this instead of the
      plain `human` (which stays the `Style.plain` fallback). -/
  render : Option (Style → String) := none

/-- Load the read view (no lock — ADR-0015 §5). Before folding, run the
    read-time refresh (ADR-0016 §3): absorb any sibling's published changes
    from the shared `refs/tl/log` so a worktree sees its siblings without an
    explicit `tl sync`. Best-effort and lock-free — it never fails the read. -/
def loadView (dirOverride : Option String) (skipBad : Bool := false) : TlM View := do
  let d ← discover dirOverride
  let replica ← loadReplica d
  -- the read-time refresh returns a `degraded` reason when it could not run
  -- (git absent, read-only FS); surface it rather than serve a silently-stale
  -- view (ADR-0008). A racing concurrent refresher does not trip this — the
  -- foreign-segment writeback uses a per-call CSPRNG temp suffix + atomic
  -- rename (ADR-0016 §3 hardening), so `degraded` reflects a real inability to
  -- read the ref, not benign contention.
  let refresh ← Tl.Sync.refreshFromRef d (replica.map (·.id))
  let now ← liftSys (fun e => .mk' .internal s!"clock read failed: {e}") nowMs
  -- skew-check foreign segments against `now` (ADR-0007): a future-dated
  -- foreign op is deferred from the fold until local time catches up; the
  -- fold itself runs through the content-keyed cache (ADR-0022)
  let loaded ← readStateCached d skipBad (some now) (replica.map (·.id))
  let st := loaded.state
  -- bind each hoisted collection once: the base fields AND the indexed views
  -- both read them, so `effStatusAll`/`provenanceMap`/`parentEdgesFast` run once
  let rollup := st.effStatusAll
  let present := st.presentIssues
  let edges := st.presentEdges
  let pedges := parentEdgesFast st
  let prov := provenanceMap loaded.ops
  return { dirs := d, loaded, now, replica, rollup, present, edges, pedges, prov,
           idx := ViewIndex.of st.data rollup present edges pedges prov st.edges.adds.toList,
           refreshNote := refresh.degraded.map (fun r =>
             s!"served a moment-stale read: could not refresh from the shared ref ({r}) — fix git/filesystem access, then `tl sync` to catch up") }

/-- The disclosure for a skew-deferred op (ADR-0007), shared by the read and
    write paths so neither silently drops a future-dated op (ADR-0008
    loud-not-silent — a fold computed without some ops always says so). The op
    is not lost; it folds once local wall-clock passes its HLC. -/
def deferredNote (rid : String) (n : Nat) : String :=
  s!"segment {rid}.jsonl line {n}: held back — its HLC is beyond the clock-skew window ({rid}'s clock is ahead of yours); it folds once local time catches up — run `tl doctor`"

/-- The ADR-0008 command-level refusal policy for reads: a refused *own*
    segment fails the command; foreign refusals are disclosed on stderr and the
    read succeeds (folding the others). The all-refused catch-all only fires
    when there is *no own replica to anchor a partial read* — with an own
    replica present (even with no own segment yet), an all-*foreign* refusal is
    a disclosure, not a failure: read-time refresh (ADR-0016 §3) now routinely
    materializes sibling segments, so a single bad sibling segment must not
    take down a worktree whose own state is fine/empty. (`doctor` is exempt.) -/
def cleanReadNotes (v : View) : TlM (List String) := do
  if let some own := v.replica then
    if let some r := v.loaded.refused.find? (·.replicaId == own.id) then
      throw r.error
  if v.replica.isNone && !v.loaded.refused.isEmpty
      && v.loaded.refused.length == v.loaded.segmentCount then
    throw (v.loaded.refused.head?.map (·.error)
      |>.getD (.mk' .internal "every segment refused — repair or remove the damaged segments under .tl/log/"))
  return v.refreshNote.toList
    ++ v.loaded.refused.map (fun r =>
      s!"segment {r.replicaId}.jsonl refused (line {r.line}): folded the others; its owner repairs or re-syncs it")
    ++ v.loaded.warnings ++ v.loaded.skipped.map (fun (rid, n) =>
      s!"--skip-bad: dropped segment {rid}.jsonl line {n}")
    ++ v.loaded.deferred.map (fun (rid, n) => deferredNote rid n)

/-- The disclosure notes a write surfaces (ADR-0008: loud, never silent): a
    refused foreign segment OR a skew-deferred future op means the guards and
    echo were computed from a fold that dropped those ops. (An own-segment
    refusal already failed the transact.) Mirrors `cleanReadNotes`' drop
    categories so neither path silently omits a dropped op. -/
def writeNotes (ctx : TxContext) : List String :=
  ctx.loaded.refused.map (fun r =>
    s!"segment {r.replicaId}.jsonl refused (line {r.line}): this write was checked against a fold without it; its owner repairs or re-syncs it")
  ++ ctx.loaded.warnings
  ++ ctx.loaded.deferred.map (fun (rid, n) => deferredNote rid n)

/-- The post-write view: the pre-state plus the appended records. -/
def postView (v : TxContext) (parsed : List ParsedOp) (now : Nat) : View :=
  let state := parsed.foldl (fun s p => Tl.Kernel.apply s p.kernelOp) v.loaded.state
  let ops := v.loaded.ops ++ parsed
  let rollup := state.effStatusAll
  let present := state.presentIssues
  let edges := state.presentEdges
  let pedges := parentEdgesFast state
  let prov := provenanceMap ops
  { dirs := v.dirs
    loaded := { v.loaded with state, ops }
    now
    replica := some v.replica
    rollup, present, edges, pedges, prov
    idx := ViewIndex.of state.data rollup present edges pedges prov state.edges.adds.toList }

private def listPayload (key : String) (total : Nat) (rows : List Json) : Json :=
  Json.mkObj [("count", jnum total), (key, Json.arr rows.toArray)]

/-! ## Read verbs -/

/-- The styled one-line listing + footer (ADR-0017 §1/§3), shared by ready
    and list. `summary` is the footer's one-line; `total` drives the
    truncation disclosure. -/
private def listRender (v : View) (rows : List IssueId) (total : Nat) (summary empty : String)
    : Style → String := fun st =>
  if rows.isEmpty && total == 0 then empty
  else String.intercalate "\n" (rows.map (styledLine st v))
    ++ "\n" ++ footer st summary rows.length total

/-- The freshness window after which `ready` nudges to sync (ADR-0011 §2):
    a generous default — sync is opt-in (`--sync`), this only reminds. -/
def syncStaleWindowMs : Nat := 60 * 60 * 1000

/-- The plain stderr line emitted right before `tl sync`'s network leg, so an
    interactive sync over a slow remote is not silent. A one-shot notice, not a
    spinner or a timer; the resolved remote name interpolated for context. -/
def remoteSyncNotice (remote : String) : String :=
  s!"syncing with remote '{remote}'…"

/-- A full `tl sync` (local leg, the remote leg in a git repo, then a second
    local leg to absorb the remote's additions), recording the last-sync marker
    so `doctor`/`ready` never contact the remote themselves (ADR-0016). Shared by
    `cmdSync` and the `--sync` flag. -/
def performSync (d : Dirs) : TlM (Tl.Sync.LocalOutcome × Tl.Sync.RemoteOutcome × List String) := do
  let own ← loadReplica d
  let ownId := own.map (·.id)
  let l ← Tl.Sync.syncLocal d ownId
  -- announce the remote leg to stderr before the (possibly multi-second) network
  -- fetch/push. The notice fires only when a remote resolves; stdout JSON stays a
  -- single atomic object (progress is stderr-only). Sanitized — the remote name is
  -- attacker-influenceable git-config data, and this bypasses Main's stderr chokepoint.
  let r ← if l.ran then Tl.Sync.syncRemote d (announce := fun remote =>
            IO.eprintln s!"tl: {sanitizeSingle (remoteSyncNotice remote)}")
          else pure { ran := false, remote := "", pushed := false, pulled := false, tip := none }
  -- a second local leg after a remote that ran materializes what the fetch added
  -- (it can pull a new replica). Best-effort — the push already succeeded, so
  -- never fail here; a failure self-heals on the next read's refresh. Fold its
  -- absorb into the reported local outcome so a remote-pulled replica is not
  -- silently dropped from `absorbed`; disclose a failure (loud-not-silent).
  let (l, pnotes) ← if r.ran then
      (try
        let l2 ← Tl.Sync.syncLocal d ownId
        pure ({ l with absorbed := (l.absorbed ++ l2.absorbed).eraseDups, tip := l2.tip }, ([] : List String))
       catch e => pure (l, [s!"reconciled with the remote, but materializing the pulled changes locally failed ({e.message}) — the next read or `tl sync` will catch up"]))
    else pure (l, [])
  -- record last-sync only when the remote leg actually reconciled: lastSync means
  -- "last reconciled with the remote", so a local-only sync (no remote, or a
  -- remote added later) must not mark the view clean-vs-remote (a false-clean source).
  if r.ran then
    let now ← liftSys (fun e => .mk' .internal s!"{e}") nowMs
    try storeLastSync d now r.tip catch _ => pure ()
  return (l, r, pnotes)

/-- The local-only sync posture (no remote contact): the resolved upstream name
    (git config), the last-sync time, and how many `refs/tl/log` commits the local
    ref sits ahead of that last sync (unpushed). The live *behind* count needs the
    remote, so it is `--sync`'s job (sync then read), not this. -/
structure SyncPosture where
  upstream : Option String
  lastSyncMs : Option Nat
  ahead : Nat

/-- This replica's own-segment ops written since the last sync: lines (= ops) in
    `.tl/log/<own>.jsonl` on disk now, minus those in that segment at the synced
    ref tip. Both local (a fs read + a `cat-file`), no network — and it counts the
    *segment* ops, so it is correct in the main worktree too (where writes don't
    advance `refs/tl/log` until a sync, so a commit-based count reads a false 0). -/
private def ownOpsSince (d : Dirs) (own : String) (syncedTip : Option String) : TlM Nat := do
  let (segs, _) ← readSegments d
  let localLines := (segs.find? (·.replicaId == own)).elim 0 (fun sd => (completeLines sd.bytes).length)
  -- ops in the own segment at the synced tip; 0 when that sync left no ref (an
  -- empty / first sync) — then all local ops are unsynced, never a false 0.
  let syncedLines ← match syncedTip with
    | some t => pure (((← Tl.Sync.readRefAt d t).find? (·.replicaId == own)).elim 0
        (fun sd => (completeLines sd.bytes).length))
    | none => pure 0
  -- Nat subtraction clamps to 0 if the synced ref held more own-segment lines
  -- than disk — only possible under same-replica-id divergence, which ADR-0007
  -- rules out; the clamp is then a safe "not ahead" rather than a wrong count.
  return localLines - syncedLines

def syncPostureOf (d : Dirs) : TlM SyncPosture := do
  let upstream ← Tl.Sync.resolveRemote d
  let ls ← loadLastSync d
  let own := (← loadReplica d).map (·.id)
  let ahead ← match ls, own with
    | some (_, syncedTip), some o => ownOpsSince d o syncedTip
    | _, _ => pure 0  -- never synced ⇒ the "never synced" message/advisory covers it
  return { upstream, lastSyncMs := ls.map (·.1), ahead }

/-- `ready`'s staleness advisory from the local posture (`now` = the view clock).
    `none` ⇒ no advisory. Fires only with a configured remote, and reports the
    first applicable reason: never-synced, unsynced local changes, or a stale
    last-sync. -/
def stalenessMsg (p : SyncPosture) (now : Nat) : Option String :=
  match p.upstream with
  | none => none
  | some name =>
    match p.lastSyncMs with
    | none => some s!"view may be stale — never synced with '{name}'; run `tl sync` (or rerun with --sync)"
    | some ms =>
      if p.ahead > 0 then some s!"view may be stale — {p.ahead} local change(s) since last sync; run `tl sync`"
      else if now - ms > syncStaleWindowMs then some s!"view may be stale — last synced {(now - ms) / 60000}m ago; run `tl sync`"
      else none

def cmdReady (dirOverride : Option String) (limit : Nat) (skipBad : Bool) (sync : Bool) : TlM CmdOut := do
  let d ← discover dirOverride
  -- --sync reconciles first, best-effort: a read must not fail on a remote
  -- hiccup, so a sync error degrades to a note and the (still-useful) listing.
  let syncNotes ← if sync then
      (try (do let (_, _, pn) ← performSync d; pure pn)
       catch e => pure [s!"could not reconcile with the remote ({e.message}) — showing local state; run `tl sync`"])
    else pure []
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let ranked := State.readyFast v.rollup v.state v.now
  let capped := if limit == 0 then ranked else ranked.take limit
  -- staleness advisory (ADR-0011 §2): always derived from the posture after any
  -- --sync. A successful sync makes it clean (ahead 0, lastSync now ⇒ none); a
  -- failed --sync leaves genuine staleness, so it must still surface in
  -- data.staleness (agents read the field; humans also get the degrade note).
  let advisory ← (do pure (stalenessMsg (← syncPostureOf d) v.now))
  let r : Style → String := fun st =>
    (match advisory with | some a => st.paint "33" s!"({a})" ++ "\n" | none => "")
      ++ (listRender v capped ranked.length
            s!"Ready: {ranked.length} issue(s) with no active blockers" "nothing is ready") st
  let data := (listPayload "items" ranked.length (capped.map (issueRow v))).setObjVal!
                "staleness" (advisory.elim Json.null Json.str)
  return { data, human := r Style.plain, render := some r, notes := notes ++ syncNotes }

/-- When a claim goes stale: the epoch-ms instant `claimedAt + window`. `claimedAt`
    is an HLC, so its physical-ms component is `hlc / 2^16` (ADR-0007). Shared by
    `list --stale`, `claim --steal`, and `doctor`'s `staleClaims` so the staleness
    boundary cannot drift between them (ADR-0013). A claim is stale when `now` is
    past this. -/
def claimStaleDeadlineMs (claimedHlc windowMs : Nat) : Nat := claimedHlc / 2 ^ 16 + windowMs

def cmdList (dirOverride : Option String) (limit : Nat) (tree showAll skipBad : Bool)
    (labels : List String) (staleArg : Option String) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  -- every issue, oldest first; then by default hide effectively-closed
  -- issues (done/cancelled, incl. rolled-up epics) — `tl ready` shows
  -- workable, `tl list` shows open work, `tl list --all` shows everything
  -- (vision / ADR-0020 list-grammar decision).
  -- createdAt from the hoisted provenance map (one log pass), not s.createdAtOf
  -- (an O(N) add-tag find per issue ⇒ O(N²) over the sort). For a present issue
  -- both are the min create-tag HLC: createdAtOf is the min over add-tag HLCs,
  -- Prov.createdAt is the min-stamp create's HLC, and Stamp orders by HLC first,
  -- so they coincide (CrossTests pins it per seed). Default 0 = createdAtOf's nil.
  let createdAt := fun i => ((v.provFor i).createdAt).getD 0
  let sorted := (v.present.map (fun i => (createdAt i, i)))
    |>.mergeSort (fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2)))
    |>.map (·.2)
  -- `--label` facet (repeatable ⇒ AND): keep issues carrying every given label
  let sorted := if labels.isEmpty then sorted
    else sorted.filter (fun i => labels.all (v.issueData i).labels.presentElements.contains)
  -- `--stale <duration>` (mandatory arg, no default — ADR-0011 amendment): keep
  -- only stale claims — InProgress with a `claimedAt` older than the window,
  -- mirroring `doctor`/`claim --steal` via the shared `claimStaleDeadlineMs`.
  let staleWindow : Option Nat ← match staleArg with
    | none => pure none
    | some raw => match Time.parseDurationMs? raw with
      | some w => pure (some w)
      | none => throw (.mk' .usage s!"--stale: '{sanitizeSingle raw}' is not a valid duration — use e.g. 45m, 1h, 24h")
  let sorted := match staleWindow with
    | none => sorted
    | some w => sorted.filter (fun i =>
        (v.issueData i).statusOf == .InProgress
          && match (v.provFor i).claimedAt with
             | some h => v.now > claimStaleDeadlineMs h w
             | none => false)
  -- `--stale` already restricts to raw-InProgress claims; it must NOT then re-hide
  -- one whose epic rolled up to done (raw in_progress but effClosed) — that is
  -- exactly the lingering claim to surface, and `doctor`'s staleClaims (raw status,
  -- no effClosed gate) lists it. So a stale query bypasses the effClosed filter and
  -- is `--all`-independent, keeping the two surfaces in agreement (ADR-0013).
  let visible := if showAll || staleArg.isSome then sorted else sorted.filter (fun i => !v.effClosed i)
  let openN := (sorted.filter (fun i => (v.issueData i).statusOf == .Open)).length
  let inProg := (sorted.filter (fun i => (v.issueData i).statusOf == .InProgress)).length
  let summary :=
    if staleArg.isSome then
      s!"{visible.length} stale claim(s) (in progress, older than the --stale window)"
    else if showAll then s!"Total: {sorted.length} issues ({openN} open, {inProg} in progress)"
    else s!"{visible.length} open issues ({inProg} in progress) — --all includes closed"
  -- the --json data is the flat items array (the tree is a human browse mode
  -- only — ADR-0017 §2; a recursive JSON shape isn't pinned)
  let capped := if limit == 0 then visible else visible.take limit
  -- tree (the default render; `--flat` opts into one-line rows): a forest over
  -- the visible set. Roots = a visible issue with no visible canonical parent
  -- (an orphan, a dangling/cycle parent, or a parent hidden by the filter →
  -- top level, §2); closed children are pruned unless --all.
  let r : Style → String :=
    if tree then
      -- the visible set as a hash for O(1) "is the parent visible?" — the root
      -- test runs per visible issue, so a List `contains` here would be Θ(N²)
      let visSet := Tl.Kernel.hashSetOf visible
      let isRoot (i : IssueId) : Bool := match canonicalParentE v i with
        | none => true | some p => !visSet.contains p
      let roots := visible.filter isRoot
      let keep : IssueId → Bool := if showAll then (fun _ => true) else (fun i => !v.effClosed i)
      fun st =>
        if roots.isEmpty then (if visible.isEmpty then "no issues" else "(no top-level issues)")
        else
          -- cap the rendered ROWS (issues, top-to-bottom), not the roots: a human
          -- asked for `limit` issues, not `limit` whole subtrees (capping roots
          -- barely bit, since a few epics expand their entire subtrees). Render the
          -- forest in reading order, then take the first `limit` lines; the footer
          -- discloses how many rows are hidden (a truncated subtree's dangling
          -- `├──` together with "Showing X of Y" reads as "more below").
          let allLines := treeForest st v roots keep v.kids
          let shown := if limit == 0 then allLines else allLines.take limit
          String.intercalate "\n" shown
            ++ "\n" ++ footer st summary shown.length allLines.length
    else listRender v capped visible.length summary "no issues"
  return { data := listPayload "items" visible.length (capped.map (issueRow v))
           human := r Style.plain, render := some r, notes }

/-- The `show` claim block: surfaces this replica's latest own claim on the
    issue. Decoupled from staleness (ADR-0013, amended) — your own claim
    provenance is shown regardless of age; the stale *window* is a `doctor`
    concern (`tl.staleAfter`), not a display gate here. `outcome` is `won` when
    the assignee is still this actor, else `superseded`. -/
def claimBlock (v : View) (i : IssueId) : Option Json := do
  let own ← v.replica
  let ownVal ← own.toNat?
  let claims := v.loaded.ops.filterMap (fun p =>
    match p.op with
    | .claim ci actor => if ci == i && p.stamp.replica == ownVal then some (p.stamp, actor) else none
    | _ => none)
  -- latest own claim by the full stamp order (the cross-op comparison rule,
  -- Tl/Cli/Project.lean §provenance)
  let (_, actor) ← claims.foldl (fun acc c =>
    match acc with
    | none => some c
    | some m => some (if Tl.Crdt.TotalOrd.le m.1 c.1 then c else m)) none
  let current := (v.state.issueData i).assignee.value.getD none
  some (Json.mkObj
    [("outcome", Json.str (if current == some actor then "won" else "superseded")),
     ("currentAssignee", current.elim Json.null Json.str)])

def cmdShow (dirOverride : Option String) (tok : String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let base := issueObj v i
  let data := match claimBlock v i with
    | some cb => base.setObjVal! "claim" cb
    | none => base
  let r : Style → String := fun st => styledShow st v i
  return { data, human := r Style.plain, render := some r, notes }

def cmdWhy (dirOverride : Option String) (tok : String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let s := v.state
  let d := s.issueData i
  if State.isReadyWith v.rollup s v.now i then
    return { data := Json.mkObj [("id", Json.str (displayId i)), ("ready", Json.bool true)]
             human := s!"{displayId i} is ready", notes }
  -- fuel = |presentIssues|; reuse the view's hoisted scan (presentElements is Θ(N²))
  let trans := State.whyFastH v.idx.btgt v.idx.presentH v.idx.rollupH s v.present.length i
  -- a node's children in the why-tree are its LIVE direct blockers (present and
  -- not effectively-closed) — the same liveSuccE relation whyFast's transitive
  -- closure is built from, so the tree's node set equals `trans` (the JSON set),
  -- just with the clear-this-first order, diamonds, and depth made visible.
  -- Every read indexed (btgt bucket + hashed discharge, like `View.blocked`), so
  -- the per-node tree descent stays O(deg) — never an O(E) edge rescan per node.
  let liveBlockers : IssueId → List IssueId := fun x =>
    (v.blockers x).filter (fun b =>
      !State.blockerDischargedH v.idx.presentH v.idx.rollupH v.state b)
  let direct := liveBlockers i
  let rows := trans.map (fun b =>
    let bd := s.issueData b
    Json.mkObj <|
      [("id", Json.str (displayId b)),
       ("status", Json.str (statusWire bd.statusOf)),
       ("effectiveStatus", Json.str (statusWire (State.effStatusWith v.rollup s b))),
       ("direct", Json.bool (direct.contains b))]
      ++ (match bd.title.value with
          | some t => [("title", Json.str (sanitizeSingle t))]
          | none => []))
  let data := Json.mkObj <|
    [("id", Json.str (displayId i)), ("ready", Json.bool false),
     ("status", Json.str (statusWire d.statusOf)),
     ("isEpic", Json.bool (s.isEpic i))]
    ++ (if rows.isEmpty then [] else [("blockedBy", Json.arr rows.toArray)])
    ++ (match d.deferUntilOf with
        | some t => if v.now < t then [("deferUntil", Json.str (Time.isoOfEpochMs t))] else []
        | none => [])
  -- human: the blocker chain as a tree (ADR-0017 §2) — single-rooted at `i`'s
  -- direct live blockers, each expanded over the same liveBlockers accessor;
  -- cycles render "↺", shared blockers render once and mark re-encounters.
  -- JSON stays the flat blockedBy refs above (agents don't read the tree).
  let r : Style → String := fun st =>
    if trans.isEmpty then s!"{displayId i} is not ready (no open blockers — check status/epic/defer)"
    else s!"{displayId i} waits on:\n" ++
      String.intercalate "\n" (treeForest st v direct (fun _ => true) liveBlockers)
  return { data, human := r Style.plain, render := some r, notes }

/-- `unblocks <id>` — the downward mirror of `why`: the issues that would
    become ready if `<id>` closed (the proved ready-diff `unblocksFast`,
    ADR-0004 thm 10). A dependent still pinned by another blocker is not freed
    and so does not appear. -/
def cmdUnblocks (dirOverride : Option String) (tok : String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let s := v.state
  let freed := State.unblocksFast s v.now i
  let rows := freed.map (fun b =>
    let bd := s.issueData b
    Json.mkObj <|
      [("id", Json.str (displayId b)),
       ("status", Json.str (statusWire bd.statusOf)),
       ("effectiveStatus", Json.str (statusWire (State.effStatusWith v.rollup s b)))]
      ++ (match bd.title.value with
          | some t => [("title", Json.str (sanitizeSingle t))]
          | none => []))
  let data := Json.mkObj
    [("id", Json.str (displayId i)),
     ("freed", Json.arr rows.toArray),
     ("count", jnum freed.length)]
  let human :=
    if freed.isEmpty then s!"closing {displayId i} would free nothing right now (no dependent becomes ready)"
    else s!"closing {displayId i} unblocks:\n" ++
      String.intercalate "\n" (freed.map (fun b => "  " ++ issueLine v b))
  return { data, human, notes }

def cmdDepCycles (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let s := v.state
  let entry (kind : String) (issues : List IssueId) : Json :=
    Json.mkObj [("kind", Json.str kind),
                ("issues", Json.arr (issues.map (Json.str ∘ displayId)).toArray)]
  -- each diagnostic computed exactly once per invocation (the fast forms,
  -- bridged to the spec by cyclesFast_eq/precCyclesFast_eq), and over the
  -- view's pre-hoisted present/edges/pedges so the Θ(N²) scans aren't redone
  -- per graph (cyclesFastWith/precCyclesFastWith)
  let blocksCycles := State.cyclesFastWith v.present v.edges EdgeKind.Blocks
  let parentCycles := State.cyclesFastWith v.present v.edges EdgeKind.Parent
  let structural := blocksCycles ++ parentCycles
  -- a ≺-cycle whose node set coincides with a structural witness is already
  -- diagnosed by that row; only genuinely mixed deadlocks add a readiness row
  let readiness := (State.precCyclesFastWith v.rollup v.present v.edges v.pedges s).filter
    (fun w => !structural.contains w)
  let rows := blocksCycles.map (entry "blocks")
    ++ parentCycles.map (entry "parent")
    ++ readiness.map (entry "readiness")
  return { data := listPayload "cycles" rows.length rows
           human :=
             if rows.isEmpty then "no cycles"
             else s!"{rows.length} cycle(s) — break each with `tl dep remove`"
           notes }

/-- The cycle count (structural per kind + the non-duplicate readiness
    deadlocks), shared with `doctor`'s graph check. Reads the view's
    pre-hoisted present/edges/pedges (one Θ(N²)/Θ(E²) scan total, not three). -/
private def cycleCount (v : View) : Nat :=
  let s := v.state
  let structural := State.cyclesFastWith v.present v.edges EdgeKind.Blocks
    ++ State.cyclesFastWith v.present v.edges EdgeKind.Parent
  structural.length
    + ((State.precCyclesFastWith v.rollup v.present v.edges v.pedges s).filter
        (fun w => !structural.contains w)).length

def cmdStats (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let s := v.state
  let issues := v.present
  let byEff (st : Status) : Nat := (issues.filter (fun i => v.effStatus i == st)).length
  let ready := (State.readyFast v.rollup s v.now).length
  let blocked := (issues.filter v.blocked).length
  let deferred := (issues.filter v.deferred).length
  let cycles := cycleCount v
  -- count effective status (rollup-aware): a rolled-up epic counts as done,
  -- exactly as `list`/the glyphs render it — never the raw stored field, which
  -- would report a finished epic as still "open" and disagree with `list`
  -- (ADR-0020 §stats amendment). `open` is split into epics vs tasks so a
  -- stored-open-but-rolled-up epic is never miscounted as workable.
  let openIssues := issues.filter (fun i => v.effStatus i == .Open)
  let openN := openIssues.length
  let openEpics := (openIssues.filter v.isEpic).length
  let openTasks := openN - openEpics
  let inProg := byEff .InProgress
  let doneN := byEff .Done
  let cancelledN := byEff .Cancelled
  let data := Json.mkObj
    [("total", jnum issues.length),
     ("open", jnum openN), ("openEpics", jnum openEpics), ("openTasks", jnum openTasks),
     ("inProgress", jnum inProg), ("done", jnum doneN), ("cancelled", jnum cancelledN),
     ("ready", jnum ready), ("blocked", jnum blocked),
     ("deferred", jnum deferred), ("cycles", jnum cycles)]
  let plural := fun (n : Nat) (w : String) => toString n ++ " " ++ w ++ (if n == 1 then "" else "s")
  let openBreak := plural openEpics "epic" ++ " · " ++ plural openTasks "task"
  -- a small labelled block (§5); §7: green marks the workable (ready) count, so
  -- the open row renders neutral and the derived ready count takes green
  let r : Style → String := fun st =>
    let c (ds : DState) (n : Nat) : String := st.paint ds.colorCode s!"{ds.word} {n}"
    s!"{issues.length} issues\n"
      ++ "  " ++ String.intercalate " · " [s!"open {openN} ({openBreak})", c .inProgress inProg, c .done doneN, c .cancelled cancelledN] ++ "\n"
      ++ "  " ++ String.intercalate " · "
           [st.paint DState.ready.colorCode s!"ready {ready}", c .blocked blocked, c .deferred deferred,
            (if cycles > 0 then st.paint "31" s!"cycles {cycles}" else s!"cycles {cycles}")]
  return { data, human := r Style.plain, render := some r, notes }

/-- The issue ids an op touches (for `tl log`'s per-issue filter and the
    entry's `targets`): the subject for scalar/meta/label ops, both endpoints
    for edge ops. -/
private def opTargets : WireOp → List IssueId
  | .create id _ | .update id _ | .claim id _ | .close id _ | .reopen id
  | .defer id _ | .undefer id | .metaSet id _ _
  | .labelAdd id _ | .labelRemove id _ _ => [id]
  | .depAdd (f, t, _) | .relate (f, t, _)
  | .depRemove (f, t, _) _ | .unrelate (f, t, _) _ => [f, t]

/-- A resumable change-feed cursor (ADR-0025): for each replica (decoded id) the
    highest `(HLC, nonce)` already delivered. The log's intra-replica order is
    `(HLC, nonce)` — two ops can share an HLC and are separated by the nonce
    (ADR-0007) — so the cursor tracks both. An op is emitted iff its `(HLC, nonce)`
    exceeds its replica's threshold. A scalar high-water mark drops a late op below
    another replica's max; a per-replica HLC-only frontier drops a same-HLC tie;
    this drops neither. -/
private abbrev LogCursor := AMap Nat (Nat × Nat)

/-- A replica's threshold, or `none` when it was never delivered. An absent
    threshold is below everything — including a `(0, 0)` stamp — so an empty cursor
    is the full history, not "everything strictly above `(0, 0)`". -/
private def cursorThreshold (c : LogCursor) (replica : Nat) : Option (Nat × Nat) :=
  c.find replica

/-- An op's `(HLC, nonce)` is strictly after a threshold (lexicographic); an
    absent threshold (`none`) is below everything. -/
private def stampAfter (hlc nonce : Nat) (thr : Option (Nat × Nat)) : Bool :=
  match thr with
  | none => true
  | some (th, tn) => Nat.blt th hlc || (th == hlc && Nat.blt tn nonce)

/-- The greater of `(hlc, nonce)` and a threshold. -/
private def maxStamp (hlc nonce : Nat) (thr : Option (Nat × Nat)) : Nat × Nat :=
  if stampAfter hlc nonce thr then (hlc, nonce) else thr.getD (hlc, nonce)

/-- Fold ops into a cursor, keeping the per-replica maximum `(HLC, nonce)`. -/
private def advanceCursor (base : LogCursor) (ops : List ParsedOp) : LogCursor :=
  ops.foldl (fun m p =>
    m.insert p.stamp.replica (maxStamp p.stamp.hlc p.stamp.nonce (cursorThreshold m p.stamp.replica))) base

/-- An op's `(HLC, nonce)` is strictly before a threshold (lexicographic); an
    absent threshold (`none`) is *above* everything — the dual of `stampAfter`.
    For `--until` (backward) a replica with no recorded edge is unconstrained, so
    all of its ops are candidates, exactly as an empty cursor is full history. -/
private def stampBefore (hlc nonce : Nat) (thr : Option (Nat × Nat)) : Bool :=
  match thr with
  | none => true
  | some (th, tn) => Nat.blt hlc th || (hlc == th && Nat.blt nonce tn)

/-- The lesser of `(hlc, nonce)` and a threshold. -/
private def minStamp (hlc nonce : Nat) (thr : Option (Nat × Nat)) : Nat × Nat :=
  if stampBefore hlc nonce thr then (hlc, nonce) else thr.getD (hlc, nonce)

/-- Fold ops into a cursor, keeping the per-replica *minimum* `(HLC, nonce)` — the
    frontier just below the oldest delivered op (`min` is order-independent, so the
    page list may be in either sort order). Emitting `(hlc, nonce) < this` (per
    replica) yields the ops older than the page's oldest delivered op, and a replica
    absent from the page (unconstrained, `none`) keeps all its ops as candidates.
    In a newest-first page (plain / `--until`) the page is a top-suffix of the total
    order, so "older than the oldest delivered" is exactly the not-yet-shown
    remainder — backward paging is gap-free. In an oldest-first `--since` page the
    delivered slice is a bottom-prefix of the delta, so this edge points below the
    feed's oldest op (into pre-feed history); the *forward* remainder of a `--since`
    feed is reached by `cursor.since`, not this edge. The dual of `advanceCursor`. -/
private def retreatCursor (base : LogCursor) (ops : List ParsedOp) : LogCursor :=
  ops.foldl (fun m p =>
    m.insert p.stamp.replica (minStamp p.stamp.hlc p.stamp.nonce (cursorThreshold m p.stamp.replica))) base

/-- Serialize a cursor as comma-joined `<replica>:<hlc>:<nonce>` triples, the
    replica in its canonical 13-char Crockford form, sorted by replica
    (`AMap.toList`). -/
private def renderCursor (c : LogCursor) : String :=
  String.intercalate "," (c.toList.map (fun (r, hn) => s!"{toCrockford r 13}:{hn.1}:{hn.2}"))

/-- Parse a `--since`/`--until` cursor (`edge` is the flag/object field name,
    `"since"` or `"until"`): comma-joined `<replica>:<hlc>:<nonce>` triples (the
    matching edge of a prior `tl log`'s `cursor` object). A trimmed-empty token is
    the empty cursor (full history); anything else is validated as strictly as the
    wire decoder (`decodeStamp`) — an empty/extra `:`-segment, a stray comma, a
    non-canonical or `≥ 2^64` replica, an hlc `≥ 2^64` or nonce `≥ 2^128`, or a
    non-numeric hlc/nonce is a usage error that names the expected shape, never a
    silent full dump. -/
private def parseCursor (edge : String) (s : String) : Except Tl.Error LogCursor := do
  let t := s.trimAscii.toString
  if t.isEmpty then return AMap.empty
  let mut c : LogCursor := AMap.empty
  for piece in t.splitOn "," do
    match piece.splitOn ":" with
    | [rid, hstr, nstr] =>
      let ridT := rid.trimAscii.toString
      match ofCrockford? ridT, hstr.trimAscii.toString.toNat?, nstr.trimAscii.toString.toNat? with
      | some r, some h, some n =>
        -- mirror `decodeStamp`: a canonical 13-char Crockford replica below 2^64,
        -- the hlc below 2^64, the nonce below 2^128
        let okReplica := ridT.length == 13 && toCrockford r 13 == ridT && decide (r < 2 ^ 64)
        let okStamp := decide (h < 2 ^ 64) && decide (n < 2 ^ 128)
        if okReplica && okStamp then
          -- a self-produced cursor has one triple per replica (`renderCursor`),
          -- but a hand-edited one may repeat a replica; collapse to the most
          -- conservative bound — the tightest that never over-emits: the maximum
          -- for a lower bound (`since`), the minimum for an upper bound (`until`).
          let folded := if edge == "until" then minStamp h n (cursorThreshold c r)
                        else maxStamp h n (cursorThreshold c r)
          c := c.insert r folded
        else if !okReplica then
          throw (.mk' .usage
            s!"--{edge}: '{ridT}' is not a canonical 13-char replica id below 2^64 — pass the `cursor.{edge}` from a prior `tl log --json`")
        else
          throw (.mk' .usage
            s!"--{edge}: '{piece}' has an out-of-range hlc or nonce (hlc < 2^64, nonce < 2^128) — pass the `cursor.{edge}` from a prior `tl log --json`")
      | _, _, _ => throw (.mk' .usage
          s!"--{edge}: bad cursor segment '{piece}' (expected <replica>:<hlc>:<nonce>) — pass the `cursor.{edge}` from a prior `tl log --json`")
    | _ => throw (.mk' .usage
        s!"--{edge}: bad cursor segment '{piece}' (expected <replica>:<hlc>:<nonce>) — pass the `cursor.{edge}` from a prior `tl log --json`")
  return c

/-- `tl log [<id>] [--since <cursor>] [--until <cursor>]`: an HLC-ordered
    projection over the op log (ADR-0008), optionally filtered to ops touching one
    issue. Without bounds it lists newest-first (capped by `--limit`). `--since` is
    a resumable forward change-feed — every op after the lower cursor, oldest-first,
    exactly-once. `--until` browses history backward — every op before the upper
    cursor, newest-first, best-effort (a still-merging log can gain an op below a
    page already passed, ADR-0025). Given both, the bounds compose into a window.
    Every response carries a dual-edge `cursor` object `{ since, until }` (field
    names match the flags) so each page is self-navigating: pass `cursor.since` to
    `--since` to continue forward, `cursor.until` to `--until` to page older. The
    cursor is scoped to the `<id>` filter it was produced under: resume with the
    same filter. -/
def cmdLog (dirOverride : Option String) (idTok : Option String) (limit : Nat)
    (since untilC : Option String) (skipBad : Bool) : TlM CmdOut := do
  -- parse both cursors before loading, so a malformed bound fails fast
  let sinceCur ← MonadExcept.ofExcept (parseCursor "since" (since.getD ""))
  let untilCur ← MonadExcept.ofExcept (parseCursor "until" (untilC.getD ""))
  let sinceGiven := since.isSome
  let untilGiven := untilC.isSome
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let visible ← match idTok with
    | none => pure v.loaded.ops
    | some tok =>
      let i ← MonadExcept.ofExcept (resolveToken v.state tok)
      pure (v.loaded.ops.filter (fun p => (opTargets p.op).contains i))
  -- `--since` keeps ops strictly after its lower cursor (per replica), `--until`
  -- strictly before its upper cursor; together a bounded window. Each bound is
  -- per-replica (HLC, nonce), so an absent edge is unconstrained on that side.
  let matching := visible.filter (fun p =>
    (!sinceGiven || stampAfter p.stamp.hlc p.stamp.nonce (cursorThreshold sinceCur p.stamp.replica))
      && (!untilGiven || stampBefore p.stamp.hlc p.stamp.nonce (cursorThreshold untilCur p.stamp.replica)))
  -- `--since` is a forward feed (oldest-first); plain and `--until` read
  -- newest-first (backward browsing). Both use the full stamp order
  -- (deterministic on equal HLCs).
  let ordered :=
    if sinceGiven then matching.mergeSort (fun a b => decide (Tl.Crdt.TotalOrd.le a.stamp b.stamp))
    else matching.mergeSort (fun a b => decide (Tl.Crdt.TotalOrd.le b.stamp a.stamp))
  let capped := if limit == 0 then ordered else ordered.take limit
  -- Resume-forward (since) edge: in since-mode the lower cursor raised by the
  -- delivered (capped) page, so a paged resume never skips/replays; otherwise the
  -- full frontier of the visible log (a point to tail from the newest). Resume-back
  -- (until) edge: the per-replica minimum of the delivered page — the frontier just
  -- below the oldest delivered op — so `--until` pages strictly older. Both edges
  -- always bracket the *delivered* page, so no op is lost: in a `--since` feed the
  -- forward remainder is reached by `cursor.since` (the until edge then points into
  -- pre-feed history, and a one-op page makes the two edges coincide — expected,
  -- not a skip; see `cliLogUntilTests` (windowed forward + limit)).
  let sinceEdge := if sinceGiven then advanceCursor sinceCur capped else advanceCursor AMap.empty visible
  -- accumulate from the input upper bound, not from empty: a replica bounded by a
  -- prior backward page must stay bounded, or paging further back re-delivers its
  -- already-seen ops (a replica absent from this page would otherwise reset to
  -- unconstrained). The dual of `advanceCursor sinceCur` for the forward feed.
  let untilEdge := retreatCursor untilCur capped
  let entry (p : ParsedOp) : Json :=
    Json.mkObj
      [("timestamp", Json.str (hlcIso p.stamp.hlc)),
       ("op", Json.str p.op.wire),
       ("actor", p.actor.elim Json.null (Json.str ∘ sanitizeSingle)),
       ("targets", Json.arr ((opTargets p.op).map (Json.str ∘ displayId)).toArray)]
  -- the human line shows each target's current title (ADR-0025): read through the
  -- O(1) indexed view (ADR-0024 `View.issueData`, not an O(N) per-op find),
  -- sanitized (attacker-controllable, ADR-0014) and truncated. A dangling or
  -- untitled target falls back to the bare id. The `--json` entry above stays
  -- id-keyed with no title (a deliberate human/json divergence, ADR-0025): the
  -- feed is an immutable op stream, the title is mutable state derived from the id.
  let titleSuffix (i : IssueId) : String :=
    match (v.issueData i).title.value with
    | none => ""
    | some raw =>
      let s := sanitizeSingle raw
      " " ++ (if s.length > 48 then String.ofList (s.toList.take 48) ++ "…" else s)
  let line (p : ParsedOp) : String :=
    -- actor is attacker-controllable (ADR-0014 T1) — sanitize for the human terminal,
    -- mirroring the `--json` arm above (titles/labels/meta all wrap it too)
    s!"{hlcIso p.stamp.hlc}  {p.op.wire}  {(p.actor.elim "—" sanitizeSingle)}  " ++
      String.intercalate ", " ((opTargets p.op).map (fun t => displayId t ++ titleSuffix t))
  let sinceStr := renderCursor sinceEdge
  let untilStr := renderCursor untilEdge
  -- newest-first pages (plain/`--until`) overflow into "older"; the forward feed
  -- (`--since`) overflows into "more".
  let body :=
    if matching.isEmpty then "no ops"
    else String.intercalate "\n" (capped.map line)
      ++ (if capped.length < matching.length then
            s!"\n… {matching.length - capped.length} {if sinceGiven then "more" else "older"} (--limit 0 for all)" else "")
  let cursorParts := (if sinceStr.isEmpty then [] else [s!"since={sinceStr}"])
                   ++ (if untilStr.isEmpty then [] else [s!"until={untilStr}"])
  return { data := Json.mkObj [("count", jnum matching.length),
                               ("entries", Json.arr (capped.map entry).toArray),
                               ("cursor", Json.mkObj [("since", Json.str sinceStr),
                                                      ("until", Json.str untilStr)])]
           human := body ++ (if cursorParts.isEmpty then ""
                             else "\ncursor: " ++ String.intercalate " " cursorParts)
           notes }

/-! ## Write verbs -/

private def writeNow (v : TxContext) (parsed : List ParsedOp) : View :=
  postView v parsed v.now

def cmdCreate (dirOverride : Option String) (title : String) (priority : Option Nat)
    (description slug : Option String) (actor : String)
    (blockedBy blocks parents related : List String) : TlM CmdOut := do
  let edgeCount := blockedBy.length + blocks.length + parents.length + related.length
  let prio : Option (Fin 5) := priority.map (fun p => ⟨min p 4, Nat.lt_succ_of_le (Nat.min_le_right p 4)⟩)
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor)
    (1 + edgeCount) (fun ctx stamps => do
      let some st := stamps.head? | .error (.mk' .internal "no stamp")
      let id := mintIssueId st
      let resolveAll (toks : List String) : Except Tl.Error (List IssueId) :=
        toks.mapM (resolveToken ctx.loaded.state)
      let bby ← resolveAll blockedBy
      let bls ← resolveAll blocks
      let pars ← resolveAll parents
      let rels ← resolveAll related
      let edgeOps : List WireOp :=
        bby.map (fun b => .depAdd (b, id, EdgeKind.Blocks))
        ++ bls.map (fun c => .depAdd (id, c, EdgeKind.Blocks))
        ++ pars.map (fun e => .depAdd (e, id, EdgeKind.Parent))
        ++ rels.map (fun r =>
            .relate (if decide (id ≤ r) then (id, r, EdgeKind.Related)
                     else (r, id, EdgeKind.Related)))
      .ok (WireOp.create id
        { title := some title, priority := prio, description := description.map some, slug := slug.map some }
        :: edgeOps))
  let v := writeNow ctx parsed
  let some newId := parsed.head?.bind (fun p =>
      match p.op with | .create i _ => some i | _ => none)
    | throw (.mk' .internal "create wrote no create record")
  return { data := issueObj v newId
           human := s!"Created {displayId newId}  {sanitizeSingle title}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- After a durable claim, re-derive the echo from the freshly-synced state via
    `reload`; if that reload fails (a transient FS / clock-read error), fall back to
    the post-write `fallback` view with a disclosure note — a durable claim must
    never report failure (an exit-code-branching agent would spuriously retry into a
    second claim). Extracted so the fallback branch is unit-testable without
    injecting a real FS failure. -/
def reloadOrFallback (reload : TlM View) (fallback : View) (i : IssueId) :
    TlM (View × List String) :=
  try (do let vf ← reload; pure (vf, ([] : List String)))
  catch e =>
    pure (fallback, [s!"the claim is recorded but the post-sync reload failed ({e.message}); this echo reflects local state — re-read with `tl show {displayId i}`"])

def cmdClaim (dirOverride : Option String) (tok : String) (actor : String)
    (sync verify steal : Bool) (staleArg : Option String) : TlM CmdOut := do
  -- `--stale` only sets the window for `--steal`; alone it is a usage error so a
  -- typo (`--stale 1h` without `--steal`) never silently does a plain claim.
  if staleArg.isSome && !steal then
    throw (.mk' .usage "--stale sets the staleness window for --steal — pass --steal too, or drop --stale")
  -- freshness preflight (ADR-0001 §5): with --sync/--verify, reconcile against
  -- the remote before the take, so the not-claimable check sees the freshest
  -- reachable state. --verify warns-and-degrades when no remote is configured
  -- (it still checks against the freshest local state, via preWriteRefresh below).
  let preNotes ← if sync || verify then do
      let d0 ← discover dirOverride
      let hasRemote := (← Tl.Sync.resolveRemote d0).isSome
      -- --verify is a gate: a configured-but-unreachable remote fails the claim
      -- (verify-failed) so a take is never made against unverified state; with no
      -- remote it degrades (claiming locally is fine). --sync alone is best-effort:
      -- a reconcile failure degrades with a note, never blocking the take.
      (try
        let (_, _, pn) ← performSync d0
        if verify && !hasRemote then
          pure ("verified against local state only — no remote is configured to fetch from" :: pn)
        else pure pn
       catch e =>
        if verify then
          throw (.mk' .verifyFailed
            s!"could not verify against the remote ({e.message}) — retry when it is reachable, or run `tl claim` without --verify to take against local state")
        else
          pure [s!"claimed against local state — could not reconcile with the remote first ({e.message}); run `tl sync`"])
    else pure []
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  -- the staleness window for --steal: inline --stale wins over tl.staleAfter.
  -- Inline (explicit input) fails fast on a bad value; the config is LENIENT — a
  -- malformed tl.staleAfter never blocks a plain/ready/own claim (only the
  -- take-over-someone-else path needs a window, and it reports the bad config
  -- there). No --steal ⇒ no read, no window.
  let inlineMs : Option Nat ← match staleArg with
    | none => pure none
    | some raw =>
      match Time.parseDurationMs? raw with
      | some w => pure (some w)
      | none => throw (.mk' .usage s!"--stale: '{sanitizeSingle raw}' is not a valid duration — use e.g. 45m, 1h, 24h")
  let cfgRaw ← if steal && staleArg.isNone then Tl.Sync.gitConfig d "tl.staleAfter" else pure none
  let cfgMs : Option Nat := cfgRaw.bind Time.parseDurationMs?
  -- a set-but-unparseable config: surfaced only on the take-over path that needs it
  let cfgBadMsg : Option String := match cfgRaw with
    | some raw => if cfgMs.isNone then
        some s!"git config tl.staleAfter='{sanitizeSingle raw}' is not a valid duration — fix it or pass --stale" else none
    | none => none
  let thresholdMs : Option Nat := inlineMs.orElse (fun _ => cfgMs)
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    let rm := s.effStatusAll
    let dta := s.issueData i
    let direct := (s.blockersOf i).filter (fun b => !State.blockerDischargedWith rm s b)
    let claimedBy := dta.assignee.value.getD none
    let deferActive := match dta.deferUntilOf with | some t => ctx.now < t | none => false
    -- `--steal` overrides ONLY an existing claim (in_progress + assigned) on an
    -- otherwise-workable item (not epic/deferred/blocked).
    let onlyClaimObstacle := dta.statusOf == .InProgress && claimedBy.isSome
      && !s.isEpic i && !deferActive && direct.isEmpty
    let holder := (claimedBy.map sanitizeSingle).getD "someone"
    let reasons := Json.mkObj <|
      (if dta.statusOf != .Open then [("status", Json.str (statusWire dta.statusOf))] else [])
      ++ (match claimedBy with | some a => [("assignee", Json.str a)] | none => [])
      ++ (if s.isEpic i then [("isEpic", Json.bool true)] else [])
      ++ (match dta.deferUntilOf with
          | some t => if ctx.now < t then [("deferUntil", Json.str (Time.isoOfEpochMs t))] else []
          | none => [])
      ++ (if direct.isEmpty then [] else
          [("blockedBy", Json.arr (direct.map (Lean.Json.str ∘ displayId)).toArray)])
    let notClaimable : String → Tl.Error := fun msg =>
      { code := .notClaimable, message := msg,
        context := [("id", .str (displayId i)), ("reasons", reasons)] }
    -- the verdict for taking over someone else's claim: a stale-claim courtesy
    -- guard, never merge-enforced (ADR-0013) — concurrent steals reconcile by LWW
    -- and the loser reads "superseded".
    let stealVerdict : Except Tl.Error (List WireOp) :=
      match thresholdMs with
      | none => .error (.mk' .usage <| cfgBadMsg.getD
          s!"{displayId i} is claimed by {holder}; --steal needs a staleness window — pass --stale <duration> (e.g. 1h) or set `git config tl.staleAfter`")
      | some w =>
        match (provenanceOf ctx.loaded.ops i).claimedAt with
        | none => .error (notClaimable
            s!"{displayId i} is claimed by {holder} but carries no claim timestamp to age — claim something from `tl ready`")
        | some claimedHlc =>
          let deadline := claimStaleDeadlineMs claimedHlc w
          if ctx.now > deadline then .ok [.claim i actor]  -- stale: take it over
          else .error (notClaimable
            s!"{displayId i} is claimed by {holder} and not stale yet (~{max 1 ((deadline - ctx.now + 59999) / 60000)}m until the window elapses) — retry later, --steal with a shorter --stale, or claim something from `tl ready`")
    if State.isReadyWith rm s ctx.now i then .ok [.claim i actor]
    else if steal && onlyClaimObstacle && claimedBy == some actor then .ok [.claim i actor]
    else if steal && onlyClaimObstacle then stealVerdict
    else .error (notClaimable
      s!"{displayId i} is not claimable — run `tl why {displayId i}`, or claim something from `tl ready`"))
  let v := writeNow ctx parsed
  let some i := parsed.head?.bind (fun p =>
      match p.op with | .claim ci _ => some ci | _ => none)
    | throw (.mk' .internal "claim wrote no claim record")
  let auto ← Tl.Sync.autoSyncLocal d replica
  -- publish-around-claim (ADR-0001 §5): with --sync, push the take to the remote
  -- right away (after it is in the local ref), closing the cross-clone race
  -- window. Best-effort — the take is already recorded locally, so a publish
  -- failure degrades with a note rather than failing the (successful) claim.
  let postNotes ← if sync then
      (try (do let (_, _, pn) ← performSync d; pure pn)
       catch e => pure [s!"the take is recorded but could not be published to the remote ({e.message}) — run `tl sync`"])
    else pure []
  -- with --sync, the post-push reconcile may have pulled a competing claim, so
  -- re-derive the outcome from the freshly-reconciled state (re-fold) — the echo
  -- then reflects a sibling that won the race. The race can't be fully closed
  -- (distributed), but the report is as fresh as the post-push fetch. Without
  -- --sync, the just-written state is the freshest we have.
  let (vFinal, reloadNotes) ←
    if sync then reloadOrFallback (loadView dirOverride) v i else pure (v, ([] : List String))
  let current := (vFinal.state.issueData i).assignee.value.getD none
  let won := current == some actor
  let data := (issueObj vFinal i).setObjVal! "claim" (Json.mkObj
    [("outcome", Json.str (if won then "won" else "superseded")),
     ("currentAssignee", current.elim Json.null Json.str)])
  -- a takeover: --steal won an item that was *in progress* under a different
  -- holder (read from ctx.loaded, the pre-fold state). Gating on the pre-state
  -- being InProgress keeps the disclosure honest — a plain claim of a ready
  -- (open) item that merely retained a stale assignee is "Claimed", not "Took
  -- over … stale", since no staleness test ran on the ready path.
  let priorHolder := (ctx.loaded.state.issueData i).assignee.value.getD none
  let tookOver := steal && won && priorHolder.isSome && priorHolder != some actor
    && (ctx.loaded.state.issueData i).statusOf == .InProgress
  -- mirror cmdClose: a folded foreign op can outstamp the fresh claim inside the
  -- skew window, so the human line must disclose supersession — not assume "Claimed"
  let human :=
    if tookOver then s!"Took over {displayId i} from {(priorHolder.map sanitizeSingle).getD "—"} as {sanitizeSingle actor} (its claim was stale)"
    else if won then s!"Claimed {displayId i} as {sanitizeSingle actor}"
    else s!"claim of {displayId i} was superseded by a later concurrent write — it is now assigned to {current.elim "no one" sanitizeSingle}; rerun if still intended"
  return { data, human
           notes := preNotes ++ freshNotes ++ writeNotes ctx ++ auto ++ postNotes ++ reloadNotes }

def cmdClose (dirOverride : Option String) (tok : String) (asStr : String)
    (ofTok : Option String) (actor : String) : TlM CmdOut := do
  let some res := resolutionOfWire? asStr
    | throw (.mk' .usage s!"--as must be done|cancelled|duplicate (got '{asStr}')")
  -- a mode-scoped flag is usage-checked against its mode: --of names the
  -- duplicate's canonical issue and means nothing for done/cancelled
  if ofTok.isSome && res != .Duplicate then
    throw (.mk' .usage "--of names the canonical issue of a duplicate — it only pairs with --as duplicate")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 2 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    let target ← ofTok.mapM (resolveToken s)
    if target == some i then
      .error { code := .notCloseable
               message := s!"{displayId i} cannot be its own duplicate — name the canonical issue in --of, or close --as cancelled"
               context := [("id", .str (displayId i)),
                           ("reasons", Json.mkObj [("selfDuplicate", Json.bool true)])] }
    else if res == .Done && s.isEpic i then
      let rm := s.effStatusAll
      let openKids := (s.presentChildren i).filter (fun c => !State.effClosedWith rm s c)
      -- an epic is `done` by child rollup (ADR-0003), never closed `--as done`; word
      -- the refusal differently once all children are closed (open: 0 would read as a
      -- contradiction — "becomes done when its children close" but they already have)
      let msg :=
        if openKids.isEmpty then
          s!"{displayId i} is an epic and is already done via child rollup — no explicit close needed (`--as cancelled` is the only manual terminal)"
        else
          s!"{displayId i} is an epic — it becomes done when its children close (open: {openKids.length}); `--as cancelled` is the manual terminal"
      .error { code := .notCloseable
               message := msg
               context := [("id", .str (displayId i)),
                           ("reasons", Json.mkObj
                             [("isEpic", Json.bool true),
                              ("openChildren", Json.arr (openKids.map (Lean.Json.str ∘ displayId)).toArray)])] }
    else
      let dta := s.issueData i
      let sameTarget := match target with
        | none => true
        | some t => duplicateOf s i == some t
      if dta.statusOf.closed && dta.closeResolution.value.getD none == some res && sameTarget then
        .ok []  -- idempotent re-close (ADR-0008): appends nothing
      else
        .ok ([WireOp.close i res] ++ (match res, target with
          | .Duplicate, some t => [WireOp.metaSet i "duplicate-of" (some t)]
          | _, _ => []))
  )
  let v := writeNow ctx parsed
  -- the echo target: re-resolve against the post view (parsed may be empty)
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  -- compute the echo from the POST-fold state, not the assumed result: a
  -- concurrent later-stamped foreign claim/reopen can outrank this close in
  -- LWW, so the issue may not actually be closed. `unblocked` is the proved
  -- freed set over the post state, and the message reports what really held.
  let actuallyClosed := (v.state.issueData i).statusOf.closed
  -- `unblocks` is the ready-diff `ready (withClosed s i) \ ready s`, so it is
  -- computed on the PRE-state (where i is still open — on the post-state the
  -- diff is empty). Report it only when the close actually took effect: a
  -- superseded close frees nothing.
  let freed := if actuallyClosed then (State.unblocksFast ctx.loaded.state ctx.now i).map (Json.str ∘ displayId)
               else []
  let data := (issueObj v i).setObjVal! "unblocked" (Json.arr freed.toArray)
  let human :=
    if parsed.isEmpty then s!"{displayId i} already closed as {asStr} — nothing to do"
    else if !actuallyClosed then
      s!"close of {displayId i} was superseded by a later concurrent write — it is {statusWire (v.state.issueData i).statusOf}; rerun if still intended"
    else s!"Closed {displayId i} as {asStr}" ++
      (if freed.isEmpty then "" else s!" (unblocked {freed.length})")
  return { data, human, notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl update`'s `--append-notes` is a non-atomic read-modify-write: it reads the
    issue's current `notes` register from the materialized state, joins the new line
    with a `\n`, and writes the whole string back as one LWW value. `notes` is a
    single register (ADR-0008 LWW), so two appends racing across replicas resolve by
    the join's triple key — the loser's line is dropped, not merged. For a serial
    agent loop (the documented primary use) this is exactly the intended accumulate;
    concurrent appenders should `sync` between writes. `--notes` (replace) and
    `--append-notes` are mutually exclusive. -/
def cmdUpdate (dirOverride : Option String) (tok : String)
    (title description notes appendNotes slug : Option String)
    (priority : Option Nat) (actor : String) : TlM CmdOut := do
  if title.isNone && description.isNone && notes.isNone && appendNotes.isNone
      && slug.isNone && priority.isNone then
    throw (.mk' .usage
      "update needs at least one of --title, --priority, --description, --notes, --append-notes, --slug")
  if notes.isSome && appendNotes.isSome then
    throw (.mk' .usage "use one of --notes (replace) or --append-notes (append a line), not both")
  let prio : Option (Fin 5) := priority.map (fun p => ⟨min p 4, Nat.lt_succ_of_le (Nat.min_le_right p 4)⟩)
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    -- replace (--notes) wins by writing the value verbatim; append reads the current
    -- notes off the same materialized state and writes current ++ "\n" ++ line.
    let notesWrite : Option (Option String) := match appendNotes with
      | some line =>
        match (ctx.loaded.state.issueData i).notes.value.getD none with
        | some cur => some (some (cur ++ "\n" ++ line))
        | none     => some (some line)
      | none => notes.map some
    .ok [.update i { title, priority := prio,
                     description := description.map some,
                     notes := notesWrite, slug := slug.map some }])
  let v := writeNow ctx parsed
  let some i := parsed.head?.bind (fun p =>
      match p.op with | .update ui _ => some ui | _ => none)
    | throw (.mk' .internal "update wrote no record")
  return { data := issueObj v i, human := s!"Updated {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl reopen <id>`: a terminal issue back to `open`, clearing both
    `closeResolution` and the `assignee` as part of the closed→open transition
    (ADR-0008's reopen delta + ADR-0013: the prior claim ended with the close).
    Idempotent on *value equality* — a no-op only when the issue already equals
    reopen's whole target (open, no resolution, no assignee), mirroring the
    re-close guard. This is deliberately not narrowed to `status == open`:
    `status` and `assignee` are independent LWW registers, so a merge can
    materialize an open-but-assigned issue that no reopen produced — e.g. a
    `claim` (which writes `status:=in_progress` and `assignee` at one stamp)
    stamped *below* a later status write (a `create`/`reopen` under clock skew, or
    a crafted segment) loses the status LWW (→ `open`) but keeps the assignee LWW.
    No write-time guard can forbid that merge (CLAUDE.md §2). Firing reopen on it
    restores the claim-only invariant — the only CLI path back to open+unassigned. -/
def cmdReopen (dirOverride : Option String) (tok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    let dta := ctx.loaded.state.issueData i
    if dta.statusOf == .Open && (dta.closeResolution.value.getD none).isNone
        && (dta.assignee.value.getD none).isNone then .ok []
    else .ok [.reopen i])
  let v := writeNow ctx parsed
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  return { data := issueObj v i
           human := if parsed.isEmpty then s!"{displayId i} is already open"
                    else s!"Reopened {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

def cmdDepAdd (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let a ← resolveToken s aTok
    let b ← resolveToken s bTok
    .ok [.depAdd (b, a, EdgeKind.Blocks)])
  let some (f, t, _) := parsed.head?.bind (fun p =>
      match p.op with | .depAdd e => some e | _ => none)
    | throw (.mk' .internal "dep add wrote no record — this is a bug in tl; please report it")
  return { data := Json.mkObj
            [("type", Json.str "blocks"), ("from", Json.str (displayId f)),
             ("to", Json.str (displayId t)), ("status", Json.str "added")]
           human := s!"{displayId t} is now blocked by {displayId f}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

def cmdDepRemove (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let a ← resolveToken s aTok
    let b ← resolveToken s bTok
    let e : Edge := (b, a, EdgeKind.Blocks)
    -- presence, not raw add-tags: a tombstoned tag still enumerates, but a
    -- non-present edge means there is nothing to retract (ADR-0020 "noop")
    if !decide (s.edges.Present e) then
      .ok []
    else
      .ok [.depRemove e (s.edges.tagsOf e)])
  -- recover endpoints for the ack (re-resolve on the pre state)
  let s := ctx.loaded.state
  let a ← MonadExcept.ofExcept (resolveToken s aTok)
  let b ← MonadExcept.ofExcept (resolveToken s bTok)
  let status := if parsed.isEmpty then "noop" else "removed"
  return { data := Json.mkObj
            [("type", Json.str "blocks"), ("from", Json.str (displayId b)),
             ("to", Json.str (displayId a)), ("status", Json.str status)]
           human :=
             if parsed.isEmpty then s!"{displayId a} was not blocked by {displayId b} — nothing to do"
             else s!"{displayId a} is no longer blocked by {displayId b}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `dep critical` — rank open issues by transitive dependent-count (the proved
    critical-path `weight`, ADR-0004 thm 4): the most-unblocking work first. Only
    issues that block at least one other appear. The weight is computed over the
    hoisted blocks adjacency — the same metric `ready` ranks by. -/
def cmdDepCritical (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let bsrc := v.idx.bsrc  -- already = blocksBySource v.edges (built once in the index)
  let pset := v.idx.presentH
  let n := v.present.length
  let weighted := (v.present.filter (fun i => v.effStatus i == .Open)).filterMap (fun i =>
    let w := State.weightFast bsrc pset n i
    if w == 0 then none else some (i, w))
  let le := fun (a b : IssueId × Nat) =>
    if a.2 != b.2 then decide (b.2 < a.2) else decide (TotalOrd.le a.1 b.1)
  let ranked := weighted.mergeSort le
  let rows := ranked.map (fun (i, w) =>
    Json.mkObj
      [("id", Json.str (displayId i)), ("weight", jnum w),
       ("status", Json.str (statusWire (v.effStatus i))),
       ("title", Json.str (sanitizeSingle ((v.issueData i).title.value.getD "")))])
  let data := Json.mkObj [("items", Json.arr rows.toArray), ("count", jnum ranked.length)]
  let human :=
    if ranked.isEmpty then "no open issue blocks another"
    else String.intercalate "\n" (ranked.map (fun (i, w) => s!"  {issueLine v i}  (blocks {w})"))
  return { data, human, notes }

/-- `dep path A B` — a witness `blocks`-edge path from A to B (A transitively
    blocks B), the cycle-breaking aid. Over the proved kernel extractor
    `State.blocksPath` (Tl/Kernel/Path.lean): `found` is true iff B is
    reach+-reachable from A over present blocks edges, and `path` is then a real
    consecutive-edge chain `[A, …, B]` (empty when none). Total on cyclic and
    dangling graphs. JSON `{from,to,path:[ids],found}`; human is an arrow line. -/
def cmdDepPath (dirOverride : Option String) (aTok bTok : String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let a ← MonadExcept.ofExcept (resolveToken v.state aTok)
  let b ← MonadExcept.ofExcept (resolveToken v.state bTok)
  let pathOpt := v.state.blocksPath a b
  let p := pathOpt.getD []
  let data := Json.mkObj
    [("from", Json.str (displayId a)), ("to", Json.str (displayId b)),
     ("path", Json.arr (p.map (Json.str ∘ displayId)).toArray),
     ("found", Json.bool pathOpt.isSome)]
  let human :=
    if pathOpt.isSome then String.intercalate " → " (p.map displayId)
    else s!"no blocks path from {displayId a} to {displayId b}"
  return { data, human, notes }

/-- `dep relate A B` — a symmetric informational link (canonicalized on the
    sorted endpoint pair, since `related` is undirected). Drives nothing (frame
    lemma); filter/display only. -/
def cmdDepRelate (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let a ← resolveToken s aTok
    let b ← resolveToken s bTok
    if a == b then .error (.mk' .usage "cannot relate an issue to itself — give two different ids")
    else .ok [.relate (if decide (a ≤ b) then (a, b, EdgeKind.Related) else (b, a, EdgeKind.Related))])
  let _ := parsed
  let s := ctx.loaded.state
  let a ← MonadExcept.ofExcept (resolveToken s aTok)
  let b ← MonadExcept.ofExcept (resolveToken s bTok)
  return { data := Json.mkObj
            [("type", Json.str "related"), ("from", Json.str (displayId a)),
             ("to", Json.str (displayId b)), ("status", Json.str "added")]
           human := s!"{displayId a} and {displayId b} are now related"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `dep unrelate A B` — retract the `related` link. A noop (nothing appended)
    when the pair is not currently related (ADR-0020). -/
def cmdDepUnrelate (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let a ← resolveToken s aTok
    let b ← resolveToken s bTok
    let e : Edge := if decide (a ≤ b) then (a, b, EdgeKind.Related) else (b, a, EdgeKind.Related)
    if !decide (s.edges.Present e) then .ok []
    else .ok [.unrelate e (s.edges.tagsOf e)])
  let s := ctx.loaded.state
  let a ← MonadExcept.ofExcept (resolveToken s aTok)
  let b ← MonadExcept.ofExcept (resolveToken s bTok)
  let status := if parsed.isEmpty then "noop" else "removed"
  return { data := Json.mkObj
            [("type", Json.str "related"), ("from", Json.str (displayId a)),
             ("to", Json.str (displayId b)), ("status", Json.str status)]
           human :=
             if parsed.isEmpty then s!"{displayId a} and {displayId b} were not related — nothing to do"
             else s!"{displayId a} and {displayId b} are no longer related"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-! ## parent verbs (reparenting) -/

/-- `tl parent set <child> <parent>`: move `<child>` under `<parent>` (the
    reparent operation). A local courtesy *replace*: it tombstones the
    child's present parent edge(s) other than `<parent>` and adds the new one in
    one transaction, so the child stays single-parented locally (no
    self-inflicted `multiParent`); a concurrent merge can still produce
    multi-parent, which `doctor` reports — never enforced, only reported
    (ADR-0003 §4 / the CRDT rule). Idempotent: a child already solely under
    `<parent>` appends nothing. A direct self-parent is a courtesy refusal;
    longer cycles stay reported by `tl dep cycles`, not rejected (matching
    `dep add`). -/
def cmdParentSet (dirOverride : Option String) (childTok parentTok : String)
    (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  -- size the stamp budget from a pre-read: at most (present parents to drop) + 1
  -- (the new edge). The build re-derives the exact ops under the lock; a rare
  -- concurrent parent-add to the same child in the window just retries.
  let now ← liftSys (fun e => .mk' .internal s!"clock read failed: {e}") nowMs
  let pre ← readStateCached d false (some now) (replica.map (·.id))
  let budget := match resolveToken pre.state childTok with
    | .ok child => (pre.state.parentsOf child).length + 1
    | .error _ => 1  -- resolution re-runs in the build and surfaces the real error
  let (ctx, parsed) ← transact d (some actor) budget (fun ctx _ => do
    let s := ctx.loaded.state
    let child ← resolveToken s childTok
    let parent ← resolveToken s parentTok
    if parent == child then
      .error (.mk' .usage
        s!"{displayId child} cannot be its own parent — name a different epic in <parent>")
    else
      -- drop every present parent edge of the child except the target, then add
      -- the target if absent (add-wins; the new edge is canonical by stamp)
      let drop := s.presentEdges.filter (fun e =>
        decide (e.2.2 = EdgeKind.Parent ∧ e.2.1 = child) && e.1 != parent)
      let needAdd := !(s.parentsOf child).contains parent
      .ok (drop.map (fun e => .depRemove e (s.edges.tagsOf e))
           ++ (if needAdd then [.depAdd (parent, child, EdgeKind.Parent)] else [])))
  let v := writeNow ctx parsed
  let child ← MonadExcept.ofExcept (resolveToken v.state childTok)
  let parent ← MonadExcept.ofExcept (resolveToken v.state parentTok)
  let replaced := parsed.filterMap (fun p => match p.op with
    | .depRemove (f, _, _) _ => some (displayId f) | _ => none)
  let status := if parsed.isEmpty then "noop" else "set"
  -- the issue object's own `parent` field already reflects the new canonical
  -- parent; `reparent` carries the action metadata
  let data := (issueObj v child).setObjVal! "reparent" (Json.mkObj
    [("status", Json.str status),
     ("replaced", Json.arr (replaced.map Json.str).toArray)])
  let human :=
    if parsed.isEmpty then s!"{displayId child} is already under {displayId parent} — nothing to do"
    else s!"Moved {displayId child} under {displayId parent}"
      ++ (if replaced.isEmpty then "" else s!" (was under {String.intercalate ", " replaced})")
  return { data, human, notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl parent remove <child> <parent>`: detach `<child>` from `<parent>` —
    retract that one parent edge if present, else a no-op (mirrors
    `dep remove`). To drop a child's only parent is to make it a root. -/
def cmdParentRemove (dirOverride : Option String) (childTok parentTok : String)
    (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let child ← resolveToken s childTok
    let parent ← resolveToken s parentTok
    let e : Edge := (parent, child, EdgeKind.Parent)
    if !decide (s.edges.Present e) then .ok []
    else .ok [.depRemove e (s.edges.tagsOf e)])
  let s := ctx.loaded.state
  let child ← MonadExcept.ofExcept (resolveToken s childTok)
  let parent ← MonadExcept.ofExcept (resolveToken s parentTok)
  let v := writeNow ctx parsed
  let status := if parsed.isEmpty then "noop" else "removed"
  let data := (issueObj v child).setObjVal! "reparent" (Json.mkObj
    [("status", Json.str status), ("removed", Json.str (displayId parent))])
  let human :=
    if parsed.isEmpty then s!"{displayId child} was not a child of {displayId parent} — nothing to do"
    else s!"{displayId child} is no longer a child of {displayId parent}"
  return { data, human, notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-! ## label verbs -/

def cmdLabelAdd (dirOverride : Option String) (tok label : String) (actor : String) : TlM CmdOut := do
  if label.trimAscii.isEmpty then
    throw (.mk' .usage "a label must be non-empty — `tl label add <id> <label>`")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    -- idempotent: an already-present label appends nothing (mirrors re-close)
    if (s.issueData i).labels.presentElements.contains label then .ok []
    else .ok [.labelAdd i label])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  let status := if parsed.isEmpty then "noop" else "added"
  return { data := Json.mkObj
            [("type", Json.str "label"), ("id", Json.str (displayId i)),
             ("label", Json.str (sanitizeSingle label)), ("status", Json.str status)]
           human := if parsed.isEmpty then s!"{displayId i} already has label '{sanitizeSingle label}'"
                    else s!"Labeled {displayId i} '{sanitizeSingle label}'"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

def cmdLabelRemove (dirOverride : Option String) (tok label : String) (actor : String) : TlM CmdOut := do
  if label.trimAscii.isEmpty then
    throw (.mk' .usage "a label must be non-empty — `tl label remove <id> <label>`")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    let lbls := (s.issueData i).labels
    -- presence, not raw add-tags: a non-present label has nothing to retract
    if !lbls.presentElements.contains label then .ok []
    else .ok [.labelRemove i label (lbls.tagsOf label)])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  let status := if parsed.isEmpty then "noop" else "removed"
  return { data := Json.mkObj
            [("type", Json.str "label"), ("id", Json.str (displayId i)),
             ("label", Json.str (sanitizeSingle label)), ("status", Json.str status)]
           human := if parsed.isEmpty then s!"{displayId i} had no label '{sanitizeSingle label}' — nothing to do"
                    else s!"Unlabeled {displayId i} '{sanitizeSingle label}'"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl label list`: the label vocabulary — every present label with how many
    issues carry it (sorted by name, a deterministic read). -/
def cmdLabelList (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  -- one pass: each present issue's label set is computed once and the counts
  -- accumulate per label into a sorted assoc map; the JSON rows and the human
  -- lines read the same counted list (the old shape re-counted every label
  -- twice, each count rescanning every issue). `insertWith` keeps the list
  -- sorted by label as it goes, so the result is already name-ordered — no
  -- separate sort. An issue's label set is duplicate-free (presentElements of
  -- the OR-Set), so counts stay per-issue. `v.issueData` reads the once-built
  -- data hash (= `s.issueData`, `issueDataH_eq`) — the raw find was O(N) per
  -- issue, Θ(N²) over the label scan.
  let counted : List (String × Nat) := Id.run do
    let mut acc : List (String × Nat) := []
    for i in v.present do
      for l in (v.issueData i).labels.presentElements do
        acc := AssocList.insertWith (· + ·) l 1 acc
    return acc
  let rows := counted.map (fun (l, n) =>
    Json.mkObj [("label", Json.str (sanitizeSingle l)), ("count", jnum n)])
  return { data := Json.mkObj [("count", jnum counted.length), ("labels", Json.arr rows.toArray)]
           human := if counted.isEmpty then "no labels"
                    else String.intercalate "\n" (counted.map (fun (l, n) => s!"{sanitizeSingle l}  {n}"))
           notes }

/-! ## meta (the opaque per-key side-channel — drives nothing, ADR-0002) -/

/-- `tl meta set <id> <key> <value>`: write an opaque metadata value (per-key
    LWW). No theorem touches it (frame lemma); filter/cross-ref only. -/
def cmdMetaSet (dirOverride : Option String) (tok key value : String) (actor : String) : TlM CmdOut := do
  if key.trimAscii.isEmpty then
    throw (.mk' .usage "a meta key must be non-empty — `tl meta set <id> <key> <value>`")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, _) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    .ok [.metaSet i key (some value)])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  return { data := Json.mkObj
            [("id", Json.str (displayId i)), ("key", Json.str (sanitizeSingle key)),
             ("value", Json.str (sanitizeSingle value)), ("status", Json.str "set")]
           human := s!"set {sanitizeSingle key} on {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl meta clear <id> <key>`: tombstone a metadata key. A disclosed noop when
    the key carries no current value. -/
def cmdMetaClear (dirOverride : Option String) (tok key : String) (actor : String) : TlM CmdOut := do
  if key.trimAscii.isEmpty then
    throw (.mk' .usage "a meta key must be non-empty — `tl meta clear <id> <key>`")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    if (((s.issueData i).metadata.find key).bind (·.value)).join.isNone then .ok []
    else .ok [.metaSet i key none])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  let status := if parsed.isEmpty then "noop" else "cleared"
  return { data := Json.mkObj
            [("id", Json.str (displayId i)), ("key", Json.str (sanitizeSingle key)), ("status", Json.str status)]
           human := if parsed.isEmpty then s!"{displayId i} had no {sanitizeSingle key} — nothing to do"
                    else s!"cleared {sanitizeSingle key} on {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl meta get <id> [<key>]`: read one metadata value, or all of an issue's. -/
def cmdMetaGet (dirOverride : Option String) (tok : String) (key : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let dta := v.issueData i
  match key with
  | some k =>
    let val := ((dta.metadata.find k).bind (·.value)).join
    return { data := Json.mkObj
              [("id", Json.str (displayId i)), ("key", Json.str (sanitizeSingle k)),
               ("value", val.elim Json.null (Json.str ∘ sanitizeSingle))]
             human := val.elim s!"(no {sanitizeSingle k})" sanitizeSingle, notes }
  | none =>
    let pairs := (AMap.keys dta.metadata).filterMap (fun k =>
      ((dta.metadata.find k).bind (·.value)).join.map (fun val => (k, val)))
    let rows := pairs.map (fun (k, val) =>
      Json.mkObj [("key", Json.str (sanitizeSingle k)), ("value", Json.str (sanitizeSingle val))])
    return { data := Json.mkObj
              [("id", Json.str (displayId i)), ("count", jnum pairs.length), ("meta", Json.arr rows.toArray)]
             human := if pairs.isEmpty then s!"{displayId i} has no meta"
                      else String.intercalate "\n" (pairs.map (fun (k, val) => s!"{sanitizeSingle k}: {sanitizeSingle val}")), notes }

/-- `tl meta list [<id>]`: the metadata keys in use — for one issue, or every key
    with how many issues carry it. -/
def cmdMetaList (dirOverride : Option String) (idTok : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  match idTok with
  | some tok =>
    let i ← MonadExcept.ofExcept (resolveToken v.state tok)
    let keys := (AMap.keys (v.issueData i).metadata).filter (fun k =>
      (((v.issueData i).metadata.find k).bind (·.value)).join.isSome)
    return { data := Json.mkObj
              [("id", Json.str (displayId i)), ("count", jnum keys.length),
               ("keys", Json.arr (keys.map (Json.str ∘ sanitizeSingle)).toArray)]
             human := if keys.isEmpty then s!"{displayId i} has no meta"
                      else String.intercalate "\n" (keys.map sanitizeSingle), notes }
  | none =>
    let counted : List (String × Nat) := Id.run do
      let mut acc : List (String × Nat) := []
      for i in v.present do
        let dta := v.issueData i
        for k in (AMap.keys dta.metadata) do
          if (((dta.metadata.find k).bind (·.value)).join.isSome) then
            acc := AssocList.insertWith (· + ·) k 1 acc
      return acc
    let rows := counted.map (fun (k, n) =>
      Json.mkObj [("key", Json.str (sanitizeSingle k)), ("count", jnum n)])
    return { data := Json.mkObj [("count", jnum counted.length), ("keys", Json.arr rows.toArray)]
             human := if counted.isEmpty then "no meta in use"
                      else String.intercalate "\n" (counted.map (fun (k, n) => s!"{sanitizeSingle k}  {n}")), notes }

/-! ## doctor / init / version -/

def cmdDoctor (dirOverride : Option String) (sync : Bool) : TlM CmdOut := do
  let d ← discover dirOverride
  -- --sync reconciles first; best-effort (doctor never fails — ADR-0008): keep
  -- the remote leg's result to report what reconciling did, or the error to
  -- disclose if it failed.
  let (synced, syncErr, syncNotes) ← if sync then
      (try (do let (_, r, pn) ← performSync d; pure (some r, none, pn))
       catch e => pure (none, some e.message, ([] : List String)))
    else pure (none, none, [])
  -- doctor reports damage instead of failing on it (ADR-0008 exemption)
  let replicaRow ← try
      match ← loadReplica d with
      | some r => pure (Json.mkObj [("name", Json.str "replica"), ("status", Json.str "ok"),
                                    ("replica", Json.str r.id)], false)
      | none => pure (Json.mkObj [("name", Json.str "replica"), ("status", Json.str "warn"),
                                  ("message", Json.str "no replica id yet — one mints on the first write")], false)
    catch e =>
      pure (Json.mkObj [("name", Json.str "replica"), ("status", Json.str "fail"),
                        ("message", Json.str e.message)], true)
  let clockRow ← try
      let _ ← loadClock d
      pure (Json.mkObj [("name", Json.str "clock"), ("status", Json.str "ok")], false)
    catch e =>
      pure (Json.mkObj [("name", Json.str "clock"), ("status", Json.str "fail"),
                        ("message", Json.str e.message)], true)
  let own ← try loadReplica d catch _ => pure none
  let now ← liftSys (fun e => .mk' .internal s!"{e}") nowMs
  -- doctor reports store damage instead of dying on it (the exemption); the
  -- skew check runs here too, so deferred foreign ops surface as clockSkew.
  -- It reads through the fold cache but never persists it (persist := false):
  -- doctor stays a pure diagnostic, mutating nothing — not even a cache.
  let (loaded, loadFail) ← try
      pure (← readStateCached d false (some now) (own.map (·.id)) (persist := false), none)
    catch e =>
      pure (materialize [] false (some now) (own.map (·.id)), some e)
  let st := loaded.state
  let rollup := st.effStatusAll
  let present := st.presentIssues
  let edges := st.presentEdges
  let pedges := parentEdgesFast st
  let prov := provenanceMap loaded.ops
  let v : View := { dirs := d, loaded, now, replica := own,
                    rollup, present, edges, pedges, prov,
                    idx := ViewIndex.of st.data rollup present edges pedges prov st.edges.adds.toList }
  let logRows := loaded.refused.map (fun r =>
    let isOwn := own.any (·.id == r.replicaId)
    (Json.mkObj [("name", Json.str "log"),
                 ("status", Json.str (if isOwn then "fail" else "warn")),
                 ("message", Json.str s!"segment {r.replicaId}.jsonl refused: {r.error.message}"),
                 ("segment", Json.str r.replicaId)], isOwn))
  let logOk := match loadFail with
    | some e =>
      [(Json.mkObj [("name", Json.str "log"), ("status", Json.str "fail"),
                    ("message", Json.str e.message)], true)]
    | none =>
      if loaded.refused.isEmpty then
        [(Json.mkObj [("name", Json.str "log"), ("status", Json.str "ok")], false)]
      else logRows
  -- graph diagnostics (incl. duplicate-of hygiene, ADR-0008) — all over the
  -- view's pre-hoisted present/edges, so doctor scans the OR-Set views once,
  -- not once per check plus three more inside cycleCount
  let cyc := cycleCount v
  -- parents of a present `i` over the hoisted parent-edge view (`pedges` already
  -- filters child-present, and `i` is the child) — avoids re-deriving presentEdges
  -- per issue (the O(N·E) doctor scan)
  -- parents of `i` via the parent-by-child bucket (was an O(E) `v.pedges` filter
  -- per present issue — the O(N·E) doctor scan); the count is order-independent
  let multi := (v.present.filter (fun i => (v.parents i).length > 1)).length
  let dangling := (v.edges.filter (fun (f, t, k) =>
    (k == EdgeKind.Blocks || k == EdgeKind.Parent)
      && (!v.has f || !v.has t))).length
  let dupIssues := (v.present.filter (fun i =>
    match v.duplicateOf i with
    | some t => !v.has t || (v.duplicateOf t).isSome
    | none => false)).length
  let graphBad := decide (cyc > 0)
  let graphRow := (Json.mkObj
    [("name", Json.str "graph"),
     ("status", Json.str (if graphBad then "fail"
                          else if multi + dangling + dupIssues > 0 then "warn" else "ok")),
     ("cycles", jnum cyc), ("multiParent", jnum multi),
     ("danglingEdges", jnum dangling), ("duplicateOfIssues", jnum dupIssues)], graphBad)
  -- stale claims: the window is the `tl.staleAfter` git config (a compact
  -- duration like 1h / 45m / 24h) — there is no hardcoded default (ADR-0013,
  -- amended). Unset ⇒ no stale verdict at all, so the row is omitted; set but
  -- unparseable ⇒ a row that teaches the format. A claim is stale when its
  -- issue is still InProgress and the claim is older than the window.
  let staleCfg ← Tl.Sync.gitConfig d "tl.staleAfter"
  let staleRows : List (Json × Bool) := match staleCfg with
    | none => []
    | some raw =>
      match Time.parseDurationMs? raw with
      | none =>
        [(Json.mkObj
           [("name", Json.str "staleClaims"), ("status", Json.str "warn"),
            ("message", Json.str s!"git config tl.staleAfter='{sanitizeSingle raw}' is not a valid duration — set e.g. 1h, 45m, or 24h")], false)]
      | some w =>
        let stale := v.present.filter (fun i =>
          (v.issueData i).statusOf == .InProgress
            && match (v.provFor i).claimedAt with
               | some h => now > claimStaleDeadlineMs h w
               | none => false)
        [(Json.mkObj <|
           [("name", Json.str "staleClaims"),
            ("status", Json.str (if stale.isEmpty then "ok" else "warn")),
            ("window", Json.str raw),
            ("count", jnum stale.length)]
           ++ (if stale.isEmpty then [] else
               [("ids", Json.arr (stale.map (Lean.Json.str ∘ displayId)).toArray),
                -- the next-step the signal otherwise dead-ends on (ADR-0013)
                ("message", Json.str s!"{stale.length} claim(s) stale past {raw} — take one over with `tl claim <id> --steal`, or check with the holder")]), false)]
  -- clock skew (ADR-0007): foreign ops dated beyond the window are deferred
  -- (held back) until wall-clock catches up — never fatal (convergent and
  -- self-healing). The lead is over both accepted and deferred ops (a deferred
  -- op is absent from maxHlc, so reading maxHlc alone would understate a
  -- far-ahead peer). Warn when an op is deferred OR a clock leads `now` by more
  -- than the (much smaller) warn threshold — so a notably-ahead-but-folded
  -- clock (e.g. a 9h TZ misconfig, within the 24h window) is still flagged.
  let leadMs := (max loaded.maxHlc loaded.maxDeferredHlc) / 2 ^ 16 - now  -- Nat sub: 0 if behind now
  let notablyAhead := leadMs > skewWarnMs
  let skewSegs := (loaded.deferred.map (·.1)).eraseDups
  let skewRow := (Json.mkObj <|
    [("name", Json.str "clockSkew"),
     ("status", Json.str (if !loaded.deferred.isEmpty || notablyAhead then "warn" else "ok")),
     ("deferredOps", jnum loaded.deferred.length),
     ("clockLeadMs", jnum leadMs)]
    ++ (if skewSegs.isEmpty then [] else
        [("segments", Json.arr (skewSegs.map Json.str).toArray)]), false)
  -- sync posture (ADR-0011 §2): local only — no remote contact unless `--sync`
  -- just ran a `tl sync`. upstream/lastSync/ahead from git config + the marker;
  -- the live behind-count is `doctor --sync`'s job (sync then read).
  let posture ← syncPostureOf d
  -- No `behind` field: it cannot be observed without a fetch, and a --sync
  -- reconcile converges it to 0 — so it would only ever be null/0, never a real
  -- count. Report `ahead` (local unsynced ops) + lastSync always, and what a
  -- --sync reconcile did (reconciled/pushed/pulled) when it ran.
  let warnSync := posture.upstream.isSome &&
    (syncErr.isSome || (synced.isNone && (posture.lastSyncMs.isNone || posture.ahead > 0)))
  let syncMsg :=
    match posture.upstream with
    | none => "no remote configured — sharing is local/stealth only"
    | some name =>
      match syncErr with
      | some err => s!"tried to reconcile with '{name}' but it failed ({err}) — showing local posture; run `tl sync`"
      | none =>
        match synced with
        | some r =>
          if !r.ran then s!"reconciled locally; remote '{name}' not configured for this branch"
          else s!"reconciled with '{name}': " ++ (if r.pushed then "pushed" else "nothing to push")
                 ++ (if r.pulled then ", pulled remote changes" else "")
        | none =>
          match posture.lastSyncMs with
          | none => s!"remote '{name}' configured but never synced — run `tl sync`"
          | some ms =>
            if posture.ahead > 0 then s!"{posture.ahead} local op(s) not yet synced — run `tl sync`"
            else s!"up to date as of the last sync ({Time.isoOfEpochMs ms})"
  let syncRow := (Json.mkObj <|
    [("name", Json.str "sync"),
     ("status", Json.str (if warnSync then "warn" else "ok")),
     ("upstream", posture.upstream.elim Json.null Json.str),
     ("lastSync", posture.lastSyncMs.elim Json.null (fun ms => Json.str (Time.isoOfEpochMs ms))),
     ("ahead", jnum posture.ahead)]
    ++ (match synced with
        | some r => [("reconciled", Json.bool true), ("pushed", Json.bool r.pushed),
                     ("pulled", Json.bool r.pulled)]
        | none => [])
    ++ [("message", Json.str syncMsg)], false)
  -- read-refresh marker vs on-disk segments (ADR-0016 §3 boundary): the marker
  -- keys off the ref OID, so an externally deleted/truncated foreign cache file
  -- under .tl/log/ stays unfixed until the ref next moves. Warn on a mismatch (a
  -- `tl sync` re-materializes unconditionally). Low-pri: .tl/ is tl-managed.
  let refMarkRow ← try
      match ← loadRefMark d with
      | none => pure (Json.mkObj [("name", Json.str "refMark"), ("status", Json.str "ok")], false)
      | some mark =>
        let refSegs ← Tl.Sync.readRefAt d mark
        let (diskSegs, _) ← readSegments d
        let ownId := own.map (·.id)
        -- a foreign ref segment whose on-disk copy is missing or byte-differs
        let stale := refSegs.filter (fun rs =>
          ownId != some rs.replicaId &&
            (match diskSegs.find? (·.replicaId == rs.replicaId) with
             | some ds => ByteArray.hash ds.bytes != ByteArray.hash rs.bytes
             | none => true))
        pure (Json.mkObj
          [("name", Json.str "refMark"),
           ("status", Json.str (if stale.isEmpty then "ok" else "warn")),
           ("staleSegments", jnum stale.length),
           ("message", Json.str (if stale.isEmpty then "on-disk segments match the refresh marker"
             else s!"{stale.length} on-disk segment(s) differ from the marked ref — run `tl sync` to re-materialize"))], false)
    catch e =>
      pure (Json.mkObj [("name", Json.str "refMark"), ("status", Json.str "warn"),
                        ("message", Json.str s!"could not check the refresh marker: {e.message}")], false)
  let rows := [replicaRow, clockRow] ++ logOk ++ [graphRow] ++ staleRows ++ [skewRow, syncRow, refMarkRow]
  let healthy := rows.all (fun (_, failed) => !failed)
  let data := Json.mkObj
    [("healthy", Json.bool healthy),
     ("checks", Json.arr (rows.map (·.1)).toArray)]
  let human := (if healthy then "healthy" else "PROBLEMS FOUND") ++
    s!" — {rows.length} checks ({(rows.filter (·.2)).length} failing)"
  return { data, human, notes := syncNotes }

/-- `tl sync`: reconcile through the shared `refs/tl/log` — the local-first leg
    (ADR-0016 §1: publish the own segment, absorb same-machine siblings), then
    the remote leg (ADR-0001 §5: fetch → union → push) when one is configured.
    The `--json` `data` carries one leg-result object per leg; `remote` is null
    only outside a git repo, and `{ran:false, reason:"no-upstream"}` when no
    remote is configured. -/
def cmdSync (dirOverride : Option String) : TlM CmdOut := do
  let d ← discover dirOverride
  let (l, r, pnotes) ← performSync d
  let localLeg : Json :=
    if l.ran then
      Json.mkObj
        [("ran", Json.bool true), ("published", Json.bool l.published),
         ("absorbed", Json.arr (l.absorbed.map Json.str).toArray),
         ("tip", l.tip.elim Json.null Json.str)]
    else Json.mkObj [("ran", Json.bool false)]
  let remoteLeg : Json :=
    if !l.ran then Json.null  -- no git repo ⇒ no transport at all
    else if r.ran then
      Json.mkObj
        [("ran", Json.bool true), ("remote", Json.str r.remote),
         ("pushed", Json.bool r.pushed), ("pulled", Json.bool r.pulled),
         ("tip", r.tip.elim Json.null Json.str)]
    else Json.mkObj [("ran", Json.bool false), ("reason", Json.str "no-upstream")]
  let data := Json.mkObj [("local", localLeg), ("remote", remoteLeg)]
  let human :=
    if !l.ran then
      "not a git repository — tl shares through refs/tl/log; run inside a git repo"
    else
      let localPart :=
        (if l.published then "published your changes" else "already up to date")
        ++ (if l.absorbed.isEmpty then "" else s!"; absorbed {l.absorbed.length} sibling(s)")
      let remotePart :=
        if !r.ran then "; no remote configured (no-upstream) — shared locally only"
        else
          let pushed := if r.pushed then "pushed" else "nothing to push"
          let pulled := if r.pulled then ", pulled remote changes" else ""
          s!"; remote '{r.remote}': {pushed}{pulled}"
      s!"Synced: {localPart}{remotePart}"
  return { data, human, notes := pnotes }

/-- The committed discovery pointer (ADR-0011 §3): the one line an agent file
    carries so any harness surfaces `tl` with zero config. -/
def discoveryPointer : String :=
  "task state lives in `tl` (a git-native tracker) — run `tl ready --json` for what to work on and `tl doctor` for health; load the tl skill or `tl help --json` for how to drive it."

/-- The gitignored `.tl/README.md` primer (ADR-0011 §3) for anyone who opens
    `.tl/` directly. -/
def readmePrimer : String :=
  "# tl — task tracker\n\n" ++
  "This directory holds tl's task state for the project. It is gitignored and\n" ++
  "managed by tl — do not edit it by hand. State is an append-only op log under\n" ++
  "`log/`; every read is a fold over it.\n\n" ++
  "  tl ready                 what to work on now (ranked, unblocked)\n" ++
  "  tl claim <id>            take a ready item\n" ++
  "  tl close <id> --as done  finish it\n" ++
  "  tl why <id>              why something is blocked\n" ++
  "  tl doctor                project health\n" ++
  "  tl help                  all commands (tl help --json for the grammar)\n"

def cmdInit (dirOverride : Option String) : TlM CmdOut := do
  -- the override is --dir, else TL_DIR (ADR-0012: the same explicit-state
  -- mechanism, --dir wins) — so `TL_DIR=… tl init && tl create …` binds one
  -- directory, not two
  let override : Option String ← match dirOverride with
    | some p => pure (some p)
    | none => liftSys (fun e => .mk' .internal s!"environment read failed: {e}") (IO.getEnv "TL_DIR")
  -- placement (ADR-0001 §4): the override wins; else the enclosing repo's
  -- toplevel; outside any repo, the cwd (with a local-only note)
  let (target, note) ← match override with
    | some p => pure (System.FilePath.mk p, ([] : List String))
    | none =>
      let cwd ← liftSys (fun e => .mk' .internal s!"{e}") IO.currentDir
      let rec findRoot (dir : System.FilePath) (fuel : Nat) : TlM (Option System.FilePath) := do
        match fuel with
        | 0 => return none
        | fuel + 1 =>
          if ← liftSys (fun e => .mk' .internal s!"{e}") (hasGitBoundary dir) then
            return some dir
          else
            match dir.parent with
            | some p => if p == dir then return none else findRoot p fuel
            | none => return none
      match ← findRoot cwd 256 with
      | some root => pure (root / ".tl", [])
      | none => pure (cwd / ".tl",
          ["not inside a git repository — state stays local-only until used under a git repo with a remote"])
  let created ← initAt target
  let dirs := Dirs.ofStatePath target.toString
  let replica ← loadReplica dirs
  -- auto-sync default (ADR-0021 §5 / ADR-0016 §4): ON for a linked worktree,
  -- opt-in elsewhere, never overriding an existing knob.
  let autosyncNote ← Tl.Sync.autoSyncInitDefault dirs
  -- write/refresh the gitignored primer (ADR-0011 §3), through the no-follow
  -- shim like every other .tl write
  writeLocalFile dirs (dirs.tlRel ++ "/README.md") readmePrimer
  -- the committed discovery pointer: suggest adding it to a root agent file;
  -- never auto-edit the user's committed files (no-surprise ethos — ADR-0011
  -- §3, decision: print, do not write; create no file when none exists)
  let rootDir := target.parent.getD (System.FilePath.mk ".")
  let mut existing : List String := []
  for f in ["AGENTS.md", "CLAUDE.md", "GEMINI.md"] do
    if ← liftSys (fun e => .mk' .internal s!"{e}") (rootDir / f).pathExists then
      existing := existing ++ [f]
  let pointerNote :=
    if existing.isEmpty then
      s!"to make tl discoverable to agents, add this line to a root agent file (e.g. AGENTS.md):\n    {discoveryPointer}"
    else
      s!"to make tl discoverable, add this line to {String.intercalate " / " existing} if not already present:\n    {discoveryPointer}"
  let data := Json.mkObj
    [("root", Json.str target.toString),
     ("replica", (replica.map (·.id)).elim Json.null Json.str),
     ("created", Json.bool created.isSome)]
  let human := match created with
    | some r => s!"Initialized tl in {target} (replica {r.id})"
    | none => s!"{target} already initialized — nothing to do (idempotent)"
  return { data, human, notes := note ++ [pointerNote] ++ autosyncNote }

/-- The product version (keep in lockstep with lakefile.lean's package
    version; `tl version` is the single user-facing source). -/
def productVersion : String := "0.1.0"

def cmdVersion : CmdOut :=
  { data := Json.mkObj [("version", Json.str productVersion), ("logFormat", jnum supportedVersion)]
    human := s!"tl {productVersion} (log format v{supportedVersion})" }

end Tl.Cli
