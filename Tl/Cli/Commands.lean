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
  -- view (ADR-0008). A racing concurrent refresher does NOT trip this — the
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

/-- A full `tl sync` (local leg, the remote leg in a git repo, then a second
    local leg to absorb the remote's additions), recording the last-sync marker
    so `doctor`/`ready` never contact the remote themselves (ADR-0016). Shared by
    `cmdSync` and the `--sync` flag. -/
def performSync (d : Dirs) : TlM (Tl.Sync.LocalOutcome × Tl.Sync.RemoteOutcome × List String) := do
  let own ← loadReplica d
  let ownId := own.map (·.id)
  let l ← Tl.Sync.syncLocal d ownId
  let r ← if l.ran then Tl.Sync.syncRemote d
          else pure { ran := false, remote := "", pushed := false, pulled := false, tip := none }
  -- a second local leg after a remote that ran materializes what the fetch added
  -- (it can pull a NEW replica). Best-effort — the push already succeeded, so
  -- never fail here; a failure self-heals on the next read's refresh. Fold its
  -- absorb into the reported local outcome so a remote-pulled replica is not
  -- silently dropped from `absorbed`; disclose a failure (loud-not-silent).
  let (l, pnotes) ← if r.ran then
      (try
        let l2 ← Tl.Sync.syncLocal d ownId
        pure ({ l with absorbed := (l.absorbed ++ l2.absorbed).eraseDups, tip := l2.tip }, ([] : List String))
       catch e => pure (l, [s!"reconciled with the remote, but materializing the pulled changes locally failed ({e.message}) — the next read or `tl sync` will catch up"]))
    else pure (l, [])
  -- record last-sync ONLY when the remote leg actually reconciled: lastSync means
  -- "last reconciled with the remote", so a local-only sync (no remote, or a
  -- remote added later) must not mark the view clean-vs-remote (a false-clean source).
  if r.ran then
    let now ← liftSys (fun e => .mk' .internal s!"{e}") nowMs
    try storeLastSync d now r.tip catch _ => pure ()
  return (l, r, pnotes)

/-- The LOCAL-only sync posture (no remote contact): the resolved upstream name
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
  -- empty / first sync) — then ALL local ops are unsynced, never a false 0.
  let syncedLines ← match syncedTip with
    | some t => pure (((← Tl.Sync.readRefAt d t).find? (·.replicaId == own)).elim 0
        (fun sd => (completeLines sd.bytes).length))
    | none => pure 0
  -- Nat subtraction clamps to 0 if the synced ref held MORE own-segment lines
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
  -- --sync reconciles first, BEST-EFFORT: a read must not fail on a remote
  -- hiccup, so a sync error degrades to a note and the (still-useful) listing.
  let syncNotes ← if sync then
      (try (do let (_, _, pn) ← performSync d; pure pn)
       catch e => pure [s!"could not reconcile with the remote ({e.message}) — showing local state; run `tl sync`"])
    else pure []
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let ranked := State.readyFast v.rollup v.state v.now
  let capped := if limit == 0 then ranked else ranked.take limit
  -- staleness advisory (ADR-0011 §2): always derived from the posture AFTER any
  -- --sync. A successful sync makes it clean (ahead 0, lastSync now ⇒ none); a
  -- FAILED --sync leaves genuine staleness, so it must still surface in
  -- data.staleness (agents read the field; humans also get the degrade note).
  let advisory ← (do pure (stalenessMsg (← syncPostureOf d) v.now))
  let r : Style → String := fun st =>
    (match advisory with | some a => st.paint "33" s!"({a})" ++ "\n" | none => "")
      ++ (listRender v capped ranked.length
            s!"Ready: {ranked.length} issue(s) with no active blockers" "nothing is ready") st
  let data := (listPayload "items" ranked.length (capped.map (issueRow v))).setObjVal!
                "staleness" (advisory.elim Json.null Json.str)
  return { data, human := r Style.plain, render := some r, notes := notes ++ syncNotes }

def cmdList (dirOverride : Option String) (limit : Nat) (tree showAll skipBad : Bool)
    (labels : List String) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  -- every issue, oldest first; then by default hide effectively-closed
  -- issues (done/cancelled, incl. rolled-up epics) — `tl ready` shows
  -- workable, `tl list` shows open work, `tl list --all` shows everything
  -- (vision / ADR-0020 list-grammar decision).
  -- createdAt from the hoisted provenance map (one log pass), not s.createdAtOf
  -- (an O(N) add-tag find per issue ⇒ O(N²) over the sort). For a present issue
  -- both are the min create-tag HLC: createdAtOf is the min over add-tag HLCs,
  -- Prov.createdAt is the min-STAMP create's HLC, and Stamp orders by HLC first,
  -- so they coincide (CrossTests pins it per seed). Default 0 = createdAtOf's nil.
  let createdAt := fun i => ((v.provFor i).createdAt).getD 0
  let sorted := (v.present.map (fun i => (createdAt i, i)))
    |>.mergeSort (fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2)))
    |>.map (·.2)
  -- `--label` facet (repeatable ⇒ AND): keep issues carrying every given label
  let sorted := if labels.isEmpty then sorted
    else sorted.filter (fun i => labels.all (v.issueData i).labels.presentElements.contains)
  let visible := if showAll then sorted else sorted.filter (fun i => !v.effClosed i)
  let openN := (sorted.filter (fun i => (v.issueData i).statusOf == .Open)).length
  let inProg := (sorted.filter (fun i => (v.issueData i).statusOf == .InProgress)).length
  let summary :=
    if showAll then s!"Total: {sorted.length} issues ({openN} open, {inProg} in progress)"
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
      let isRoot (i : IssueId) : Bool := match canonicalParentE v i with
        | none => true | some p => !(visible.contains p)
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
          let allLines := treeForest st v roots keep
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
  -- latest own claim by the FULL stamp order (the cross-op comparison rule,
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
  let trans := State.whyFast v.rollup s i
  let direct := (State.blockersOfE v.edges i).filter (fun b => !State.blockerDischargedWith v.rollup s b)
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
  let human :=
    if trans.isEmpty then s!"{displayId i} is not ready (no open blockers — check status/epic/defer)"
    else s!"{displayId i} waits on:\n" ++
      String.intercalate "\n" (trans.map (fun b => "  " ++ issueLine v b))
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
  -- count EFFECTIVE status (rollup-aware): a rolled-up epic counts as done,
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

/-- `tl log [<id>]`: the op history, newest first (ADR-0008 — an HLC-ordered
    projection over the log), optionally filtered to ops touching one issue.
    The `--since` cursor is deferred (it needs a version vector, backlog). -/
def cmdLog (dirOverride : Option String) (idTok : Option String) (limit : Nat)
    (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let filtered ← match idTok with
    | none => pure v.loaded.ops
    | some tok =>
      let i ← MonadExcept.ofExcept (resolveToken v.state tok)
      pure (v.loaded.ops.filter (fun p => (opTargets p.op).contains i))
  -- newest first by the full stamp order (deterministic on equal HLCs)
  let sorted := filtered.mergeSort (fun a b => decide (Tl.Crdt.TotalOrd.le b.stamp a.stamp))
  let capped := if limit == 0 then sorted else sorted.take limit
  let entry (p : ParsedOp) : Json :=
    Json.mkObj
      [("timestamp", Json.str (hlcIso p.stamp.hlc)),
       ("op", Json.str p.op.wire),
       ("actor", p.actor.elim Json.null (Json.str ∘ sanitizeSingle)),
       ("targets", Json.arr ((opTargets p.op).map (Json.str ∘ displayId)).toArray)]
  let line (p : ParsedOp) : String :=
    s!"{hlcIso p.stamp.hlc}  {p.op.wire}  {(p.actor.getD "—")}  " ++
      String.intercalate "," ((opTargets p.op).map displayId)
  return { data := Json.mkObj [("count", jnum filtered.length),
                               ("entries", Json.arr (capped.map entry).toArray)]
           human :=
             if filtered.isEmpty then "no ops"
             else String.intercalate "\n" (capped.map line)
               ++ (if capped.length < filtered.length then
                     s!"\n… {filtered.length - capped.length} older (--limit 0 for all)" else "")
           notes }

/-! ## Write verbs -/

private def writeNow (v : TxContext) (parsed : List ParsedOp) : View :=
  postView v parsed v.now

def cmdCreate (dirOverride : Option String) (title : String) (priority : Option Nat)
    (description : Option String) (actor : String)
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
        { title := some title, priority := prio, description := description.map some }
        :: edgeOps))
  let v := writeNow ctx parsed
  let some newId := parsed.head?.bind (fun p =>
      match p.op with | .create i _ => some i | _ => none)
    | throw (.mk' .internal "create wrote no create record")
  return { data := issueObj v newId
           human := s!"Created {displayId newId}  {sanitizeSingle title}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

def cmdClaim (dirOverride : Option String) (tok : String) (actor : String)
    (sync verify : Bool) : TlM CmdOut := do
  -- freshness preflight (ADR-0001 §5): with --sync/--verify, reconcile against
  -- the remote BEFORE the take, so the not-claimable check sees the freshest
  -- reachable state. --verify warns-and-degrades when no remote is configured
  -- (it still checks against the freshest LOCAL state, via preWriteRefresh below).
  let preNotes ← if sync || verify then do
      let d0 ← discover dirOverride
      let hasRemote := (← Tl.Sync.resolveRemote d0).isSome
      -- --verify is a GATE: a configured-but-unreachable remote fails the claim
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
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    let rm := s.effStatusAll
    if State.isReadyWith rm s ctx.now i then
      .ok [.claim i actor]
    else
      let dta := s.issueData i
      let direct := (s.blockersOf i).filter (fun b => !State.blockerDischargedWith rm s b)
      let reasons := Json.mkObj <|
        (if dta.statusOf != .Open then [("status", Json.str (statusWire dta.statusOf))] else [])
        ++ (match dta.assignee.value.getD none with
            | some a => [("assignee", Json.str a)]
            | none => [])
        ++ (if s.isEpic i then [("isEpic", Json.bool true)] else [])
        ++ (match dta.deferUntilOf with
            | some t => if ctx.now < t then [("deferUntil", Json.str (Time.isoOfEpochMs t))] else []
            | none => [])
        ++ (if direct.isEmpty then [] else
            [("blockedBy", Json.arr (direct.map (Lean.Json.str ∘ displayId)).toArray)])
      .error { code := .notClaimable
               message := s!"{displayId i} is not claimable — run `tl why {displayId i}`, or claim something from `tl ready`"
               context := [("id", .str (displayId i)), ("reasons", reasons)] })
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
  -- with --sync, the post-push reconcile may have PULLED a competing claim, so
  -- re-derive the outcome from the freshly-reconciled state (re-fold) — the echo
  -- then reflects a sibling that won the race. The race can't be fully closed
  -- (distributed), but the report is as fresh as the post-push fetch. Without
  -- --sync, the just-written state is the freshest we have.
  let vFinal ← if sync then loadView dirOverride else pure v
  let current := (vFinal.state.issueData i).assignee.value.getD none
  let won := current == some actor
  let data := (issueObj vFinal i).setObjVal! "claim" (Json.mkObj
    [("outcome", Json.str (if won then "won" else "superseded")),
     ("currentAssignee", current.elim Json.null Json.str)])
  -- mirror cmdClose: a folded foreign op can outstamp the fresh claim inside the
  -- skew window, so the human line must disclose supersession — not assume "Claimed"
  let human :=
    if won then s!"Claimed {displayId i} as {sanitizeSingle actor}"
    else s!"claim of {displayId i} was superseded by a later concurrent write — it is now assigned to {current.elim "no one" sanitizeSingle}; rerun if still intended"
  return { data, human
           notes := preNotes ++ freshNotes ++ writeNotes ctx ++ auto ++ postNotes }

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
      .error { code := .notCloseable
               message := s!"{displayId i} is an epic — it becomes done when its children close (open: {openKids.length}); `--as cancelled` is the manual terminal"
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

def cmdUpdate (dirOverride : Option String) (tok : String) (title description notes : Option String)
    (priority : Option Nat) (actor : String) : TlM CmdOut := do
  if title.isNone && description.isNone && notes.isNone && priority.isNone then
    throw (.mk' .usage "update needs at least one of --title, --priority, --description, --notes")
  let prio : Option (Fin 5) := priority.map (fun p => ⟨min p 4, Nat.lt_succ_of_le (Nat.min_le_right p 4)⟩)
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    .ok [.update i { title, priority := prio,
                     description := description.map some,
                     notes := notes.map some }])
  let v := writeNow ctx parsed
  let some i := parsed.head?.bind (fun p =>
      match p.op with | .update ui _ => some ui | _ => none)
    | throw (.mk' .internal "update wrote no record")
  return { data := issueObj v i, human := s!"Updated {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl reopen <id>`: a terminal issue back to `open`, clearing
    `closeResolution` (ADR-0008's reopen delta). Idempotent — an already-open
    issue is a no-op that appends nothing (mirroring the re-close rule). -/
def cmdReopen (dirOverride : Option String) (tok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    if (ctx.loaded.state.issueData i).statusOf == .Open then .ok []
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

/-! ## doctor / init / version -/

def cmdDoctor (dirOverride : Option String) (sync : Bool) : TlM CmdOut := do
  let d ← discover dirOverride
  -- --sync reconciles first; BEST-EFFORT (doctor never fails — ADR-0008): keep
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
  -- duration like 1h / 45m / 24h) — there is NO hardcoded default (ADR-0013,
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
               | some h => now > h / 2 ^ 16 + w
               | none => false)
        [(Json.mkObj <|
           [("name", Json.str "staleClaims"),
            ("status", Json.str (if stale.isEmpty then "ok" else "warn")),
            ("window", Json.str raw),
            ("count", jnum stale.length)]
           ++ (if stale.isEmpty then [] else
               [("ids", Json.arr (stale.map (Lean.Json.str ∘ displayId)).toArray)]), false)]
  -- clock skew (ADR-0007): foreign ops dated beyond the window are deferred
  -- (held back) until wall-clock catches up — never fatal (convergent and
  -- self-healing). The lead is over BOTH accepted and deferred ops (a deferred
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
  -- sync posture (ADR-0011 §2): LOCAL only — no remote contact unless `--sync`
  -- just ran a `tl sync`. upstream/lastSync/ahead from git config + the marker;
  -- the live behind-count is `doctor --sync`'s job (sync then read).
  let posture ← syncPostureOf d
  -- No `behind` field: it cannot be observed without a fetch, and a --sync
  -- reconcile converges it to 0 — so it would only ever be null/0, never a real
  -- count. Report `ahead` (local unsynced ops) + lastSync always, and what a
  -- --sync reconcile DID (reconciled/pushed/pulled) when it ran.
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
  -- the committed discovery pointer: SUGGEST adding it to a root agent file;
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
