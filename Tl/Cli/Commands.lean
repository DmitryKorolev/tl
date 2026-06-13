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
  return { dirs := d, loaded, now, replica, rollup := st.effStatusAll,
           edges := st.presentEdges, pedges := st.parentEdges,
           prov := provenanceMap loaded.ops,
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
  { dirs := v.dirs
    loaded := { v.loaded with state, ops := v.loaded.ops ++ parsed }
    now
    replica := some v.replica
    rollup := state.effStatusAll
    edges := state.presentEdges
    pedges := state.parentEdges
    prov := provenanceMap (v.loaded.ops ++ parsed) }

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

def cmdReady (dirOverride : Option String) (limit : Nat) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let ranked := State.readyFast v.rollup v.state v.now
  let capped := if limit == 0 then ranked else ranked.take limit
  let r := listRender v capped ranked.length
    s!"Ready: {ranked.length} issue(s) with no active blockers" "nothing is ready"
  return { data := listPayload "items" ranked.length (capped.map (issueRow v))
           human := r Style.plain, render := some r, notes }

def cmdList (dirOverride : Option String) (limit : Nat) (tree showAll skipBad : Bool)
    (labels : List String) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let s := v.state
  -- every issue, oldest first; then by default hide effectively-closed
  -- issues (done/cancelled, incl. rolled-up epics) — `tl ready` shows
  -- workable, `tl list` shows open work, `tl list --all` shows everything
  -- (vision / ADR-0020 list-grammar decision).
  let sorted := (s.presentIssues.map (fun i => (s.createdAtOf i, i)))
    |>.mergeSort (fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2)))
    |>.map (·.2)
  -- `--label` facet (repeatable ⇒ AND): keep issues carrying every given label
  let sorted := if labels.isEmpty then sorted
    else sorted.filter (fun i => labels.all (s.issueData i).labels.presentElements.contains)
  let visible := if showAll then sorted else sorted.filter (fun i => !State.effClosedWith v.rollup s i)
  let openN := (sorted.filter (fun i => (s.issueData i).statusOf == .Open)).length
  let inProg := (sorted.filter (fun i => (s.issueData i).statusOf == .InProgress)).length
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
      let cappedRoots := if limit == 0 then roots else roots.take limit
      let keep : IssueId → Bool := if showAll then (fun _ => true) else (fun i => !State.effClosedWith v.rollup s i)
      fun st =>
        if roots.isEmpty then (if visible.isEmpty then "no issues" else "(no top-level issues)")
        else String.intercalate "\n" (treeForest st v cappedRoots keep)
          ++ "\n" ++ footer st summary cappedRoots.length roots.length
    else listRender v capped visible.length summary "no issues"
  return { data := listPayload "items" visible.length (capped.map (issueRow v))
           human := r Style.plain, render := some r, notes }

/-- The `show` claim block: meaningful when this replica claimed recently
    (the ADR-0013 24h staleness default bounds "recent"). -/
def claimBlock (v : View) (i : IssueId) : Option Json := do
  let own ← v.replica
  let ownVal ← own.toNat?
  let claims := v.loaded.ops.filterMap (fun p =>
    match p.op with
    | .claim ci actor => if ci == i && p.stamp.replica == ownVal then some (p.stamp, actor) else none
    | _ => none)
  -- latest own claim by the FULL stamp order (the cross-op comparison rule,
  -- Tl/Cli/Project.lean §provenance)
  let (st, actor) ← claims.foldl (fun acc c =>
    match acc with
    | none => some c
    | some m => some (if Tl.Crdt.TotalOrd.le m.1 c.1 then c else m)) none
  let ageMs := v.now - st.hlc / 2 ^ 16
  if ageMs > 24 * 3600 * 1000 then none
  else
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
  -- bridged to the spec by cyclesFast_eq/precCyclesFast_eq) and reused
  let blocksCycles := State.cyclesFast s EdgeKind.Blocks
  let parentCycles := State.cyclesFast s EdgeKind.Parent
  let structural := blocksCycles ++ parentCycles
  -- a ≺-cycle whose node set coincides with a structural witness is already
  -- diagnosed by that row; only genuinely mixed deadlocks add a readiness row
  let readiness := (State.precCyclesFast v.rollup s).filter (fun w => !structural.contains w)
  let rows := blocksCycles.map (entry "blocks")
    ++ parentCycles.map (entry "parent")
    ++ readiness.map (entry "readiness")
  return { data := listPayload "cycles" rows.length rows
           human :=
             if rows.isEmpty then "no cycles"
             else s!"{rows.length} cycle(s) — break each with `tl dep remove`"
           notes }

/-- The cycle count (structural per kind + the non-duplicate readiness
    deadlocks), shared with `doctor`'s graph check. -/
private def cycleCount (m : AMap IssueId Status) (s : State) : Nat :=
  let structural := State.cyclesFast s EdgeKind.Blocks ++ State.cyclesFast s EdgeKind.Parent
  structural.length + ((State.precCyclesFast m s).filter (fun w => !structural.contains w)).length

def cmdStats (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let s := v.state
  let issues := s.presentIssues
  let byStored (st : Status) : Nat := (issues.filter (fun i => (s.issueData i).statusOf == st)).length
  let ready := (State.readyFast v.rollup s v.now).length
  let blocked := (issues.filter (blockedOf v.rollup v.edges s)).length
  let deferred := (issues.filter (deferredOf s v.now)).length
  let cycles := cycleCount v.rollup s
  let openN := byStored .Open
  let inProg := byStored .InProgress
  let doneN := byStored .Done
  let cancelledN := byStored .Cancelled
  let data := Json.mkObj
    [("total", jnum issues.length),
     ("open", jnum openN), ("inProgress", jnum inProg),
     ("done", jnum doneN), ("cancelled", jnum cancelledN),
     ("ready", jnum ready), ("blocked", jnum blocked),
     ("deferred", jnum deferred), ("cycles", jnum cycles)]
  -- a small labelled block (§5); each state's count in its status color (§7)
  let r : Style → String := fun st =>
    let c (ds : DState) (n : Nat) : String := st.paint ds.colorCode s!"{ds.word} {n}"
    s!"{issues.length} issues\n"
      ++ "  " ++ String.intercalate " · " [c .ready openN, c .inProgress inProg, c .done doneN, c .cancelled cancelledN] ++ "\n"
      ++ "  " ++ String.intercalate " · "
           [st.paint "1" s!"ready {ready}", c .blocked blocked, c .deferred deferred,
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

/-- The pre-write refresh (ADR-0016 §3 amendment): absorb any sibling's
    published changes from the shared `refs/tl/log` BEFORE the write's guards
    run, so a directed `claim`/`close`/`update`/`dep` by id sees a sibling's
    concurrent write — and finds a task that exists only on the ref — instead
    of deciding against a stale local view (the double-claim hazard). The exact
    O(1) ref-mark check reads already do (`loadView`); lock-free, runs before
    `transact` takes the mutation lock, best-effort (a degrade is disclosed and
    the write proceeds a moment stale, never failing). Returns the located
    dirs, the loaded replica (reused by the post-write auto-sync), and any
    degrade note. The remote leg stays explicit (`tl sync` / a future
    `claim --verify`). -/
def preWrite (dirOverride : Option String) :
    TlM (Dirs × Option Tl.Clock.Replica × List String) := do
  let d ← discover dirOverride
  let replica ← loadReplica d
  let refresh ← Tl.Sync.refreshFromRef d (replica.map (·.id))
  let notes := refresh.degraded.toList.map (fun r =>
    s!"wrote against a moment-stale view: could not refresh from the shared ref ({r}) — fix git/filesystem access, then `tl sync`")
  return (d, replica, notes)

/-- Auto-sync (ADR-0021): after a successful write, if `tl.autosync` is on,
    publish this replica's segment into the shared `refs/tl/log` (and absorb
    siblings) so a worktree sibling sees the write without an explicit
    `tl sync`. Best-effort and lock-free — it runs after `transact` has released
    the lock, and ANY failure (no git, read-only FS, ref contention surviving
    the CAS retry) is swallowed and disclosed as a non-fatal note, NEVER failing
    the write (ADR-0021 §4 — the record is already durable). It catches both
    thrown `Tl.Error`s and raw `IO.Error`s, mirroring `refreshFromRef`. The
    remote leg stays explicit `tl sync`. -/
def autoSyncNotes (d : Dirs) (replica : Option Tl.Clock.Replica) : TlM (List String) := do
  if (← Tl.Sync.gitConfig d "tl.autosync") != some "true" then return []
  match ← ((Tl.Sync.syncLocal d (replica.map (·.id))).run.toBaseIO : IO _) with
  | .ok (.ok _) => return []
  | .ok (.error e) =>
    return [s!"auto-sync skipped ({e.message}) — run `tl sync` to publish this write to siblings"]
  | .error ioErr =>
    return [s!"auto-sync skipped ({toString ioErr}) — run `tl sync` to publish this write to siblings"]

def cmdCreate (dirOverride : Option String) (title : String) (priority : Option Nat)
    (description : Option String) (actor : String)
    (blockedBy blocks parents related : List String) : TlM CmdOut := do
  let edgeCount := blockedBy.length + blocks.length + parents.length + related.length
  let prio : Option (Fin 5) := priority.map (fun p => ⟨min p 4, Nat.lt_succ_of_le (Nat.min_le_right p 4)⟩)
  let (d, replica, freshNotes) ← preWrite dirOverride
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
           notes := freshNotes ++ writeNotes ctx ++ (← autoSyncNotes d replica) }

def cmdClaim (dirOverride : Option String) (tok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← preWrite dirOverride
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
  let current := (v.state.issueData i).assignee.value.getD none
  let data := (issueObj v i).setObjVal! "claim" (Json.mkObj
    [("outcome", Json.str (if current == some actor then "won" else "superseded")),
     ("currentAssignee", current.elim Json.null Json.str)])
  return { data, human := s!"Claimed {displayId i} as {sanitizeSingle actor}"
           notes := freshNotes ++ writeNotes ctx ++ (← autoSyncNotes d replica) }

def cmdClose (dirOverride : Option String) (tok : String) (asStr : String)
    (ofTok : Option String) (actor : String) : TlM CmdOut := do
  let some res := resolutionOfWire? asStr
    | throw (.mk' .usage s!"--as must be done|cancelled|duplicate (got '{asStr}')")
  -- a mode-scoped flag is usage-checked against its mode: --of names the
  -- duplicate's canonical issue and means nothing for done/cancelled
  if ofTok.isSome && res != .Duplicate then
    throw (.mk' .usage "--of names the canonical issue of a duplicate — it only pairs with --as duplicate")
  let (d, replica, freshNotes) ← preWrite dirOverride
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
  return { data, human, notes := freshNotes ++ writeNotes ctx ++ (← autoSyncNotes d replica) }

def cmdUpdate (dirOverride : Option String) (tok : String) (title description notes : Option String)
    (priority : Option Nat) (actor : String) : TlM CmdOut := do
  if title.isNone && description.isNone && notes.isNone && priority.isNone then
    throw (.mk' .usage "update needs at least one of --title, --priority, --description, --notes")
  let prio : Option (Fin 5) := priority.map (fun p => ⟨min p 4, Nat.lt_succ_of_le (Nat.min_le_right p 4)⟩)
  let (d, replica, freshNotes) ← preWrite dirOverride
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
           notes := freshNotes ++ writeNotes ctx ++ (← autoSyncNotes d replica) }

/-- `tl reopen <id>`: a terminal issue back to `open`, clearing
    `closeResolution` (ADR-0008's reopen delta). Idempotent — an already-open
    issue is a no-op that appends nothing (mirroring the re-close rule). -/
def cmdReopen (dirOverride : Option String) (tok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← preWrite dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    if (ctx.loaded.state.issueData i).statusOf == .Open then .ok []
    else .ok [.reopen i])
  let v := writeNow ctx parsed
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  return { data := issueObj v i
           human := if parsed.isEmpty then s!"{displayId i} is already open"
                    else s!"Reopened {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← autoSyncNotes d replica) }

def cmdDepAdd (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← preWrite dirOverride
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
           notes := freshNotes ++ writeNotes ctx ++ (← autoSyncNotes d replica) }

def cmdDepRemove (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← preWrite dirOverride
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
           notes := freshNotes ++ writeNotes ctx ++ (← autoSyncNotes d replica) }

/-! ## label verbs -/

def cmdLabelAdd (dirOverride : Option String) (tok label : String) (actor : String) : TlM CmdOut := do
  if label.trimAscii.isEmpty then
    throw (.mk' .usage "a label must be non-empty — `tl label add <id> <label>`")
  let (d, replica, freshNotes) ← preWrite dirOverride
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
           notes := freshNotes ++ writeNotes ctx ++ (← autoSyncNotes d replica) }

def cmdLabelRemove (dirOverride : Option String) (tok label : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← preWrite dirOverride
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
           notes := freshNotes ++ writeNotes ctx ++ (← autoSyncNotes d replica) }

/-- `tl label list`: the label vocabulary — every present label with how many
    issues carry it (sorted by name, a deterministic read). -/
def cmdLabelList (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let s := v.state
  -- one pass: each present issue's label set is computed once and the counts
  -- accumulate per label into a sorted assoc map; the JSON rows and the human
  -- lines read the same counted list (the old shape re-counted every label
  -- twice, each count rescanning every issue). `insertWith` keeps the list
  -- sorted by label as it goes, so the result is already name-ordered — no
  -- separate sort. An issue's label set is duplicate-free (presentElements of
  -- the OR-Set), so counts stay per-issue.
  let counted : List (String × Nat) := Id.run do
    let mut acc : List (String × Nat) := []
    for i in s.presentIssues do
      for l in (s.issueData i).labels.presentElements do
        acc := AssocList.insertWith (· + ·) l 1 acc
    return acc
  let rows := counted.map (fun (l, n) =>
    Json.mkObj [("label", Json.str (sanitizeSingle l)), ("count", jnum n)])
  return { data := Json.mkObj [("count", jnum counted.length), ("labels", Json.arr rows.toArray)]
           human := if counted.isEmpty then "no labels"
                    else String.intercalate "\n" (counted.map (fun (l, n) => s!"{sanitizeSingle l}  {n}"))
           notes }

/-! ## doctor / init / version -/

def cmdDoctor (dirOverride : Option String) : TlM CmdOut := do
  let d ← discover dirOverride
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
  let v : View := { dirs := d, loaded, now, replica := own,
                    rollup := loaded.state.effStatusAll,
                    edges := loaded.state.presentEdges,
                    pedges := loaded.state.parentEdges,
                    prov := provenanceMap loaded.ops }
  let s := v.state
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
  -- graph diagnostics (incl. duplicate-of hygiene, ADR-0008)
  let cyc := cycleCount v.rollup s
  -- parents of a present `i` over the hoisted parent-edge view (`pedges` already
  -- filters child-present, and `i` is the child) — avoids re-deriving presentEdges
  -- per issue (the O(N·E) doctor scan)
  let multi := (s.presentIssues.filter (fun i => (v.pedges.filter (·.2 == i)).length > 1)).length
  let dangling := (s.presentEdges.filter (fun (f, t, k) =>
    (k == EdgeKind.Blocks || k == EdgeKind.Parent)
      && (!decide (s.hasIssue f) || !decide (s.hasIssue t)))).length
  let dupIssues := (s.presentIssues.filter (fun i =>
    match duplicateOf s i with
    | some t => !decide (s.hasIssue t) || (duplicateOf s t).isSome
    | none => false)).length
  let graphBad := decide (cyc > 0)
  let graphRow := (Json.mkObj
    [("name", Json.str "graph"),
     ("status", Json.str (if graphBad then "fail"
                          else if multi + dangling + dupIssues > 0 then "warn" else "ok")),
     ("cycles", jnum cyc), ("multiParent", jnum multi),
     ("danglingEdges", jnum dangling), ("duplicateOfIssues", jnum dupIssues)], graphBad)
  -- stale claims (ADR-0013 24h default)
  let stale := s.presentIssues.filter (fun i =>
    (s.issueData i).statusOf == .InProgress
      && match (provOf v.prov i).claimedAt with
         | some h => now > h / 2 ^ 16 + 24 * 3600 * 1000
         | none => false)
  let staleRow := (Json.mkObj <|
    [("name", Json.str "staleClaims"),
     ("status", Json.str (if stale.isEmpty then "ok" else "warn")),
     ("count", jnum stale.length)]
    ++ (if stale.isEmpty then [] else
        [("ids", Json.arr (stale.map (Lean.Json.str ∘ displayId)).toArray)]), false)
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
  let rows := [replicaRow, clockRow] ++ logOk ++ [graphRow, staleRow, skewRow]
  let healthy := rows.all (fun (_, failed) => !failed)
  let data := Json.mkObj
    [("healthy", Json.bool healthy),
     ("checks", Json.arr (rows.map (·.1)).toArray)]
  let human := (if healthy then "healthy" else "PROBLEMS FOUND") ++
    s!" — {rows.length} checks ({(rows.filter (·.2)).length} failing)"
  return { data, human }

/-- `tl sync`: reconcile through the shared `refs/tl/log` — the local-first leg
    (ADR-0016 §1: publish the own segment, absorb same-machine siblings), then
    the remote leg (ADR-0001 §5: fetch → union → push) when one is configured.
    The `--json` `data` carries one leg-result object per leg; `remote` is null
    only outside a git repo, and `{ran:false, reason:"no-upstream"}` when no
    remote is configured. -/
def cmdSync (dirOverride : Option String) : TlM CmdOut := do
  let d ← discover dirOverride
  let own ← loadReplica d
  let ownId := own.map (·.id)
  -- local-first leg: publish own + absorb same-machine siblings (ADR-0016 §1)
  let l ← Tl.Sync.syncLocal d ownId
  -- remote leg (only in a git repo): fetch → union → push (ADR-0001 §5)
  let r ← if l.ran then Tl.Sync.syncRemote d
          else pure { ran := false, remote := "", pushed := false, pulled := false, tip := none }
  -- after a remote leg that ran, materialize anything it added to the local ref
  -- onto disk (a second local leg — its publish is a no-op, its absorb is the
  -- work; run on `ran` not `pulled`, since a retry can under-report `pulled`
  -- while still having advanced the ref)
  if r.ran then
    let _ ← Tl.Sync.syncLocal d ownId
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
  return { data, human }

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
  -- auto-sync default (ADR-0021 §5 / ADR-0016 §4): ON for a linked worktree
  -- (the local leg is free and the whole point of cross-worktree sharing),
  -- opt-in elsewhere. Never overrides an existing `tl.autosync` (a re-init is
  -- idempotent on the knob too).
  let autosyncNote ←
    if (← Tl.Sync.gitConfig dirs "tl.autosync").isSome then pure []
    else if ← Tl.Sync.isLinkedWorktree dirs then
      if ← Tl.Sync.gitConfigSet dirs "tl.autosync" "true" then
        pure ["auto-sync on (linked worktree): writes publish to siblings automatically; turn off with `git config tl.autosync false` (ADR-0021)"]
      else pure []
    else if ← Tl.Sync.inGitRepo dirs then
      pure ["auto-sync is off; enable publish-on-write to siblings with `git config tl.autosync true` (ADR-0021)"]
    else pure []
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
