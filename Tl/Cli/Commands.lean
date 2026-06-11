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
import Tl.Cli.Resolve
import Tl.Cli.Init

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

/-- Load the read view (no lock — ADR-0015 §5). -/
def loadView (dirOverride : Option String) (skipBad : Bool := false) : TlM View := do
  let d ← discover dirOverride
  let replica ← loadReplica d
  let loaded ← readState d skipBad
  let now ← liftSys (fun e => .mk' .internal s!"clock read failed: {e}") nowMs
  return { dirs := d, loaded, now, replica }

/-- The ADR-0008 command-level refusal policy for reads: a refused *own*
    segment — or every segment — fails the command; foreign refusals are
    disclosed on stderr and the read succeeds. (`doctor` is exempt.) -/
def cleanReadNotes (v : View) : TlM (List String) := do
  if let some own := v.replica then
    if let some r := v.loaded.refused.find? (·.replicaId == own.id) then
      throw r.error
  if !v.loaded.refused.isEmpty && v.loaded.refused.length == v.loaded.segmentCount then
    throw (v.loaded.refused.head?.map (·.error)
      |>.getD (.mk' .internal "every segment refused — repair or remove the damaged segments under .tl/log/"))
  return v.loaded.refused.map (fun r =>
      s!"segment {r.replicaId}.jsonl refused (line {r.line}): folded the others; its owner repairs or re-syncs it")
    ++ v.loaded.warnings ++ v.loaded.skipped.map (fun (rid, n) =>
      s!"--skip-bad: dropped segment {rid}.jsonl line {n}")

/-- The disclosure notes a write surfaces (ADR-0008: loud, never silent):
    a refused foreign segment means the guards and echo were computed from a
    fold that dropped its ops. (An own-segment refusal already failed the
    transact.) -/
def writeNotes (ctx : TxContext) : List String :=
  ctx.loaded.refused.map (fun r =>
    s!"segment {r.replicaId}.jsonl refused (line {r.line}): this write was checked against a fold without it; its owner repairs or re-syncs it")
  ++ ctx.loaded.warnings

/-- The post-write view: the pre-state plus the appended records. -/
def postView (v : TxContext) (parsed : List ParsedOp) (now : Nat) : View :=
  let state := parsed.foldl (fun s p => Tl.Kernel.apply s p.kernelOp) v.loaded.state
  { dirs := v.dirs
    loaded := { v.loaded with state, ops := v.loaded.ops ++ parsed }
    now
    replica := some v.replica }

private def listPayload (key : String) (total : Nat) (rows : List Json) : Json :=
  Json.mkObj [("count", jnum total), (key, Json.arr rows.toArray)]

/-! ## Read verbs -/

def cmdReady (dirOverride : Option String) (limit : Nat) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let ranked := v.state.ready v.now
  let capped := if limit == 0 then ranked else ranked.take limit
  return { data := listPayload "items" ranked.length (capped.map (issueRow v))
           human :=
             if ranked.isEmpty then "nothing is ready"
             else String.intercalate "\n" (capped.map (issueLine v))
               ++ (if capped.length < ranked.length then
                     s!"\n… {ranked.length - capped.length} more (--limit 0 for all)"
                   else "")
           notes }

def cmdList (dirOverride : Option String) (limit : Nat) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  -- bare list: every issue, oldest first (the input-facet grammar is a
  -- recorded backlog decision; bare-and-total is the safe stage-1 surface)
  let all := (v.state.presentIssues.map (fun i => (v.state.createdAtOf i, i)))
    |>.mergeSort (fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2)))
    |>.map (·.2)
  let capped := if limit == 0 then all else all.take limit
  return { data := listPayload "items" all.length (capped.map (issueRow v))
           human :=
             if all.isEmpty then "no issues"
             else String.intercalate "\n" (capped.map (issueLine v))
               ++ (if capped.length < all.length then
                     s!"\n… {all.length - capped.length} more (--limit 0 for all)"
                   else "")
           notes }

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
  return { data, human := issueLine v i, notes }

def cmdWhy (dirOverride : Option String) (tok : String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let s := v.state
  let d := s.issueData i
  if s.isReady v.now i then
    return { data := Json.mkObj [("id", Json.str (displayId i)), ("ready", Json.bool true)]
             human := s!"{displayId i} is ready", notes }
  let trans := s.why i
  let direct := (s.blockersOf i).filter (fun b => !s.blockerDischarged b)
  let rows := trans.map (fun b =>
    let bd := s.issueData b
    Json.mkObj <|
      [("id", Json.str (displayId b)),
       ("status", Json.str (statusWire bd.statusOf)),
       ("effectiveStatus", Json.str (statusWire (s.effectiveStatus b))),
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
  let structural := s.cycles EdgeKind.Blocks ++ s.cycles EdgeKind.Parent
  -- a ≺-cycle whose node set coincides with a structural witness is already
  -- diagnosed by that row; only genuinely mixed deadlocks add a readiness row
  let readiness := s.precCycles.filter (fun w => !structural.contains w)
  let rows := (s.cycles EdgeKind.Blocks).map (entry "blocks")
    ++ (s.cycles EdgeKind.Parent).map (entry "parent")
    ++ readiness.map (entry "readiness")
  return { data := listPayload "cycles" rows.length rows
           human :=
             if rows.isEmpty then "no cycles"
             else s!"{rows.length} cycle(s) — break each with `tl dep remove`"
           notes }

/-! ## Write verbs -/

private def writeNow (v : TxContext) (parsed : List ParsedOp) : View :=
  postView v parsed v.now

def cmdCreate (dirOverride : Option String) (title : String) (priority : Option Nat)
    (description : Option String) (actor : String)
    (blockedBy blocks parents related : List String) : TlM CmdOut := do
  let edgeCount := blockedBy.length + blocks.length + parents.length + related.length
  let prio : Option (Fin 5) := priority.map (fun p => ⟨min p 4, Nat.lt_succ_of_le (Nat.min_le_right p 4)⟩)
  let d ← discover dirOverride
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
           notes := writeNotes ctx }

def cmdClaim (dirOverride : Option String) (tok : String) (actor : String) : TlM CmdOut := do
  let d ← discover dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    if s.isReady ctx.now i then
      .ok [.claim i actor]
    else
      let dta := s.issueData i
      let direct := (s.blockersOf i).filter (fun b => !s.blockerDischarged b)
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
           notes := writeNotes ctx }

def cmdClose (dirOverride : Option String) (tok : String) (asStr : String)
    (ofTok : Option String) (actor : String) : TlM CmdOut := do
  let some res := resolutionOfWire? asStr
    | throw (.mk' .usage s!"--as must be done|cancelled|duplicate (got '{asStr}')")
  -- a mode-scoped flag is usage-checked against its mode: --of names the
  -- duplicate's canonical issue and means nothing for done/cancelled
  if ofTok.isSome && res != .Duplicate then
    throw (.mk' .usage "--of names the canonical issue of a duplicate — it only pairs with --as duplicate")
  let d ← discover dirOverride
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
      let openKids := (s.presentChildren i).filter (fun c => !s.effClosed c)
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
  let freed := (ctx.loaded.state.unblocks ctx.now i).map (Json.str ∘ displayId)
  let data := (issueObj v i).setObjVal! "unblocked" (Json.arr freed.toArray)
  let human :=
    if parsed.isEmpty then s!"{displayId i} already closed as {asStr} — nothing to do"
    else s!"Closed {displayId i} as {asStr}" ++
      (if freed.isEmpty then "" else s!" (unblocked {freed.length})")
  return { data, human, notes := writeNotes ctx }

def cmdUpdate (dirOverride : Option String) (tok : String) (title description notes : Option String)
    (priority : Option Nat) (actor : String) : TlM CmdOut := do
  if title.isNone && description.isNone && notes.isNone && priority.isNone then
    throw (.mk' .usage "update needs at least one of --title, --priority, --description, --notes")
  let prio : Option (Fin 5) := priority.map (fun p => ⟨min p 4, Nat.lt_succ_of_le (Nat.min_le_right p 4)⟩)
  let d ← discover dirOverride
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
           notes := writeNotes ctx }

def cmdDepAdd (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let d ← discover dirOverride
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
           notes := writeNotes ctx }

def cmdDepRemove (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let d ← discover dirOverride
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
           notes := writeNotes ctx }

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
  -- doctor reports store damage instead of dying on it (the exemption)
  let (loaded, loadFail) ← try
      pure (← readState d, none)
    catch e =>
      pure (materialize [], some e)
  let now ← liftSys (fun e => .mk' .internal s!"{e}") nowMs
  let v : View := { dirs := d, loaded, now, replica := own }
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
  let structural := s.cycles EdgeKind.Blocks ++ s.cycles EdgeKind.Parent
  let cyc := structural.length
    + (s.precCycles.filter (fun w => !structural.contains w)).length
  let multi := (s.presentIssues.filter (fun i => (s.parentsOf i).length > 1)).length
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
      && match (provenanceOf loaded.ops i).claimedAt with
         | some h => now > h / 2 ^ 16 + 24 * 3600 * 1000
         | none => false)
  let staleRow := (Json.mkObj <|
    [("name", Json.str "staleClaims"),
     ("status", Json.str (if stale.isEmpty then "ok" else "warn")),
     ("count", jnum stale.length)]
    ++ (if stale.isEmpty then [] else
        [("ids", Json.arr (stale.map (Lean.Json.str ∘ displayId)).toArray)]), false)
  let rows := [replicaRow, clockRow] ++ logOk ++ [graphRow, staleRow]
  let healthy := rows.all (fun (_, failed) => !failed)
  let data := Json.mkObj
    [("healthy", Json.bool healthy),
     ("checks", Json.arr (rows.map (·.1)).toArray)]
  let human := (if healthy then "healthy" else "PROBLEMS FOUND") ++
    s!" — {rows.length} checks ({(rows.filter (·.2)).length} failing)"
  return { data, human }

def cmdInit (dirOverride : Option String) : TlM CmdOut := do
  -- placement (ADR-0001 §4): --dir wins; else the enclosing repo's toplevel;
  -- outside any repo, the cwd (with a local-only note)
  let (target, note) ← match dirOverride with
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
  let data := Json.mkObj
    [("root", Json.str target.toString),
     ("replica", (replica.map (·.id)).elim Json.null Json.str),
     ("created", Json.bool created.isSome)]
  let human := match created with
    | some r => s!"Initialized tl in {target} (replica {r.id})"
    | none => s!"{target} already initialized — nothing to do (idempotent)"
  return { data, human, notes := note }

/-- The product version (keep in lockstep with lakefile.lean's package
    version; `tl version` is the single user-facing source). -/
def productVersion : String := "0.1.0"

def cmdVersion : CmdOut :=
  { data := Json.mkObj [("version", Json.str productVersion), ("logFormat", jnum supportedVersion)]
    human := s!"tl {productVersion} (log format v{supportedVersion})" }

end Tl.Cli
