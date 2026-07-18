/-
`Tests.StoreTests` — the store adversity battery (ADR-0008 §corruption,
ADR-0012, ADR-0015).

Discrete tests per documented branch: discovery (found / repo-boundary stop /
not-found / override validation / uninitialized / symlinked `.tl`), the
locked write path (create commit, guard refusal writes nothing, zero-record
no-op), crash-fragment hygiene and its pinned cascade (the closed fragment
becomes a malformed line and the own segment is refused loudly), hostile
foreign segments (segment-scoped refusal; `--skip-bad` with disclosures),
the line-scoped HLC scan, clock recovery (absent → reseed above the
segments' max; corrupt → fail-closed `reason:"unreadable"`), replica
recovery (absent → auto-mint; corrupt → `corrupt-replica`), and lock
contention (bounded `lock-busy`).

`TL_DIR`/`GIT_CEILING_DIRECTORIES` env reads are not unit-testable here
(core Lean has no `setEnv`); the override code path is covered via
`discover (override := …)`, which shares everything but the env read.
-/
import Tl.Store.Lock
import Tl.Cli.Init
import Tl.Format.Ids
import Tests.Harness

namespace Tl.Tests

open Tl.Store
open Tl.Format
open Tl.Crdt (Stamp)

private def fixedReplica : String := "0123456789abc"

/-- A fresh project: `.tl/local` with a pinned replica id and a zero clock. -/
private def mkProject : IO (System.FilePath × Dirs) := do
  let root ← IO.FS.createTempDir
  IO.FS.createDirAll (root / ".tl" / "local")
  IO.FS.writeFile (root / ".tl" / ".gitignore") "*\n"
  IO.FS.writeFile (root / ".tl" / "local" / "replica") (fixedReplica ++ "\n")
  IO.FS.writeFile (root / ".tl" / "local" / "clock") "0000000000000000\n"
  return (root, { base := root.toString, tlRel := ".tl" })

private def runTl (act : TlM α) : IO (Except Tl.Error α) := act.run

/-- Expect a structured failure with the given code. -/
private def expectCode (name : String) (code : Tl.ErrorCode) (act : TlM α) : IO Outcome := do
  match ← runTl act with
  | .error e =>
    if e.code = code then return { name, passed := true }
    else return { name, passed := false, msg := s!"expected {code.wire}, got {e.code.wire}: {e.message}" }
  | .ok _ => return { name, passed := false, msg := s!"expected {code.wire}, succeeded" }

private def expectOk (name : String) (act : TlM α) (checkFn : α → Outcome) : IO Outcome := do
  match ← runTl act with
  | .ok a => return checkFn a
  | .error e => return { name, passed := false, msg := s!"failed: {e.code.wire}: {e.message}" }

private def symlink (target linkPath : String) : IO Unit := do
  let out ← IO.Process.output { cmd := "ln", args := #["-s", target, linkPath] }
  unless out.exitCode == 0 do throw (IO.userError s!"ln -s failed: {out.stderr}")

/-- Build exactly one `create` from the minted stamp. -/
private def buildCreate (title : String) : TxContext → List Stamp →
    Except Tl.Error (List WireOp) := fun _ stamps =>
  match stamps with
  | [st] => .ok [.create (mintIssueId st) { title := some title }]
  | _ => .error (.mk' .internal "expected exactly one stamp")

def storeDiscoveryTests : IO (List Outcome) := do
  let mut outcomes : List Outcome := []
  let (root, _) ← mkProject
  -- found from a nested cwd
  IO.FS.createDirAll (root / "src" / "deep")
  let prev ← IO.currentDir
  IO.Process.setCurrentDir (root / "src" / "deep")
  outcomes := outcomes ++
    [← expectOk "discovery walks up to .tl" (discover none)
        (fun d => check "discovery walks up to .tl" (d.tlRel == ".tl"))]
  -- a nested repo boundary stops the walk (never binds the outer .tl)
  IO.FS.createDirAll (root / "src" / "deep" / ".git")
  outcomes := outcomes ++
    [← expectCode "repo boundary stops the walk" .noProject (discover none)]
  -- a .git file (linked worktree/submodule) bounds it too
  IO.FS.removeDirAll (root / "src" / "deep" / ".git")
  IO.FS.writeFile (root / "src" / "deep" / ".git") "gitdir: elsewhere\n"
  outcomes := outcomes ++
    [← expectCode "gitfile boundary stops the walk" .noProject (discover none)]
  IO.Process.setCurrentDir prev
  -- a bare gitdir bounds the walk: from inside a bare repo nested under a
  -- project, discovery must not ascend past it and bind the enclosing .tl
  let bare := root / "srv" / "mirror.git"
  IO.FS.createDirAll (bare / "objects")
  IO.FS.createDirAll (bare / "refs")
  IO.FS.createDirAll (bare / "hooks")
  IO.FS.writeFile (bare / "HEAD") "ref: refs/heads/main\n"
  IO.Process.setCurrentDir (bare / "hooks")
  outcomes := outcomes ++
    [← expectCode "bare-gitdir boundary stops the walk" .noProject (discover none)]
  -- the boundary teaches: the message names the bare layout, not a bare "no project"
  outcomes := outcomes ++ [← (do
    match ← runTl (discover none) with
    | .error e => pure (check "bare boundary error message teaches"
        ((e.message.splitOn "git repository directory").length > 1) e.message)
    | .ok _ => pure { name := "bare boundary error message teaches", passed := false,
                      msg := "unexpectedly bound a project" })]
  -- a linked worktree's private gitdir (HEAD but no objects/) is NOT a bare
  -- boundary — the walk ascends normally and finds the project .tl
  let wtPriv := root / "wt" / "worktrees" / "feature"
  IO.FS.createDirAll wtPriv
  IO.FS.writeFile (wtPriv / "HEAD") "ref: refs/heads/feature\n"
  IO.Process.setCurrentDir wtPriv
  -- compare canonically: createTempDir may hand back a symlinked path
  -- (macOS /var → /private/var) while the walk sees the canonical cwd
  let realRoot ← IO.FS.realPath root
  outcomes := outcomes ++
    [← expectOk "worktree private gitdir does not bound the walk" (discover none)
        (fun d => check "worktree private gitdir does not bound the walk"
          (d.base == realRoot.toString) s!"base={d.base} expected={realRoot}")]
  IO.Process.setCurrentDir prev
  -- structural bare-gitdir detection: objects/ dir + refs/ + a HEAD entry of
  -- ANY form bounds the walk. The check is deliberately at-least-as-inclusive
  -- as git, so tl never climbs out of a directory git treats as a gitdir —
  -- every HEAD shape git accepts (and then some) bounds here. Build one gitdir
  -- per HEAD variant git considers valid but a content-matching check missed,
  -- cd in, and assert discovery stops (no-project) rather than binding the
  -- enclosing project.
  let mkBare (name : String) (writeHead : System.FilePath → IO Unit) : IO System.FilePath := do
    let g := root / "bares" / name
    IO.FS.createDirAll (g / "objects")
    IO.FS.createDirAll (g / "refs")
    writeHead g
    pure g
  let variants : List (String × (System.FilePath → IO Unit)) :=
    [("symref-spaced", fun g => IO.FS.writeFile (g / "HEAD") "ref: refs/heads/main\n"),
     ("symref-nospace", fun g => IO.FS.writeFile (g / "HEAD") "ref:refs/heads/main\n"),
     ("symref-tab", fun g => IO.FS.writeFile (g / "HEAD") "ref:\trefs/heads/main\n"),
     ("hash-lower", fun g => IO.FS.writeFile (g / "HEAD") (String.ofList (List.replicate 40 'a') ++ "\n")),
     ("hash-upper", fun g => IO.FS.writeFile (g / "HEAD") (String.ofList (List.replicate 40 'A') ++ "\n")),
     ("hash-trailing", fun g => IO.FS.writeFile (g / "HEAD") (String.ofList (List.replicate 40 'a') ++ " extra junk\n")),
     ("head-oversized", fun g => IO.FS.writeFile (g / "HEAD") (String.ofList (List.replicate 5000 'a') ++ "\n")),
     ("symlink-dangling", fun g => symlink "refs/heads/gone" (g / "HEAD").toString)]
  for (name, wr) in variants do
    let g ← mkBare name wr
    IO.Process.setCurrentDir g
    outcomes := outcomes ++
      [← expectCode s!"bare gitdir ({name}) bounds the walk" .noProject (discover none),
       check s!"isGitDirLayout matches ({name})" (← isGitDirLayout g)]
  IO.Process.setCurrentDir prev
  -- refs as an executable regular FILE (git checks access(refs, X_OK), which a
  -- dir OR an executable file satisfies) still bounds — requiring refs/ to be a
  -- directory would be stricter than git
  let refsFile := root / "bares" / "refs-as-file"
  IO.FS.createDirAll (refsFile / "objects")
  IO.FS.writeFile (refsFile / "refs") ""
  IO.FS.writeFile (refsFile / "HEAD") "ref: refs/heads/main\n"
  outcomes := outcomes ++
    [check "isGitDirLayout matches when refs is a regular file" (← isGitDirLayout refsFile)]
  -- a usable but UNLISTABLE gitdir (mode 0711 — traversable, not readable):
  -- git operates in it, and the no-follow shim probe still finds HEAD where a
  -- readDir listing would get EACCES and falsely report "no HEAD"
  let locked := root / "bares" / "locked.git"
  IO.FS.createDirAll (locked / "objects")
  IO.FS.createDirAll (locked / "refs")
  IO.FS.writeFile (locked / "HEAD") "ref: refs/heads/main\n"
  let _ ← IO.Process.output { cmd := "chmod", args := #["0711", locked.toString] }
  outcomes := outcomes ++
    [check "isGitDirLayout matches an unlistable 0711 gitdir" (← isGitDirLayout locked)]
  -- non-matches: HEAD absent, objects/ absent (worktree-private gitdir), plain
  let noHead := root / "bares" / "no-head"
  IO.FS.createDirAll (noHead / "objects"); IO.FS.createDirAll (noHead / "refs")
  outcomes := outcomes ++
    [check "isGitDirLayout: no HEAD entry does not match" (!(← isGitDirLayout noHead)),
     check "isGitDirLayout: worktree private gitdir (no objects/) does not match"
       (!(← isGitDirLayout wtPriv)),
     check "isGitDirLayout: an ordinary directory does not match"
       (!(← isGitDirLayout (root / "src")))]
  -- override: valid state dir is found without discovery
  outcomes := outcomes ++
    [← expectOk "override binds the state dir" (discover (some (root / ".tl").toString))
        (fun d => check "override binds the state dir" (d.tlRel == ".tl"))]
  -- override at a missing path / an uninitialized (empty) dir
  outcomes := outcomes ++
    [← expectCode "override at a missing path is no-project" .noProject
        (discover (some (root / "nope").toString))]
  let emptyDir ← IO.FS.createTempDir
  outcomes := outcomes ++
    [← expectCode "an empty dir is not a project" .noProject
        (discover (some emptyDir.toString))]
  -- a symlinked .tl is refused (T4)
  let lroot ← IO.FS.createTempDir
  symlink (root / ".tl").toString (lroot / ".tl").toString
  outcomes := outcomes ++
    [← expectCode "symlinked .tl is unsafe-path" .unsafePath
        (validate { base := lroot.toString, tlRel := ".tl" })]
  return outcomes

def storeWriteTests : IO (List Outcome) := do
  let mut outcomes : List Outcome := []
  let (root, d) ← mkProject
  -- first commit: one create
  outcomes := outcomes ++
    [← expectOk "transact commits one create" (transact d (some "carol") 1 (buildCreate "first"))
        (fun (_, parsed) => check "transact commits one create"
          (parsed.length == 1 && parsed.all (fun p => p.actor == some "carol")))]
  -- the segment holds exactly one canonical line; the clock advanced
  let seg ← IO.FS.readFile (root / ".tl" / "log" / (fixedReplica ++ ".jsonl"))
  let clock ← IO.FS.readFile (root / ".tl" / "local" / "clock")
  outcomes := outcomes ++
    [check "own segment has one LF-terminated line"
      ((seg.toList.filter (· == '\n')).length == 1 && seg.endsWith "\n") seg,
     check "the line decodes canonically"
       (match decodeLine ((seg.dropEnd 1).toString) with
        | .ok p => renderLine p ++ "\n" == seg
        | .error _ => false),
     check "clock advanced past zero" (clock.trimAscii.toString != "0000000000000000") clock]
  -- the materialized state sees the issue
  outcomes := outcomes ++
    [← expectOk "readState folds the create" (readState d)
        (fun loaded => check "readState folds the create"
          (loaded.state.presentIssues.length == 1 && loaded.refused.isEmpty))]
  -- a guard refusal writes nothing
  let segBefore ← IO.FS.readFile (root / ".tl" / "log" / (fixedReplica ++ ".jsonl"))
  outcomes := outcomes ++
    [← expectCode "guard refusal aborts before writing" .notCloseable
        (transact d none 1 (fun _ _ => .error (.mk' .notCloseable "refused")))]
  let segAfter ← IO.FS.readFile (root / ".tl" / "log" / (fixedReplica ++ ".jsonl"))
  outcomes := outcomes ++
    [check "no bytes appended on refusal" (segBefore == segAfter)]
  -- zero records (idempotent no-op): nothing appended, clock file untouched
  let clockBefore ← IO.FS.readFile (root / ".tl" / "local" / "clock")
  outcomes := outcomes ++
    [← expectOk "zero-record transact is a no-op" (transact d none 1 (fun _ _ => .ok []))
        (fun (_, parsed) => check "zero-record transact is a no-op" parsed.isEmpty)]
  let clockAfter ← IO.FS.readFile (root / ".tl" / "local" / "clock")
  outcomes := outcomes ++
    [check "no-op leaves the clock file untouched" (clockBefore == clockAfter)]
  return outcomes

def storeAdversityTests : IO (List Outcome) := do
  let mut outcomes : List Outcome := []
  let (root, d) ← mkProject
  let _ ← runTl (transact d none 1 (buildCreate "mine"))
  let ownSeg := root / ".tl" / "log" / (fixedReplica ++ ".jsonl")
  -- foreign segment: a good line with the global max HLC, then garbage
  let foreignId := "1zzzzzzzzzzzz"
  let goodForeign :=
    "{\"v\":1,\"op\":\"reopen\",\"hlc\":\"7fffffffffff0000\",\"replica\":\"" ++ foreignId ++
    "\",\"nonce\":\"0123456789abcdefghjkmnpqrs\",\"actor\":null,\"id\":\"0123456789abcdef\"}"
  IO.FS.writeFile (root / ".tl" / "log" / (foreignId ++ ".jsonl"))
    (goodForeign ++ "\nGARBAGE NOT JSON\n")
  outcomes := outcomes ++
    [← expectOk "hostile foreign segment is refused, others fold" (readState d)
        (fun loaded => check "hostile foreign segment is refused, others fold"
          (loaded.refused.length == 1
            && loaded.refused.all (fun r => r.replicaId == foreignId && r.line == 2)
            && loaded.state.presentIssues.length == 1     -- own create only
            && loaded.maxHlc == 0x7fffffffffff0000)        -- line-scoped scan
          s!"refused={loaded.refused.length} max={loaded.maxHlc}"),
     ← expectOk "--skip-bad folds around the bad line" (readState d (skipBad := true))
        (fun loaded => check "--skip-bad folds around the bad line"
          (loaded.refused.isEmpty && loaded.skipped == [(foreignId, 2)]
            && loaded.state.presentIssues.length == 1)    -- reopen of a dangling id adds no issue
          s!"skipped={loaded.skipped}")]
  -- clock recovery: an absent file reseeds from the segments' max — but a
  -- far-future foreign HLC is deferred (ADR-0007 skew window), so it does not
  -- inflate the reseed toward saturation; the minted clock stays sane (≈ now),
  -- below the planted 0x7fff… foreign HLC rather than jumping to it.
  IO.FS.removeFile (root / ".tl" / "local" / "clock")
  outcomes := outcomes ++
    [← expectOk "absent-clock reseed defers a far-future foreign HLC (no inflation)"
        (transact d none 1 (buildCreate "post-reseed"))
        (fun (_, parsed) => check "absent-clock reseed defers a far-future foreign HLC (no inflation)"
          (!parsed.isEmpty && parsed.all (fun p => p.stamp.hlc < 0x7fffffffffff0000))
          s!"minted {parsed.map (·.stamp.hlc)}")]
  -- corrupt clock fails closed
  IO.FS.writeFile (root / ".tl" / "local" / "clock") "not-a-clock\n"
  outcomes := outcomes ++
    [← expectCode "corrupt clock is corrupt-clock" .corruptClock
        (transact d none 1 (buildCreate "x"))]
  -- the saturated-clock bridge: mintStamps at the 48-bit physical ceiling throws the
  -- structured corrupt-clock(reason:"saturated") — distinct from the unreadable path
  -- above (which is reason:"unreadable"); assert the context, not just the code
  outcomes := outcomes ++
    [← (do
        match ← runTl (mintStamps 1
            (⟨Tl.Clock.Hlc.physMax, Tl.Clock.Hlc.logMax⟩ : Tl.Clock.Hlc) Tl.Clock.Hlc.physMax 1) with
        | .error e =>
          let satCtx := e.context.any (fun p => p.1 == "reason" &&
            (match p.2 with | .str s => s == "saturated" | _ => false))
          pure (check "mintStamps at saturation throws corrupt-clock(reason:saturated)"
            (decide (e.code = .corruptClock) && satCtx) s!"got {e.code.wire}, ctx {e.context.length} entries")
        | .ok _ =>
          pure (check "mintStamps at saturation throws corrupt-clock(reason:saturated)"
            false "unexpectedly succeeded"))]
  IO.FS.removeFile (root / ".tl" / "local" / "clock")
  -- writeLocalFile's rename-failure .error arm: a non-empty directory at the clock
  -- target makes `rename` fail (regardless of uid — unlike a chmod, bypassed under
  -- root); assert (a) a structured throw (the under-lock callers rethrow, unlike the
  -- best-effort saveCache), (b) the CSPRNG-suffixed .tmp is removed, not stranded (a
  -- persistent failure would otherwise pile up one temp per attempt).
  IO.FS.createDirAll (root / ".tl" / "local" / "clock")
  IO.FS.writeFile (root / ".tl" / "local" / "clock" / "blocker") "x"
  let wres ← runTl (writeLocalFile d d.relClock "0000000000000000\n")
  let entries ← (root / ".tl" / "local").readDir
  let stranded := entries.filter (fun e => e.fileName.endsWith ".tmp")
  outcomes := outcomes ++ [
    check "writeLocalFile over a directory target throws (not swallowed)"
      (match wres with | .error _ => true | .ok _ => false) "unexpectedly succeeded",
    check "no .tmp stranded by the failed rename" stranded.isEmpty
      s!"stranded {stranded.size} temp file(s)"]
  IO.FS.removeDirAll (root / ".tl" / "local" / "clock")
  -- corrupt replica fails closed
  IO.FS.writeFile (root / ".tl" / "local" / "replica") "NOT!VALID!ID!\n"
  outcomes := outcomes ++
    [← expectCode "corrupt replica is corrupt-replica" .corruptReplica
        (transact d none 1 (buildCreate "x"))]
  -- absent replica with state present auto-mints a new id
  IO.FS.removeFile (root / ".tl" / "local" / "replica")
  outcomes := outcomes ++
    [← expectOk "absent replica auto-mints" (transact d none 1 (buildCreate "reborn"))
        (fun (ctx, _) => check "absent replica auto-mints"
          (ctx.replica.id != fixedReplica && ctx.replica.valid) ctx.replica.id)]
  -- crash fragment: the next writer closes it; the closed line then refuses
  IO.FS.writeFile (root / ".tl" / "local" / "replica") (fixedReplica ++ "\n")
  let pre ← IO.FS.readBinFile ownSeg
  IO.FS.writeBinFile ownSeg (pre ++ "{\"v\":1,\"op\"".toUTF8)   -- torn, no LF
  outcomes := outcomes ++
    [← expectOk "torn tail is skipped on read (uncommitted, not corruption)" (readState d)
        (fun loaded => check "torn tail is skipped on read (uncommitted, not corruption)"
          (loaded.refused.all (fun r => r.replicaId != fixedReplica))),
     ← expectOk "next write closes the crash fragment" (transact d none 1 (buildCreate "after-crash"))
        (fun _ => check "next write closes the crash fragment" true)]
  let bytes ← IO.FS.readBinFile ownSeg
  let lines := completeLines bytes
  outcomes := outcomes ++
    [check "fragment became its own complete line"
      (lines.any (fun l => String.fromUTF8? l == some "{\"v\":1,\"op\"")) "",
     -- and the pinned cascade: the own segment is now refused, loudly
     ← expectCode "the closed fragment now refuses the own segment (write path)"
        .malformedLine (transact d none 1 (buildCreate "blocked")),
     ← expectOk "the closed fragment refuses the own segment on read (disclosed)"
        (readState d)
        (fun loaded => check "the closed fragment refuses the own segment on read (disclosed)"
          (loaded.refused.any (fun r => r.replicaId == fixedReplica)))]
  return outcomes

def storeLockTests : IO (List Outcome) := do
  let mut outcomes : List Outcome := []
  let (_, d) ← mkProject
  -- hold the lock through a raw shim fd, then watch transact bounce
  let fd ← Tl.Store.Sys.openNoFollow d.base d.relLock
    (Tl.Store.Sys.flagCreate ||| Tl.Store.Sys.flagWrite)
  let _ ← Tl.Store.Sys.tryLock fd true
  outcomes := outcomes ++
    [← expectCode "contended lock is lock-busy after the bounded wait" .lockBusy
        (transact d none 1 (buildCreate "x") (timeoutMs := 120))]
  Tl.Store.Sys.unlock fd
  Tl.Store.Sys.close fd
  outcomes := outcomes ++
    [← expectOk "released lock admits the write" (transact d none 1 (buildCreate "x"))
        (fun (_, parsed) => check "released lock admits the write" (parsed.length == 1))]
  -- pure helpers
  outcomes := outcomes ++
    [check "completeLines drops the torn tail"
      ((completeLines "a\nb\nfrag".toUTF8).length == 2),
     check "tornTail detects the fragment" (tornTail "a\nfrag".toUTF8),
     check "tornTail is false on clean LF end" (!tornTail "a\n".toUTF8),
     check "tornTail is false on empty" (!tornTail ByteArray.empty)]
  return outcomes

/-- A crafted record line for a segment with replica id `stem` (the per-replica
    owner check requires the stamp's replica to match the segment name). -/
private def craftLine (op : WireOp) (hlc nonce : Nat) (stem : String) : String :=
  renderLine { v := op.recordVersion, op,
               stamp := ⟨hlc, (ofCrockford? stem).getD 0, nonce⟩, actor := some "x" }

/-- The HLC skew window (ADR-0007): foreign ops dated beyond `now + W` are
    deferred (held back from the fold and from `maxHlc`) until wall-clock catches
    up; within-window foreign ops fold; the own segment is exempt. Deterministic
    — `now` is passed explicitly, so the test never depends on the wall clock. -/
def storeSkewTests : IO (List Outcome) := do
  let now := 2000000000000                                  -- a fixed "now" in ms (~2033)
  let ownId := fixedReplica
  let foreignId := "1zzzzzzzzzzzz"
  let withinHlc := (now + 60000) * 2 ^ 16                   -- 1 min ahead: within W
  let futureHlc := (now + skewWindowMs + 60000) * 2 ^ 16    -- just past W: deferred
  let ownFutureHlc := (now + skewWindowMs + 120000) * 2 ^ 16 -- own, far future: exempt
  let foreignSeg : SegmentData := { replicaId := foreignId, bytes :=
    (craftLine (.create "aaaabbbbccccdddd" { title := some "near" }) withinHlc 1 foreignId ++ "\n"
      ++ craftLine (.create "1111222233334444" { title := some "future" }) futureHlc 2 foreignId ++ "\n").toUTF8 }
  let ownSeg : SegmentData := { replicaId := ownId, bytes :=
    (craftLine (.create "ffff0000ffff0000" { title := some "ownfuture" }) ownFutureHlc 1 ownId ++ "\n").toUTF8 }
  let loaded := materialize [ownSeg, foreignSeg] false (some now) (some ownId)
  let off := materialize [ownSeg, foreignSeg]
  -- own-id unknown: nothing is deferred (we cannot tell a segment from our own)
  let ownUnknown := materialize [foreignSeg] false (some now) none
  -- a refused segment (future-dated line 1, malformed line 2) must report only
  -- its refusal — not also "held back, appears later" for the future line
  let refusedSeg : SegmentData := { replicaId := foreignId, bytes :=
    (craftLine (.create "1111222233334444" { title := some "future" }) futureHlc 1 foreignId ++ "\n"
      ++ "GARBAGE NOT JSON\n").toUTF8 }
  let refusedDec := decodeSegment refusedSeg false (some (now + skewWindowMs))
  return [
    check "a far-future foreign op is deferred (recorded, not folded)"
      (loaded.deferred == [(foreignId, 2)]) s!"deferred={loaded.deferred}",
    check "deferral keeps the future op out of the fold (within + own fold, future does not)"
      (loaded.state.presentIssues.length == 2) s!"present={loaded.state.presentIssues.length}",
    check "a deferred foreign HLC does not inflate maxHlc; the exempt own-future one does"
      (loaded.maxHlc == ownFutureHlc) s!"maxHlc={loaded.maxHlc} ownFuture={ownFutureHlc}",
    check "the deferred op's lead is recorded (maxDeferredHlc) for doctor"
      (loaded.maxDeferredHlc == futureHlc) s!"maxDeferred={loaded.maxDeferredHlc} future={futureHlc}",
    check "with the skew check off (no now) all three fold and nothing defers"
      (off.state.presentIssues.length == 3 && off.deferred.isEmpty),
    check "own-id unknown ⇒ nothing deferred (never risk deferring our own op)"
      (ownUnknown.deferred.isEmpty) s!"deferred={ownUnknown.deferred}",
    check "a refused segment reports ONLY its refusal, never a held-back disclosure"
      (refusedDec.refusal.isSome && refusedDec.deferred.isEmpty && refusedDec.maxDeferred == 0)
      s!"refusal={refusedDec.refusal.isSome} deferred={refusedDec.deferred}"]

/-- Element-scoped OR-Set tombstones at the `WireOp.toOp → apply` fold seam
    (ADR-0002): an `unrelate` whose `observed` payload also names ANOTHER edge's
    add-tag (here the `blocks` edge's) removes only its own `related` element.
    Under the retired global-tombstone semantics the cross-element tag would
    kill the `blocks` edge too — this is the one row where the two semantics
    diverge (every other remove row in the suite observes only its own
    element's tags, where they coincide). -/
def storeTombstoneScopeTests : List Outcome :=
  let idA := "a000000000000000"
  let idB := "b000000000000000"
  let hlc (i : Nat) : Nat := 2000000000000 * 2 ^ 16 + i
  let stampAt (i : Nat) : Stamp := ⟨hlc i, (ofCrockford? fixedReplica).getD 0, 5000 + i⟩
  -- lines are rendered from the SAME `stampAt` values the observed set uses,
  -- so the tag the test tombstones cannot drift from the tag the line minted
  let line (op : WireOp) (i : Nat) : String :=
    renderLine { v := op.recordVersion, op, stamp := stampAt i, actor := some "x" }
  -- the adversarial observed set: the related edge's own tag AND the blocks edge's
  let obs : Tl.Crdt.FinSet Stamp :=
    Tl.Crdt.FinSet.union (Tl.Crdt.FinSet.singleton (stampAt 3))
      (Tl.Crdt.FinSet.singleton (stampAt 4))
  let seg : SegmentData := { replicaId := fixedReplica, bytes :=
    (line (.create idA { title := some "A" }) 1
      ++ "\n" ++ line (.create idB { title := some "B" }) 2
      ++ "\n" ++ line (.depAdd (idA, idB, .Blocks)) 3
      ++ "\n" ++ line (.relate (idA, idB, .Related)) 4
      ++ "\n" ++ line (.unrelate (idA, idB, .Related) obs) 5
      ++ "\n").toUTF8 }
  let loaded := materialize [seg]
  let readyIds := loaded.state.ready 2000000000000
  [ check "unrelate with a cross-element observed tag removes only its own related edge"
      (loaded.state.presentEdges == [(idA, idB, .Blocks)])
      s!"live edges={loaded.state.presentEdges.length} (want exactly the blocks edge)",
    check "the blocks edge still blocks: B's blocker list is untouched"
      (loaded.state.blockersOf idB == [idA])
      s!"blockers of B={loaded.state.blockersOf idB}",
    check "B stays blocked in ready; A is ready"
      (readyIds.contains idA && !readyIds.contains idB) s!"ready={readyIds}" ]


/-- The journal fold semantics at the wire seam (ADR-0027): concurrent adds
    all retained; removal hides in either delivery order (tombstone by tag
    value); remove-exactness under a forged duplicate handle; the same-triple
    payload join is order-independent; duplicate delivery is one entry; equal
    text from separate ops stays two entries; ordering is stamp-ascending;
    `updatedAt` bumps on a note add, never on a note remove, and a legacy
    notes-only update (unknown-bag routed) neither materializes nor bumps. -/
def storeJournalTests : List Outcome :=
  let idA := "a000000000000000"
  let foreignId := "1zzzzzzzzzzzz"
  let hlc (i : Nat) : Nat := 2000000000000 * 2 ^ 16 + i
  let stampAt (i : Nat) (repl : String := fixedReplica) : Stamp :=
    ⟨hlc i, (ofCrockford? repl).getD 0, 5000 + i⟩
  let lineAs (repl : String) (op : WireOp) (i : Nat) : String :=
    renderLine { v := op.recordVersion, op, stamp := stampAt i repl, actor := some "x" }
  let line := lineAs fixedReplica
  let segOf (repl : String) (ls : List String) : SegmentData :=
    { replicaId := repl, bytes := (ls.foldl (fun a l => a ++ l ++ "\n") "").toUTF8 }
  let journalOf (segs : List SegmentData) : Tl.Crdt.Journal :=
    ((materialize segs).state.issueData idA).notes
  let texts (jn : Tl.Crdt.Journal) : List String :=
    jn.visibleEntries.map (fun (_, pl) => pl.text)
  let createL := line (.create idA { title := some "A" }) 1
  -- (a) concurrent adds from two replicas: both retained, stamp-ascending
  let ownAdd := line (.noteAdd idA (mintNoteId (stampAt 3)) "own progress") 3
  let forAdd := lineAs foreignId (.noteAdd idA (mintNoteId (stampAt 2 foreignId)) "foreign progress") 2
  let jConc := journalOf [segOf fixedReplica [createL, ownAdd], segOf foreignId [forAdd]]
  -- (b) remove folded before its add still hides the entry on arrival
  let remove3 := line (.noteRemove idA (mintNoteId (stampAt 3)) (Tl.Crdt.FinSet.singleton (stampAt 3))) 6
  let jRemFirst := journalOf [segOf fixedReplica [createL, remove3, ownAdd]]
  -- (c) forged duplicate handle from a distinct stamp: independent entries;
  -- removal touches exactly the observed tag
  let dupHandle := mintNoteId (stampAt 3)
  let forged := line (.noteAdd idA dupHandle "forged twin") 4
  let jDup := journalOf [segOf fixedReplica [createL, ownAdd, forged]]
  let jDupRemoved := journalOf [segOf fixedReplica [createL, ownAdd, forged, remove3]]
  -- (d) same complete triple, different payloads: the join is order-independent
  let twinA := renderLine { v := 2, op := .noteAdd idA dupHandle "alpha payload",
                            stamp := stampAt 5, actor := some "x" }
  let twinB := renderLine { v := 2, op := .noteAdd idA dupHandle "beta payload",
                            stamp := stampAt 5, actor := some "x" }
  let jTwinAB := journalOf [segOf fixedReplica [createL, twinA, twinB]]
  let jTwinBA := journalOf [segOf fixedReplica [createL, twinB, twinA]]
  -- (e) duplicate delivery of one op is one entry
  let jDouble := journalOf [segOf fixedReplica [createL, ownAdd, ownAdd]]
  -- (f) identical text from separate ops stays two entries
  let sameText := line (.noteAdd idA (mintNoteId (stampAt 7)) "own progress") 7
  let jSame := journalOf [segOf fixedReplica [createL, ownAdd, sameText]]
  -- (g) updatedAt: bumps on add, never on remove; a legacy notes-only update
  -- routes to the unknown bag — no materialization, no bump
  let upd (segs : List SegmentData) : Option Stamp :=
    ((materialize segs).state.issueData idA).updatedAtStamp
  let legacyNotes :=
    "{\"v\":1,\"op\":\"update\",\"hlc\":\"" ++ hlcHex (hlc 9)
      ++ "\",\"replica\":\"" ++ fixedReplica
      ++ "\",\"nonce\":\"" ++ toCrockford 5009 26
      ++ "\",\"actor\":\"x\",\"id\":\"" ++ idA
      ++ "\",\"notes\":\"legacy scalar text\"}"
  let jLegacy := journalOf [segOf fixedReplica [createL, legacyNotes]]
  [ check "concurrent note adds are both retained, stamp-ascending"
      (texts jConc == ["foreign progress", "own progress"]) s!"texts={texts jConc}",
    check "a remove folded before its add hides the entry on arrival"
      ((texts jRemFirst).isEmpty) s!"texts={texts jRemFirst}",
    check "a forged duplicate handle from a distinct stamp is an independent entry"
      ((texts jDup).length == 2) s!"texts={texts jDup}",
    check "removal touches exactly the observed tag, not its handle twin"
      (texts jDupRemoved == ["forged twin"]) s!"texts={texts jDupRemoved}",
    check "same-triple payload twins join order-independently (lexicographic max)"
      (texts jTwinAB == ["beta payload"] && texts jTwinBA == ["beta payload"])
      s!"ab={texts jTwinAB} ba={texts jTwinBA}",
    check "duplicate delivery of one add renders once"
      (texts jDouble == ["own progress"]) s!"texts={texts jDouble}",
    check "identical text from separate ops renders twice"
      (texts jSame == ["own progress", "own progress"]) s!"texts={texts jSame}",
    check "note add bumps updatedAt to its own stamp"
      (upd [segOf fixedReplica [createL, ownAdd]] == some (stampAt 3))
      s!"upd={(upd [segOf fixedReplica [createL, ownAdd]]).map (fun st => st.hlc)}",
    check "note remove does not bump updatedAt (the disclosed asymmetry)"
      (upd [segOf fixedReplica [createL, ownAdd, remove3]] == some (stampAt 3)),
    check "a legacy scalar-notes update neither materializes nor bumps updatedAt"
      ((texts jLegacy).isEmpty
        && upd [segOf fixedReplica [createL, legacyNotes]] == some (stampAt 1)) ]

def storeTests : IO (List Outcome) := do
  return (← storeDiscoveryTests) ++ (← storeWriteTests)
    ++ (← storeAdversityTests) ++ (← storeLockTests) ++ (← storeSkewTests)
    ++ storeTombstoneScopeTests ++ storeJournalTests

end Tl.Tests
