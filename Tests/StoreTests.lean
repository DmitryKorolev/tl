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
  -- a .git FILE (linked worktree/submodule) bounds it too
  IO.FS.removeDirAll (root / "src" / "deep" / ".git")
  IO.FS.writeFile (root / "src" / "deep" / ".git") "gitdir: elsewhere\n"
  outcomes := outcomes ++
    [← expectCode "gitfile boundary stops the walk" .noProject (discover none)]
  IO.Process.setCurrentDir prev
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
  -- foreign segment: a good line with the GLOBAL max HLC, then garbage
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
  -- clock recovery: absent file reseeds ABOVE the foreign max (all segments)
  IO.FS.removeFile (root / ".tl" / "local" / "clock")
  outcomes := outcomes ++
    [← expectOk "absent clock reseeds above the all-segments max"
        (transact d none 1 (buildCreate "post-reseed"))
        (fun (_, parsed) => check "absent clock reseeds above the all-segments max"
          (parsed.all (fun p => p.stamp.hlc > 0x7fffffffffff0000))
          s!"minted {parsed.map (·.stamp.hlc)}")]
  -- corrupt clock fails closed
  IO.FS.writeFile (root / ".tl" / "local" / "clock") "not-a-clock\n"
  outcomes := outcomes ++
    [← expectCode "corrupt clock is corrupt-clock" .corruptClock
        (transact d none 1 (buildCreate "x"))]
  IO.FS.removeFile (root / ".tl" / "local" / "clock")
  -- corrupt replica fails closed
  IO.FS.writeFile (root / ".tl" / "local" / "replica") "NOT!VALID!ID!\n"
  outcomes := outcomes ++
    [← expectCode "corrupt replica is corrupt-replica" .corruptReplica
        (transact d none 1 (buildCreate "x"))]
  -- absent replica with state present auto-mints a NEW id
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

def storeTests : IO (List Outcome) := do
  return (← storeDiscoveryTests) ++ (← storeWriteTests)
    ++ (← storeAdversityTests) ++ (← storeLockTests)

end Tl.Tests
