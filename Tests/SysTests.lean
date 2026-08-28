/-
`Tests.SysTests` — per-branch tests for the native shim (ADR-0019).

Each shim function's documented branches get a discrete assertion: symlink
refusal at the final and an intermediate `rel` component (ADR-0015 §6 — the
component walk), the base-follows/rel-refuses split (a macOS temp dir lives
under the `/var` symlink, so the *base* leg is exercised by every row here),
`O_EXCL` collision, append+sync round-trip, lock contention between two open
file descriptions, entropy shape/freshness, the ownership check, and
read-to-EOF on empty input. POSIX is the gating path (ADR-0015 §7); symlinks
are created with `ln -s` (core Lean has no symlink API).

The durability barrier is the exception to "a real syscall on a real file",
because the branches worth covering are the ones no filesystem will produce on
request. Its rows drive the shipped policy through a scripted-fault probe —
see the section heading below for what that probe is and why it is bound here.

The intermediate-symlink errno is platform-split — Linux reports `ELOOP`,
Darwin `ENOTDIR` (the link, unfollowed, is not a directory) — both are the
refusal; the policy layer maps either to `unsafe-path`.
-/
import Tl.Store.Sys
import Tests.Harness
import Tests.SyncBarrierProbe

namespace Tl.Tests

open Tl.Store
open Tl.Store.Sys (flagWrite flagAppend flagCreateExcl flagDirectory flagCreate)

/-- Run an IO action, expecting a shim failure with one of the errno tokens. -/
private def expectErrno (name : String) (codes : List String) (act : IO α) : IO Outcome := do
  match ← act.toBaseIO with
  | .error e =>
    if codes.any (fun c => Sys.errnoOf e == some c) then return { name, passed := true }
    else return { name, passed := false, msg := s!"expected one of {codes}, got: {e}" }
  | .ok _ => return { name, passed := false, msg := s!"expected one of {codes}, succeeded instead" }

private def symlink (target linkPath : String) : IO Unit := do
  let out ← IO.Process.output { cmd := "ln", args := #["-s", target, linkPath] }
  unless out.exitCode == 0 do
    throw (IO.userError s!"ln -s failed: {out.stderr}")

/-! ### The durability barrier (ADR-0015 §2, ADR-0019)

The barrier's policy is driven through `tl_sys_sync_probe`, which runs the same
`tl_sync_barrier` the product and release paths run but takes each attempt's
result from a script instead of a syscall. That is the only way to cover the
branches that matter most — an interrupted barrier, `EIO`, `ENOSPC` — since no
filesystem produces them on request. The probe is bound *here* rather than in
`Tl/`, so the product has no path to it at all.

`hasFull` selects the platform shape rather than inheriting it, so the Darwin
policy (a full barrier to fall back from) and the everywhere-else one (ordinary
`fsync` already is the barrier) are both exercised on whichever host runs. -/

/-- A scripted run that must reach a barrier, and which one it must reach. -/
private def probeReaches (name : String) (hasFull : Bool) (script : List UInt8)
    (expected : Sys.SyncStrength) : IO Outcome := do
  match ← (SyncBarrierProbe.run hasFull script).toBaseIO with
  | .ok got =>
    return if got == expected then { name, passed := true }
      else { name, passed := false, msg := s!"reached {repr got}, expected {repr expected}" }
  | .error e => return { name, passed := false, msg := s!"expected {repr expected}, failed: {e}" }

/-- A scripted run that must refuse, under the errno it was given. -/
private def probeRefuses (name : String) (hasFull : Bool) (script : List UInt8)
    (code : String) : IO Outcome := do
  match ← (SyncBarrierProbe.run hasFull script).toBaseIO with
  | .error e =>
    if Sys.errnoOf e == some code then return { name, passed := true }
    else return { name, passed := false, msg := s!"expected {code}, got: {e}" }
  | .ok got =>
    return { name, passed := false, msg := s!"expected {code}, reached {repr got} instead" }

private def barrierTests : IO (List Outcome) := do
  -- The shape production compiled to must be the one this platform calls for.
  -- Without this row, a build that dropped Darwin's F_FULLFSYNC attempt would
  -- still pass every assertion below and the real-file row above, because an
  -- ordinary fsync reports a full barrier wherever it *is* the barrier.
  let shape ← SyncBarrierProbe.hasFullBarrier
  let expected : UInt8 := if System.Platform.isOSX then 1 else 0
  return [
    check "barrier: production compiled to this platform's barrier shape"
      (shape == expected)
      s!"attempts-a-full-barrier={shape}, expected {expected} on this platform",
    -- The refusal `sync` takes when the shim reports a strength this binding
    -- does not know. Unreachable from the shim, which returns only 0 or 1, so
    -- it is driven directly — through the shipped function.
    ← (do match ← (Sys.strengthOrThrow 2).toBaseIO with
          | .error e =>
            return check "barrier: an unknown strength refuses in the shim's error shape"
              (Sys.errnoOf e == some "ESTRENGTH") s!"got: {e}"
          | .ok got =>
            return { name := "barrier: an unknown strength refuses in the shim's error shape",
                     passed := false, msg := s!"accepted it as {repr got}" }),
    -- The full barrier, reached.
    ← probeReaches "barrier: a full barrier that succeeds is reported full"
        true [SyncBarrierProbe.ok] .fullBarrier,
    -- The regression this policy exists for: a signal must not downgrade it.
    -- The old code took any failure as "unsupported" and answered with a plain
    -- fsync, so an interrupted barrier silently became an ordinary one.
    ← probeReaches "barrier: an interrupted full barrier is retried, not downgraded"
        true [SyncBarrierProbe.eintr, SyncBarrierProbe.ok] .fullBarrier,
    ← probeReaches "barrier: it is retried as often as it is interrupted"
        true [SyncBarrierProbe.eintr, SyncBarrierProbe.eintr,
          SyncBarrierProbe.eintr, SyncBarrierProbe.ok] .fullBarrier,
    -- Each documented "this filesystem does not implement that" result, and
    -- only these, may answer with the weaker flush.
    ← probeReaches "barrier: ENOTSUP falls back to ordinary fsync"
        true [SyncBarrierProbe.enotsup, SyncBarrierProbe.ok] .ordinaryFsync,
    ← probeReaches "barrier: EINVAL falls back to ordinary fsync"
        true [SyncBarrierProbe.einval, SyncBarrierProbe.ok] .ordinaryFsync,
    ← probeReaches "barrier: ENOTTY falls back to ordinary fsync"
        true [SyncBarrierProbe.enotty, SyncBarrierProbe.ok] .ordinaryFsync,
    -- Darwin separates these (ENOTSUP 45, EOPNOTSUPP 102), so this is a
    -- distinct condition there; Linux aliases them to 95, where the row repeats
    -- the one above. The shim spells both for the platform that separates them.
    ← probeReaches "barrier: EOPNOTSUPP falls back to ordinary fsync"
        true [SyncBarrierProbe.eopnotsupp, SyncBarrierProbe.ok] .ordinaryFsync,
    -- The other regression: an operational failure means no barrier was
    -- reached, and must not be answered with a flush that reports one. The
    -- scripts below would all have *succeeded* before, because the fall-back
    -- fsync is scripted to succeed right after.
    ← probeRefuses "barrier: EIO on the full barrier propagates, never falls back"
        true [SyncBarrierProbe.eio, SyncBarrierProbe.ok] "EIO",
    ← probeRefuses "barrier: ENOSPC on the full barrier propagates"
        true [SyncBarrierProbe.enospc, SyncBarrierProbe.ok] "ENOSPC",
    ← probeRefuses "barrier: EACCES on the full barrier propagates"
        true [SyncBarrierProbe.eacces, SyncBarrierProbe.ok] "EACCES",
    ← probeRefuses "barrier: EBADF on the full barrier propagates"
        true [SyncBarrierProbe.ebadf, SyncBarrierProbe.ok] "EBADF",
    -- The ordinary leg, after a legitimate fall-back.
    ← probeReaches "barrier: an interrupted fall-back fsync is retried"
        true [SyncBarrierProbe.enotsup, SyncBarrierProbe.eintr,
          SyncBarrierProbe.ok] .ordinaryFsync,
    ← probeRefuses "barrier: a failing fall-back fsync refuses"
        true [SyncBarrierProbe.enotsup, SyncBarrierProbe.eio] "EIO",
    ← probeRefuses "barrier: a full disk under the fall-back refuses"
        true [SyncBarrierProbe.enotsup, SyncBarrierProbe.enospc] "ENOSPC",
    -- The platform whose ordinary fsync already is the barrier: no attempt is
    -- made to fall back from, and success is a *full* barrier, not a weaker one.
    ← probeReaches "barrier: where fsync is the barrier, success is full"
        false [SyncBarrierProbe.ok] .fullBarrier,
    ← probeReaches "barrier: where fsync is the barrier, EINTR is retried"
        false [SyncBarrierProbe.eintr, SyncBarrierProbe.ok] .fullBarrier,
    ← probeRefuses "barrier: where fsync is the barrier, EIO refuses"
        false [SyncBarrierProbe.eio] "EIO",
    ← probeRefuses "barrier: where fsync is the barrier, ENOSPC refuses"
        false [SyncBarrierProbe.enospc] "ENOSPC",
    -- An unsupported result there has nothing to fall back to, so it is a
    -- refusal rather than a second attempt.
    ← probeRefuses "barrier: where fsync is the barrier, ENOTSUP refuses"
        false [SyncBarrierProbe.enotsup] "ENOTSUP",
    -- The errno-name additions used by storage rendering are driven through C,
    -- not only manufactured as strings at the Lean mapping layer.
    ← probeRefuses "barrier: EINVAL on the ordinary leg is named"
        false [SyncBarrierProbe.einval] "EINVAL",
    ← probeRefuses "barrier: ENOTTY on the ordinary leg is named"
        false [SyncBarrierProbe.enotty] "ENOTTY",
    ← probeRefuses "barrier: EROFS is named"
        false [SyncBarrierProbe.erofs] "EROFS",
    ← probeRefuses "barrier: EDQUOT is named"
        false [SyncBarrierProbe.edquot] "EDQUOT",
    ← probeRefuses "barrier: ENXIO is named"
        false [SyncBarrierProbe.enxio] "ENXIO",
    ← probeRefuses "barrier: ENODEV is named"
        false [SyncBarrierProbe.enodev] "ENODEV",
    ← probeRefuses "barrier: EOPNOTSUPP is named under this platform's aliasing"
        false [SyncBarrierProbe.eopnotsupp]
          (if System.Platform.isOSX then "EOPNOTSUPP" else "ENOTSUP"),
    -- The probe's own guard: a script that runs out ends the run under a name
    -- of its own, so a mis-written row above fails visibly instead of looping.
    ← probeRefuses "barrier: a script that runs out ends the run"
        true [SyncBarrierProbe.eintr] "ESCRIPT",
    ← probeRefuses "barrier: an unknown script code is rejected visibly"
        true [255] "ESCRIPT",
    -- The strength wire, decoded. An unrecognized code is not a weaker barrier
    -- to accept: it means this binding and the shim disagree.
    checkOk "barrier: the full-barrier code decodes"
      (Sys.strengthOfCode 0) .fullBarrier,
    checkOk "barrier: the ordinary-fsync code decodes"
      (Sys.strengthOfCode 1) .ordinaryFsync,
    checkError "barrier: an unknown strength code is refused"
      (Sys.strengthOfCode 2),
    check "barrier: the two strengths are distinct"
      (Sys.SyncStrength.fullBarrier != Sys.SyncStrength.ordinaryFsync)]

def sysTests : IO (List Outcome) := do
  let dir ← IO.FS.createTempDir
  let base := dir.toString
  let mut outcomes : List Outcome := []

  -- create-excl, write, sync, read round-trip (base itself sits under the
  -- macOS /var symlink, so this also proves the base leg follows symlinks)
  let payload := "hello\nshim\n".toUTF8
  let fd ← Sys.openNoFollow base "seg.jsonl" (flagCreateExcl ||| flagAppend)
  Sys.writeAll fd payload
  let strength ← Sys.sync fd
  Sys.close fd
  let back ← Sys.withFd base "seg.jsonl" 0 Sys.readAll
  outcomes := outcomes ++
    [check "create-excl + append + sync + readAll round-trip" (back == payload)
      s!"got {back.size} bytes",
     -- The real syscall path, on a real file on whatever filesystem backs the
     -- host's temp directory. Linux's selected fsync barrier reports full;
     -- Darwin may legitimately report ordinary when that filesystem refuses
     -- F_FULLFSYNC. The separate shape row below, not this result, detects a
     -- Darwin build that accidentally omitted the full attempt entirely.
     check "sync on a real file reports the selected platform's result"
       (strength == .fullBarrier ||
         (System.Platform.isOSX && strength == .ordinaryFsync))
       s!"reached {repr strength}"]

  -- The real production symbol's failure path, end to end: an fd that was
  -- never opened is EBADF, which is not a "this filesystem cannot" answer and
  -- so propagates rather than falling back to a plain fsync.
  outcomes := outcomes ++
    [← expectErrno "sync on an unopened fd refuses with EBADF" ["EBADF"]
        (Sys.sync 999999)]

  -- a second append lands after the first (O_APPEND positioning)
  let fd2 ← Sys.openNoFollow base "seg.jsonl" flagAppend
  Sys.writeAll fd2 "tail\n".toUTF8
  Sys.close fd2
  let back2 ← Sys.withFd base "seg.jsonl" 0 Sys.readAll
  outcomes := outcomes ++
    [check "O_APPEND writes land at the tail"
      (String.fromUTF8! back2 == "hello\nshim\ntail\n") (String.fromUTF8! back2)]

  -- O_EXCL collision
  outcomes := outcomes ++
    [← expectErrno "create-excl collision is EEXIST" ["EEXIST"]
        (Sys.openNoFollow base "seg.jsonl" flagCreateExcl)]

  -- read-to-EOF on an empty file
  let fdE ← Sys.openNoFollow base "empty" flagCreateExcl
  Sys.close fdE
  let empty ← Sys.withFd base "empty" 0 Sys.readAll
  outcomes := outcomes ++ [check "readAll on empty file is empty" (empty.size == 0)]

  -- symlink at the final rel component is refused (read, append, and O_CREAT)
  symlink (base ++ "/seg.jsonl") (base ++ "/link.jsonl")
  outcomes := outcomes ++
    [← expectErrno "symlink at final component refused (read)" ["ELOOP"]
        (Sys.openNoFollow base "link.jsonl" 0),
     ← expectErrno "symlink at final component refused (append)" ["ELOOP"]
        (Sys.openNoFollow base "link.jsonl" flagAppend),
     ← expectErrno "symlink at final component refused even with O_CREAT" ["ELOOP"]
        (Sys.openNoFollow base "link.jsonl" (flagCreate ||| flagWrite))]

  -- symlink at an intermediate rel component is refused (the component walk;
  -- ELOOP on Linux, ENOTDIR on Darwin — both are the refusal)
  IO.FS.createDir (dir / "realdir")
  IO.FS.writeFile (dir / "realdir" / "inner.txt") "x"
  symlink (base ++ "/realdir") (base ++ "/dirlink")
  outcomes := outcomes ++
    [← expectErrno "symlink at intermediate component refused" ["ELOOP", "ENOTDIR"]
        (Sys.openNoFollow base "dirlink/inner.txt" 0),
     check "real path through real directories opens"
       ((← Sys.withFd base "realdir/inner.txt" 0 Sys.readAll).size == 1)]

  -- directory open ("." = the base itself) + ownership checks
  let dirFd ← Sys.openNoFollow base "." flagDirectory
  let ownedDir ← Sys.ownedByCaller dirFd
  Sys.close dirFd
  let segFd ← Sys.openNoFollow base "seg.jsonl" 0
  let ownedFile ← Sys.ownedByCaller segFd
  Sys.close segFd
  outcomes := outcomes ++
    [check "fresh temp dir is owned by the caller" ownedDir,
     check "fresh file is owned by the caller" ownedFile,
     ← expectErrno "directory-open of a file is ENOTDIR" ["ENOTDIR"]
        (Sys.openNoFollow base "seg.jsonl" flagDirectory)]

  -- lock contention between two open file descriptions (flock semantics)
  let lockA ← Sys.openNoFollow base "lockfile" (flagCreate ||| flagWrite)
  let lockB ← Sys.openNoFollow base "lockfile" (flagCreate ||| flagWrite)
  let gotA ← Sys.tryLock lockA true
  let gotB ← Sys.tryLock lockB true
  Sys.unlock lockA
  let gotB2 ← Sys.tryLock lockB true
  Sys.unlock lockB
  Sys.close lockA
  Sys.close lockB
  outcomes := outcomes ++
    [check "first exclusive lock wins" gotA,
     check "contended exclusive lock reports busy (no block)" (!gotB),
     check "released lock is acquirable" gotB2]

  -- entropy: exact size, and two draws differ (256 random bits never collide)
  let e1 ← Sys.entropy 32
  let e2 ← Sys.entropy 32
  let big ← Sys.entropy 600   -- exercises the >256-byte chunk loop
  outcomes := outcomes ++
    [check "entropy returns the requested size" (e1.size == 32 && big.size == 600),
     check "two entropy draws differ" (e1 != e2)]

  -- missing path is ENOENT (the walk's not-found branch)
  outcomes := outcomes ++
    [← expectErrno "missing path is ENOENT" ["ENOENT"]
        (Sys.openNoFollow base "no-such/file" 0)]

  outcomes := outcomes ++ (← barrierTests)

  return outcomes

end Tl.Tests
