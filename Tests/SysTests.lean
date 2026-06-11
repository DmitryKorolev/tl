/-
`Tests.SysTests` — per-branch tests for the native shim (ADR-0019).

Each shim function's documented branches get a discrete assertion: symlink
refusal at the final AND an intermediate `rel` component (ADR-0015 §6 — the
component walk), the base-follows/rel-refuses split (a macOS temp dir lives
under the `/var` symlink, so the *base* leg is exercised by every row here),
`O_EXCL` collision, append+sync round-trip, lock contention between two open
file descriptions, entropy shape/freshness, the ownership check, and
read-to-EOF on empty input. POSIX is the gating path (ADR-0015 §7); symlinks
are created with `ln -s` (core Lean has no symlink API).

The intermediate-symlink errno is platform-split — Linux reports `ELOOP`,
Darwin `ENOTDIR` (the link, unfollowed, is not a directory) — both are the
refusal; the policy layer maps either to `unsafe-path`.
-/
import Tl.Store.Sys
import Tests.Harness

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

def sysTests : IO (List Outcome) := do
  let dir ← IO.FS.createTempDir
  let base := dir.toString
  let mut outcomes : List Outcome := []

  -- create-excl, write, sync, read round-trip (base itself sits under the
  -- macOS /var symlink, so this also proves the base leg follows symlinks)
  let payload := "hello\nshim\n".toUTF8
  let fd ← Sys.openNoFollow base "seg.jsonl" (flagCreateExcl ||| flagAppend)
  Sys.writeAll fd payload
  Sys.sync fd
  Sys.close fd
  let back ← Sys.withFd base "seg.jsonl" 0 Sys.readAll
  outcomes := outcomes ++
    [check "create-excl + append + sync + readAll round-trip" (back == payload)
      s!"got {back.size} bytes"]

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

  -- symlink at the FINAL rel component is refused (read, append, and O_CREAT)
  symlink (base ++ "/seg.jsonl") (base ++ "/link.jsonl")
  outcomes := outcomes ++
    [← expectErrno "symlink at final component refused (read)" ["ELOOP"]
        (Sys.openNoFollow base "link.jsonl" 0),
     ← expectErrno "symlink at final component refused (append)" ["ELOOP"]
        (Sys.openNoFollow base "link.jsonl" flagAppend),
     ← expectErrno "symlink at final component refused even with O_CREAT" ["ELOOP"]
        (Sys.openNoFollow base "link.jsonl" (flagCreate ||| flagWrite))]

  -- symlink at an INTERMEDIATE rel component is refused (the component walk;
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

  return outcomes

end Tl.Tests
