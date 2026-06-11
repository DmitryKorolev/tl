/-
`Tl.Store.Sys` — bindings to the native shim (`ffi/tlsys.c`, ADR-0019).

Mechanism only: no-follow opens (a symlink at ANY path component is refused
by the shim's component walk — ADR-0015 §6), read/write/fsync on the shim's
own fds, the advisory fd lock, OS CSPRNG entropy, and the ownership check.
Policy — the `.tl` path discipline, error codes (`unsafe-path`, `lock-busy`),
bounded lock waits — lives in the callers (`Tl/Store/*`), where every branch
is testable. Swapping a shim function for a future core API never touches
the Store: call sites reach the mechanism only through this module.

Shim failures surface as `IO.Error` userErrors of the fixed shape
`tlsys:<op>:<ERRNO-NAME>: <detail>`; `errnoOf` recovers the token so callers
can map conditions (`ELOOP` → symlink refusal, `EEXIST` → exclusive-create
collision, `EWOULDBLOCK` → contended lock) to their structured codes.
-/
import Tl.Error

namespace Tl.Store.Sys

/-! ### Open-flag bits (keep in sync with `ffi/tlsys.c`) -/

/-- Open write-only (without it, read-only). -/
def flagWrite : UInt32 := 1
/-- `O_APPEND`: every write goes atomically to the tail (ADR-0015 §2). -/
def flagAppend : UInt32 := 2
/-- `O_CREAT|O_EXCL`: create, failing `EEXIST` if present. -/
def flagCreateExcl : UInt32 := 4
/-- `O_TRUNC`. -/
def flagTruncate : UInt32 := 8
/-- Open a directory (read-only). -/
def flagDirectory : UInt32 := 16
/-- `O_CREAT` without `O_EXCL` (create if missing, reuse if present). -/
def flagCreate : UInt32 := 32

/-- Open `rel` under the directory `base` (`""` = the current directory),
    refusing to follow a symlink at any `rel` component (ADR-0015 §6). The
    base is opened with normal symlink semantics: the no-follow discipline is
    scoped to the `.tl` components — a repo root reached through a symlinked
    ancestor (a symlinked home, a macOS `/var` temp path) is legitimate. -/
@[extern "tl_sys_open"]
opaque openNoFollow (base : @&String) (rel : @&String) (flags : UInt32) : IO UInt32

/-- Read from the fd's current offset to EOF. -/
@[extern "tl_sys_read_all"]
opaque readAll (fd : UInt32) : IO ByteArray

/-- Write the whole buffer (restarting on `EINTR`/short writes). -/
@[extern "tl_sys_write_all"]
opaque writeAll (fd : UInt32) (data : @&ByteArray) : IO Unit

/-- `fsync` — `F_FULLFSYNC` on Darwin (ADR-0019: the real durability barrier). -/
@[extern "tl_sys_sync"]
opaque sync (fd : UInt32) : IO Unit

/-- Non-blocking advisory lock attempt; `false` = held elsewhere. Bounded
    waiting is caller policy (`Tl/Store/Lock.lean`), not mechanism. -/
@[extern "tl_sys_try_lock"]
opaque tryLock (fd : UInt32) (exclusive : Bool) : IO Bool

@[extern "tl_sys_unlock"]
opaque unlock (fd : UInt32) : IO Unit

/-- `n` bytes from the OS CSPRNG (`getentropy`) — the ADR-0007 entropy
    contract core's `IO.getRandomBytes` explicitly does not promise. -/
@[extern "tl_sys_entropy"]
opaque entropy (n : UInt32) : IO ByteArray

/-- Whether the open file is owned by the calling (effective) user —
    the ADR-0015 §6 ownership check. -/
@[extern "tl_sys_owned_by_caller"]
opaque ownedByCaller (fd : UInt32) : IO Bool

@[extern "tl_sys_close"]
opaque close (fd : UInt32) : IO Unit

/-- The `ERRNO-NAME` token of a shim failure, if the error is one
    (`tlsys:<op>:<ERRNO-NAME>: <detail>`). -/
def errnoOf (e : IO.Error) : Option String :=
  let s := e.toString
  if s.startsWith "tlsys:" then
    match s.splitOn ":" with
    | _ :: _ :: code :: _ => some code
    | _ => none
  else none

/-- Open, run, close — exception-safe fd bracket. -/
def withFd (base rel : String) (flags : UInt32) (f : UInt32 → IO α) : IO α := do
  let fd ← openNoFollow base rel flags
  try f fd finally close fd

end Tl.Store.Sys
