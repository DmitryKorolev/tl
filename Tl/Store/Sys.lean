/-
`Tl.Store.Sys` — bindings to the native shim (`ffi/tlsys.c`, ADR-0019).

Mechanism only: no-follow opens (a symlink at any path component is refused
by the shim's component walk — ADR-0015 §6), read/write/fsync on the shim's
own fds, the advisory fd lock, OS CSPRNG entropy, and the ownership check.
Policy — the `.tl` path discipline, error codes (`unsafe-path`, `lock-busy`),
bounded lock waits — lives in the callers (`Tl/Store/*`), where every branch
is testable. The one policy that lives *here* is the durable-write one
(`syncBestEffort`), because it is the same decision at all three write sites
and stating it three times is how they would come to differ. Swapping a shim
function for a future core API never touches the Store: call sites reach the
mechanism only through this module.

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

/-! ### The durability barrier and the policy over it -/

/-- Which durability barrier a completed `sync` actually reached.

    The constructor names match release administration's own `SyncStrength`
    (`release/Write.lean`) on purpose: the two surfaces share one shim
    mechanism, so they should share its vocabulary. The *types* stay separate
    because `ReleaseCore` imports nothing from `Tl` (ADR-0028), and the
    *policies* over them differ — see `syncBestEffort`. -/
inductive SyncStrength where
  /-- The platform's real durability barrier: `F_FULLFSYNC` on Darwin, plain
      `fsync` everywhere else (where it already is the barrier). -/
  | fullBarrier
  /-- Ordinary `fsync` only, because the filesystem answered that it does not
      implement the full barrier. On Darwin the bytes may still be sitting in
      the drive's cache when this returns. -/
  | ordinaryFsync
  deriving DecidableEq, Repr, Inhabited

/-- The wire code the shim reports (`TL_SYNC_FULL` / `TL_SYNC_ORDINARY`). -/
def SyncStrength.code : SyncStrength → UInt8
  | .fullBarrier => 0
  | .ordinaryFsync => 1

/-- Read the shim's strength byte. An unknown code is not a weaker barrier to
    accept: it means the binding and the shim disagree about the wire, so this
    build cannot be trusted to say what it did. -/
def strengthOfCode (code : UInt8) : Except String SyncStrength :=
  if code == 0 then .ok .fullBarrier
  else if code == 1 then .ok .ordinaryFsync
  else .error s!"sync strength {code} is not one this build knows"

theorem strengthOfCode_code (strength : SyncStrength) :
    strengthOfCode strength.code = .ok strength := by
  cases strength <;> rfl

/-- `fsync`, through the platform's durability barrier — `F_FULLFSYNC` on
    Darwin (ADR-0019). Reports which barrier it reached; an interrupted attempt
    is retried and an operational failure (`EIO`, `ENOSPC`, …) is raised rather
    than answered with a weaker flush. -/
@[extern "tl_sys_sync"]
opaque syncRaw (fd : UInt32) : IO UInt8

/-- Decode a strength byte or fail in the shim's own error shape. Kept separate
    from `sync` so the tests' scripted probe refuses through *this* function
    rather than a copy of it — a second copy is how the covered refusal and the
    shipped one come to differ. -/
def strengthOrThrow (code : UInt8) : IO SyncStrength :=
  match strengthOfCode code with
  | .ok strength => return strength
  | .error message => throw (IO.userError s!"tlsys:sync:ESTRENGTH: {message}")

/-- `syncRaw` with the strength decoded. -/
def sync (fd : UInt32) : IO SyncStrength := do strengthOrThrow (← syncRaw fd)

/-- A durability mechanism with the same answer as the native barrier. Store
    functions accept one explicitly at their test seams; production always uses
    `sync`. Keeping the strength in the type ensures tests exercise the product
    policy over both answers instead of bypassing it with an `IO Unit` stub. -/
abbrev SyncMechanism := UInt32 → IO SyncStrength

/-- The product's durable-write policy over the barrier that was reached.

    ADR-0015 §2 makes local durability best-effort — the durable publish is
    `git push` (ADR-0001) — so an ordinary `fsync` on a filesystem that does not
    implement the full barrier is a weaker guarantee the contract already
    permits, and refusing the write would refuse it on a placement the ADR
    supports. What is not permitted is the two being confused: an operational
    failure propagates out of `sync` instead of being answered with a weaker
    flush, and a signal no longer downgrades a full barrier. So a write that
    gets past here reached one of the two barriers, and which one is a property
    of where `.tl` lives (ADR-0015 §8), not of this write.

    Release administration applies a different policy over the same mechanism
    (`release/Write.lean`): it carries the achieved strength into the evidence
    row, because an artifact's durability is a fact a release has to report. -/
def syncBestEffortWith (mechanism : SyncMechanism) (fd : UInt32) : IO Unit := do
  let _ ← mechanism fd

/-- Apply the product policy to the native durability mechanism. -/
def syncBestEffort (fd : UInt32) : IO Unit :=
  syncBestEffortWith sync fd

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

/-- Create `rel` under `base` like a no-follow `createDirAll`: each component
    is created then descended through a no-follow/ownership-checked open, so a
    symlink planted as any `.tl` component is refused, never followed and
    created through (ADR-0015 §6). Idempotent. The toolchain exposes no
    no-follow `mkdir`, hence this shim entry. -/
@[extern "tl_sys_mkdir"]
opaque mkdirNoFollow (base : @&String) (rel : @&String) : IO Unit

/-- A whole byte buffer as a big-endian `Nat` (entropy → numeric ids); a
    plain list fold, so no index can panic. Callers check the buffer length
    (the width *is* the contract — 8 entropy bytes are a 64-bit id). -/
def natOfBytesBE (bytes : ByteArray) : Nat :=
  bytes.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

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
