/-
`Tl.Store.Lock` — the mutation lock and the locked critical section
(ADR-0015 §1).

`transact` is the one write path: *acquire → load replica (auto-mint if
absent) → materialize → read+advance the HLC (the absent arm reseeds from
`max(max line-scoped HLC over every local segment, now())` — ADR-0007; the
whole branch runs inside the lock, never before acquisition) → build the
records (guards may refuse before anything is written) → append → fsync →
persist clock → release*. Acquisition is a bounded non-blocking poll: a
contended lock fails `lock-busy` after the timeout rather than blocking
forever; no stale-lock reclaim is needed (the OS releases an exiting
holder's flock).
-/
import Tl.Store.Local
import Tl.Store.Materialize

namespace Tl.Store

open Tl.Crdt (Stamp)
open Tl.Clock (Hlc)
open Tl.Format

/-- The bounded blocking wait (ADR-0015 §1: "a few seconds"). -/
def defaultLockTimeoutMs : Nat := 5000

private def lockPollMs : Nat := 50

/-- Acquire the mutation lock, polling up to `timeoutMs`. Returns the held
    fd; the caller must `releaseLock` it. -/
def acquireLock (d : Dirs) (timeoutMs : Nat := defaultLockTimeoutMs) : TlM UInt32 := do
  let rel := d.relLock
  let fd ← liftSys (mapSysError rel)
    (Sys.openNoFollow d.base rel (Sys.flagCreate ||| Sys.flagWrite))
  let attempts := timeoutMs / lockPollMs + 1
  let rec loop : Nat → TlM UInt32
    | 0 => do
      throw { code := .lockBusy
              message := "another tl process holds the mutation lock — retry shortly; a crashed holder's lock is released by the OS automatically"
              context := [("path", .str (d.tlPath ++ "/local/lock")),
                          ("timeoutMs", .num ⟨timeoutMs, 0⟩)] }
    | n + 1 => do
      if ← liftSys (mapSysError rel) (Sys.tryLock fd true) then
        return fd
      liftSys (fun e => .mk' .internal s!"{e}") (IO.sleep lockPollMs.toUInt32)
      loop n
  -- close the fd on EVERY non-success exit (timeout or an unexpected errno)
  try loop attempts
  catch e =>
    let _ ← (Sys.close fd).toBaseIO
    throw e

/-- Release and close the lock fd (best-effort: the OS would reclaim it). -/
def releaseLock (fd : UInt32) : TlM Unit := do
  let _ ← (Sys.unlock fd).toBaseIO
  let _ ← (Sys.close fd).toBaseIO
  return ()

/-- What a write sees under the lock: the materialized state (for guards),
    the located dirs, this working copy's replica, and the injected `now`. -/
structure TxContext where
  dirs : Dirs
  replica : Tl.Clock.Replica
  loaded : Loaded
  now : Nat

private def unpackHlc (packed : Nat) : Hlc := ⟨packed / 2 ^ 16, packed % 2 ^ 16⟩

/-- Mint `n` fresh stamps: each advances the clock (`localEvent`, saturation
    → `corrupt-clock reason:"saturated"`) and draws a 128-bit nonce from the
    OS CSPRNG. -/
def mintStamps (replicaVal : Nat) (clock0 : Hlc) (now : Nat) (n : Nat) :
    TlM (List Stamp × Hlc) := do
  let mut clock := clock0
  let mut stamps : List Stamp := []
  for _ in [0:n] do
    clock ← match Hlc.localEvent clock now with
      | .ok h => pure h
      | .error msg => throw (saturatedClock msg)
    let bytes ← liftSys (fun e => .mk' .internal s!"entropy unavailable: {e}")
      (Sys.entropy 16)
    unless bytes.size == 16 do
      throw (.mk' .internal
        "the entropy source returned a short read — this is a bug in tl; please report it")
    stamps := stamps ++ [⟨clock.pack, replicaVal, Sys.natOfBytesBE bytes⟩]
  return (stamps, clock)

/-- The locked critical section (ADR-0015 §1). `build` receives the state and
    `nStamps` fresh stamps and returns the records to append — at most one
    per stamp (fewer is fine: an idempotent re-close appends none); a guard
    refusal aborts before anything is written. Returns the context and the
    appended records. -/
def transact (d : Dirs) (actor : Option String) (nStamps : Nat)
    (build : TxContext → List Stamp → Except Tl.Error (List WireOp))
    (timeoutMs : Nat := defaultLockTimeoutMs) :
    TlM (TxContext × List ParsedOp) := do
  let fd ← acquireLock d timeoutMs
  try
    let replica ← loadOrMintReplica d
    let segs ← readSegments d
    let loaded := materialize segs
    -- a refused OWN segment fails the write: guards would run against a
    -- wrong fold, and the segment needs repair anyway (ADR-0008 §corruption)
    if let some r := loaded.refused.find? (·.replicaId == replica.id) then
      throw r.error
    let now ← liftSys (fun e => .mk' .internal s!"clock read failed: {e}") nowMs
    let clock0 ← match ← loadClock d with
      | some h => pure h
      | none =>
        -- the pinned absent-clock reseed (ADR-0007), inside the lock
        pure (unpackHlc (max loaded.maxHlc (now * 2 ^ 16)))
    let ctx : TxContext := { dirs := d, replica, loaded, now }
    let some replicaVal := replica.toNat?
      | throw (.mk' .internal
          "replica id failed to decode after validation — this is a bug in tl; please report it")
    let (stamps, clockN) ← mintStamps replicaVal clock0 now nStamps
    let wireOps ← match build ctx stamps with
      | .ok ws => pure ws
      | .error e => throw e
    if wireOps.length > stamps.length then
      throw (.mk' .internal
        s!"transact built {wireOps.length} records for {stamps.length} stamps")
    let parsed := List.zipWith (fun w st =>
        ({ v := supportedVersion, op := w, stamp := st, actor } : ParsedOp))
      wireOps stamps
    unless parsed.isEmpty do
      let ownBytes := ((segs.find? (·.replicaId == replica.id)).map (·.bytes)).getD ByteArray.empty
      appendOwn d replica.id (parsed.map renderLine) (tornTail ownBytes)
      persistClock d clockN
    return (ctx, parsed)
  finally
    releaseLock fd

end Tl.Store
