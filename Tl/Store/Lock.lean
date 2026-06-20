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
import Tl.Store.Cache

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
      -- don't sleep into the terminal poll: the next call would be `loop 0` (which
      -- only throws), so sleeping first overshoots the timeout by one poll interval
      if n == 0 then loop 0
      else do
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
    stamps := ⟨clock.pack, replicaVal, Sys.natOfBytesBE bytes⟩ :: stamps
  -- built in reverse (cons, not the O(n²) right-append); restore mint order so
  -- stamp i pairs with wireOp i and the HLCs stay ascending (`transact`)
  return (stamps.reverse, clock)

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
    let (segs, segNotes) ← readSegments d
    let now ← liftSys (fun e => .mk' .internal s!"clock read failed: {e}") nowMs
    -- skew-check foreign segments against `now` (ADR-0007): a future-dated
    -- foreign op neither folds into the guard state nor inflates the reseed.
    -- The guard state folds through the cache (ADR-0022) — under the lock, so
    -- the write path stops paying the whole-log refold; the appended ops are
    -- NOT folded into the persisted cache here (it is keyed to the pre-append
    -- bytes and stays exactly valid — the next invocation folds the suffix).
    let cache ← loadCache d
    let (loaded0, refreshed) := materializeCached segs cache false (some now) (some replica.id)
    if let some c := refreshed then
      saveCache d c
    let loaded := { loaded0 with warnings := segNotes ++ loaded0.warnings }
    -- a refused OWN segment fails the write: guards would run against a
    -- wrong fold, and the segment needs repair anyway (ADR-0008 §corruption)
    if let some r := loaded.refused.find? (·.replicaId == replica.id) then
      throw r.error
    -- the max HLC the OWN segment already carries — the floor the present clock must
    -- clear so this replica's new writes beat its PAST ones even if the persisted
    -- clock is stale (a crash in the §1 window, or a stray `init` zeroing it). It is
    -- DELIBERATELY not floored past within-window FOREIGN HLCs: a folded foreign op
    -- with a higher HLC may win LWW — pure last-writer-wins, eventual consistency;
    -- there is no causal-safety-across-transport (that is why no `observeRemote` rule
    -- exists). The absent arm below floors by the all-segment max only because it has
    -- no persisted clock to trust. `materializeCached` already decoded the own
    -- segment, so its max is threaded out as `loaded.ownMaxHlc` — no re-decode.
    let ownMax : Nat := loaded.ownMaxHlc
    let clock0 ← match ← loadClock d with
      -- present clock: floor by the own-segment max (crash/`init`-zero recovery);
      -- localEvent then advances past `now`.
      | some h => pure (unpackHlc (max h.pack ownMax))
      | none =>
        -- the pinned absent-clock reseed (ADR-0007): max over all segments'
        -- WITHIN-WINDOW writes (covers the byte-copied orphan under the old
        -- replica id) and now, inside the lock. `loaded.maxHlc` already excludes
        -- skew-deferred foreign HLCs, so a *future-dated* orphan (a wrong-clock
        -- copy, > now+W) does NOT drag the reseed forward: it stays ~now rather
        -- than honoring a future timestamp. The freshly-minted replica id starts
        -- its own monotonic sequence regardless, so this only loses LWW to the
        -- orphan until wall-clock catches up (eventual), never propagating the
        -- inflation onward (ADR-0007 amendment).
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
