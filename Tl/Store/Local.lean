/-
`Tl.Store.Local` — the `.tl/local/` files: replica id and clock (ADR-0007,
ADR-0012; the file-persistence wiring the codebase map schedules "with the
Store").

Recovery rules are the pinned ones (ADR-0007 §HLC / ADR-0012): an absent
replica id with state present auto-mints on the write path (a byte-copied
working tree IS a new replica); an absent clock file reseeds — under the
mutation lock, in `Tl/Store/Lock.lean` — from `max(max HLC over every local
segment, now())`; a corrupt/unreadable file never silently reseeds or
re-mints, it fails closed (`corrupt-replica` / `corrupt-clock` with
`reason: "unreadable"`) with the remove-and-rerun fix in the message. HLC
saturation is `corrupt-clock` with `reason: "saturated"` and its own message
(removing the file cannot clear range exhaustion).

Replica minting draws 64 bits from the shim's OS CSPRNG (`Sys.entropy`) —
closing the recorded `IO.rand` defect (ADR-0019); `Replica.valid` is the
strengthened canonical check (exact width, canonical chars, 64-bit range).
-/
import Tl.Store.Paths
import Tl.Clock.Hlc
import Tl.Clock.Replica
import Tl.Format.Crockford
import Std.Time

namespace Tl.Store

open Tl.Clock
open Tl.Format

/-- Wall-clock ms since the Unix epoch (clamped at zero — a pre-epoch system
    clock yields the epoch rather than wrapping). -/
def nowMs : IO Nat := do
  let t ← Std.Time.Timestamp.now
  let ms := t.toMillisecondsSinceUnixEpoch.toInt
  return (max ms 0).toNat

private def fileContents (d : Dirs) (rel : String) : TlM (Option String) := do
  let r ← (Sys.withFd d.base rel 0 Sys.readAll).toBaseIO
  match r with
  | .ok bytes =>
    match String.fromUTF8? bytes with
    | some s => return some s
    | none => return some ""  -- not UTF-8: surface as corrupt via the caller's parse
  | .error e =>
    match Sys.errnoOf e with
    | some "ENOENT" => return none
    | _ => throw (mapSysError rel e)

/-- Atomically replace a small `.tl/local` file: write a `.tmp` sibling
    (no-follow), fsync it, then `rename` over the target (ADR-0015 §3 — the
    atomic-replace pattern, so a crash mid-write never leaves a torn
    clock/replica that would read as corrupt and wedge every later command).
    The temp open is no-follow; `rename` replaces a symlink at the target
    name rather than following it. -/
def writeLocalFile (d : Dirs) (rel : String) (content : String) : TlM Unit := do
  -- a per-call CSPRNG temp suffix so concurrent lock-free writers never collide
  -- on one `.tmp` inode (the read-time `ref-mark` refresh writes here without
  -- the mutation lock — ADR-0016 §3); harmless for the under-lock callers
  -- (clock/replica), matching `Tl.Sync.writeForeignSegment`'s discipline
  let entropy ← liftSys (fun e => .mk' .internal s!"entropy unavailable: {e}") (Sys.entropy 8)
  let tmpRel := rel ++ "." ++ toCrockford (Sys.natOfBytesBE entropy) 13 ++ ".tmp"
  liftSys (mapSysError tmpRel) do
    let fd ← Sys.openNoFollow d.base tmpRel
      (Sys.flagCreate ||| Sys.flagWrite ||| Sys.flagTruncate)
    try
      Sys.writeAll fd content.toUTF8
      Sys.sync fd
    finally
      Sys.close fd
  match ← (IO.FS.rename (d.absOf tmpRel) (d.absOf rel)).toBaseIO with
  | .ok _ => return ()
  | .error e =>
    -- a failed replace must not strand the uniquely-named temp (CSPRNG suffixes
    -- mean a persistent failure would otherwise pile up a new file per attempt)
    let _ ← (IO.FS.removeFile (d.absOf tmpRel)).toBaseIO
    throw (mapSysError rel e)

/-- Load `.tl/local/replica`. Absent → `none` (the write path auto-mints,
    ADR-0012); present but not a canonical 13-char id → `corrupt-replica`. -/
def loadReplica (d : Dirs) : TlM (Option Replica) := do
  match ← fileContents d d.relReplica with
  | none => return none
  | some raw =>
    let id := raw.trimAscii.toString
    let r : Replica := ⟨id⟩
    unless r.valid do
      throw { code := .corruptReplica
              message := s!"{d.relReplica} does not hold a canonical 13-char replica id (got '{id}') — remove the file and rerun; tl mints a fresh replica id on the next write"
              context := [("path", .str d.relReplica)] }
    return some r

/-- Mint a fresh replica id from 64 OS-CSPRNG bits and persist it. -/
def mintReplica (d : Dirs) : TlM Replica := do
  let bytes ← liftSys (fun e => .mk' .internal s!"entropy unavailable: {e}") (Sys.entropy 8)
  unless bytes.size == 8 do
    throw (.mk' .internal
      "the entropy source returned a short read — this is a bug in tl; please report it")
  let r := Replica.ofNat (Sys.natOfBytesBE bytes)
  writeLocalFile d d.relReplica (r.id ++ "\n")
  return r

/-- The write path's replica: load, or auto-mint when absent with state
    present (ADR-0012 — a byte-copied `.tl/` is a new replica). -/
def loadOrMintReplica (d : Dirs) : TlM Replica := do
  match ← loadReplica d with
  | some r => return r
  | none => mintReplica d

/-- Load `.tl/local/clock`. Absent → `none` (the locked write path reseeds
    from the segments' max, ADR-0007); unreadable → `corrupt-clock` with the
    remove-and-rerun fix (deliberate manual step — a silent reseed would mask
    whatever damaged the file). -/
def loadClock (d : Dirs) : TlM (Option Hlc) := do
  match ← fileContents d d.relClock with
  | none => return none
  | some raw =>
    match Hlc.ofHex? raw.trimAscii.toString with
    | some h => return some h
    | none =>
      throw { code := .corruptClock
              message := s!"{d.relClock} does not hold a 16-hex clock value — remove the file and rerun; tl reseeds safely from the log's own timestamps"
              context := [("path", .str d.relClock), ("reason", .str "unreadable")] }

/-- Persist the clock (the *persist clock* step of the ADR-0015 §1 critical
    section — always after the appended records are fsynced). -/
def persistClock (d : Dirs) (h : Hlc) : TlM Unit :=
  writeLocalFile d d.relClock (h.toHex ++ "\n")

/-- The ref-refresh marker (ADR-0016 §3): the `refs/tl/log` OID this working
    copy has already materialized siblings from. Absent (never refreshed) or
    unreadable → `none`, which makes the next read re-materialize — safe, since
    the materialized content is a pure function of the ref OID. -/
def loadRefMark (d : Dirs) : TlM (Option String) := do
  match ← fileContents d d.relRefMark with
  | some raw => let s := raw.trimAscii.toString; return (if s.isEmpty then none else some s)
  | none => return none

/-- Record the ref OID just materialized (atomic-replace like the other
    `.tl/local` files). The caller decides whether a failure is fatal: a read
    treats it as best-effort, an explicit `sync` lets it surface. -/
def storeRefMark (d : Dirs) (oid : String) : TlM Unit :=
  writeLocalFile d d.relRefMark (oid ++ "\n")

/-- The auto-sync publish marker `<tip> <ownLen> <ownHash>` (see `relSyncPub`):
    the ref OID our own segment is published into, with that segment's byte
    length and `ByteArray.hash` at publish time. Absent or unparsable → `none`
    (the next reconcile runs the full path and re-records it). -/
def loadSyncPub (d : Dirs) : TlM (Option (String × Nat × UInt64)) := do
  match ← fileContents d d.relSyncPub with
  | none => return none
  | some raw =>
    match raw.trimAscii.toString.splitOn " " with
    | [tip, lenS, hashS] =>
      match lenS.toNat?, hashS.toNat? with
      | some len, some h => return some (tip, len, h.toUInt64)
      | _, _ => return none
    | _ => return none

/-- Record the publish marker (atomic-replace, best-effort like the ref-mark).
    The caller writes it ONLY when the own segment `ownBytes` is in `oid`, so a
    later fast-out at this `(oid, len, hash)` provably skips an already-published
    own segment — never a real publish. -/
def storeSyncPub (d : Dirs) (oid : String) (ownBytes : ByteArray) : TlM Unit :=
  writeLocalFile d d.relSyncPub s!"{oid} {ownBytes.size} {ByteArray.hash ownBytes}\n"

/-- The last-sync marker `(ms, tip)` (see `relLastSync`): when this clone last
    ran `tl sync` and the `refs/tl/log` tip it left. Absent/unparsable → `none`
    ("never synced"). `tip` is `none` when the marker records `-`. -/
def loadLastSync (d : Dirs) : TlM (Option (Nat × Option String)) := do
  match ← fileContents d d.relLastSync with
  | none => return none
  | some raw =>
    match raw.trimAscii.toString.splitOn " " with
    | [msS, tip] =>
      match msS.toNat? with
      | some ms => return some (ms, if tip == "-" then none else some tip)
      | none => return none
    | _ => return none

/-- Record the last-sync marker (atomic-replace, best-effort like the other
    `.tl/local` markers). Written only after a sync completes. -/
def storeLastSync (d : Dirs) (ms : Nat) (tip : Option String) : TlM Unit :=
  writeLocalFile d d.relLastSync s!"{ms} {tip.getD "-"}\n"

/-- The `corrupt-clock` saturation error (ADR-0007: removing the clock file
    cannot clear range exhaustion — the reseed re-derives the same near-max
    value from the segments). -/
def saturatedClock (detail : String) : Tl.Error :=
  { code := .corruptClock
    message := s!"the clock's 48-bit physical range is exhausted ({detail}) — removing {".tl/local/clock"} will not help; check the system clock, or find and repair the segment carrying a near-max HLC (a broken or hostile writer put it there)"
    context := [("reason", .str "saturated")] }

end Tl.Store
