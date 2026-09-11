/-
`Tl.Store.Segment` — per-replica segment I/O (ADR-0001 §3, ADR-0008
§corruption, ADR-0015 §2/§5).

Reading is lock-free: a segment's bytes split into complete LF-terminated
lines; a trailing newline-less fragment is an uncommitted (or crashed)
write, skipped silently this read (§5 — not corruption). Lines stay raw
bytes here; per-line UTF-8/JSON decode happens at the codec stage so one bad
line refuses one segment, never the whole read.

Writing is the own-segment append discipline: ensure the log dir exists,
close any crash fragment with a single LF first (ADR-0008 crash hygiene — a
writer never appends onto a newline-less tail), then one `O_APPEND` write
per record line, then fsync. All opens ride the no-follow walk (§6).
-/
import Tl.Store.Paths
import Tl.Clock.Replica

namespace Tl.Store

/-- One replica's segment, as read. -/
structure SegmentData where
  replicaId : String
  bytes : ByteArray

/-- The replica ids with a segment on disk, sorted (deterministic fold and
    display order; the fold itself is order-insensitive — ADR-0004), plus a
    disclosure per ignored `.jsonl` whose stem is not a canonical replica id
    (segments are per-replica files, ADR-0001 — anything else in `log/` is
    junk, never silently folded *or* silently dropped). The directory is
    no-follow/ownership-validated through the shim before listing, so a
    symlinked or foreign-owned `log/` is refused at the listing itself, not
    only at the later per-file opens. Non-`.jsonl` names (editor droppings,
    `.DS_Store`) are OS noise, ignored silently. -/
def enumerateSegments (d : Dirs) : TlM (List String × List String) := do
  match ← (Sys.openNoFollow d.base d.relLog Sys.flagDirectory).toBaseIO with
  | .error e =>
    match Sys.errnoOf e with
    | some "ENOENT" => return ([], [])
    | _ => throw (mapSysError d.relLog e)
  | .ok fd => liftSys (mapSysError d.relLog) (Sys.close fd)
  let entries ← liftSys (fun e => .mk' .internal s!"cannot list {d.relLog}: {e}")
    d.logPath.readDir
  let stems := entries.toList.filterMap (fun ent =>
    if ent.fileName.endsWith ".jsonl" then some (ent.fileName.dropEnd 6).toString else none)
  let (ids, junk) := stems.partition (fun stem => (Tl.Clock.Replica.mk stem).valid)
  return (ids.mergeSort (fun a b => decide (a ≤ b)),
          junk.map (fun stem =>
            s!"ignored {d.relLog}/{stem}.jsonl: not a replica segment (the name is not a canonical replica id)"))

/-- Read one segment's bytes (a segment that vanished between enumerate and
    read counts as empty — only a concurrent cleanup can cause it). -/
def readSegment (d : Dirs) (replicaId : String) : TlM ByteArray := do
  let rel := d.relSegment replicaId
  match ← (Sys.withFd d.base rel 0 Sys.readAll).toBaseIO with
  | .ok bytes => return bytes
  | .error e =>
    match Sys.errnoOf e with
    | some "ENOENT" => return ByteArray.empty
    | _ => throw (mapSysError rel e)

/-- All segments, in enumeration order, plus enumeration disclosures. -/
def readSegments (d : Dirs) : TlM (List SegmentData × List String) := do
  let (ids, notes) ← enumerateSegments d
  let segs ← ids.mapM fun rid => do
    return ({ replicaId := rid, bytes := ← readSegment d rid } : SegmentData)
  return (segs, notes)

/-- The complete LF-terminated lines (without their LF); a trailing
    fragment without a newline is dropped (ADR-0015 §5). Iterates the bytes
    themselves with a position accumulator — no index, nothing to panic. -/
def completeLines (bytes : ByteArray) : List ByteArray := Id.run do
  let mut lines : List ByteArray := []
  let mut start := 0
  let mut i := 0
  for b in bytes do
    if b == 10 then
      lines := bytes.extract start i :: lines
      start := i + 1
    i := i + 1
  return lines.reverse

/-- Does the segment end in a newline-less crash fragment the next writer
    must close (ADR-0008 crash hygiene)? -/
def tornTail (bytes : ByteArray) : Bool :=
  match bytes[bytes.size - 1]? with
  | some b => b != 10
  | none => false

/-- Append rendered record lines to the replica's own segment under the
    mutation lock (the caller holds it): close a crash fragment if needed,
    one `O_APPEND` write per record (§2), fsync (§2; F_FULLFSYNC on Darwin). -/
def appendOwnRaw (d : Dirs) (replicaId : String) (lines : List ByteArray)
    (closeFragment : Bool) (syncMechanism : Sys.SyncMechanism := Sys.sync) : TlM Unit := do
  -- create .tl/log through the no-follow shim mkdir (a planted
  -- `.tl/log -> /elsewhere` symlink is refused, never followed and created
  -- through — ADR-0015 §6; init makes only .tl/local, so the first write is
  -- what creates log/)
  liftSys (mapSysError d.relLog) (Sys.mkdirNoFollow d.base d.relLog)
  let rel := d.relSegment replicaId
  liftSys (mapSysError rel) do
    let fd ← Sys.openNoFollow d.base rel (Sys.flagCreate ||| Sys.flagAppend)
    try
      if closeFragment then
        Sys.writeAll fd "\n".toUTF8
      for line in lines do
        Sys.writeAll fd (line ++ "\n".toUTF8)
      Sys.syncBestEffortWith syncMechanism fd
    finally
      Sys.close fd

/-- Rendered local operations use the same raw append path as recovered
    complete lines. Recovery must preserve even unknown/non-UTF-8 bytes. -/
def appendOwn (d : Dirs) (replicaId : String) (lines : List String)
    (closeFragment : Bool) (syncMechanism : Sys.SyncMechanism := Sys.sync) : TlM Unit :=
  appendOwnRaw d replicaId (lines.map String.toUTF8) closeFragment syncMechanism

end Tl.Store
