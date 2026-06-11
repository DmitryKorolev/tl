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

namespace Tl.Store

/-- One replica's segment, as read. -/
structure SegmentData where
  replicaId : String
  bytes : ByteArray

/-- The replica ids with a segment on disk, sorted (deterministic fold and
    display order; the fold itself is order-insensitive — ADR-0004). -/
def enumerateSegments (d : Dirs) : TlM (List String) := do
  let dirPath := d.logPath
  unless ← liftSys (fun e => .mk' .internal s!"{e}") dirPath.pathExists do
    return []
  let entries ← liftSys (fun e => .mk' .internal s!"cannot list {d.relLog}: {e}")
    dirPath.readDir
  let ids := entries.toList.filterMap (fun ent =>
    if ent.fileName.endsWith ".jsonl" then some (ent.fileName.dropEnd 6).toString else none)
  return ids.mergeSort (fun a b => decide (a ≤ b))

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

/-- All segments, in enumeration order. -/
def readSegments (d : Dirs) : TlM (List SegmentData) := do
  (← enumerateSegments d).mapM fun rid => do
    return { replicaId := rid, bytes := ← readSegment d rid }

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
def appendOwn (d : Dirs) (replicaId : String) (lines : List String)
    (closeFragment : Bool) : TlM Unit := do
  liftSys (fun e => .mk' .internal s!"cannot create {d.relLog}: {e}")
    (IO.FS.createDirAll d.logPath)
  let rel := d.relSegment replicaId
  liftSys (mapSysError rel) do
    let fd ← Sys.openNoFollow d.base rel (Sys.flagCreate ||| Sys.flagAppend)
    try
      if closeFragment then
        Sys.writeAll fd "\n".toUTF8
      for line in lines do
        Sys.writeAll fd (line ++ "\n").toUTF8
      Sys.sync fd
    finally
      Sys.close fd

end Tl.Store
