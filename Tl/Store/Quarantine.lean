/- Shared quarantine decisions identify the exact bytes of a complete line
   within one replica segment. The transport retains the line and the marker. -/
import Tl.Format.Codec
import Tl.Store.Lines
import Std.Data.HashSet.Lemmas

namespace Tl.Store

open Lean (Json)
open Tl.Format

/-- Quarantine records have no task operation or LWW stamp. Zeroes fill the
    ordering fields of the common wire envelope. -/
def quarantineRecord (replica : String) (raw : ByteArray) (actor : Option String) : Record :=
  { v := 3, op := "quarantine", replica, actor, hlc := "0000000000000000",
    nonce := "00000000000000000000000000",
    fields := [("bytes", Json.arr (raw.data.map fun b => Lean.toJson b.toNat))] }

/-- Accept exact, bounded byte values. LF cannot belong to a framed line. -/
def quarantineTarget? (replica : String) (raw : ByteArray) : Option (Array UInt8) := do
  let r ← (Record.parse (← String.fromUTF8? raw)).toOption
  guard (r.v == 3 && r.op == "quarantine" && r.replica == replica &&
    r.hlc == "0000000000000000" && r.nonce == "00000000000000000000000000")
  let target ← r.fields.lookup "bytes"
  let values ← target.getArr?.toOption
  values.mapM fun value => do
    let n ← value.getNat?.toOption
    guard (n ≤ 255 && n != 10)
    return n.toUInt8

def quarantineIndex (replica : String) (lines : List ByteArray) : Std.HashSet (Array UInt8) :=
  Std.HashSet.ofList (lines.filterMap (quarantineTarget? replica))

theorem quarantineIndex_contains (replica : String) (lines : List ByteArray) (target : Array UInt8) :
    (quarantineIndex replica lines).contains target = true ↔
      ∃ line ∈ lines, quarantineTarget? replica line = some target := by
  rw [quarantineIndex, Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_filterMap]

/-- A missing envelope can itself be damage. Preserve recognizable future
    versions even when another field is broken. Operation kinds are closed within a version. -/
def repairableDamage (raw : ByteArray) (e : Tl.Error) : Bool := Id.run do
  if e.code != .malformedLine then return false
  let some text := String.fromUTF8? raw | return true
  let .ok j := Json.parse text | return true
  if let .ok v := (j.getObjVal? "v").bind (·.getNat?) then
    if v > supportedVersion then return false
  return true

/-- Applied only after normal decoding fails and the line is not a valid marker. -/
def excludesDamage (targets : Std.HashSet (Array UInt8)) (raw : ByteArray) (error : Tl.Error) : Bool :=
  repairableDamage raw error && targets.contains raw.data

end Tl.Store
