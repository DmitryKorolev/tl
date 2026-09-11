/- Same-replica recovery is an append under the mutation lock. The pure
   missing-line selection is characterized below; byte I/O, lock exclusion,
   crash tails, and clock-floor recovery are exercised through the shell. -/
import Tl.Store.Lock
import Std.Data.HashSet.Lemmas

namespace Tl.Sync

open Tl.Store

-- ByteArray's executable equality compares its data array. These local
-- instances connect that implementation to the standard hash-set lemmas;
-- they neither change its native comparator nor its hash function.
local instance : LawfulBEq ByteArray where
  rfl := by
    intro a
    change (a.data == a.data) = true
    exact beq_self_eq_true a.data
  eq_of_beq := by
    intro a b h
    change (a.data == b.data) = true at h
    exact ByteArray.ext (eq_of_beq h)

/-- Select received complete lines absent from the current local segment.
    Index the local lines once: expected O(local bytes + received bytes),
    rather than rescanning the local segment for each received line. -/
def recoveryDelta (present incoming : List ByteArray) : List ByteArray :=
  let known := Std.HashSet.ofList present
  incoming.filter (fun line => !known.contains line)

/-- The production selector admits exactly received lines absent locally. -/
theorem recoveryDelta_mem_iff (present incoming : List ByteArray) (line : ByteArray) :
    line ∈ recoveryDelta present incoming ↔ line ∈ incoming ∧ line ∉ present := by
  simp only [recoveryDelta, List.mem_filter, Bool.not_eq_true',
    Std.HashSet.contains_ofList, Bool.eq_false_iff]
  constructor
  · intro ⟨received, absent⟩
    exact ⟨received, fun found => absent (List.contains_iff_mem.mpr found)⟩
  · intro ⟨received, absent⟩
    exact ⟨received, fun found => absent (List.contains_iff_mem.mp found)⟩

/-- Appending the selected delta preserves the entire old line set and
    delivers the entire received line set, without inventing a third source. -/
theorem recoveryDelta_append_iff (present incoming : List ByteArray) (line : ByteArray) :
    line ∈ present ++ recoveryDelta present incoming ↔ line ∈ present ++ incoming := by
  rw [List.mem_append, List.mem_append, recoveryDelta_mem_iff]
  constructor
  · intro h
    cases h with
    | inl old => exact Or.inl old
    | inr fresh => exact Or.inr fresh.1
  · intro h
    cases h with
    | inl old => exact Or.inl old
    | inr received =>
      by_cases old : line ∈ present
      · exact Or.inl old
      · exact Or.inr ⟨received, old⟩

/-- Once the selected lines have been appended, replaying the same received
    snapshot requires no further append, even if it contains duplicates. -/
theorem recoveryDelta_after_append (present incoming : List ByteArray) :
    recoveryDelta (present ++ recoveryDelta present incoming) incoming = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro line found
  have selected := (recoveryDelta_mem_iff _ _ line).mp found
  have received : line ∈ present ++ incoming := List.mem_append.mpr (Or.inr selected.1)
  exact selected.2 ((recoveryDelta_append_iff present incoming line).mpr received)

/-- Recover peer appends under a duplicated replica ID. The unlocked check
    avoids taking a lock in the ordinary unique-replica case. After acquisition
    both identity and bytes are reread; a writer that appended in between is
    preserved and excluded from the delta. Never rename over the own segment.
    `transact` already floors every subsequent stamp above the own segment's
    maximum HLC, including records recovered here, so no clock rewrite is needed.

    `beforeLock`, timeout, and the barrier are deterministic I/O test seams. -/
def recoverOwnSegment (d : Dirs) (own : String) (incoming : ByteArray)
    (beforeLock : TlM Unit := pure ())
    (timeoutMs : Nat := defaultLockTimeoutMs)
    (syncMechanism : Sys.SyncMechanism := Sys.sync) : TlM Bool := do
  let received := completeLines incoming
  if (recoveryDelta (completeLines (← readSegment d own)) received).isEmpty then
    return false
  beforeLock
  let fd ← acquireLock d timeoutMs
  try
    let replica ← loadReplica d
    unless replica.map (·.id) == some own do
      throw (.mk' .internal "the replica identity changed during recovery — rerun `tl sync` with the current state directory")
    let current ← readSegment d own
    let delta := recoveryDelta (completeLines current) received
    if delta.isEmpty then return false
    appendOwnRaw d own delta (tornTail current) syncMechanism
    return true
  finally
    releaseLock fd

end Tl.Sync
