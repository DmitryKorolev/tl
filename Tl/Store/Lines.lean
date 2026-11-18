/- Byte framing for replica segments. The scanner copies each completed
   slice once. Its proofs characterize the same loop using list splitting. -/
import Init.Data.List.SplitOn.Lemmas
import Init.Data.Array.Extract

namespace Tl.Store

private structure LineScan where
  lines : List ByteArray := []
  start : Nat := 0
  offset : Nat := 0

@[inline] private def scanLine (bytes : ByteArray) (byte : UInt8) (s : LineScan) : LineScan :=
  if byte == 10 then
    { lines := bytes.extract s.start s.offset :: s.lines, start := s.offset + 1, offset := s.offset + 1 }
  else { s with offset := s.offset + 1 }

@[inline] private def lineScanStep (bytes : ByteArray) (byte : UInt8) (state : LineScan) :
    Id (ForInStep LineScan) := pure (.yield (scanLine bytes byte state))

/-- Split on LF in one pass, copying only completed slices. A trailing
    fragment without LF is left out. -/
def completeLines (bytes : ByteArray) : List ByteArray :=
  (ByteArray.forIn bytes ({} : LineScan) (lineScanStep bytes)).run.lines.reverse

private def lineOfBytes (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩

private theorem lineOfBytes_data (bytes : ByteArray) : lineOfBytes bytes.data.toList = bytes := by
  apply ByteArray.ext
  exact Array.toArray_toList

private theorem extract_data_eq (bytes : ByteArray) {start stop : Nat} (hle : start ≤ stop) :
    (bytes.extract start stop).data = bytes.data.extract start stop := by
  simp only [ByteArray.extract, ByteArray.copySlice, ByteArray.empty, Nat.add_sub_of_le hle]
  change (#[] : Array UInt8).extract 0 0 ++ bytes.data.extract start stop ++
    (#[] : Array UInt8).extract (0 + min (stop - start) (bytes.data.size - start)) 0 =
      bytes.data.extract start stop
  rw [Array.extract_empty_of_size_le_start (xs := #[]) (Nat.zero_le 0), Array.empty_append,
    Array.extract_empty_of_size_le_start (xs := #[]) (Nat.zero_le _), Array.append_empty]

private theorem extract_same (bytes : ByteArray) (i : Nat) :
    (bytes.extract i i).data.toList = [] := by
  rw [extract_data_eq bytes (Nat.le_refl i), Array.extract_empty_of_stop_le_start (Nat.le_refl i)]

private theorem extract_next (bytes : ByteArray) {start i : Nat}
    (hs : start ≤ i) (hi : i < bytes.size) :
    (bytes.extract start (i + 1)).data.toList =
      (bytes.extract start i).data.toList ++ [bytes[i]] := by
  rw [extract_data_eq bytes (Nat.le_succ_of_le hs), extract_data_eq bytes hs,
    Array.extract_succ_right (Nat.lt_succ_of_le hs) hi, Array.toList_push, ByteArray.getElem_eq_getElem_data]

private theorem split_dropLast_cons (p : UInt8 → Bool) (xs : List UInt8) (a : List UInt8) :
    (a :: xs.splitOnP p).dropLast = a :: (xs.splitOnP p).dropLast := by
  cases h : xs.splitOnP p with
  | nil => exact False.elim (List.splitOnP_ne_nil p xs h)
  | cons b bs => exact List.dropLast_cons_cons

private theorem scanLoop_spec (bytes : ByteArray) (n : Nat) (hn : n ≤ bytes.size)
    (state : LineScan) (offset : state.offset = bytes.size - n)
    (hs : state.start ≤ state.offset) :
    (ByteArray.forIn.loop bytes (lineScanStep bytes) n hn state).run.lines.reverse =
      state.lines.reverse ++
        ((List.splitOnPPrepend (· == (10 : UInt8))
          (bytes.data.toList.drop state.offset)
          (bytes.extract state.start state.offset).data.toList.reverse).dropLast.map lineOfBytes) := by
  induction n generalizing state with
  | zero =>
    have endOfInput : bytes.data.toList.length ≤ state.offset := by
      rw [offset, Nat.sub_zero, Array.length_toList, ByteArray.size_data]
      exact Nat.le_refl _
    rw [ByteArray.forIn.loop.eq_1, List.drop_of_length_le endOfInput]
    simp only [pure, Id.run, List.splitOnPPrepend_nil, List.dropLast_singleton,
      List.map_nil, List.append_nil]
  | succ n ih =>
    have index : bytes.size - 1 - n = state.offset := by
      rw [Nat.sub_sub, Nat.add_comm 1 n, offset]
    have hn' : n < bytes.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have iBound : state.offset < bytes.size := by
      rw [offset]
      exact Nat.sub_lt (Nat.zero_lt_of_lt hn') (Nat.succ_pos n)
    have next : state.offset + 1 = bytes.size - n := by
      apply Nat.eq_sub_of_add_eq
      calc
        (state.offset + 1) + n = state.offset + (n + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 n]
        _ = bytes.size := by rw [offset, Nat.sub_add_cancel hn]
    have drop := List.drop_eq_getElem_cons (l := bytes.data.toList)
      (i := state.offset) (by simpa only [Array.length_toList, ByteArray.size_data] using iBound)
    rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data] at drop
    rw [ByteArray.forIn.loop.eq_2]
    simp only [lineScanStep, pure, bind, Id.run]
    -- Rewrite the index in a dependent lookup.
    simp only [index]
    rw [drop]
    cases hit : (bytes[state.offset] == 10) with
    | false =>
      simp only [scanLine, hit, Bool.false_eq_true, ite_false]
      let advanced : LineScan := { state with offset := state.offset + 1 }
      have step := ih (Nat.le_of_lt hn') advanced next (Nat.le_succ_of_le hs)
      simp only [Id.run] at step
      rw [step, List.splitOnPPrepend_cons_neg (p := (· == (10 : UInt8))) (a := bytes[state.offset]) hit]
      simp only [advanced, extract_next bytes hs iBound, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
    | true =>
      simp only [scanLine, hit, ite_true]
      let advanced : LineScan := {
        lines := bytes.extract state.start state.offset :: state.lines
        start := state.offset + 1
        offset := state.offset + 1 }
      have step := ih (Nat.le_of_lt hn') advanced next (Nat.le_refl _)
      simp only [Id.run] at step
      rw [step, List.splitOnPPrepend_cons_pos (p := (· == (10 : UInt8))) (a := bytes[state.offset]) hit, split_dropLast_cons]
      simp only [advanced, extract_same, List.reverse_nil, List.splitOnPPrepend_nil_right,
        List.reverse_cons, List.map_cons, List.append_assoc, List.reverse_reverse,
        lineOfBytes_data, List.singleton_append]
theorem completeLines_eq_splitOn (bytes : ByteArray) :
    completeLines bytes = ((bytes.data.toList.splitOn (10 : UInt8)).dropLast.map lineOfBytes) := by
  unfold completeLines ByteArray.forIn
  rw [scanLoop_spec bytes bytes.size (Nat.le_refl _) {} (Nat.sub_self _).symm (Nat.le_refl 0)]
  simp only [extract_same, List.reverse_nil, List.nil_append, List.drop_zero,
    List.splitOnPPrepend_nil_right, List.splitOn_eq_splitOnP]

private theorem splitPrepend_lfFree (bytes pending : List UInt8)
    (pendingFree : (10 : UInt8) ∉ pending) (line : List UInt8)
    (found : line ∈ List.splitOnPPrepend (· == (10 : UInt8)) bytes pending) :
    (10 : UInt8) ∉ line := by
  induction bytes generalizing pending with
  | nil =>
    rw [List.splitOnPPrepend_nil, List.mem_singleton] at found
    rw [found, List.mem_reverse]
    exact pendingFree
  | cons byte tail ih =>
    cases hit : (byte == 10) with
    | false =>
      rw [List.splitOnPPrepend_cons_neg (p := (· == (10 : UInt8))) (a := byte) hit] at found
      refine ih _ (fun present => ?_) found
      rw [List.mem_cons] at present
      exact present.elim (fun eq => (beq_eq_false_iff_ne.mp hit) eq.symm) pendingFree
    | true =>
      rw [List.splitOnPPrepend_cons_pos (p := (· == (10 : UInt8))) (a := byte) hit, List.mem_cons] at found
      rcases found with h | h
      · rw [h, List.mem_reverse]
        exact pendingFree
      · exact ih [] List.not_mem_nil ((List.splitOnPPrepend_nil_right (p := (· == (10 : UInt8)))).symm ▸ h)

theorem completeLines_lfFree (bytes line : ByteArray) (found : line ∈ completeLines bytes) :
    (10 : UInt8) ∉ line.data.toList := by
  rw [completeLines_eq_splitOn, List.mem_map] at found
  obtain ⟨lineBytes, found, rfl⟩ := found
  change (10 : UInt8) ∉ lineBytes.toArray.toList
  rw [List.toList_toArray]
  apply splitPrepend_lfFree bytes.data.toList [] List.not_mem_nil
  rw [List.splitOnPPrepend_nil_right, ← List.splitOn_eq_splitOnP]
  exact (List.dropLast_sublist _).subset found

/-- Frame a list of LF-free lines for storage or transport. -/
def joinLines (lines : List ByteArray) : ByteArray :=
  lines.foldl (fun bytes line => (bytes ++ line).push 10) .empty

private theorem foldJoin_data (lines : List ByteArray) (init : ByteArray) :
    (lines.foldl (fun bytes line => (bytes ++ line).push 10) init).data.toList =
      init.data.toList ++ lines.flatMap (fun line => line.data.toList ++ [10]) := by
  induction lines generalizing init with
  | nil => rw [List.foldl_nil, List.flatMap_nil, List.append_nil]
  | cons line tail ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons]
    change ((init ++ line).data.push 10).toList ++ _ = _
    simp only [Array.toList_push, ← ByteArray.append_eq, ByteArray.toList_data_append', List.append_assoc]

private theorem split_join_data (lines : List ByteArray)
    (lfFree : ∀ line ∈ lines, (10 : UInt8) ∉ line.data.toList) :
    (lines.flatMap (fun line => line.data.toList ++ [10])).splitOn (10 : UInt8) =
      lines.map (·.data.toList) ++ [[]] := by
  induction lines with
  | nil => rw [List.flatMap_nil, List.splitOn_nil, List.map_nil, List.nil_append]
  | cons line tail ih =>
    rw [List.flatMap_cons, List.append_assoc, List.singleton_append,
      List.splitOn_append_cons_self_of_not_mem (lfFree line List.mem_cons_self),
      ih (fun other h => lfFree other (List.mem_cons_of_mem _ h)),
      List.map_cons, List.cons_append]

theorem completeLines_joinLines (lines : List ByteArray)
    (lfFree : ∀ line ∈ lines, (10 : UInt8) ∉ line.data.toList) :
    completeLines (joinLines lines) = lines := by
  rw [completeLines_eq_splitOn, joinLines, foldJoin_data]
  change ((([] ++ lines.flatMap _).splitOn _).dropLast.map lineOfBytes) = lines
  rw [List.nil_append, split_join_data lines lfFree, List.dropLast_concat, List.map_map]
  change lines.map (fun line => lineOfBytes line.data.toList) = lines
  exact List.map_id'' lineOfBytes_data lines
end Tl.Store
