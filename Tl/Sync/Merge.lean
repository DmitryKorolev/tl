/-
`Tl.Sync.Merge` — the CRDT join at the segment level (ADR-0001 §5).

Reconciling two `refs/tl/log` views is a *per-segment complete-line set
union*: different replicas' segments are taken whole; a same-named segment
(the duplicate-replica-id corner case — a byte-copied working copy, ADR-0007)
is the set union of its complete lines across both copies, so no op is
dropped even if the two diverged. Torn (newline-less) trailing fragments are
not complete lines and never enter the union.

The union is canonicalized — lines deduplicated and byte-lexicographically
sorted — so the same line-set always yields the same bytes (hence the same
git blob/tree), making a re-sync a no-op. Re-sorting a replica's own
append-only segment is harmless: the kernel fold is order-insensitive
(ADR-0004), and `tl log` orders by HLC regardless of on-disk order.

Pure; no I/O. Tested I/O-shell tier (ADR-0004); no Mathlib (ADR-0009).
-/
import Tl.Store.Segment
import Init.Data.List.Lex
import Init.Data.List.BasicAux
import Init.Data.UInt.Package

namespace Tl.Sync

open Tl.Store

/-- Byte-lexicographic `≤` directly over the arrays — the comparator runs per
    merge-sort comparison, so it must not materialize per-comparison copies
    (the previous shape built two boxed `List UInt8` per call). The fuel is
    `a.size + 1`: the index only grows, so `a` exhausts (the `none` arm) before
    the fuel does — the zero arm is dead by construction. -/
private def lexLeBytesAux (a b : ByteArray) : Nat → Nat → Bool
  | _, 0 => true
  | i, fuel + 1 =>
    match a[i]?, b[i]? with
    | none, _ => true
    | some _, none => false
    | some x, some y =>
      if x < y then true
      else if y < x then false
      else lexLeBytesAux a b (i + 1) fuel

def lexLeBytes (a b : ByteArray) : Bool := lexLeBytesAux a b 0 (a.size + 1)

private theorem byteDrop_cons (a : ByteArray) {i : Nat} (hi : i < a.size) :
    a.data.toList.drop i = a[i] :: a.data.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa only [Array.length_toList, ByteArray.size_data] using hi),
    Array.getElem_toList, ByteArray.getElem_eq_getElem_data]

private theorem byteDrop_nil (a : ByteArray) {i : Nat} (hi : a.size ≤ i) :
    a.data.toList.drop i = [] :=
  List.drop_of_length_le (by simpa only [Array.length_toList, ByteArray.size_data] using hi)

private theorem byteLex_spec (a b : ByteArray) (fuel i : Nat) (enough : a.size ≤ i + fuel) :
    lexLeBytesAux a b i fuel = true ↔ a.data.toList.drop i ≤ b.data.toList.drop i := by
  induction fuel generalizing i with
  | zero =>
    rw [lexLeBytesAux, byteDrop_nil a (Nat.add_zero i ▸ enough)]
    exact ⟨fun _ => List.not_lex_nil, fun _ => rfl⟩
  | succ fuel ih =>
    rw [lexLeBytesAux]
    by_cases ha : i < a.size
    · rw [getElem?_pos a i ha, byteDrop_cons a ha]
      by_cases hb : i < b.size
      · rw [getElem?_pos b i hb, byteDrop_cons b hb, List.cons_le_cons_iff]
        by_cases ab : a[i] < b[i]
        · simp only [ab, ite_true, true_or]
        · by_cases ba : b[i] < a[i]
          · have ne : a[i] ≠ b[i] := fun eq => ab (eq ▸ ba)
            simp only [ab, ba, ite_false, ite_true, ne, false_or, false_and, Bool.false_eq_true]
          · have eq : a[i] = b[i] := Std.Trichotomous.trichotomous _ _ ab ba
            have next : a.size ≤ i + 1 + fuel := by
              rw [Nat.add_assoc, Nat.add_comm 1 fuel]
              exact enough
            simp only [ab, ba, ite_false, false_or]
            simp only [eq, true_and]
            exact ih (i + 1) next
      · rw [getElem?_neg b i hb, byteDrop_nil b (Nat.le_of_not_gt hb), List.le_nil]
        simp only [Bool.false_eq_true, List.cons_ne_nil]
    · rw [getElem?_neg a i ha, byteDrop_nil a (Nat.le_of_not_gt ha)]
      exact ⟨fun _ => List.not_lex_nil, fun _ => rfl⟩

theorem lexLeBytes_spec (a b : ByteArray) :
    lexLeBytes a b = true ↔ a.data.toList ≤ b.data.toList := by
  unfold lexLeBytes
  simpa only [List.drop_zero] using byteLex_spec a b (a.size + 1) 0
    (by rw [Nat.zero_add]; exact Nat.le_succ _)

theorem lexLeBytes_total (a b : ByteArray) : lexLeBytes a b = true ∨ lexLeBytes b a = true := by
  rw [lexLeBytes_spec, lexLeBytes_spec]
  exact List.le_total _ _

theorem lexLeBytes_trans (a b c : ByteArray) (ab : lexLeBytes a b = true) (bc : lexLeBytes b c = true) :
    lexLeBytes a c = true :=
  (lexLeBytes_spec a c).mpr (List.le_trans ((lexLeBytes_spec a b).mp ab) ((lexLeBytes_spec b c).mp bc))

theorem lexLeBytes_antisymm (a b : ByteArray) (ab : lexLeBytes a b = true) (ba : lexLeBytes b a = true) :
    a = b :=
  ByteArray.ext (Array.toList_inj.mp
    (List.le_antisymm ((lexLeBytes_spec a b).mp ab) ((lexLeBytes_spec b a).mp ba)))

/-- Adjacent dedup — on a sorted list duplicates are adjacent, so this equals
    `eraseDups` (which rescans its accumulator per element, Θ(L²)) and stays
    linear. -/
private def dedupAdjacentGo (prev : ByteArray) : List ByteArray → List ByteArray
  | [] => [prev]
  | x :: xs => if prev == x then dedupAdjacentGo prev xs else prev :: dedupAdjacentGo x xs

private def dedupAdjacent : List ByteArray → List ByteArray
  | [] => []
  | x :: xs => dedupAdjacentGo x xs

private local instance : LawfulBEq ByteArray where
  rfl := by
    intro a
    change (a.data == a.data) = true
    exact beq_self_eq_true a.data
  eq_of_beq := by
    intro a b h
    change (a.data == b.data) = true at h
    exact ByteArray.ext (eq_of_beq h)

private theorem dedupAdjacentGo_mem (x : ByteArray) (xs : List ByteArray) (line : ByteArray) :
    line ∈ dedupAdjacentGo x xs ↔ line ∈ x :: xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    cases same : (x == y) with
    | false =>
      simp only [dedupAdjacentGo, same, Bool.false_eq_true, ite_false, List.mem_cons, ih]
    | true =>
      have eq := eq_of_beq same
      subst y
      simp only [dedupAdjacentGo, beq_self_eq_true, ite_true, ih, List.mem_cons, or_self_left]

private theorem dedupAdjacentGo_sublist (x : ByteArray) (xs : List ByteArray) :
    List.Sublist (dedupAdjacentGo x xs) (x :: xs) := by
  induction xs generalizing x with
  | nil => exact List.Sublist.refl _
  | cons y ys ih =>
    cases same : (x == y) with
    | false =>
      simp only [dedupAdjacentGo, same, Bool.false_eq_true, ite_false]
      exact List.Sublist.cons_cons x (ih y)
    | true =>
      have eq := eq_of_beq same
      subst y
      simp only [dedupAdjacentGo, beq_self_eq_true, ite_true]
      exact List.Sublist.cons x (ih x)

private theorem dedupAdjacentGo_nodup (x : ByteArray) (xs : List ByteArray)
    (sorted : (x :: xs).Pairwise (fun a b => lexLeBytes a b = true)) :
    (dedupAdjacentGo x xs).Nodup := by
  induction xs generalizing x with
  | nil => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | cons y ys ih =>
    obtain ⟨xBefore, tailSorted⟩ := List.pairwise_cons.mp sorted
    cases same : (x == y) with
    | true =>
      have eq := eq_of_beq same
      subst y
      simp only [dedupAdjacentGo, beq_self_eq_true, ite_true]
      exact ih x tailSorted
    | false =>
      simp only [dedupAdjacentGo, same, Bool.false_eq_true, ite_false, List.nodup_cons]
      refine ⟨?_, ih y tailSorted⟩
      intro present
      have distinct := beq_eq_false_iff_ne.mp same
      have found := (dedupAdjacentGo_mem y ys x).mp present
      rw [List.mem_cons] at found
      exact found.elim distinct (fun inTail =>
        distinct (lexLeBytes_antisymm x y (xBefore y List.mem_cons_self)
          ((List.pairwise_cons.mp tailSorted).1 x inTail)))

private theorem dedupAdjacent_mem (xs : List ByteArray) (line : ByteArray) :
    line ∈ dedupAdjacent xs ↔ line ∈ xs := by
  cases xs with
  | nil => rfl
  | cons x xs => exact dedupAdjacentGo_mem x xs line

private theorem dedupAdjacent_sortedNodup (xs : List ByteArray)
    (sorted : xs.Pairwise (fun a b => lexLeBytes a b = true)) :
    (dedupAdjacent xs).Pairwise (fun a b => lexLeBytes a b = true) ∧ (dedupAdjacent xs).Nodup := by
  cases xs with
  | nil => exact ⟨List.Pairwise.nil, List.nodup_nil⟩
  | cons x xs =>
    exact ⟨sorted.sublist (dedupAdjacentGo_sublist x xs), dedupAdjacentGo_nodup x xs sorted⟩

private def canonicalLines (xs : List ByteArray) : List ByteArray :=
  dedupAdjacent (xs.mergeSort lexLeBytes)

private theorem canonicalLines_mem (xs : List ByteArray) (line : ByteArray) :
    line ∈ canonicalLines xs ↔ line ∈ xs :=
  (dedupAdjacent_mem _ line).trans ((List.mergeSort_perm xs lexLeBytes).mem_iff)

private theorem canonicalLines_sortedNodup (xs : List ByteArray) :
    (canonicalLines xs).Pairwise (fun a b => lexLeBytes a b = true) ∧ (canonicalLines xs).Nodup :=
  dedupAdjacent_sortedNodup _
    (List.pairwise_mergeSort lexLeBytes_trans
      (fun a b => Bool.or_eq_true_iff.mpr (lexLeBytes_total a b)) xs)

private theorem canonicalLines_eq (xs ys : List ByteArray)
    (same : ∀ line, line ∈ xs ↔ line ∈ ys) : canonicalLines xs = canonicalLines ys := by
  obtain ⟨xsSorted, xsNodup⟩ := canonicalLines_sortedNodup xs
  obtain ⟨ysSorted, ysNodup⟩ := canonicalLines_sortedNodup ys
  apply List.Perm.eq_of_pairwise (fun a b _ _ => lexLeBytes_antisymm a b) xsSorted ysSorted
  apply (List.perm_ext_iff_of_nodup xsNodup ysNodup).mpr
  intro line
  rw [canonicalLines_mem, canonicalLines_mem]
  exact same line

/-- The complete line set of both streams in canonical byte order. -/
def unionLines (a b : ByteArray) : ByteArray :=
  joinLines (canonicalLines (completeLines a ++ completeLines b))

private theorem completeLines_unionLines (a b : ByteArray) :
    completeLines (unionLines a b) = canonicalLines (completeLines a ++ completeLines b) := by
  apply completeLines_joinLines
  intro line h
  have found := List.mem_append.mp ((canonicalLines_mem _ _).mp h)
  exact found.elim (completeLines_lfFree a line) (completeLines_lfFree b line)

/-- Transport preserves exactly the complete lines from either input. -/
theorem unionLines_mem_iff (a b line : ByteArray) :
    line ∈ completeLines (unionLines a b) ↔ line ∈ completeLines a ∨ line ∈ completeLines b := by
  rw [completeLines_unionLines, canonicalLines_mem, List.mem_append]

/-- Opposite merge directions yield byte-identical canonical output. -/
theorem unionLines_comm (a b : ByteArray) : unionLines a b = unionLines b a := by
  apply congrArg joinLines
  apply canonicalLines_eq
  intro line
  rw [List.mem_append, List.mem_append, or_comm]

/-- Replaying the same input after the union leaves the canonical bytes fixed. -/
theorem unionLines_idem (a b : ByteArray) : unionLines (unionLines a b) b = unionLines a b := by
  apply congrArg joinLines
  apply canonicalLines_eq
  intro line
  rw [List.mem_append, unionLines_mem_iff, List.mem_append]
  exact ⟨fun h => h.elim id Or.inr, Or.inl⟩

/-- The linear merge-join of two replica-id-sorted segment lists: each id
    present on either side yields one segment whose bytes are the line-union of
    that replica's copies (the absent side contributes `ByteArray.empty`),
    ascending by replica id. Replica ids are unique within each side (one
    segment file per replica, ADR-0001), so the heads alone decide each step.
    Fuel is `|xs| + |ys|` — every step consumes one head, so the fuel never
    runs out while either side is non-empty (the zero arm is dead). -/
private def unionSegmentsGo : Nat → List SegmentData → List SegmentData → List SegmentData
  | _, [], ys => ys.map (fun s => { replicaId := s.replicaId, bytes := unionLines ByteArray.empty s.bytes })
  | _, x :: xs, [] => (x :: xs).map (fun s => { replicaId := s.replicaId, bytes := unionLines s.bytes ByteArray.empty })
  | 0, _ :: _, _ :: _ => []
  | fuel + 1, x :: xs, y :: ys =>
    if x.replicaId == y.replicaId then
      { replicaId := x.replicaId, bytes := unionLines x.bytes y.bytes } :: unionSegmentsGo fuel xs ys
    else if decide (x.replicaId ≤ y.replicaId) then
      { replicaId := x.replicaId, bytes := unionLines x.bytes ByteArray.empty } :: unionSegmentsGo fuel xs (y :: ys)
    else
      { replicaId := y.replicaId, bytes := unionLines ByteArray.empty y.bytes } :: unionSegmentsGo fuel (x :: xs) ys

/-- Union two sets of per-replica segments (ADR-0001 §5): each replica id
    present on either side yields one segment whose bytes are the line-union of
    that replica's copies (an absent side contributes nothing). Sort each side
    by replica id once, then merge-join in one pass — the previous shape paid
    `eraseDups` (Θ(S²)) plus a `find?` per id (Θ(S²)); this is O(S log S). The
    result is the same ascending-by-id segment list as before. -/
def unionSegments (xs ys : List SegmentData) : List SegmentData :=
  let le := fun (a b : SegmentData) => decide (a.replicaId ≤ b.replicaId)
  unionSegmentsGo (xs.length + ys.length) (xs.mergeSort le) (ys.mergeSort le)

end Tl.Sync
