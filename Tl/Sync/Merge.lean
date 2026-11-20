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

Pure byte and segment operations with exact membership and canonicality proofs.
-/
import Tl.Store.Segment
import Tl.Store.Quarantine
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

/-- The exact-byte exclusion set observed by materialization is a grow-only
    set under transport union, including after delivery in a different order. -/
def quarantined (replica : String) (bytes : ByteArray) (target : Array UInt8) : Bool :=
  (quarantineIndex replica (completeLines bytes)).contains target

theorem quarantined_union (replica : String) (a b : ByteArray) (target : Array UInt8) :
    quarantined replica (unionLines a b) target =
      (quarantined replica a target || quarantined replica b target) := by
  apply Bool.eq_iff_iff.mpr
  simp only [quarantined, Bool.or_eq_true, quarantineIndex_contains, unionLines_mem_iff]
  constructor
  · rintro ⟨line, ha | hb, matchTarget⟩
    · exact Or.inl ⟨line, ha, matchTarget⟩
    · exact Or.inr ⟨line, hb, matchTarget⟩
  · rintro (⟨line, ha, matchTarget⟩ | ⟨line, hb, matchTarget⟩)
    · exact ⟨line, Or.inl ha, matchTarget⟩
    · exact ⟨line, Or.inr hb, matchTarget⟩

theorem quarantine_merge_comm (r : String) (a b : ByteArray) (t : Array UInt8) :
    quarantined r (unionLines a b) t = quarantined r (unionLines b a) t := by
  rw [quarantined_union, quarantined_union, Bool.or_comm]

theorem quarantine_merge_assoc (r : String) (a b c : ByteArray) (t : Array UInt8) :
    quarantined r (unionLines (unionLines a b) c) t =
      quarantined r (unionLines a (unionLines b c)) t := by
  simp only [quarantined_union, Bool.or_assoc]

theorem quarantine_merge_idem (r : String) (a : ByteArray) (t : Array UInt8) :
    quarantined r (unionLines a a) t = quarantined r a t := by
  rw [quarantined_union, Bool.or_self]

theorem quarantine_survives_merge (r : String) (a b : ByteArray) (t : Array UInt8)
    (held : quarantined r a t = true) : quarantined r (unionLines a b) t = true := by
  rw [quarantined_union, held, Bool.true_or]

/-- The decoder's exact exclusion predicate survives any subsequent transport merge. -/
theorem excludesDamage_after_merge (r : String) (a b raw : ByteArray) (error : Tl.Error)
    (excluded : excludesDamage (quarantineIndex r (completeLines a)) raw error = true) :
    excludesDamage (quarantineIndex r (completeLines (unionLines a b))) raw error = true := by
  change (repairableDamage raw error && quarantined r a raw.data) = true at excluded
  change (repairableDamage raw error && quarantined r (unionLines a b) raw.data) = true
  obtain ⟨eligible, marked⟩ := (Bool.and_eq_true ..).mp excluded
  rw [eligible, quarantine_survives_merge r a b raw.data marked, Bool.true_and]


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

private def segmentLe (a b : SegmentData) : Bool := decide (a.replicaId ≤ b.replicaId)

/-- Union two sets of per-replica segments (ADR-0001 §5): each replica id
    present on either side yields one segment whose bytes are the line-union of
    that replica's copies (an absent side contributes nothing). Sort each side
    by replica id once, then merge-join in one pass — the previous shape paid
    `eraseDups` (Θ(S²)) plus a `find?` per id (Θ(S²)); this is O(S log S). The
    result is the same ascending-by-id segment list as before. -/
def unionSegments (xs ys : List SegmentData) : List SegmentData :=
  unionSegmentsGo (xs.length + ys.length)
    (xs.mergeSort segmentLe) (ys.mergeSort segmentLe)

/-- The first segment's bytes for a replica, with empty bytes when absent.
    With unique replica IDs this is the entire segment for that replica. -/
def replicaBytes (segments : List SegmentData) (replica : String) : ByteArray :=
  ((segments.find? (fun s => s.replicaId == replica)).map (·.bytes)).getD .empty

private theorem replicaBytes_cons_match (x : SegmentData) (xs : List SegmentData) (replica : String)
    (keeps : x.replicaId = replica) : replicaBytes (x :: xs) replica = x.bytes := by
  simp only [replicaBytes, List.find?_cons, keeps, beq_self_eq_true, Option.map_some, Option.getD_some]

private theorem replicaBytes_cons_miss (x : SegmentData) (xs : List SegmentData) (replica : String)
    (miss : x.replicaId ≠ replica) : replicaBytes (x :: xs) replica = replicaBytes xs replica := by
  simp only [replicaBytes, List.find?_cons, beq_eq_false_iff_ne.mpr miss]

private theorem replicaBytes_map (segments : List SegmentData) (replica : String)
    (f : ByteArray → ByteArray) (empty : f .empty = .empty) :
    replicaBytes (segments.map (fun s => { s with bytes := f s.bytes })) replica =
      f (replicaBytes segments replica) := by
  simp only [replicaBytes, List.find?_map, Option.map_map]
  change (((segments.find? (fun s => s.replicaId == replica)).map (fun s => f s.bytes)).getD .empty)
    = f (((segments.find? (fun s => s.replicaId == replica)).map (·.bytes)).getD .empty)
  cases segments.find? (fun s => s.replicaId == replica) with
  | none => exact empty.symm
  | some s => rfl

private theorem replicaBytes_before (x : SegmentData) (xs : List SegmentData) (replica : String)
    (sorted : (x :: xs).Pairwise (fun a b => segmentLe a b = true))
    (earlier : ¬ x.replicaId ≤ replica) :
    replicaBytes (x :: xs) replica = .empty := by
  have absent : (x :: xs).find? (fun s => s.replicaId == replica) = none := by
    apply List.find?_eq_none.mpr
    intro other found hit
    have eq := beq_iff_eq.mp hit
    rw [List.mem_cons] at found
    rcases found with h | h
    · exact earlier (by rw [← eq, h]; exact Std.le_refl _)
    · exact earlier (eq ▸ of_decide_eq_true ((List.pairwise_cons.mp sorted).1 other h))
  simp only [replicaBytes, absent, Option.map_none, Option.getD_none]

private theorem unionLines_empty_empty : unionLines .empty .empty = .empty := by
  have noLines : completeLines .empty = [] := by
    rw [completeLines_eq_splitOn]
    rfl
  rw [unionLines, noLines, List.nil_append]
  simp only [canonicalLines, List.mergeSort_nil, dedupAdjacent, joinLines, List.foldl_nil]

private theorem unionSegmentsGo_replicaBytes (fuel : Nat) (xs ys : List SegmentData) (replica : String)
    (bound : xs.length + ys.length ≤ fuel)
    (sx : xs.Pairwise (fun a b => segmentLe a b = true))
    (sy : ys.Pairwise (fun a b => segmentLe a b = true)) :
    replicaBytes (unionSegmentsGo fuel xs ys) replica =
      unionLines (replicaBytes xs replica) (replicaBytes ys replica) := by
  cases xs with
  | nil =>
    rw [unionSegmentsGo]
    change replicaBytes (ys.map (fun s => { s with bytes := unionLines .empty s.bytes })) replica = _
    exact replicaBytes_map ys replica _ unionLines_empty_empty
  | cons x xs =>
    cases ys with
    | nil =>
      rw [unionSegmentsGo]
      change replicaBytes ((x :: xs).map (fun s => { s with bytes := unionLines s.bytes .empty })) replica = _
      exact replicaBytes_map (x :: xs) replica (unionLines · .empty) unionLines_empty_empty
    | cons y ys =>
      cases fuel with
      | zero => exact False.elim (Nat.not_succ_le_zero _ bound)
      | succ fuel =>
        have leftBound : xs.length + (y :: ys).length ≤ fuel := by
          apply Nat.le_of_succ_le_succ
          simpa only [List.length_cons, Nat.succ_add] using bound
        have rightBound : (x :: xs).length + ys.length ≤ fuel := Nat.le_of_succ_le_succ bound
        rw [unionSegmentsGo]
        by_cases same : x.replicaId = y.replicaId
        · simp only [beq_iff_eq, same, ite_true]
          by_cases hit : x.replicaId = replica
          · have hitY := same.symm.trans hit
            rw [replicaBytes_cons_match ⟨y.replicaId, unionLines x.bytes y.bytes⟩ _ _ hitY,
              replicaBytes_cons_match x xs replica hit,
              replicaBytes_cons_match y ys replica hitY]
          · have missY : y.replicaId ≠ replica := fun eq => hit (same.trans eq)
            rw [replicaBytes_cons_miss ⟨y.replicaId, unionLines x.bytes y.bytes⟩ _ _ missY,
              replicaBytes_cons_miss x xs replica hit,
              replicaBytes_cons_miss y ys replica missY]
            exact unionSegmentsGo_replicaBytes fuel xs ys replica
              (Nat.le_trans (Nat.le_succ _) leftBound) sx.tail sy.tail
        · simp only [beq_iff_eq, same, ite_false]
          by_cases le : x.replicaId ≤ y.replicaId
          · simp only [le, decide_true, ite_true]
            by_cases hit : x.replicaId = replica
            · have earlier : ¬ y.replicaId ≤ replica := fun rev =>
                same (Std.le_antisymm le (hit.symm ▸ rev))
              rw [replicaBytes_cons_match ⟨x.replicaId, unionLines x.bytes .empty⟩ _ _ hit,
                replicaBytes_cons_match x xs replica hit,
                replicaBytes_before y ys replica sy earlier]
            · rw [replicaBytes_cons_miss ⟨x.replicaId, unionLines x.bytes .empty⟩ _ _ hit,
                replicaBytes_cons_miss x xs replica hit]
              exact unionSegmentsGo_replicaBytes fuel xs (y :: ys) replica leftBound sx.tail sy
          · simp only [le, decide_false, Bool.false_eq_true, ite_false]
            by_cases hit : y.replicaId = replica
            · have earlier : ¬ x.replicaId ≤ replica := fun h => le (hit.symm ▸ h)
              rw [replicaBytes_cons_match ⟨y.replicaId, unionLines .empty y.bytes⟩ _ _ hit,
                replicaBytes_before x xs replica sx earlier,
                replicaBytes_cons_match y ys replica hit]
            · rw [replicaBytes_cons_miss ⟨y.replicaId, unionLines .empty y.bytes⟩ _ _ hit,
                replicaBytes_cons_miss y ys replica hit]
              exact unionSegmentsGo_replicaBytes fuel (x :: xs) ys replica rightBound sx sy.tail
termination_by fuel

private theorem segmentLe_trans (x y z : SegmentData) (xy : segmentLe x y = true) (yz : segmentLe y z = true) :
    segmentLe x z = true :=
  decide_eq_true (Std.le_trans (of_decide_eq_true xy) (of_decide_eq_true yz))

private theorem segmentLe_total (x y : SegmentData) : (segmentLe x y || segmentLe y x) = true :=
  Bool.or_eq_true_iff.mpr ((Std.le_total (a := x.replicaId) (b := y.replicaId)).imp decide_eq_true decide_eq_true)

private theorem filteredReplica_sorted (segments : List SegmentData) (replica : String) :
    (segments.filter (fun s => s.replicaId == replica)).Pairwise (fun a b => segmentLe a b = true) := by
  induction segments with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    cases hit : (x.replicaId == replica) with
    | false => simpa only [List.filter_cons, hit, Bool.false_eq_true, ite_false] using ih
    | true =>
      simp only [List.filter_cons, hit, ite_true, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro y found
      have h := (List.mem_filter.mp found).2
      exact decide_eq_true (by rw [beq_iff_eq.mp hit, beq_iff_eq.mp h]; exact Std.le_refl _)

private theorem replicaBytes_mergeSort (segments : List SegmentData) (replica : String) :
    replicaBytes (segments.mergeSort segmentLe) replica = replicaBytes segments replica := by
  let keeps : SegmentData → Bool := fun s => s.replicaId == replica
  have stable : List.Sublist (segments.filter keeps) (segments.mergeSort segmentLe) :=
    List.sublist_mergeSort segmentLe_trans segmentLe_total (filteredReplica_sorted segments replica)
      List.filter_sublist
  have stableFiltered := stable.filter keeps
  rw [List.filter_filter,
    show (fun x => keeps x && keeps x) = keeps from funext (fun s => Bool.and_self (keeps s))] at stableFiltered
  have lengthEq := ((List.mergeSort_perm segments segmentLe).filter keeps).length_eq
  have same := stableFiltered.eq_of_length lengthEq.symm
  unfold replicaBytes
  change (((segments.mergeSort segmentLe).find? keeps).map (·.bytes)).getD .empty =
    ((segments.find? keeps).map (·.bytes)).getD .empty
  rw [← List.head?_filter, ← List.head?_filter, same]

private theorem unionSegmentsGo_id_mem (fuel : Nat) (xs ys : List SegmentData) (replica : String)
    (bound : xs.length + ys.length ≤ fuel) :
    replica ∈ (unionSegmentsGo fuel xs ys).map (·.replicaId) ↔
      replica ∈ xs.map (·.replicaId) ∨ replica ∈ ys.map (·.replicaId) := by
  cases xs with
  | nil =>
    simp only [unionSegmentsGo, List.map_map, Function.comp_def, List.map_nil, List.not_mem_nil, false_or]
  | cons x xs =>
    cases ys with
    | nil =>
      simp only [unionSegmentsGo, List.map_map, Function.comp_def, List.map_nil, List.not_mem_nil, or_false]
    | cons y ys =>
      cases fuel with
      | zero => exact False.elim (Nat.not_succ_le_zero _ bound)
      | succ fuel =>
        have leftBound : xs.length + (y :: ys).length ≤ fuel := by
          apply Nat.le_of_succ_le_succ
          simpa only [List.length_cons, Nat.succ_add] using bound
        have rightBound : (x :: xs).length + ys.length ≤ fuel := Nat.le_of_succ_le_succ bound
        rw [unionSegmentsGo]
        by_cases same : x.replicaId = y.replicaId
        · simp only [beq_iff_eq, same, ite_true, List.map_cons, List.mem_cons,
            unionSegmentsGo_id_mem fuel xs ys replica (Nat.le_trans (Nat.le_succ _) leftBound)]
          constructor
          · intro h
            exact h.elim (fun eq => Or.inl (Or.inl eq))
              (fun tail => tail.elim (fun hx => Or.inl (Or.inr hx)) (fun hy => Or.inr (Or.inr hy)))
          · intro h
            exact h.elim (fun hx => hx.imp id Or.inl) (fun hy => hy.imp id Or.inr)
        · by_cases le : x.replicaId ≤ y.replicaId
          · simp only [beq_iff_eq, same, ite_false, le, decide_true, ite_true,
              List.map_cons, List.mem_cons,
              unionSegmentsGo_id_mem fuel xs (y :: ys) replica leftBound, or_assoc]
          · simp only [beq_iff_eq, same, le, decide_false, Bool.false_eq_true, ite_false,
              List.map_cons, List.mem_cons,
              unionSegmentsGo_id_mem fuel (x :: xs) ys replica rightBound]
            exact or_left_comm
termination_by fuel

private theorem id_absent_before (x : SegmentData) (xs : List SegmentData) (replica : String)
    (sorted : (x :: xs).Pairwise (fun a b => segmentLe a b = true))
    (earlier : ¬ x.replicaId ≤ replica) :
    replica ∉ (x :: xs).map (·.replicaId) := by
  intro found
  obtain ⟨s, present, eq⟩ := List.mem_map.mp found
  rcases List.mem_cons.mp present with head | tail
  · exact earlier (by rw [← eq, head]; exact Std.le_refl _)
  · exact earlier (eq ▸ of_decide_eq_true ((List.pairwise_cons.mp sorted).1 s tail))

private theorem unionSegmentsGo_ids_nodup (fuel : Nat) (xs ys : List SegmentData)
    (bound : xs.length + ys.length ≤ fuel)
    (sx : xs.Pairwise (fun a b => segmentLe a b = true))
    (sy : ys.Pairwise (fun a b => segmentLe a b = true))
    (nx : (xs.map (·.replicaId)).Nodup) (ny : (ys.map (·.replicaId)).Nodup) :
    ((unionSegmentsGo fuel xs ys).map (·.replicaId)).Nodup := by
  cases xs with
  | nil => simpa only [unionSegmentsGo, List.map_map, Function.comp_def] using ny
  | cons x xs =>
    cases ys with
    | nil => simpa only [unionSegmentsGo, List.map_map, Function.comp_def] using nx
    | cons y ys =>
      cases fuel with
      | zero => exact False.elim (Nat.not_succ_le_zero _ bound)
      | succ fuel =>
        obtain ⟨xAbsent, nxTail⟩ := List.nodup_cons.mp nx
        obtain ⟨yAbsent, nyTail⟩ := List.nodup_cons.mp ny
        have leftBound : xs.length + (y :: ys).length ≤ fuel := by
          apply Nat.le_of_succ_le_succ
          simpa only [List.length_cons, Nat.succ_add] using bound
        have rightBound : (x :: xs).length + ys.length ≤ fuel := Nat.le_of_succ_le_succ bound
        rw [unionSegmentsGo]
        by_cases same : x.replicaId = y.replicaId
        · have tailBound := Nat.le_trans (Nat.le_succ (xs.length + ys.length)) leftBound
          simp only [beq_iff_eq, same, ite_true, List.map_cons, List.nodup_cons,
            unionSegmentsGo_id_mem fuel xs ys y.replicaId tailBound]
          exact ⟨fun h => h.elim (same ▸ xAbsent) yAbsent,
            unionSegmentsGo_ids_nodup fuel xs ys tailBound sx.tail sy.tail nxTail nyTail⟩
        · by_cases le : x.replicaId ≤ y.replicaId
          · have earlier : ¬ y.replicaId ≤ x.replicaId := fun rev => same (Std.le_antisymm le rev)
            simp only [beq_iff_eq, same, ite_false, le, decide_true, ite_true, List.map_cons,
              List.nodup_cons, unionSegmentsGo_id_mem fuel xs (y :: ys) x.replicaId leftBound]
            exact ⟨fun h => h.elim xAbsent (id_absent_before y ys x.replicaId sy earlier),
              unionSegmentsGo_ids_nodup fuel xs (y :: ys) leftBound sx.tail sy nxTail ny⟩
          · simp only [beq_iff_eq, same, le, decide_false, Bool.false_eq_true, ite_false,
              List.map_cons, List.nodup_cons,
              unionSegmentsGo_id_mem fuel (x :: xs) ys y.replicaId rightBound]
            exact ⟨fun h => h.elim (id_absent_before x xs y.replicaId sx le) yAbsent,
              unionSegmentsGo_ids_nodup fuel (x :: xs) ys rightBound sx sy.tail nx nyTail⟩
termination_by fuel

/-- The production merge emits exactly the replica IDs present in either input. -/
theorem unionSegments_id_mem_iff (xs ys : List SegmentData) (replica : String) :
    replica ∈ (unionSegments xs ys).map (·.replicaId) ↔
      replica ∈ xs.map (·.replicaId) ∨ replica ∈ ys.map (·.replicaId) := by
  let px := List.mergeSort_perm xs segmentLe
  let py := List.mergeSort_perm ys segmentLe
  have bound : (xs.mergeSort segmentLe).length + (ys.mergeSort segmentLe).length ≤
      xs.length + ys.length := by
    rw [px.length_eq, py.length_eq]
    exact Nat.le_refl _
  rw [unionSegments, unionSegmentsGo_id_mem _ _ _ replica bound, (px.map (·.replicaId)).mem_iff,
    (py.map (·.replicaId)).mem_iff]

/-- One segment per replica on each side gives one segment per replica after merging. -/
theorem unionSegments_ids_nodup (xs ys : List SegmentData)
    (nx : (xs.map (·.replicaId)).Nodup) (ny : (ys.map (·.replicaId)).Nodup) :
    ((unionSegments xs ys).map (·.replicaId)).Nodup := by
  let px := List.mergeSort_perm xs segmentLe
  let py := List.mergeSort_perm ys segmentLe
  have bound : (xs.mergeSort segmentLe).length + (ys.mergeSort segmentLe).length ≤
      xs.length + ys.length := by
    rw [px.length_eq, py.length_eq]
    exact Nat.le_refl _
  exact unionSegmentsGo_ids_nodup _ _ _ bound
    (List.pairwise_mergeSort segmentLe_trans segmentLe_total xs)
    (List.pairwise_mergeSort segmentLe_trans segmentLe_total ys)
    ((px.map (·.replicaId)).symm.nodup nx) ((py.map (·.replicaId)).symm.nodup ny)

/-- The segment merge computes the canonical union of the first segment for
    each replica on both sides. For unique input IDs, this covers every segment
    for that replica, and `unionSegments_ids_nodup` preserves that invariant. -/
theorem unionSegments_replicaBytes (xs ys : List SegmentData) (replica : String) :
    replicaBytes (unionSegments xs ys) replica =
      unionLines (replicaBytes xs replica) (replicaBytes ys replica) := by
  unfold unionSegments
  have bound : (xs.mergeSort segmentLe).length + (ys.mergeSort segmentLe).length ≤
      xs.length + ys.length := by
    rw [(List.mergeSort_perm xs segmentLe).length_eq, (List.mergeSort_perm ys segmentLe).length_eq]
    exact Nat.le_refl _
  rw [unionSegmentsGo_replicaBytes _ _ _ _ bound
    (List.pairwise_mergeSort segmentLe_trans segmentLe_total xs)
    (List.pairwise_mergeSort segmentLe_trans segmentLe_total ys),
    replicaBytes_mergeSort, replicaBytes_mergeSort]

/-- Exact line membership for the selected segment of a replica. When the input
    ID lists are unique, this covers all lines for that replica. -/
theorem unionSegments_mem_iff (xs ys : List SegmentData) (replica : String) (line : ByteArray) :
    line ∈ completeLines (replicaBytes (unionSegments xs ys) replica) ↔
      line ∈ completeLines (replicaBytes xs replica) ∨ line ∈ completeLines (replicaBytes ys replica) := by
  rw [unionSegments_replicaBytes, unionLines_mem_iff]

theorem unionSegments_comm (xs ys : List SegmentData) (replica : String) :
    replicaBytes (unionSegments xs ys) replica = replicaBytes (unionSegments ys xs) replica := by
  rw [unionSegments_replicaBytes, unionSegments_replicaBytes, unionLines_comm]

theorem unionSegments_idem (xs ys : List SegmentData) (replica : String) :
    replicaBytes (unionSegments (unionSegments xs ys) ys) replica =
      replicaBytes (unionSegments xs ys) replica := by
  rw [unionSegments_replicaBytes, unionSegments_replicaBytes, unionLines_idem]

end Tl.Sync
