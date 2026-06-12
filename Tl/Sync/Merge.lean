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

private def lexLeBytes (a b : ByteArray) : Bool := lexLeBytesAux a b 0 (a.size + 1)

/-- Adjacent dedup — on a sorted list duplicates are adjacent, so this equals
    `eraseDups` (which rescans its accumulator per element, Θ(L²)) and stays
    linear. -/
private def dedupAdjacentGo (prev : ByteArray) : List ByteArray → List ByteArray
  | [] => [prev]
  | x :: xs => if prev == x then dedupAdjacentGo prev xs else prev :: dedupAdjacentGo x xs

private def dedupAdjacent : List ByteArray → List ByteArray
  | [] => []
  | x :: xs => dedupAdjacentGo x xs

/-- The set union of the complete lines of two segment byte streams,
    deduplicated and byte-lexicographically sorted, each line re-terminated
    with LF (ADR-0001 §5). The output bytes are pinned by tests: the
    canonicalized form must not move (it is what makes a re-sync build no
    churn commit). -/
def unionLines (a b : ByteArray) : ByteArray :=
  let lines := completeLines a ++ completeLines b
  let sorted := lines.mergeSort lexLeBytes
  let uniq := dedupAdjacent sorted
  uniq.foldl (fun acc l => acc ++ l ++ "\n".toUTF8) ByteArray.empty

/-- Union two sets of per-replica segments (ADR-0001 §5): each replica id
    present on either side yields one segment whose bytes are the line-union
    of that replica's copies (an absent side contributes nothing). Replica
    ids are sorted for a deterministic result. -/
def unionSegments (xs ys : List SegmentData) : List SegmentData :=
  let ids := (xs.map (·.replicaId) ++ ys.map (·.replicaId)).eraseDups.mergeSort (· ≤ ·)
  ids.map (fun rid =>
    let xb := ((xs.find? (·.replicaId == rid)).map (·.bytes)).getD ByteArray.empty
    let yb := ((ys.find? (·.replicaId == rid)).map (·.bytes)).getD ByteArray.empty
    { replicaId := rid, bytes := unionLines xb yb })

end Tl.Sync
