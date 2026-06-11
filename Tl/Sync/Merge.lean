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

private def lexLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else lexLe as bs

/-- The set union of the complete lines of two segment byte streams,
    deduplicated and byte-lexicographically sorted, each line re-terminated
    with LF (ADR-0001 §5). -/
def unionLines (a b : ByteArray) : ByteArray :=
  let lines := completeLines a ++ completeLines b
  let sorted := lines.mergeSort (fun x y => lexLe x.toList y.toList)
  let uniq := sorted.eraseDups
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
