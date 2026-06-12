/-
`Tl.Sync.Local` — the local-first leg of `tl sync` (ADR-0016 §1/§6 step 2).

This is the same-machine transport: linked worktrees of one repo share
`refs/tl/log` (git keeps it in the common `.git`, like `refs/heads`), while
each keeps its own gitignored `.tl/` (own replica-id, clock, segment —
ADR-0012). So the local leg, with no remote at all, is what lets
worktree-per-agent setups see each other.

It does two things against the shared ref, both idempotent:

  1. Publish — union this replica's own segment into the ref and compare-and-set
     `update-ref`. The union is canonicalized (`Merge`), so a sync with nothing
     new is a byte-for-byte no-op detected up front (no churn commit). A lost
     CAS race (a sibling moved the ref first) re-reads and retries.
  2. Absorb — materialize the *other* replicas' segments from the ref into
     `.tl/log/` by the atomic temp-file + rename writeback (ADR-0015 §3),
     **never** the own segment (it stays the authoritative append-only file).

No mutation lock is taken (ADR-0016 §3 — the foreign-cache writeback is
lock-free; the CAS is the cross-worktree serialization). The remote
`fetch → union → push` leg (ADR-0001 §5) layers on top of these primitives and
is a separate increment. Tested I/O shell; no Mathlib.
-/
import Tl.Sync.Merge
import Tl.Sync.Ref
import Tl.Store.Local
import Tl.Format.Crockford

namespace Tl.Sync

open Tl.Store
open Tl.Format

/-- What a local-leg reconcile did, for the command echo and the tests. -/
structure LocalOutcome where
  /-- Did the leg run? (False outside a git repo — no shared ref transport.) -/
  ran : Bool
  /-- Did this replica's own ops actually move the ref? -/
  published : Bool
  /-- The sibling replica ids whose local cache was (re)materialized. -/
  absorbed : List String
  /-- The resulting `refs/tl/log` tip (`none` only when `ran` is false). -/
  tip : Option String
deriving Repr, Inhabited

/-- A replica's segment bytes within a list (absent → empty). -/
def segBytesOf (segs : List SegmentData) (rid : String) : ByteArray :=
  ((segs.find? (·.replicaId == rid)).map (·.bytes)).getD ByteArray.empty

/-- Do two segment sets carry byte-identical content per replica id? The union
    is canonicalized (`Merge`), so equal line-sets are equal bytes — this makes
    "nothing to publish" an exact, cheap check rather than a fold comparison. -/
def segsEquiv (a b : List SegmentData) : Bool :=
  let ids := (a.map (·.replicaId) ++ b.map (·.replicaId)).eraseDups
  ids.all (fun rid => segBytesOf a rid == segBytesOf b rid)

/-- Materialize a foreign replica's segment into `.tl/log/<rid>.jsonl` by an
    atomic temp-file + rename (ADR-0015 §3, ADR-0016 §1). The caller guarantees
    `replicaId` is not the own replica. The temp name carries CSPRNG bytes so
    concurrent lock-free refreshes (ADR-0016 §3) never collide on a temp path;
    the log dir is created no-follow first, the temp open is no-follow, and the
    `rename` replaces the target name atomically (raw bytes, never a lossy
    String round-trip — a foreign segment may not be valid UTF-8). -/
def writeForeignSegment (d : Dirs) (replicaId : String) (bytes : ByteArray) : TlM Unit := do
  liftSys (mapSysError d.relLog) (Sys.mkdirNoFollow d.base d.relLog)
  let entropy ← liftSys (fun e => .mk' .internal s!"entropy unavailable: {e}") (Sys.entropy 8)
  let rel := d.relSegment replicaId
  let tmpRel := rel ++ "." ++ toCrockford (Sys.natOfBytesBE entropy) 13 ++ ".tmp"
  liftSys (mapSysError tmpRel) do
    let fd ← Sys.openNoFollow d.base tmpRel
      (Sys.flagCreate ||| Sys.flagWrite ||| Sys.flagTruncate)
    try
      Sys.writeAll fd bytes
      Sys.sync fd
    finally
      Sys.close fd
  liftSys (mapSysError rel) (IO.FS.rename (d.absOf tmpRel) (d.absOf rel))

/-- Write every segment of `final` that is NOT this replica's own and whose
    on-disk copy differs into `.tl/log/`. Returns the (re)materialized ids. -/
private def absorbForeign (d : Dirs) (ownReplica : Option String)
    (localSegs final : List SegmentData) : TlM (List String) := do
  let mut absorbed : List String := []
  for s in final do
    let onDisk := localSegs.find? (·.replicaId == s.replicaId)
    -- write a FOREIGN segment whose on-disk copy differs. When our own replica
    -- id is unknown (the `.tl/local/replica` file was removed), we cannot prove
    -- a given on-disk segment is not our own authoritative one, so we only
    -- CREATE absent segments — never clobber an existing file. That protects
    -- unpublished own ops from being overwritten by the ref's older copy.
    let mayWrite := match ownReplica with
      | some own => s.replicaId != own
      | none => onDisk.isNone
    if mayWrite && (onDisk.map (·.bytes)).getD ByteArray.empty != s.bytes then
      writeForeignSegment d s.replicaId s.bytes
      absorbed := absorbed ++ [s.replicaId]
  return absorbed

/-- Record the reconciled tip in the read-time refresh marker, best-effort: a
    marker-write failure must never fail an otherwise-successful sync (the next
    read just re-materializes). Keeps a read right after `tl sync` on the fast
    path instead of re-reading the ref it already reconciled. -/
private def markTip (d : Dirs) : Option String → TlM Unit
  | some t => try storeRefMark d t catch _ => pure ()
  | none => pure ()

/-- The bounded CAS-retry: a sibling that moves the ref between our read and
    our `update-ref` costs one re-read, never a clobber. Same-machine worktree
    contention is brief, so the cap only guards a pathological live-lock. -/
private def maxAttempts : Nat := 8

private def reconcile (d : Dirs) (ownReplica : Option String)
    (localSegs : List SegmentData) : Nat → TlM LocalOutcome
  | 0 => throw (.mk' .internal
      "sync: refs/tl/log kept moving under concurrent writers — retry `tl sync`")
  | fuel + 1 => do
    let tip ← refTip d
    let refSegs ← readRef d
    let merged := unionSegments refSegs localSegs
    -- publish only our own ops, and only when they change the ref (a worktree
    -- with no own writes never re-sorts a sibling's segment into a churn commit)
    let publish := ownReplica.isSome && !segsEquiv merged refSegs
    if publish then
      match ← writeRefCas d merged tip with
      | none => reconcile d ownReplica localSegs fuel  -- lost the CAS race: retry
      | some newTip =>
        let absorbed ← absorbForeign d ownReplica localSegs merged
        markTip d (some newTip)
        return { ran := true, published := true, absorbed, tip := some newTip }
    else
      -- `merged`'s foreign content equals the ref's (the local cache is a
      -- subset of the canonicalized ref), so we can absorb without writing it
      let absorbed ← absorbForeign d ownReplica localSegs merged
      markTip d tip
      return { ran := true, published := false, absorbed, tip }

/-- The local leg: reconcile against `refs/tl/log` (publish own, absorb
    siblings). A no-op `ran := false` outside a git repo — there is no shared
    ref to reconcile against, and the remote leg reports `no-upstream`. -/
def syncLocal (d : Dirs) (ownReplica : Option String) : TlM LocalOutcome := do
  if !(← inGitRepo d) then
    return { ran := false, published := false, absorbed := [], tip := none }
  let (localSegs, _) ← readSegments d
  reconcile d ownReplica localSegs maxAttempts

/-! ## Read-time refresh (ADR-0016 §3) -/

/-- What a read-time refresh did, for the read echo and the tests. -/
structure RefreshOutcome where
  /-- Did the ref move since last time, prompting a materialize? -/
  refreshed : Bool
  /-- The foreign replica ids (re)materialized this refresh. -/
  absorbed : List String
  /-- The ref OID now reflected in `.tl/log/` (`none` when there is no ref). -/
  tip : Option String
  /-- Set when the refresh could not run (no git, read-only FS, a racing
      refresher): the read still succeeds — a moment stale — and this carries
      the reason for callers that want to surface it. -/
  degraded : Option String
deriving Repr, Inhabited

private def refreshBody (d : Dirs) (ownReplica : Option String) : TlM RefreshOutcome := do
  match ← refTip d with  -- the O(1) trigger: one `rev-parse`, no object store
  | none => return { refreshed := false, absorbed := [], tip := none, degraded := none }
  | some tip =>
    if (← loadRefMark d) == some tip then
      -- unchanged (the common case): fold the local files, git untouched
      return { refreshed := false, absorbed := [], tip := some tip, degraded := none }
    -- the ref moved: materialize the changed foreign segments, record the OID
    let refSegs ← readRef d
    let (localSegs, _) ← readSegments d
    let absorbed ← absorbForeign d ownReplica localSegs refSegs
    storeRefMark d tip
    return { refreshed := true, absorbed, tip := some tip, degraded := none }

/-- Read-time refresh: before a read folds `.tl/log/`, cheaply detect whether a
    sibling published to the shared `refs/tl/log` (an O(1) OID compare against
    the `ref-mark`) and, only if it moved, materialize the changed foreign
    segments into `.tl/log/` (the atomic-rename writeback, never the own
    segment). So a worktree sees its siblings without an explicit `tl sync`,
    while git stays off the steady-state read path (an unchanged ref costs one
    `rev-parse` + one small file read).

    Entirely best-effort and lock-free: ANY failure — git absent, a read-only
    filesystem, a concurrent refresher — degrades to "fold what is on disk"
    and never fails the read (ADR-0016 §3). It catches both thrown `Tl.Error`s
    and raw `IO.Error`s for that reason. A genuine path-safety / corruption
    problem is not hidden: the subsequent `readState` fold re-encounters and
    surfaces it through the normal read policy. -/
def refreshFromRef (d : Dirs) (ownReplica : Option String) : TlM RefreshOutcome := do
  match ← ((refreshBody d ownReplica).run.toBaseIO : IO _) with
  | .ok (.ok o) => return o
  | .ok (.error e) =>
    return { refreshed := false, absorbed := [], tip := none, degraded := some e.message }
  | .error ioErr =>
    return { refreshed := false, absorbed := [], tip := none, degraded := some (toString ioErr) }

end Tl.Sync
