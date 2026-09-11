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
     CAS race (a sibling moved the ref first) re-reads and retries. Tree
     entries the transport does not recognize are re-emitted verbatim into
     the published commit (ADR-0008 transport preserve-unknown) — never
     dropped, never a publish trigger by themselves.
  2. Absorb — materialize the *other* replicas' segments from the ref into
     `.tl/log/` by the atomic temp-file + rename writeback (ADR-0015 §3),
     never rename over the own segment. Missing same-replica lines from a
     copied working directory are recovered by a locked append.

The ordinary unique-replica path takes no mutation lock. Same-replica recovery
uses the mutation lock to reread and append; foreign-cache writeback stays
lock-free, and CAS is the cross-worktree serialization. The remote
`fetch → union → push` leg (ADR-0001 §5) layers on top of these primitives and
is a separate increment. Tested I/O shell; no Mathlib.
-/
import Tl.Sync.Merge
import Tl.Sync.Recovery
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
  /-- Replica ids whose bytes changed through foreign writeback or own recovery. -/
  absorbed : List String
  /-- The resulting `refs/tl/log` tip. `none` when `ran` is false, or when
      the ref does not exist yet and this run published nothing into it —
      nothing new to publish, or no readable local replica to publish from
      (the no-publish reconcile path). -/
  tip : Option String
deriving Repr, Inhabited

/-- A linear walk of two replica-id-sorted segment lists: equal iff every
    replica id carries byte-identical content, where an absent id and a
    present-but-empty one are equal (an empty segment is no content — the
    previous `segBytesOf` defaulted an absent id to `ByteArray.empty`). Fuel is
    `|a| + |b|`; the zero arm is dead. -/
private def segsEquivGo : Nat → List SegmentData → List SegmentData → Bool
  | _, [], ys => ys.all (·.bytes == ByteArray.empty)
  | _, x :: xs, [] => (x :: xs).all (·.bytes == ByteArray.empty)
  | 0, _ :: _, _ :: _ => true
  | fuel + 1, x :: xs, y :: ys =>
    if x.replicaId == y.replicaId then (x.bytes == y.bytes) && segsEquivGo fuel xs ys
    else if decide (x.replicaId ≤ y.replicaId) then
      (x.bytes == ByteArray.empty) && segsEquivGo fuel xs (y :: ys)
    else (y.bytes == ByteArray.empty) && segsEquivGo fuel (x :: xs) ys

/-- Do two segment sets carry byte-identical content per replica id? The union
    is canonicalized (`Merge`), so equal line-sets are equal bytes — this makes
    "nothing to publish" an exact, cheap check rather than a fold comparison.
    Sort each side by replica id once, then walk in lockstep — O(S log S),
    where the previous shape paid `eraseDups` plus a `find?` per id (Θ(S²)). -/
def segsEquiv (a b : List SegmentData) : Bool :=
  let le := fun (x y : SegmentData) => decide (x.replicaId ≤ y.replicaId)
  segsEquivGo (a.length + b.length) (a.mergeSort le) (b.mergeSort le)

/-- Materialize a foreign replica's segment into `.tl/log/<rid>.jsonl` by an
    atomic temp-file + rename (ADR-0015 §3, ADR-0016 §1). The caller guarantees
    `replicaId` is not the own replica. The temp name carries CSPRNG bytes so
    concurrent lock-free refreshes (ADR-0016 §3) never collide on a temp path;
    the log dir is created no-follow first, the temp open is no-follow, and the
    `rename` replaces the target name atomically (raw bytes, never a lossy
    String round-trip — a foreign segment may not be valid UTF-8). -/
def writeForeignSegment (d : Dirs) (replicaId : String) (bytes : ByteArray)
    (syncMechanism : Sys.SyncMechanism := Sys.sync) : TlM Unit := do
  liftSys (mapSysError d.relLog) (Sys.mkdirNoFollow d.base d.relLog)
  let entropy ← liftSys (fun e => .mk' .internal s!"entropy unavailable: {e}") (Sys.entropy 8)
  let rel := d.relSegment replicaId
  let tmpRel := rel ++ "." ++ toCrockford (Sys.natOfBytesBE entropy) 13 ++ ".tmp"
  let fd ← liftSys (mapSysError tmpRel) (Sys.openNoFollow d.base tmpRel
    (Sys.flagCreate ||| Sys.flagWrite ||| Sys.flagTruncate))
  try
    liftSys (mapSysError tmpRel) do
      try
        Sys.writeAll fd bytes
        Sys.syncBestEffortWith syncMechanism fd
      finally
        Sys.close fd
  catch e =>
    let _ ← (IO.FS.removeFile (d.absOf tmpRel)).toBaseIO
    throw e
  match ← (IO.FS.rename (d.absOf tmpRel) (d.absOf rel)).toBaseIO with
  | .ok _ => return ()
  | .error e =>
    let _ ← (IO.FS.removeFile (d.absOf tmpRel)).toBaseIO
    throw (mapSysError rel e)

/-- Materialize received segments: foreign files use atomic replace; an own
    segment uses locked append recovery. Unknown identity still forbids replacing
    existing files. Returns the ids whose local bytes changed. -/
private def absorbForeign (d : Dirs) (ownReplica : Option String)
    (localSegs final : List SegmentData) : TlM (List String) := do
  let diskIndex := localSegs.foldl (fun index s => index.insert s.replicaId s.bytes)
    ({} : Std.HashMap String ByteArray)
  let mut absorbed : List String := []
  for s in final do
    let onDisk := diskIndex[s.replicaId]?
    -- write a foreign segment whose on-disk copy differs. When our own replica
    -- id is unknown (the `.tl/local/replica` file was removed), we cannot prove
    -- a given on-disk segment is not our own authoritative one, so we only
    -- create absent segments — never clobber an existing file. That protects
    -- unpublished own ops from being overwritten by the ref's older copy.
    let mayWrite := match ownReplica with
      | some own => s.replicaId != own
      | none => onDisk.isNone
    if ownReplica == some s.replicaId then
      if ← recoverOwnSegment d s.replicaId s.bytes then
        absorbed := s.replicaId :: absorbed
    else if mayWrite && onDisk.getD ByteArray.empty != s.bytes then
      writeForeignSegment d s.replicaId s.bytes
      absorbed := s.replicaId :: absorbed
  return absorbed.reverse

/-- Record the reconciled tip in the read-time refresh marker, best-effort: a
    marker-write failure must never fail an otherwise-successful sync (the next
    read just re-materializes). Keeps a read right after `tl sync` on the fast
    path instead of re-reading the ref it already reconciled. -/
private def markTip (d : Dirs) : Option String → TlM Unit
  | some t => try storeRefMark d t catch _ => pure ()
  | none => pure ()

/-- The own segment's bytes within `localSegs` (empty if this replica has not
    written yet, or the own replica id is unknown). -/
private def ownBytesOf (ownReplica : Option String) (localSegs : List SegmentData) : ByteArray :=
  match ownReplica with
  | some own => ((localSegs.find? (·.replicaId == own)).map (·.bytes)).getD ByteArray.empty
  | none => ByteArray.empty

/-- Record the publish marker after a reconcile that left our own segment in
    `tip` (best-effort, and only with a known own replica + an existing ref — a
    marker against `none` would never match a future `refTip`). -/
private def markPub (d : Dirs) (ownReplica : Option String) (localSegs : List SegmentData) :
    Option String → TlM Unit
  | some t =>
    match ownReplica with
    | some _ => try storeSyncPub d t (ownBytesOf ownReplica localSegs) catch _ => pure ()
    | none => pure ()
  | none => pure ()

/-- The bounded CAS-retry: a sibling that moves the ref between our read and
    our `update-ref` costs one re-read, never a clobber. Same-machine worktree
    contention is brief, so the cap only guards a pathological live-lock. -/
private def maxAttempts : Nat := 8

/-- `beforeCas` runs immediately before each publish's compare-and-set; it is
    a parameter only so a test can deterministically *lose* the CAS (moving
    the ref like a racing sibling between the read and the `update-ref`) and
    pin the retry's re-read. Production callers omit it. -/
private def reconcile (d : Dirs) (ownReplica : Option String)
    (localSegs : List SegmentData) (beforeCas : TlM Unit) : Nat → TlM LocalOutcome
  | 0 => throw (.mk' .internal
      "sync: refs/tl/log kept moving under concurrent writers — retry `tl sync`")
  | fuel + 1 => do
    let pinned ← pinLogRef d
    let tip := pinned.map (·.oid)
    -- Publish-marker fast-out (ADR-0023 write-path analogue of the fold cache):
    -- if the ref still sits at the OID our own segment is published into, and the
    -- own segment is byte-identical to then, nothing publishes and the absorbed
    -- siblings are already current — return without the readRef + whole-log
    -- union the publish check would otherwise pay on every write. The marker is
    -- written only after the own segment is in the tip (`markPub`), so a match
    -- provably means "already published" — never a skipped publish. The outcome
    -- equals the no-publish branch below (published := false, nothing absorbed).
    let ownBytes := ownBytesOf ownReplica localSegs
    if ownReplica.isSome then
      if let some (mTip, mLen, mHash) ← loadSyncPub d then
        if tip == some mTip && ownBytes.size == mLen && ByteArray.hash ownBytes == mHash then
          return { ran := true, published := false, absorbed := [], tip }
    let (refSegs, refForeign) ← readPinnedEntries? d pinned
    let merged := unionSegments refSegs localSegs
    -- publish only our own ops, and only when they change the ref (a worktree
    -- with no own writes never re-sorts a sibling's segment into a churn
    -- commit; a carried-unknown entry rides every commit built but never
    -- prompts one — ADR-0008 transport preserve-unknown)
    let publish := ownReplica.isSome && !segsEquiv merged refSegs
    if publish then
      beforeCas
      match ← writeRefCas d merged refForeign tip with
      | none => reconcile d ownReplica localSegs beforeCas fuel  -- lost the CAS race: retry
      | some newTip =>
        let absorbed ← absorbForeign d ownReplica localSegs merged
        markTip d (some newTip)
        markPub d ownReplica localSegs (some newTip)
        return { ran := true, published := true, absorbed, tip := some newTip }
    else
      -- `merged`'s foreign content equals the ref's (the local cache is a
      -- subset of the canonicalized ref), so we can absorb without writing it
      let absorbed ← absorbForeign d ownReplica localSegs merged
      markTip d tip
      -- own's content is in `tip` (no divergence ⇒ no publish), so record the
      -- marker for the next fast-out (no-op when `tip` is none — no ref yet)
      markPub d ownReplica localSegs tip
      return { ran := true, published := false, absorbed, tip }

/-- The local leg: reconcile against `refs/tl/log` (publish own, absorb
    siblings). A no-op `ran := false` outside a git repo — there is no shared
    ref to reconcile against, and the remote leg reports `no-upstream`.
    `beforeCas` is the test-only CAS-race seam (see `reconcile`); production
    callers omit it. -/
def syncLocal (d : Dirs) (ownReplica : Option String)
    (beforeCas : TlM Unit := pure ()) : TlM LocalOutcome := do
  if !(← inGitRepo d) then
    return { ran := false, published := false, absorbed := [], tip := none }
  let (localSegs, _) ← readSegments d
  reconcile d ownReplica localSegs beforeCas maxAttempts

/-! ## Read-time refresh (ADR-0016 §3) -/

/-- What a read-time refresh did, for the read echo and the tests. -/
structure RefreshOutcome where
  /-- Did the ref move since last time, prompting a materialize? -/
  refreshed : Bool
  /-- Replica ids changed by foreign writeback or own append recovery. -/
  absorbed : List String
  /-- The ref OID now reflected in `.tl/log/` (`none` when there is no ref). -/
  tip : Option String
  /-- Set when the refresh could not run (no git, read-only FS, a racing
      refresher): the read still succeeds — a moment stale — and this carries
      the reason for callers that want to surface it. -/
  degraded : Option String
deriving Repr, Inhabited

private def refreshBody (d : Dirs) (ownReplica : Option String) : TlM RefreshOutcome := do
  let captured ← try pinLogRef d catch e => do
    if ← inGitRepo d then throw e else pure none
  match captured with  -- the O(1) trigger: one `rev-parse`, no object store
  | none => return { refreshed := false, absorbed := [], tip := none, degraded := none }
  | some pinned =>
    let tip := pinned.oid
    if (← loadRefMark d) == some tip then
      -- unchanged (the common case): fold the local files, git untouched
      return { refreshed := false, absorbed := [], tip := some tip, degraded := none }
    -- the ref moved: materialize the changed foreign segments, record the OID
    let (refSegs, _) ← readPinnedEntries d pinned
    let (localSegs, _) ← readSegments d
    let absorbed ← absorbForeign d ownReplica localSegs refSegs
    storeRefMark d tip
    return { refreshed := true, absorbed, tip := some tip, degraded := none }

/-- Read-time refresh: before a read folds `.tl/log/`, cheaply detect whether a
    sibling published to the shared `refs/tl/log` (an O(1) OID compare against
    the `ref-mark`) and, only if it moved, materialize the changed foreign
    segments into `.tl/log/` (atomic foreign replace or locked own append). So a worktree sees its siblings without an explicit `tl sync`,
    while git stays off the steady-state read path (an unchanged ref costs one
    `rev-parse` + one small file read).

    Best-effort, with a lock only for same-replica recovery: any failure — git absent, a read-only
    filesystem, a concurrent refresher — degrades to "fold what is on disk"
    and never fails the read (ADR-0016 §3). It catches both thrown `Tl.Error`s
    and raw `IO.Error`s for that reason. A genuine path-safety / corruption
    problem is not hidden: the subsequent `readState` fold re-encounters and
    surfaces it through the normal read policy. -/
def refreshFromRef (d : Dirs) (ownReplica : Option String) : TlM RefreshOutcome := do
  -- stealth (ADR-0001 §7): a single local replica that is never shared — so it
  -- neither publishes nor absorbs. Skip the ref entirely (no `rev-parse`, no
  -- foreign-segment writeback): a clean no-op, not a degraded read.
  if ← isStealth d then
    return { refreshed := false, absorbed := [], tip := none, degraded := none }
  match ← ((refreshBody d ownReplica).run.toBaseIO : IO _) with
  | .ok (.ok o) => return o
  | .ok (.error e) =>
    return { refreshed := false, absorbed := [], tip := none, degraded := some e.message }
  | .error ioErr =>
    return { refreshed := false, absorbed := [], tip := none, degraded := some (toString ioErr) }

end Tl.Sync
