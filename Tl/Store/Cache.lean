/-
`Tl.Store.Cache` — the materialization fold cache (ADR-0022; vision §Scale
target: "an automatic, self-validating cache in gitignored `.tl/local/`,
keyed to log content; rebuilt from scratch if stale/absent — never a
user-managed command").

What is cached is ONLY the kernel fold — the quadratic part of a read. Every
other `Loaded` field (`ops`, refusals, skips, deferrals, HLC maxima,
warnings) is recomputed from the live line decode on every invocation, so
the cache can never change what a command *reports*, only how the state it
reports *about* is computed.

Validity is per segment, against the live bytes and the live decode:

* the live segment must still carry the cached prefix byte-for-byte
  (length extends, the prefix checksum matches) — appends keep a cache
  warm, any rewrite (repair, a reordering ref absorb) forces a rebuild;
* the refusal flag must match: parse/refusal classification is a pure
  function of the bytes, but a bad line APPENDED to a clean segment refuses
  the whole segment — a fresh fold then drops the prefix ops the cache
  still holds, so the flag divergence must invalidate;
* every line deferred now (within the prefix) must have been deferred at
  snapshot time: deferral is monotone in `now` (ADR-0007), so the normal
  drift is deferred-then, admissible-now — those lines fold on top
  (`fold_append` + order-insensitivity); the reverse direction (a clock
  that went backwards) invalidates.

A cached segment missing live, or a shrunk prefix, fails the check; a live
segment the cache has never seen contributes all its ops as suffix. Anything
invalid → full refold of the live decode, and the refreshed cache is written
back (atomic replace, best-effort — a read-only filesystem never fails a
read). `--skip-bad` folds are different folds (skipped lines are absent):
they neither consult nor produce the cache.

The file is a non-crypto checksum line (core's `ByteArray.hash`, `ckOf`) over a
payload line: the values the fold trusts (the state, line counts, deferral sets)
are integrity-checked before any of them is believed, so bit rot anywhere in the
file is a rebuild, never a silently wrong read — the cache stays the discardable
one. The checksum is a rot/content check, NOT a security digest: deliberate
tampering inside `.tl/` is the segments' trust domain (ADR-0014), so a 64-bit
non-crypto hash suffices here (a faster choice than the pure-Lean SHA-256 this
replaced; ADR-0022/0023/0024). `cacheVersion` is a *semantics* version, not just a format
version: any change to per-line classification (`decodeLine`, the owner
check), to `WireOp.toOp`, or to kernel `apply`/`merge` semantics must bump
it, or a binary-version skew on one working copy could suffix-fold
new-semantics ops onto an old-semantics cached state.

Tested-shell tier (ADR-0004): codec round-trip, every validity branch, and
the property test pinning `materializeCached` = `materialize` live in
`Tests/CacheTests.lean`.
-/
import Tl.Store.Materialize
import Tl.Store.Local
import Tl.Kernel.FoldFast

namespace Tl.Store

open Tl.Crdt
open Tl.Kernel
open Tl.Format
open Lean (Json)

/-- The cache version — local-only (never synced, no log `v` impact); a
    mismatch just forces a rebuild, so it moves freely. It versions the
    *semantics*, not only the bytes: bump it for any change to per-line
    classification, `WireOp.toOp`, or kernel `apply`/`merge` (see the module
    header). -/
def cacheVersion : Nat := 2

/-- One segment's content key at snapshot time. -/
structure CacheSegMeta where
  replicaId : String
  /-- Byte length when the cache was written — live bytes must extend it. -/
  byteLen : Nat
  /-- Complete lines when the cache was written — the fold-membership
      boundary (a torn trailing fragment is not a line). -/
  lineCount : Nat
  /-- Non-crypto rot-check (decimal `ByteArray.hash`) of the first `byteLen`
      bytes — a content key, not a security digest (see `ckOf`). -/
  ck : String
  /-- Whether the segment was refused — a refused segment contributed
      nothing to the cached state. -/
  refused : Bool
  /-- Skew-deferred line numbers at snapshot time — the prefix lines the
      cached state did NOT fold. -/
  deferred : List Nat
deriving BEq, Repr

/-- The persisted cache: the folded state plus the exact per-segment content
    keys it folded. -/
structure FoldCache where
  segments : List CacheSegMeta
  state : State

/-! ## Codec — `State` to/from one compressed JSON line

Decode is fail-closed to `none` (= rebuild): every list that backs a
canonical `AMap` is re-checked strictly ascending (`AMap.ofAscList?`), so a
decoded state is canonical by construction — `ascending_of_sorted`
guarantees an encode is never rejected. Stamps reuse the wire add-tag
encoding (`tagOfStamp`/`stampOfTag`, ADR-0008), already canonical and
order-preserving. -/

private def jnum (n : Nat) : Json := Json.num ⟨Int.ofNat n, 0⟩

private def encStamp (st : Stamp) : Json := Json.str (tagOfStamp st)

private def decStamp (j : Json) : Option Stamp := do
  let s ← j.getStr?.toOption
  (stampOfTag s).toOption

private def decStr (j : Json) : Option String := j.getStr?.toOption

private def encAMap {K V : Type} [TotalOrd K] (encK : K → Json) (encV : V → Json)
    (m : AMap K V) : Json :=
  Json.arr (m.toList.map (fun p => Json.arr #[encK p.1, encV p.2])).toArray

private def decAMap {K V : Type} [TotalOrd K] (decK : Json → Option K)
    (decV : Json → Option V) : Json → Option (AMap K V)
  | Json.arr a => do
    let entries ← a.toList.mapM (fun e =>
      match e with
      | Json.arr pe =>
        match pe.toList with
        | [ek, ev] => do
          let k ← decK ek
          let v ← decV ev
          some (k, v)
        | _ => none
      | _ => none)
    AMap.ofAscList? entries
  | _ => none

private def encFinSet (s : FinSet Stamp) : Json :=
  Json.arr (s.toList.map (fun p => encStamp p.1)).toArray

private def decFinSet (j : Json) : Option (FinSet Stamp) :=
  match j with
  | Json.arr a => do
    let stamps ← a.toList.mapM decStamp
    AMap.ofAscList? (stamps.map (fun st => (st, ())))
  | _ => none

private def encOrSet {α : Type} [TotalOrd α] (encEl : α → Json) (s : OrSet α) : Json :=
  Json.mkObj [("a", encAMap encEl encFinSet s.adds), ("r", encFinSet s.removed)]

private def decOrSet {α : Type} [TotalOrd α] (decEl : Json → Option α) (j : Json) :
    Option (OrSet α) := do
  let adds ← decAMap decEl decFinSet (← (j.getObjVal? "a").toOption)
  let removed ← decFinSet (← (j.getObjVal? "r").toOption)
  some ⟨adds, removed⟩

private def encReg {V : Type} (encV : V → Json) : Reg V → Json
  | none => Json.null
  | some (st, v) => Json.arr #[encStamp st, encV v]

private def decReg {V : Type} (decV : Json → Option V) : Json → Option (Reg V)
  | Json.null => some none
  | Json.arr pe =>
    match pe.toList with
    | [es, ev] => do
      let st ← decStamp es
      let v ← decV ev
      some (some (st, v))
    | _ => none
  | _ => none

private def encOptStr : Option String → Json
  | none => Json.null
  | some s => Json.str s

private def decOptStr : Json → Option (Option String)
  | Json.null => some none
  | Json.str s => some (some s)
  | _ => none

private def encOptNat : Option Nat → Json
  | none => Json.null
  | some n => jnum n

private def decOptNat (j : Json) : Option (Option Nat) :=
  match j with
  | Json.null => some none
  | _ => (j.getNat?.toOption).map some

private def decStatus (j : Json) : Option Status := do
  match ← j.getNat?.toOption with
  | 0 => some .Open
  | 1 => some .InProgress
  | 2 => some .Done
  | 3 => some .Cancelled
  | _ => none

private def encOptCloseRes : Option CloseResolution → Json
  | none => Json.null
  | some r => jnum r.toNat

private def decOptCloseRes (j : Json) : Option (Option CloseResolution) :=
  match j with
  | Json.null => some none
  | _ =>
    match j.getNat?.toOption with
    | some 0 => some (some .Done)
    | some 1 => some (some .Cancelled)
    | some 2 => some (some .Duplicate)
    | _ => none

private def decFin5 (j : Json) : Option (Fin 5) := do
  let n ← j.getNat?.toOption
  if h : n < 5 then some ⟨n, h⟩ else none

private def encEdge (e : Edge) : Json :=
  let (f, t, k) := e
  Json.arr #[Json.str f, Json.str t, jnum k.toNat]

private def decEdge (j : Json) : Option Edge :=
  match j with
  | Json.arr a =>
    match a.toList with
    | [f, t, k] => do
      let f ← f.getStr?.toOption
      let t ← t.getStr?.toOption
      let kind ← match ← k.getNat?.toOption with
        | 0 => some EdgeKind.Blocks
        | 1 => some EdgeKind.Parent
        | 2 => some EdgeKind.Related
        | _ => none
      some (f, t, kind)
    | _ => none
  | _ => none

private def encIssueData (d : IssueData) : Json :=
  Json.mkObj [
    ("title", encReg Json.str d.title),
    ("status", encReg (fun s => jnum s.toNat) d.status),
    ("prio", encReg (fun (p : Fin 5) => jnum p.val) d.priority),
    ("assignee", encReg encOptStr d.assignee),
    ("desc", encReg encOptStr d.description),
    ("notes", encReg encOptStr d.notes),
    ("slug", encReg encOptStr d.slug),
    ("defer", encReg encOptNat d.deferUntil),
    ("close", encReg encOptCloseRes d.closeResolution),
    ("labels", encOrSet Json.str d.labels),
    ("meta", encAMap Json.str (encReg encOptStr) d.metadata)]

private def decIssueData (j : Json) : Option IssueData := do
  let title ← decReg decStr (← (j.getObjVal? "title").toOption)
  let status ← decReg decStatus (← (j.getObjVal? "status").toOption)
  let priority ← decReg decFin5 (← (j.getObjVal? "prio").toOption)
  let assignee ← decReg decOptStr (← (j.getObjVal? "assignee").toOption)
  let description ← decReg decOptStr (← (j.getObjVal? "desc").toOption)
  let notes ← decReg decOptStr (← (j.getObjVal? "notes").toOption)
  let slug ← decReg decOptStr (← (j.getObjVal? "slug").toOption)
  let deferUntil ← decReg decOptNat (← (j.getObjVal? "defer").toOption)
  let closeResolution ← decReg decOptCloseRes (← (j.getObjVal? "close").toOption)
  let labels ← decOrSet decStr (← (j.getObjVal? "labels").toOption)
  let metadata ← decAMap decStr (decReg decOptStr) (← (j.getObjVal? "meta").toOption)
  some { title, status, priority, assignee, description, notes, slug,
         deferUntil, closeResolution, labels, metadata }

private def encState (s : State) : Json :=
  Json.mkObj [
    ("issues", encOrSet Json.str s.issues),
    ("data", encAMap Json.str encIssueData s.data),
    ("edges", encOrSet encEdge s.edges)]

private def decState (j : Json) : Option State := do
  let issues ← decOrSet decStr (← (j.getObjVal? "issues").toOption)
  let data ← decAMap decStr decIssueData (← (j.getObjVal? "data").toOption)
  let edges ← decOrSet decEdge (← (j.getObjVal? "edges").toOption)
  some ⟨issues, data, edges⟩

/-- A stable, version-INDEPENDENT digest of a materialized `State` under the
    cache codec (`encState`). The cacheVersion-bump guard (Tests.CacheTests)
    pins this against the current `cacheVersion`: any change to the fold
    semantics (`decodeSegment` / the owner check / `WireOp.toOp` / kernel
    `apply`/`merge`) or to the cache codec moves the digest, so the ADR-0022 §3
    obligation to bump `cacheVersion` on a semantics change becomes a failing
    test rather than reviewer memory. Version-independent on purpose, so the
    guard can tell an unbumped semantics drift from an honest bump. -/
def stateFoldDigest (s : State) : String :=
  toString (ByteArray.hash (encState s).compress.toUTF8)

private def encSegMeta (m : CacheSegMeta) : Json :=
  Json.mkObj [
    ("replica", Json.str m.replicaId),
    ("bytes", jnum m.byteLen),
    ("lines", jnum m.lineCount),
    ("ck", Json.str m.ck),
    ("refused", Json.bool m.refused),
    ("deferred", Json.arr (m.deferred.map jnum).toArray)]

private def decSegMeta (j : Json) : Option CacheSegMeta := do
  let replicaId ← (← (j.getObjVal? "replica").toOption).getStr?.toOption
  let byteLen ← (← (j.getObjVal? "bytes").toOption).getNat?.toOption
  let lineCount ← (← (j.getObjVal? "lines").toOption).getNat?.toOption
  let ck ← (← (j.getObjVal? "ck").toOption).getStr?.toOption
  let refused ← (← (j.getObjVal? "refused").toOption).getBool?.toOption
  let deferred ← match ← (j.getObjVal? "deferred").toOption with
    | Json.arr a => a.toList.mapM (fun e => e.getNat?.toOption)
    | _ => none
  some { replicaId, byteLen, lineCount, ck, refused, deferred }

/-- A fast non-crypto rot-check over the cached bytes. The cache is the
    discardable, content-keyed artifact (ADR-0022), NOT a security surface —
    deliberate tampering inside `.tl/` is the segments' trust domain
    (ADR-0014) — so collision-resistance is not required: a 64-bit hash
    detects bit rot and prefix changes, and core's `ByteArray.hash` is a fast
    extern over raw bytes (this was a pure-Lean SHA-256, ≈25× slower at the
    cache's sizes; ADR-0023/0024). -/
private def ckOf (b : ByteArray) : String := toString (ByteArray.hash b)

/-- Encode the cache: a non-crypto checksum line (`ckOf`) over the compressed JSON
    payload line. The checksum is what makes "corrupt ⇒ rebuild" hold for *value*
    corruption too (a flipped digit in a line count or a state string is not a
    JSON shape error — only the checksum catches it).

    Load-bearing invariant: `Json.compress` emits a single line — newlines
    inside string values are escaped to the two-char `\n`, never a literal `\n`
    — so the payload is always exactly one line, and `decodeCache`'s
    `splitOn "\n"` recovers `[checksum, payload]` unambiguously. -/
def encodeCache (c : FoldCache) : String :=
  let payload := (Json.mkObj [
    ("v", jnum cacheVersion),
    ("segments", Json.arr (c.segments.map encSegMeta).toArray),
    ("state", encState c.state)]).compress
  ckOf payload.toUTF8 ++ "\n" ++ payload ++ "\n"

/-- Decode a cache file. ANY failure — a checksum mismatch anywhere in the
    file, parse error, version mismatch, non-canonical content — is `none`:
    the cache is rebuilt, never repaired. -/
def decodeCache (s : String) : Option FoldCache := do
  let payload ← match s.splitOn "\n" with
    | [sum, payload] | [sum, payload, ""] =>
      if ckOf payload.toUTF8 == sum then some payload else none
    | _ => none
  let j ← (Json.parse payload).toOption
  let v ← (← (j.getObjVal? "v").toOption).getNat?.toOption
  if v != cacheVersion then none else
  let segs ← match ← (j.getObjVal? "segments").toOption with
    | Json.arr a => a.toList.mapM decSegMeta
    | _ => none
  -- one entry per replica, in enumeration (ascending) order — an encode always
  -- satisfies this (`enumerateSegments` sorts); rejects duplicate entries
  if AssocList.ascending (segs.map (fun m => (m.replicaId, ()))) then do
    let st ← decState (← (j.getObjVal? "state").toOption)
    some { segments := segs, state := st }
  else none

/-! ## Validity and the cached fold -/

/-- Is the cache valid against the live segments and their decode? See the
    module header for why each conjunct exists. -/
def cacheValid (c : FoldCache) (pairs : List (SegmentData × SegmentDecode)) : Bool :=
  c.segments.all (fun m =>
    match pairs.find? (fun pr => pr.1.replicaId == m.replicaId) with
    | none => false
    | some (sd, dec) =>
      decide (m.byteLen ≤ sd.bytes.size)
      && ckOf (sd.bytes.extract 0 m.byteLen) == m.ck
      && dec.refusal.isSome == m.refused
      && dec.deferred.all (fun n => decide (m.lineCount < n) || m.deferred.contains n))

/-- The live ops a VALID cache has not folded: a segment the cache never saw
    contributes everything; a known segment contributes its appended lines plus
    the snapshot-deferred lines that are admissible now. With validity this is
    exactly `keptNow \ foldedAtSnapshot` (kept prefix lines outside the snapshot
    deferral set were folded then — same bytes, same classification — and a
    snapshot-folded line cannot be deferred now, or validity failed). -/
def extraOps (c : FoldCache) (pairs : List (SegmentData × SegmentDecode)) :
    List ParsedOp :=
  pairs.flatMap (fun (sd, dec) =>
    match c.segments.find? (fun m => m.replicaId == sd.replicaId) with
    | none => dec.ops.map (·.2)
    | some m =>
      (dec.ops.filter (fun (n, _) => decide (m.lineCount < n) || m.deferred.contains n)).map (·.2))

/-- The per-segment content keys for a cache written against these segments. -/
def liveMeta (pairs : List (SegmentData × SegmentDecode)) : List CacheSegMeta :=
  pairs.map (fun (sd, dec) =>
    { replicaId := sd.replicaId
      byteLen := sd.bytes.size
      lineCount := dec.lineCount
      ck := ckOf sd.bytes
      refused := dec.refusal.isSome
      deferred := dec.deferred })

private def refold (pairs : List (SegmentData × SegmentDecode)) : Loaded × Option FoldCache :=
  let loaded := assemble pairs State.empty
  let loaded := { loaded with state := Tl.Kernel.foldFast (loaded.ops.map ParsedOp.kernelOp) }
  (loaded, some { segments := liveMeta pairs, state := loaded.state })

/-- `materialize` through the cache: the same `Loaded` (pinned by the property
    tests), plus the refreshed cache to persist — `none` when the cache was
    exactly fresh (the common repeated-read case writes nothing). A valid cache
    turns the fold into `extras.foldl apply cached` (`fold_append` +
    `fold_perm`); anything else is a full refold. `skipBad` folds bypass the
    cache entirely. -/
def materializeCached (segs : List SegmentData) (cache : Option FoldCache)
    (skipBad : Bool := false) (now : Option Nat := none)
    (ownReplica : Option String := none) : Loaded × Option FoldCache :=
  let pairs := decodeAll segs skipBad now ownReplica
  if skipBad then
    let loaded := assemble pairs State.empty
    ({ loaded with state := Tl.Kernel.foldFast (loaded.ops.map ParsedOp.kernelOp) }, none)
  else
    match cache with
    | none => refold pairs
    | some c =>
      if cacheValid c pairs then
        let extras := extraOps c pairs
        let state := extras.foldl (fun s p => Tl.Kernel.apply s p.kernelOp) c.state
        -- exactly-fresh detection without re-hashing: validity already pinned
        -- the prefix bytes, so an equal byteLen implies an equal sha — compare
        -- only the cheap key fields (in order; both lists ascend by replica)
        let fresh := extras.isEmpty
          && c.segments.length == pairs.length
          && (c.segments.zip pairs).all (fun (m, sd, dec) =>
               m.replicaId == sd.replicaId && m.byteLen == sd.bytes.size
               && m.lineCount == dec.lineCount && m.refused == dec.refusal.isSome
               && m.deferred == dec.deferred)
        let refreshed := if fresh then none else some { segments := liveMeta pairs, state }
        (assemble pairs state, refreshed)
      else
        refold pairs

/-! ## The cache file -/

/-- Load `.tl/local/cache`. ANY failure — absent, unreadable, non-UTF-8,
    corrupt — is `none` (rebuild); a symlinked path is refused by the
    no-follow open and lands here too (the later atomic-replace rename never
    follows it either). -/
def loadCache (d : Dirs) : TlM (Option FoldCache) := do
  match ← (Sys.withFd d.base d.relCache 0 Sys.readAll).toBaseIO with
  | .error _ => return none
  | .ok bytes =>
    match String.fromUTF8? bytes with
    | none => return none
    | some s => return decodeCache s

/-- Persist the refreshed cache — atomic replace (ADR-0015 §3), best-effort:
    a read-only filesystem or a lost write race never fails the command;
    staleness only costs the next invocation a rebuild. -/
def saveCache (d : Dirs) (c : FoldCache) : TlM Unit := do
  let _ ← liftM ((writeLocalFile d d.relCache (encodeCache c)).run.toBaseIO)
  return ()

/-- The cached read path — `readState` through the fold cache: enumerate →
    read → cached materialize → best-effort persist of the refreshed cache.
    `persist := false` keeps `doctor` a pure diagnostic (the ADR-0016 §3
    discipline: doctor mutates nothing, not even a cache). The returned
    `Loaded` is exactly what `readState` returns (pinned by tests). -/
def readStateCached (d : Dirs) (skipBad : Bool := false)
    (now : Option Nat := none) (ownReplica : Option String := none)
    (persist : Bool := true) : TlM Loaded := do
  let (segs, notes) ← readSegments d
  let cache ← if skipBad then pure none else loadCache d
  let (loaded, refreshed) := materializeCached segs cache skipBad now ownReplica
  if persist then
    if let some c := refreshed then
      saveCache d c
  return { loaded with warnings := notes ++ loaded.warnings }

end Tl.Store
