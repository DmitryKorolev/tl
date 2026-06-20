/-
`Tests.CacheTests` — the fold cache battery (ADR-0022).

Four suites, per the tested-shell mandate (every branch, in the same change):

* codec — round-trip over a state exercising every `IssueData` field and
  OR-Set tombstones; fail-closed decode (non-JSON, version bump, truncation,
  non-ascending canonical lists, duplicate entries, bad stamp tags,
  out-of-range enum/`Fin` payloads each yield `none`, never a wrong state);
* validity branches — for each stale/valid case the cached result must equal
  the fresh `materialize`, AND the path taken is observed directly: a cache
  "poisoned" with a marker issue keeps the marker iff the cache was used, so
  a test asserts rebuild-vs-suffix, not just the (identical) end state;
* the seeded property — `materializeCached` ≡ `materialize` on generated
  multi-replica logs split at random prefix points, at the cache's own `now`
  and at a later `now` (skew-deferred lines admitted on top of the cache);
* IO — transact/read warm the file, corrupt caches heal on persisted reads,
  `persist := false` (doctor) mutates nothing, `--skip-bad` bypasses, and a
  symlinked cache file is never followed (read or replace).
-/
import Tl.Store.Cache
import Tl.Store.Lock
import Tl.Cli.Main
import Tl.Format.Ids
import Tests.Harness

namespace Tl.Tests

open Tl.Store
open Tl.Format
open Tl.Kernel
open Tl.Crdt (Stamp FinSet)

/-! ## Shared fixtures -/

private def ownStem : String := "0123456789abc"
private def forStem : String := "1111111111111"
private def newStem : String := "2222222222222"

private def idA : String := "a000000000000000"
private def idB : String := "b000000000000000"
private def idC : String := "c000000000000000"
private def markerId : String := "f000000000000000"

private def now0 : Nat := 2000000000000

/-- A crafted record line for a segment owned by `stem` (the per-replica owner
    check requires the stamp's replica to encode to the segment name). -/
private def craftLine (op : WireOp) (hlc nonce : Nat) (stem : String) : String :=
  renderLine { v := supportedVersion, op,
               stamp := ⟨hlc, (ofCrockford? stem).getD 0, nonce⟩, actor := some "x" }

/-- A line at physical time `phys` (logical = `idx`), nonce-distinct per `idx`. -/
private def mkLine (op : WireOp) (idx : Nat) (stem : String) (phys : Nat := now0) : String :=
  craftLine op (phys * 2 ^ 16 + idx) (5000 + idx) stem

private def segOf (stem : String) (ls : List String) : SegmentData :=
  { replicaId := stem, bytes := (ls.foldl (fun a l => a ++ l ++ "\n") "").toUTF8 }

/-- State identity via the (injective on canonical states) cache encoding. -/
private def stateBytes (s : State) : String := encodeCache ⟨[], s⟩

/-- Full `Loaded` agreement — every field a command can observe. -/
private def loadedEq (a b : Loaded) : Bool :=
  stateBytes a.state == stateBytes b.state
  && a.ops.map renderLine == b.ops.map renderLine
  && a.refused.map (fun r => (r.replicaId, r.line)) == b.refused.map (fun r => (r.replicaId, r.line))
  && a.skipped == b.skipped
  && a.deferred == b.deferred
  && a.maxHlc == b.maxHlc
  && a.maxDeferredHlc == b.maxDeferredHlc
  && a.ownMaxHlc == b.ownMaxHlc
  && a.warnings == b.warnings
  && a.segmentCount == b.segmentCount

/-! ## Codec round-trip and fail-closed decode -/

private def mkst (h n : Nat) : Stamp := ⟨h, 7, n⟩

/-- Every `IssueData` field written (including a written-`none` clear), labels
    and an edge tombstoned, meta set and cleared — the codec's full surface. -/
private def fullWrites : ScalarWrites :=
  { title := some "alpha", status := some Status.InProgress,
    priority := some (1 : Fin 5), assignee := some (some "ann"),
    description := some (some "desc"), notes := some (some "note"),
    slug := some (some "alpha-slug"), deferUntil := some (some 123456),
    closeResolution := some none }

private def clearWrites : ScalarWrites :=
  { assignee := some none, status := some Status.Done,
    closeResolution := some (some CloseResolution.Done) }

private def richState : State :=
  Tl.Kernel.fold [
    Op.create idA (mkst 10 1) fullWrites,
    Op.create idB (mkst 11 2) { title := some "beta" },
    Op.setFields idB (mkst 12 3) clearWrites,
    Op.metaSet idA (mkst 13 4) "k1" (some "v1"),
    Op.metaSet idA (mkst 14 5) "k2" none,
    Op.edgeAdd (idA, idB, .Blocks) (mkst 15 6),
    Op.edgeAdd (idA, idB, .Parent) (mkst 16 7),
    Op.edgeAdd (idA, idB, .Related) (mkst 17 8),
    Op.edgeRemove (idA, idB, .Related) (FinSet.singleton (mkst 17 8)),
    Op.labelAdd idA "ui" (mkst 18 9),
    Op.labelAdd idA "perf" (mkst 19 10),
    Op.labelRemove idA "ui" (FinSet.singleton (mkst 18 9))]

private def metaOwn : CacheSegMeta :=
  { replicaId := ownStem, byteLen := 420, lineCount := 12, ck := "abcd",
    refused := false, deferred := [3, 7] }

private def metaFor : CacheSegMeta :=
  { replicaId := forStem, byteLen := 0, lineCount := 0, ck := "ee",
    refused := true, deferred := [] }

private def richMeta : List CacheSegMeta := [metaOwn, metaFor]

/-- Sign a payload line as a well-formed cache file — crafted negative rows
    must carry a CORRECT checksum so they exercise the inner decoder arm they
    target, not the checksum gate. -/
private def sign (payload : String) : String :=
  toString (ByteArray.hash payload.toUTF8) ++ "\n" ++ payload ++ "\n"

private def orsetJson (a r : String) : String := "{\"a\":" ++ a ++ ",\"r\":" ++ r ++ "}"

/-- A handcrafted, correctly-signed payload with all three state components
    injectable — for shapes the encoder can never produce. -/
private def handState (issues data edges : String) : String :=
  sign ("{\"v\":2,\"segments\":[],\"state\":{\"issues\":" ++ issues ++ ",\"data\":" ++ data
    ++ ",\"edges\":" ++ edges ++ "}}")

private def handIssues (aaa rrr : String) : String :=
  handState (orsetJson aaa rrr) "[]" (orsetJson "[]" "[]")

/-- A full `IssueData` JSON object with selected fields overridden. -/
private def issueDataJson (overrides : List (String × String)) : String :=
  let base := [("title", "null"), ("status", "null"), ("prio", "null"),
               ("assignee", "null"), ("desc", "null"), ("notes", "null"),
               ("slug", "null"), ("defer", "null"), ("close", "null"),
               ("labels", orsetJson "[]" "[]"), ("meta", "[]")]
  "{" ++ String.intercalate "," (base.map (fun (k, v) =>
    "\"" ++ k ++ "\":" ++ ((overrides.lookup k).getD v))) ++ "}"

private def handData (entry : String) : String :=
  handState (orsetJson "[]" "[]") ("[[\"a\"," ++ entry ++ "]]") (orsetJson "[]" "[]")

private def handEdges (aaa : String) : String :=
  handState (orsetJson "[]" "[]") "[]" (orsetJson aaa "[]")

private def emptyStateJson : String :=
  "{\"issues\":" ++ orsetJson "[]" "[]" ++ ",\"data\":[],\"edges\":" ++ orsetJson "[]" "[]" ++ "}"

private def handSeg (segJson : String) : String :=
  sign ("{\"v\":2,\"segments\":[" ++ segJson ++ "],\"state\":" ++ emptyStateJson ++ "}")

private def validTag : String := tagOfStamp (mkst 10 1)

def cacheCodecTests : List Outcome :=
  let c : FoldCache := { segments := richMeta, state := richState }
  let enc := encodeCache c
  let payload := (enc.splitOn "\n").getD 1 ""
  let dec? := decodeCache enc
  -- a re-signed payload edit: exercises the targeted decoder arm
  let surgery (needle repl : String) := decodeCache (sign (payload.replace needle repl))
  -- an UNsigned payload edit: structurally valid, caught only by the checksum
  let bitrot (needle repl : String) :=
    decodeCache ((enc.splitOn "\n").getD 0 "" ++ "\n" ++ payload.replace needle repl ++ "\n")
  [ check "round-trip re-encodes byte-identically"
      ((dec?.map encodeCache) == some enc),
    check "round-trip preserves the segment keys"
      ((dec?.map (·.segments)) == some richMeta),
    check "round-trip preserves observed state (issues, fields, labels, edges)"
      (match dec? with
       | none => false
       | some d =>
         d.state.presentIssues == [idA, idB]
         && decide ((d.state.issueData idB).statusOf = Status.Done)
         && (d.state.issueData idA).labels.presentElements == ["perf"]
         && d.state.presentEdges.length == 2
         && (d.state.issueData idA).deferUntilOf == some 123456),
    -- the checksum gate: structurally-valid VALUE corruption must rebuild,
    -- never serve a silently wrong state (deferred-set, line-count, and
    -- state-string flips are all shape-preserving)
    check "a flipped deferred-line digit is rejected by the checksum"
      (bitrot "\"deferred\":[3,7]" "\"deferred\":[4,7]").isNone,
    check "a flipped lineCount is rejected by the checksum"
      (bitrot "\"lines\":12" "\"lines\":13").isNone,
    check "a flipped state string byte is rejected by the checksum"
      (bitrot "alpha" "alphb").isNone,
    check "a missing checksum line is rejected" (decodeCache (payload ++ "\n")).isNone,
    check "a wrong checksum is rejected" (decodeCache ("0" ++ enc.drop 1)).isNone,
    check "non-JSON input is rejected" (decodeCache "{not json").isNone,
    check "a signed non-JSON payload is rejected" (decodeCache (sign "{not json")).isNone,
    check "a future cache version is rejected (forces a rebuild)"
      (surgery "\"v\":2}" "\"v\":3}").isNone,
    check "a missing version is rejected"
      (decodeCache (sign ("{\"segments\":[],\"state\":" ++ emptyStateJson ++ "}"))).isNone,
    check "a non-numeric version is rejected"
      (decodeCache (sign ("{\"v\":\"1\",\"segments\":[],\"state\":" ++ emptyStateJson ++ "}"))).isNone,
    check "truncated input is rejected"
      (decodeCache (enc.take (enc.length / 2)).toString).isNone,
    check "a missing state object is rejected"
      (decodeCache (sign "{\"v\":2,\"segments\":[]}")).isNone,
    check "a state missing a component is rejected"
      (decodeCache (sign ("{\"v\":2,\"segments\":[],\"state\":{\"issues\":"
        ++ orsetJson "[]" "[]" ++ ",\"data\":[]}}"))).isNone,
    check "segments must be an array"
      (decodeCache (sign ("{\"v\":2,\"segments\":{},\"state\":" ++ emptyStateJson ++ "}"))).isNone,
    check "a segment entry missing fields is rejected"
      (decodeCache (handSeg "{\"replica\":\"x\"}")).isNone,
    check "a wrongly-typed segment scalar is rejected"
      (decodeCache (handSeg "{\"replica\":\"x\",\"bytes\":\"y\",\"lines\":0,\"sha\":\"e\",\"refused\":false,\"deferred\":[]}")).isNone,
    check "a non-array deferred set is rejected"
      (decodeCache (handSeg "{\"replica\":\"x\",\"bytes\":0,\"lines\":0,\"sha\":\"e\",\"refused\":false,\"deferred\":{}}")).isNone,
    check "a non-numeric deferred entry is rejected"
      (decodeCache (handSeg "{\"replica\":\"x\",\"bytes\":0,\"lines\":0,\"sha\":\"e\",\"refused\":false,\"deferred\":[\"x\"]}")).isNone,
    check "duplicate segment entries are rejected"
      (decodeCache (encodeCache { c with segments := [metaOwn, metaOwn] })).isNone,
    -- canonicality + per-decoder arms: a decoding twin is each row's control
    check "a canonical handcrafted state decodes (control)"
      (match decodeCache (handIssues s!"[[\"a\",[\"{validTag}\"]]]" "[]") with
       | some d => d.state.presentIssues == ["a"]
       | none => false),
    check "a non-ascending canonical list is rejected"
      (decodeCache (handIssues "[[\"b\",[]],[\"a\",[]]]" "[]")).isNone,
    check "duplicate stamps in a tombstone set are rejected"
      (decodeCache (handIssues "[]" s!"[\"{validTag}\",\"{validTag}\"]")).isNone,
    check "a malformed stamp tag is rejected"
      (decodeCache (handIssues "[[\"a\",[\"bogus\"]]]" "[]")).isNone,
    check "a non-string tombstone entry is rejected"
      (decodeCache (handIssues "[]" "[5]")).isNone,
    check "a non-array tag set is rejected"
      (decodeCache (handIssues "[[\"a\",5]]" "[]")).isNone,
    check "an or-set missing a component is rejected"
      (decodeCache (handState "{\"a\":[]}" "[]" (orsetJson "[]" "[]"))).isNone,
    check "a full handcrafted issue-data record decodes (control)"
      (decodeCache (handData (issueDataJson []))).isSome,
    check "a non-register field payload is rejected"
      (decodeCache (handData (issueDataJson [("title", "5")]))).isNone,
    check "a wrong-arity register is rejected"
      (decodeCache (handData (issueDataJson [("title", "[\"x\"]")]))).isNone,
    check "a non-numeric defer payload is rejected"
      (decodeCache (handData (issueDataJson [("defer", s!"[\"{validTag}\",\"x\"]")]))).isNone,
    check "a non-string assignee payload is rejected"
      (decodeCache (handData (issueDataJson [("assignee", s!"[\"{validTag}\",5]")]))).isNone,
    check "an out-of-range close payload is rejected"
      (decodeCache (handData (issueDataJson [("close", s!"[\"{validTag}\",9]")]))).isNone,
    check "a non-pair meta entry is rejected"
      (decodeCache (handData (issueDataJson [("meta", "[[\"k\"]]")]))).isNone,
    check "a non-array meta map is rejected"
      (decodeCache (handData (issueDataJson [("meta", "5")]))).isNone,
    check "a handcrafted edge decodes (control)"
      (decodeCache (handEdges s!"[[[\"a\",\"b\",0],[\"{validTag}\"]]]")).isSome,
    check "an out-of-range edge kind is rejected"
      (decodeCache (handEdges "[[[\"a\",\"b\",9],[]]]")).isNone,
    check "a non-string edge endpoint is rejected"
      (decodeCache (handEdges "[[[\"a\",5,0],[]]]")).isNone,
    check "a wrong-arity edge is rejected"
      (decodeCache (handEdges "[[[\"a\",\"b\"],[]]]")).isNone,
    check "an out-of-range status payload is rejected"
      (surgery s!"\"status\":[\"{validTag}\",1]" s!"\"status\":[\"{validTag}\",9]").isNone,
    check "an out-of-range priority payload is rejected"
      (surgery s!"\"prio\":[\"{validTag}\",1]" s!"\"prio\":[\"{validTag}\",9]").isNone ]

/-! ## Validity branches

Each case asserts BOTH that the cached result equals the fresh `materialize`
AND which path ran: a marker issue folded only into the cache's state
survives iff the cache was used (`apply` is the only way state enters the
result), so `hasMarker` distinguishes suffix-fold from rebuild. -/

private def poison (c : FoldCache) : FoldCache :=
  { c with state := Tl.Kernel.apply c.state (Op.create markerId ⟨1, 1, 999⟩ {}) }

private def hasMarker (l : Loaded) : Bool := l.state.presentIssues.contains markerId

private def baseOwn : List String :=
  [mkLine (.create idA { title := some "A" }) 1 ownStem,
   mkLine (.create idB { title := some "B" }) 2 ownStem,
   mkLine (.depAdd (idA, idB, .Blocks)) 3 ownStem]

private def forPlain : List String :=
  [mkLine (.create idC { title := some "C" }) 4 forStem]

private def futureLine : String :=
  mkLine (.update idC { description := some (some "future") }) 5 forStem
    (now0 + 2 * skewWindowMs)

private def forDefer : List String := forPlain ++ [futureLine]

/-- Build the honest cache a read at `now` over `segs` would persist. -/
private def cacheOf (segs : List SegmentData) (now : Option Nat := some now0) : FoldCache :=
  ((materializeCached segs none false now (some ownStem)).2).getD ⟨[], State.empty⟩

/-- One validity-branch case: cached run vs fresh run, plus the path marker. -/
private def branchCase (name : String) (segs : List SegmentData) (c : FoldCache)
    (cacheUsed : Bool) (now : Option Nat := some now0) : List Outcome :=
  let fresh := materialize segs false now (some ownStem)
  let (viaCache, _) := materializeCached segs (some c) false now (some ownStem)
  let (viaPoison, _) := materializeCached segs (some (poison c)) false now (some ownStem)
  [ check s!"{name}: cached result ≡ fresh fold" (loadedEq viaCache fresh)
      s!"state {stateBytes viaCache.state == stateBytes fresh.state}",
    check (s!"{name}: " ++ (if cacheUsed then "cache used (marker survives)"
                            else "cache rebuilt (marker gone)"))
      (hasMarker viaPoison == cacheUsed) ]

def cacheFoldTests : List Outcome := Id.run do
  let base := [segOf ownStem baseOwn, segOf forStem forPlain]
  let c0 := cacheOf base
  let mut o : List Outcome := []
  -- absent cache → refold, and the refreshed cache carries the live keys
  let (l0, r0) := materializeCached base none false (some now0) (some ownStem)
  o := o ++ [
    check "no cache: result ≡ fresh fold" (loadedEq l0 (materialize base false (some now0) (some ownStem))),
    -- ownMaxHlc (transact's present-clock floor) is the OWN segment's max, distinct
    -- from the all-segment `maxHlc`: baseOwn tops at idx 3, the foreign forPlain at
    -- idx 4 (higher), so a regression returning `maxHlc` or 0 is caught directly —
    -- not just by the cached≡fresh equivalence (which compares both paths' fields)
    check "ownMaxHlc is the OWN segment's max (now0·2^16+3), below the foreign-inflated maxHlc"
      (l0.ownMaxHlc == now0 * 2 ^ 16 + 3 && l0.maxHlc == now0 * 2 ^ 16 + 4
        && l0.ownMaxHlc < l0.maxHlc)
      s!"ownMaxHlc={l0.ownMaxHlc} maxHlc={l0.maxHlc}",
    -- with no own segment present, the floor is 0 (a freshly-minted replica id)
    check "ownMaxHlc is 0 when the own replica has no segment"
      ((materialize base false (some now0) (some "9999999999999")).ownMaxHlc == 0) "",
    check "no cache: a refreshed cache is produced with the live per-segment keys"
      (match r0 with
       | some c => c.segments.map (·.replicaId) == [ownStem, forStem]
           && c.segments.map (·.lineCount) == [3, 1]
           && c.segments.all (fun m => !m.refused && m.deferred.isEmpty)
       | none => false)]
  -- exactly fresh → no rewrite
  let (_, rFresh) := materializeCached base (some c0) false (some now0) (some ownStem)
  o := o ++ branchCase "unchanged log" base c0 true
  o := o ++ [check "unchanged log: nothing to persist" rFresh.isNone]
  -- appended suffix on the own segment
  let grown := [segOf ownStem (baseOwn ++ [mkLine (.update idA { description := some (some "A2") }) 6 ownStem]),
                segOf forStem forPlain]
  let (_, rGrown) := materializeCached grown (some c0) false (some now0) (some ownStem)
  o := o ++ branchCase "appended suffix" grown c0 true
  o := o ++ [check "appended suffix: the refreshed cache is persisted" rGrown.isSome]
  -- a segment the cache never saw (its issue id must differ from the poison
  -- marker, or the path observation is vacuous — a rebuild would also fold it)
  let withNew := base ++ [segOf newStem [mkLine (.create "9000000000000000" { title := some "N" }) 7 newStem]]
  o := o ++ branchCase "new segment appears" withNew c0 true
  -- a cached segment missing live (deleted/renamed segment, or a byte-copied
  -- cache from a working copy that had more segments)
  o := o ++ branchCase "cached segment missing live" [segOf ownStem baseOwn] c0 false
  -- shrunk prefix
  o := o ++ branchCase "shrunk segment" [segOf ownStem (baseOwn.take 2), segOf forStem forPlain] c0 false
  -- same length, different bytes (in-place rewrite)
  let flipped := [segOf ownStem ([mkLine (.create idA { title := some "X" }) 1 ownStem] ++ baseOwn.drop 1),
                  segOf forStem forPlain]
  o := o ++ branchCase "same-length rewrite (hash mismatch)" flipped c0 false
  -- a bad line APPENDED refuses the whole segment → flag mismatch → rebuild
  let refusedNow := [segOf ownStem (baseOwn ++ ["GARBAGE NOT JSON"]), segOf forStem forPlain]
  o := o ++ branchCase "refusal appears in the suffix" refusedNow c0 false
  -- refused at snapshot time, unchanged (and grown-after-garbage) → consistent
  let refusedSegs := [segOf ownStem baseOwn, segOf forStem ["NOT JSON"]]
  let cRef := cacheOf refusedSegs
  o := o ++ branchCase "refused at snapshot, unchanged" refusedSegs cRef true
  o := o ++ branchCase "refused at snapshot, grown after the bad line"
    [segOf ownStem baseOwn, segOf forStem ["NOT JSON", forPlain.head!]] cRef true
  -- skew deferral: cached as deferred, admitted at a later now
  let deferSegs := [segOf ownStem baseOwn, segOf forStem forDefer]
  let cDefer := cacheOf deferSegs
  let later := now0 + 3 * skewWindowMs
  o := o ++ branchCase "still-deferred line stays held back" deferSegs cDefer true
  o := o ++ branchCase "deferred line admitted at a later now" deferSegs cDefer true (some later)
  let (_, rAdmit) := materializeCached deferSegs (some cDefer) false (some later) (some ownStem)
  o := o ++ [check "admission refreshes the cache (the admitted op advanced the state)" rAdmit.isSome]
  -- a far-future line APPENDED after the snapshot: valid, and stays held back
  let appendedDefer := [segOf ownStem baseOwn, segOf forStem forDefer]
  o := o ++ branchCase "deferred line appended after the snapshot" appendedDefer c0 true
  let (lDef, _) := materializeCached appendedDefer (some c0) false (some now0) (some ownStem)
  o := o ++ [check "the appended deferred line is disclosed" (lDef.deferred == [(forStem, 2)])]
  -- a clock that went backwards: cached-as-folded line is deferred now → rebuild
  let cLater := cacheOf deferSegs (some later)
  o := o ++ branchCase "deferral grew (clock went backwards)" deferSegs cLater false
  -- skew off (now = none): deferred-at-snapshot lines fold on top
  o := o ++ branchCase "skew check off (now := none)" deferSegs cDefer true none
  -- --skip-bad bypasses the cache entirely
  let skipSegs := [segOf ownStem (baseOwn ++ ["GARBAGE NOT JSON"]), segOf forStem forPlain]
  let freshSkip := materialize skipSegs true (some now0) (some ownStem)
  let (viaSkip, rSkip) := materializeCached skipSegs (some (poison c0)) true (some now0) (some ownStem)
  o := o ++ [
    check "--skip-bad: result ≡ fresh --skip-bad fold" (loadedEq viaSkip freshSkip),
    check "--skip-bad: the cache is not consulted (marker gone)" (!hasMarker viaSkip),
    check "--skip-bad: no cache is produced" rSkip.isNone]
  -- a torn fragment closed into a valid line is the suffix line after the boundary
  let fragLine := mkLine (.create markerId { title := some "frag" }) 8 ownStem
  let tornBytes := (segOf ownStem baseOwn).bytes ++ fragLine.toUTF8
  let cTorn := cacheOf [{ replicaId := ownStem, bytes := tornBytes }, segOf forStem forPlain]
  let closed := [({ replicaId := ownStem, bytes := tornBytes ++ "\n".toUTF8 } : SegmentData),
                 segOf forStem forPlain]
  o := o ++ branchCase "torn fragment closed into a valid suffix line" closed cTorn true
  -- key-only drift: a torn fragment grows the bytes but closes no line — the
  -- cache stays valid with nothing to fold, yet the key must be re-persisted
  let fragOnly := [({ replicaId := ownStem,
                      bytes := (segOf ownStem baseOwn).bytes ++ "unfinished".toUTF8 } : SegmentData),
                   segOf forStem forPlain]
  o := o ++ branchCase "torn fragment grows the bytes, no new line" fragOnly c0 true
  let (_, rFrag) := materializeCached fragOnly (some c0) false (some now0) (some ownStem)
  o := o ++ [check "key-only drift still refreshes the cache" rFrag.isSome]
  return o

/-! ## The seeded property: cached fold ≡ fresh fold -/

private def poolIds : List String :=
  [idA, idB, idC, "d000000000000000", "e000000000000000"]

private def genLines (stem : String) (count startIdx seed : Nat) : List String × Nat :=
  (List.range count).foldl (fun (acc, s) k =>
    let idx := startIdx + k
    let (s1, kind) := nextNat s 5
    let (s2, i) := nextNat s1 poolIds.length
    let (s3, j) := nextNat s2 poolIds.length
    let (s4, fut) := nextNat s3 8
    let id := poolIds.getD i ""
    let other := poolIds.getD j ""
    -- ~1 in 8 lines is far-future (skew-deferred on foreign segments)
    let phys := if fut == 0 then now0 + 2 * skewWindowMs else now0 - 5000 + idx
    let op : WireOp := match kind with
      | 0 => .create id { title := some s!"t{idx}" }
      | 1 => .update id { description := some (some s!"d{idx}") }
      | 2 => .depAdd (id, other, .Blocks)
      | 3 => .labelAdd id "lbl"
      | _ => .close id .Done
    (acc ++ [mkLine op idx stem phys], s4)) ([], seed)

def cacheSuffixFoldProp : List Outcome :=
  (List.range 15).flatMap (fun k =>
    let seed := 0xcafe + 7919 * k
    let (ownLines, s1) := genLines ownStem 12 0 seed
    let (forLines, s2) := genLines forStem 12 100 s1
    let (s3, splitOwn) := nextNat s2 (ownLines.length + 1)
    let (_, splitFor) := nextNat s3 (forLines.length + 1)
    let prefSegs := [segOf ownStem (ownLines.take splitOwn), segOf forStem (forLines.take splitFor)]
    let fullSegs := [segOf ownStem ownLines, segOf forStem forLines]
    let c := cacheOf prefSegs
    let fresh := materialize fullSegs false (some now0) (some ownStem)
    let (viaCache, r1) := materializeCached fullSegs (some c) false (some now0) (some ownStem)
    -- the same prefix cache consumed at a later now: deferred lines admitted
    let later := now0 + 3 * skewWindowMs
    let freshLater := materialize fullSegs false (some later) (some ownStem)
    let (viaLater, _) := materializeCached fullSegs (some c) false (some later) (some ownStem)
    -- and the refreshed cache is a fixpoint: consuming it changes nothing
    let (viaAgain, rAgain) := materializeCached fullSegs (some (r1.getD c)) false (some now0) (some ownStem)
    [ check s!"seed {k}: prefix-cached fold ≡ fresh fold (split {splitOwn}/{splitFor})"
        (loadedEq viaCache fresh),
      check s!"seed {k}: cache from `now` consumed at a later now ≡ fresh later fold"
        (loadedEq viaLater freshLater),
      check s!"seed {k}: the refreshed cache is a fixpoint (no rewrite, same result)"
        (loadedEq viaAgain fresh && rAgain.isNone) ])

/-! ## The cache file: lifecycle, healing, doctor non-persist, symlinks -/

private def fixedReplica : String := ownStem

private def mkProject : IO (System.FilePath × Dirs) := do
  let root ← IO.FS.createTempDir
  IO.FS.createDirAll (root / ".tl" / "local")
  IO.FS.writeFile (root / ".tl" / ".gitignore") "*\n"
  IO.FS.writeFile (root / ".tl" / "local" / "replica") (fixedReplica ++ "\n")
  IO.FS.writeFile (root / ".tl" / "local" / "clock") "0000000000000000\n"
  return (root, { base := root.toString, tlRel := ".tl" })

private def runTl (act : TlM α) : IO (Except Tl.Error α) := act.run

private def expectOk (name : String) (act : TlM α) (checkFn : α → Outcome) : IO Outcome := do
  match ← runTl act with
  | .ok a => return checkFn a
  | .error e => return { name, passed := false, msg := s!"failed: {e.code.wire}: {e.message}" }

private def buildCreate (title : String) : TxContext → List Stamp →
    Except Tl.Error (List WireOp) := fun _ stamps =>
  match stamps with
  | [st] => .ok [.create (mintIssueId st) { title := some title }]
  | _ => .error (.mk' .internal "expected exactly one stamp")

private def symlink (target linkPath : String) : IO Unit := do
  let out ← IO.Process.output { cmd := "ln", args := #["-s", target, linkPath] }
  unless out.exitCode == 0 do throw (IO.userError s!"ln -s failed: {out.stderr}")

/-- Both read paths against the live project — the IO-level agreement check. -/
private def readsAgree (name : String) (d : Dirs) (skipBad : Bool := false)
    (persist : Bool := true) : IO Outcome :=
  expectOk name (do
      let a ← readStateCached d skipBad (some now0) (some fixedReplica) (persist := persist)
      let b ← readState d skipBad (some now0) (some fixedReplica)
      pure (a, b))
    (fun (a, b) => check name (loadedEq a b))

/-- The cacheVersion-bump guard (ADR-0022 §3). A fixed corpus of wire lines —
    every WireOp kind, across two segments so the per-segment owner check, the
    cross-segment LWW tie-break, and the OR-Set/observed-tag removes all run — is
    folded through the production read path (`materialize` = decodeSegment + the
    kernel fold). Its `stateFoldDigest` (version-independent) is pinned against
    the current `cacheVersion`. Any change to per-line classification, the owner
    check, `WireOp.toOp`, kernel apply/merge, or the cache codec moves the
    digest; the guard then FAILS, turning ADR-0022's "bump cacheVersion on a
    semantics change" obligation into a CI gate instead of reviewer memory. -/
def cacheVersionGuardTests : List Outcome :=
  -- the recorded (cacheVersion, digest) the guard is pinned to. On an INTENDED
  -- semantics change, bump Tl.Store.cacheVersion AND set this to the printed value.
  let expectedFold : Nat × String :=
    (2, "7194777635966312595")
  -- the stamp `mkLine idx stem` emits — lets a remove tombstone a prior add-tag
  let stamp (idx : Nat) (stem : String) : Stamp :=
    ⟨now0 * 2 ^ 16 + idx, (ofCrockford? stem).getD 0, 5000 + idx⟩
  -- own segment: the full lifecycle + both edge kinds + a relate + labels + meta
  -- + REAL removes (observed = the matching add-tag)
  let own : List String :=
    [ mkLine (.create idA { title := some "Alpha", priority := some (1 : Fin 5) }) 0 ownStem,
      mkLine (.create idB { title := some "Beta" }) 1 ownStem,
      mkLine (.create idC { title := some "Gamma" }) 2 ownStem,
      mkLine (.claim idA "alice") 3 ownStem,
      mkLine (.update idA { description := some (some "the body"),
                            notes := some (some "a note") }) 4 ownStem,
      mkLine (.close idA .Done) 5 ownStem,
      mkLine (.reopen idA) 6 ownStem,
      mkLine (.defer idB 2100000000000) 7 ownStem,
      mkLine (.undefer idB) 8 ownStem,
      mkLine (.depAdd (idC, idB, .Blocks)) 9 ownStem,
      mkLine (.depAdd (idA, idC, .Parent)) 10 ownStem,
      mkLine (.relate (idA, idB, .Related)) 11 ownStem,
      mkLine (.metaSet idA "owner" (some "team-x")) 12 ownStem,
      mkLine (.metaSet idA "owner" none) 13 ownStem,
      mkLine (.labelAdd idA "urgent") 14 ownStem,
      mkLine (.labelAdd idB "backend") 15 ownStem,
      mkLine (.labelRemove idB "backend" (FinSet.singleton (stamp 15 ownStem))) 16 ownStem,
      mkLine (.depRemove (idC, idB, .Blocks) (FinSet.singleton (stamp 9 ownStem))) 17 ownStem,
      mkLine (.unrelate (idA, idB, .Related) (FinSet.singleton (stamp 11 ownStem))) 18 ownStem,
      mkLine (.close idC .Cancelled) 19 ownStem ]
  -- forStem segment: a higher-stamped title write WINS the LWW on idA.title
  -- (cross-segment merge over the create at idx 0)
  let foreign : List String :=
    [ mkLine (.update idA { title := some "Alpha-merged" }) 20 forStem ]
  -- a SEPARATE segment whose one line is stamped by ownStem (not newStem): the
  -- per-segment owner check refuses the whole segment, so it folds nothing. A
  -- regression that accepted it would re-take idA.title at the higher hlc 21 and
  -- move the digest. (One bad line refuses its segment wholesale, ADR-0001 — so
  -- this sentinel must live alone, not poison the real forStem merge.)
  let refused : List String :=
    [ craftLine (.update idA { title := some "REFUSED" }) (now0 * 2 ^ 16 + 21) 5021 ownStem ]
  let st := (materialize
    [segOf ownStem own, segOf forStem foreign, segOf newStem refused]).state
  let live := stateFoldDigest st
  (if expectedFold.1 != cacheVersion then
    [{ name := "cacheVersion-bump guard is pinned to the live cacheVersion",
       passed := false,
       msg := s!"guard pinned to cacheVersion {expectedFold.1}, but Tl.Store.cacheVersion is "
         ++ s!"{cacheVersion} — set expectedFold := ({cacheVersion}, \"{live}\")" }]
  else
    [check "the fixed-corpus fold digest is unchanged under cacheVersion (else bump it)"
       (live == expectedFold.2)
       (s!"semantics/codec drift under cacheVersion {cacheVersion}: a stale cache could fold "
         ++ s!"mismatched ops across two builds sharing a worktree. If intended, bump "
         ++ s!"Tl.Store.cacheVersion AND set expectedFold to ({cacheVersion + 1}, \"{live}\"); "
         ++ s!"else revert. live={live}")])
  -- the merge/owner-check outcome pinned explicitly: the higher-stamped foreign
  -- title wins, and the foreign-owned line was refused (not folded at idx 21)
  ++ [check "cross-segment LWW takes the higher-stamped title; the foreign-owned line is refused"
       (((st.issueData idA).title.value) == some "Alpha-merged")
       (toString ((st.issueData idA).title.value))]

def cacheIoTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let (root, d) ← mkProject
  let cachePath := root / ".tl" / "local" / "cache"
  -- transact folds through the cache and persists it (keyed to pre-append bytes)
  for t in ["one", "two", "three"] do
    match ← runTl (transact d (some "t") 1 (buildCreate t)) with
    | .ok _ => pure ()
    | .error e => o := o ++ [{ name := s!"transact {t}", passed := false, msg := e.message }]
  o := o ++ [check "transact persisted a decodable cache file"
    ((← cachePath.pathExists) && (decodeCache (← IO.FS.readFile cachePath)).isSome)]
  o := o ++ [← readsAgree "cached read ≡ uncached read after writes" d]
  -- after a persisted read, the cache validates against the segments on disk
  let raw ← IO.FS.readFile cachePath
  o := o ++ [check "the persisted cache decodes and carries the own segment key"
    (match decodeCache raw with
     | some c => c.segments.map (·.replicaId) == [fixedReplica]
     | none => false)]
  -- a corrupt cache file heals on the next persisted read
  IO.FS.writeFile cachePath "{not json"
  o := o ++ [← readsAgree "a corrupt cache degrades to the plain fold" d]
  o := o ++ [check "a corrupt cache heals on a persisted read"
    (decodeCache (← IO.FS.readFile cachePath)).isSome]
  -- persist := false (doctor) reads through but mutates nothing
  IO.FS.writeFile cachePath "{not json"
  o := o ++ [← readsAgree "persist := false still reads correctly" d (persist := false)]
  o := o ++ [check "persist := false leaves the file untouched"
    ((← IO.FS.readFile cachePath) == "{not json")]
  let _ ← runTl (readStateCached d false (some now0) (some fixedReplica))  -- heal it
  -- --skip-bad: bypasses, and never persists a skip-bad fold
  let segPath := root / ".tl" / "log" / (fixedReplica ++ ".jsonl")
  let goodSeg ← IO.FS.readBinFile segPath
  IO.FS.writeBinFile segPath (goodSeg ++ "GARBAGE\n".toUTF8)
  let healthyCache ← IO.FS.readFile cachePath
  o := o ++ [← readsAgree "--skip-bad read agrees with the uncached --skip-bad fold" d (skipBad := true)]
  o := o ++ [check "--skip-bad does not rewrite the cache"
    ((← IO.FS.readFile cachePath) == healthyCache)]
  -- the appended garbage refuses the own segment: flag mismatch → rebuild, equal
  o := o ++ [← readsAgree "a suffix refusal rebuilds and agrees" d]
  IO.FS.writeBinFile segPath goodSeg
  -- a symlinked cache file is neither followed on read nor on replace
  let outside := root / "outside.txt"
  IO.FS.writeFile outside "X"
  IO.FS.removeFile cachePath
  symlink outside.toString cachePath.toString
  o := o ++ [← readsAgree "a symlinked cache file degrades to the plain fold" d]
  o := o ++ [
    check "the persisted cache replaced the symlink with a regular file"
      (decodeCache (← IO.FS.readFile cachePath)).isSome,
    check "the symlink target was never written through"
      ((← IO.FS.readFile outside) == "X")]
  -- the actual doctor verb never persists: a corrupt cache survives it untouched
  IO.FS.writeFile cachePath "{not json"
  let _ ← runTl (Tl.Cli.runVerb ["doctor", "--json", "--dir", (root / ".tl").toString])
  o := o ++ [check "doctor leaves a corrupt cache untouched (mutates nothing)"
    ((← IO.FS.readFile cachePath) == "{not json")]
  let _ ← runTl (readStateCached d false (some now0) (some fixedReplica))  -- heal it
  -- a directory at the cache path: the read degrades, the save's failed atomic
  -- replace is swallowed AND does not strand its temp file
  IO.FS.removeFile cachePath
  IO.FS.createDir cachePath
  o := o ++ [← readsAgree "a directory at the cache path degrades to the plain fold" d]
  let localEntries ← (root / ".tl" / "local").readDir
  o := o ++ [
    check "the failed replace is swallowed (the path is still a directory)"
      (← cachePath.isDir),
    check "no temp file is stranded by the failed replace"
      (localEntries.toList.all (fun e => !e.fileName.endsWith ".tmp"))]
  IO.FS.removeDir cachePath
  -- a non-UTF-8 cache file degrades and heals
  IO.FS.writeBinFile cachePath (ByteArray.mk #[0xff, 0x01, 0x02])
  o := o ++ [← readsAgree "a non-UTF-8 cache degrades to the plain fold" d]
  o := o ++ [check "a non-UTF-8 cache heals on a persisted read"
    (decodeCache (← IO.FS.readFile cachePath)).isSome]
  return o

end Tl.Tests
