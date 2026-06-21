/-
`Tl.Store.Materialize` — records → ops → the kernel fold (ADR-0001/0008).

Fail-closed is *segment*-scoped (ADR-0008 §corruption): the first malformed
or unknown-version line refuses its whole segment — its ops never fold — but
every other segment folds normally; the `--skip-bad` escape hatch instead
skips individual bad lines with a disclosed list (no silent caps). Whether a
refusal fails the command (own/every segment) or just discloses (foreign) is
the CLI layer's call — this module reports facts.

The HLC scan is *line*-scoped (ADR-0007 §HLC recovery): every line that
parses contributes to `maxHlc` — including lines of a refused segment before
and after its bad line — because the absent-clock reseed needs the max over
the working copy's visible past writes, and a refused segment's good lines
are still past writes.

Container/record consistency is validated here too: segments are
per-replica authored (ADR-0001), so a record whose stamp replica does not
encode to its segment's name is a malformed line — it rides the exact same
refusal/`--skip-bad`/disclosure machinery as a parse failure, never a new
code path.
-/
import Tl.Store.Segment
import Tl.Format.Codec
import Tl.Kernel.Apply
import Tl.Clock.Skew

namespace Tl.Store

open Tl.Format
open Tl.Clock.Skew (admittedB)

/-- The clock-skew window (ADR-0007 amendment): a foreign op whose HLC physical
    time is more than this far beyond local wall-clock is *deferred* — held back
    from the fold and from the clock-reseed max until local time catches up,
    then it appears (eventually consistent). Computed on UTC epoch milliseconds,
    so it is immune to DST and civil-time (no spring-forward discontinuity).
    Deliberately generous — 24h — so it comfortably exceeds the worst plausible
    *honest* skew (a clock misconfigured to local-time-as-UTC is off by its
    timezone offset, up to ~14h): deferring an honest sibling's ops (too-small
    window) is worse than a weaker guard against a broken/hostile clock
    (too-large). Convergence safety is independent of this value (the deferral
    is monotone in `now` → eventual); it tunes only timeliness vs LWW exposure. -/
def skewWindowMs : Nat := 24 * 3600 * 1000

/-- The `doctor` *warn* threshold — distinct from, and much smaller than, the
    deferral window. Deferral (hiding an op, 24h) is functional, so it is
    generous (never hide an honest TZ-misconfigured peer). Warning is
    observability only — it adds a `doctor` note, never hides or fails anything —
    so it is tuned *sensitive*: a false warn costs a note, a missed misconfig
    costs silent LWW unfairness (a peer's ops ordering "from the future").

    15 minutes. Rationale: (1) the smallest timezone offsets are ±1h, so the
    common local-time-as-UTC misconfig leads by ~1h — a 1h threshold would miss
    it; 15min catches it. (2) ≈ NTP's default "panic" offset (1000s ≈ 16.7min),
    the point at which `ntpd` itself refuses to sync, treating the clock as
    pathologically wrong. (3) far above NTP-grade jitter (sub-second), so a
    healthy clock — and any same-machine worktree set (lead ≈ 0) — never trips
    it. `doctor` flags any clock leading `now` by more than this regardless of
    whether the op was deferred. -/
def skewWarnMs : Nat := 15 * 60 * 1000

/-- A refused segment: the first bad line (1-based) and its structured error
    (already carrying the ADR-0020 `segment`/`line` context). -/
structure Refusal where
  replicaId : String
  line : Nat
  error : Tl.Error

/-- The materialized view of the log. -/
structure Loaded where
  state : Tl.Kernel.State
  /-- The folded ops (refused segments contribute none), in segment-then-line
      order — the fold is order-insensitive (ADR-0004), this is for display. -/
  ops : List ParsedOp
  refused : List Refusal
  /-- `--skip-bad` disclosures: each skipped `(segment, line)`. -/
  skipped : List (String × Nat)
  /-- Skew-deferred lines (ADR-0007): each foreign `(segment, line)` whose HLC
      is beyond the skew window, held back from the fold and from `maxHlc` until
      wall-clock catches up. Disclosed, never dropped. -/
  deferred : List (String × Nat)
  /-- Line-scoped max envelope HLC across every segment (clock reseed); excludes
      skew-deferred lines, so a future-dated foreign op cannot inflate it. -/
  maxHlc : Nat
  /-- Max HLC among the *deferred* (skew-future) lines — the real lead of an
      ahead-of-now clock, for `doctor` to report (it is absent from `maxHlc`). -/
  maxDeferredHlc : Nat
  /-- The own replica's segment max HLC, threaded out of the decode so `transact`
      floors the present clock (ADR-0015 §1) without re-decoding the own segment.
      `0` when `ownReplica` is unset or has no segment; set by `materializeCached`.
      (The own segment is never skew-checked, and `transact` throws on a refused
      own segment before reading this, so the skipBad value cannot matter here.) -/
  ownMaxHlc : Nat := 0
  /-- Decode-time disclosures (e.g. the priority clamp), with provenance. -/
  warnings : List String
  /-- How many segments were read (the all-refused policy compares against
      `refused.length`, not against an empty fold — an empty project with one
      refused foreign segment is still an all-refused read). -/
  segmentCount : Nat

private def enrich (rid : String) (n : Nat) (e : Tl.Error) : Tl.Error :=
  { e with
    message := s!"segment {rid}.jsonl line {n}: {e.message}"
    context := e.context ++ [("segment", .str rid), ("line", .num ⟨n, 0⟩)] }

/-- One segment's decode result. A named structure (not a tuple), since it is
    consumed by `materialize` and by `transact`'s own-segment `maxHlc` probe
    (ADR-0015 §1) — 5+ components across 2+ callers (AGENTS.md). -/
structure SegmentDecode where
  /-- The kept ops, each with its 1-based line number — the fold cache
      (ADR-0022) keys fold membership on `(segment, line)`; plain materialize
      drops the numbers. -/
  ops : List (Nat × ParsedOp)
  refusal : Option Refusal
  skipped : List Nat
  /-- Skew-future lines held back (ADR-0007): excluded from `ops` and `maxHlc`. -/
  deferred : List Nat
  maxHlc : Nat
  /-- Max HLC among the deferred lines (the ahead clock's real lead). -/
  maxDeferred : Nat
  warnings : List String
  /-- How many complete lines the segment held (a torn trailing fragment is not
      a line) — the fold cache's prefix boundary. -/
  lineCount : Nat

/-- Decode one segment: kept ops, the refusal (first bad line, unless
    `skipBad`), skipped lines, skew-deferred lines, the line-scoped max HLC, and
    clamp warnings. `skewBound`, when set, is the packed-HLC *physical* ceiling
    `now + W` for a foreign segment (ADR-0007): a line whose HLC physical
    exceeds it is deferred — kept out of `ops` and `maxHlc`, recorded in
    `deferred`, and it does not refuse the segment. The own segment passes
    `none` (authoritative, never skew-checked). -/
def decodeSegment (sd : SegmentData) (skipBad : Bool := false)
    (skewBound : Option Nat := none) : SegmentDecode := Id.run do
  let mut ops : List (Nat × ParsedOp) := []
  let mut refusal : Option Refusal := none
  let mut skipped : List Nat := []
  let mut deferred : List Nat := []
  let mut maxHlc := 0
  let mut maxDeferred := 0
  let mut warnings : List String := []
  let mut n := 0
  for lineBytes in completeLines sd.bytes do
    n := n + 1
    let decoded : Except Tl.Error ParsedOp :=
      match String.fromUTF8? lineBytes with
      | none => .error (.mk' .malformedLine
          "the line is not valid UTF-8 — repair it or rerun the read with --skip-bad")
      | some line =>
        match decodeLine line with
        | .ok p =>
          -- segments are per-replica authored (ADR-0001): a record stamped
          -- by another replica cannot live in this file
          if toCrockford p.stamp.replica 13 == sd.replicaId then .ok p
          else .error (.mk' .malformedLine
            s!"the record is stamped by replica {toCrockford p.stamp.replica 13} but sits in {sd.replicaId}.jsonl — the segment is mis-assembled; restore it from sync or remove it")
        | .error e => .error e
    match decoded with
    | .ok p =>
      -- a foreign op from beyond the skew window is deferred (ADR-0007): held
      -- back from the fold and from maxHlc until local time passes it, so it
      -- can neither win LWW from the future nor inflate the clock reseed. The
      -- branch is `¬ admittedB` — the exact predicate `Tl.Clock.Skew` proves
      -- monotone-in-now (deferral is eventual) and convergence-safe.
      if skewBound.any (fun b => !admittedB p.stamp.hlc b) then
        deferred := n :: deferred
        maxDeferred := max maxDeferred p.stamp.hlc
      else
        maxHlc := max maxHlc p.stamp.hlc
        warnings := warnings ++ p.warnings.map (s!"segment {sd.replicaId}.jsonl line {n}: " ++ ·)
        -- a refused segment's later good lines still feed maxHlc, never the fold
        if refusal.isNone then
          ops := (n, p) :: ops
    | .error e =>
      if skipBad then
        skipped := n :: skipped
      else if refusal.isNone then
        refusal := some { replicaId := sd.replicaId, line := n, error := enrich sd.replicaId n e }
  -- a refused segment contributes only its refusal: it is repaired, not waited
  -- on, so suppress its deferred lines (and their lead) too — a read/doctor must
  -- never say "held back, appears later" for a line that is actually refused
  let kept := if refusal.isSome then [] else ops.reverse
  let deferredKept := if refusal.isSome then [] else deferred.reverse
  let maxDeferredKept := if refusal.isSome then 0 else maxDeferred
  return { ops := kept, refusal, skipped := skipped.reverse,
           deferred := deferredKept, maxDeferred := maxDeferredKept, maxHlc, warnings,
           lineCount := n }

/-- Decode every segment, pairing each with its result. The skew bound applies
    to foreign segments only, and only when the own replica id is known: with it
    unknown (the `.tl/local/replica` file absent) we cannot tell a segment apart
    from our own, so we never defer — better to fold a maybe-future op than to
    silently defer one of our own (ADR-0007). Shared by `materialize` and the
    fold cache (`Tl.Store.Cache`), so the two paths cannot drift in per-line
    classification. -/
def decodeAll (segs : List SegmentData) (skipBad : Bool := false)
    (now : Option Nat := none) (ownReplica : Option String := none) :
    List (SegmentData × SegmentDecode) :=
  segs.map (fun sd =>
    let skewBound : Option Nat := match now, ownReplica with
      | some t, some own => if sd.replicaId == own then none else some (t + skewWindowMs)
      | _, _ => none
    (sd, decodeSegment sd skipBad skewBound))

/-- Assemble the `Loaded` from decoded segments and an already-computed state —
    the fold is the one thing the cached path does differently, every other
    field is the same function of the live decode. -/
def assemble (pairs : List (SegmentData × SegmentDecode)) (state : Tl.Kernel.State)
    (ownReplica : Option String := none) :
    Loaded :=
  -- linear accumulation (flatMap/filterMap, same order) — the loop-with-append
  -- shape walked the accumulator per segment
  { state
    ops := pairs.flatMap (fun (_, dec) => dec.ops.map (·.2))
    refused := pairs.filterMap (fun (_, dec) => dec.refusal)
    skipped := pairs.flatMap (fun (sd, dec) => dec.skipped.map (sd.replicaId, ·))
    deferred := pairs.flatMap (fun (sd, dec) => dec.deferred.map (sd.replicaId, ·))
    maxHlc := pairs.foldl (fun a (_, dec) => max a dec.maxHlc) 0
    maxDeferredHlc := pairs.foldl (fun a (_, dec) => max a dec.maxDeferred) 0
    -- the own replica's segment max HLC (transact's present-clock floor), computed
    -- here in the shared assembler so the cached and reference paths agree by
    -- construction (the cache property tests compare it — ADR-0022)
    ownMaxHlc := match ownReplica with
      | some rid => (pairs.find? (fun p => p.1.replicaId == rid)).elim 0 (fun p => p.2.maxHlc)
      | none => 0
    warnings := pairs.flatMap (fun (_, dec) => dec.warnings)
    segmentCount := pairs.length }

/-- Materialize a set of segments (pure — I/O happens in `readSegments`).
    When `now` is given, foreign segments are skew-checked against `now +
    skewWindowMs` (ADR-0007): a future-dated foreign op is deferred from the
    fold and from `maxHlc`. The own segment (`ownReplica`) is exempt. With
    `now := none` the skew check is off (the pure-fold default for tests).
    This is the uncached reference fold; `Tl.Store.Cache.materializeCached`
    must agree with it exactly (pinned by the cache property tests). -/
def materialize (segs : List SegmentData) (skipBad : Bool := false)
    (now : Option Nat := none) (ownReplica : Option String := none) : Loaded :=
  let pairs := decodeAll segs skipBad now ownReplica
  let loaded := assemble pairs Tl.Kernel.State.empty ownReplica
  { loaded with state := Tl.Kernel.fold (loaded.ops.map ParsedOp.kernelOp) }

/-- The lock-free read path: enumerate, read, materialize (ADR-0015 §5);
    enumeration disclosures (ignored non-segment files) join the warnings.
    `now`/`ownReplica` enable the foreign skew check (ADR-0007); callers on the
    read/write path pass them, pure-fold tests do not. -/
def readState (d : Dirs) (skipBad : Bool := false)
    (now : Option Nat := none) (ownReplica : Option String := none) : TlM Loaded := do
  let (segs, notes) ← readSegments d
  let loaded := materialize segs skipBad now ownReplica
  return { loaded with warnings := notes ++ loaded.warnings }

end Tl.Store
