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

namespace Tl.Store

open Tl.Format

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
  /-- Line-scoped max envelope HLC across every segment (clock reseed). -/
  maxHlc : Nat
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

/-- Decode one segment: kept ops, the refusal (first bad line, unless
    `skipBad`), skipped lines, the line-scoped max HLC, and clamp warnings. -/
def decodeSegment (sd : SegmentData) (skipBad : Bool) :
    List ParsedOp × Option Refusal × List Nat × Nat × List String := Id.run do
  let mut ops : List ParsedOp := []
  let mut refusal : Option Refusal := none
  let mut skipped : List Nat := []
  let mut maxHlc := 0
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
      maxHlc := max maxHlc p.stamp.hlc
      warnings := warnings ++ p.warnings.map (s!"segment {sd.replicaId}.jsonl line {n}: " ++ ·)
      -- a refused segment's later good lines still feed maxHlc, never the fold
      if refusal.isNone then
        ops := p :: ops
    | .error e =>
      if skipBad then
        skipped := n :: skipped
      else if refusal.isNone then
        refusal := some { replicaId := sd.replicaId, line := n, error := enrich sd.replicaId n e }
  -- a refused segment contributes no ops at all
  let kept := if refusal.isSome then [] else ops.reverse
  return (kept, refusal, skipped.reverse, maxHlc, warnings)

/-- Materialize a set of segments (pure — I/O happens in `readSegments`). -/
def materialize (segs : List SegmentData) (skipBad : Bool := false) : Loaded := Id.run do
  let mut allOps : List ParsedOp := []
  let mut refused : List Refusal := []
  let mut skipped : List (String × Nat) := []
  let mut maxHlc := 0
  let mut warnings : List String := []
  for sd in segs do
    let (ops, refusal, skip, segMax, warns) := decodeSegment sd skipBad
    allOps := allOps ++ ops
    if let some r := refusal then
      refused := refused ++ [r]
    skipped := skipped ++ skip.map (sd.replicaId, ·)
    maxHlc := max maxHlc segMax
    warnings := warnings ++ warns
  return { state := Tl.Kernel.fold (allOps.map ParsedOp.kernelOp)
           ops := allOps, refused, skipped, maxHlc, warnings
           segmentCount := segs.length }

/-- The lock-free read path: enumerate, read, materialize (ADR-0015 §5);
    enumeration disclosures (ignored non-segment files) join the warnings. -/
def readState (d : Dirs) (skipBad : Bool := false) : TlM Loaded := do
  let (segs, notes) ← readSegments d
  let loaded := materialize segs skipBad
  return { loaded with warnings := notes ++ loaded.warnings }

end Tl.Store
