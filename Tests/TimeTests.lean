/-
`Tests.TimeTests` — the canonical ISO-8601 UTC instant codec (ADR-0008/0010).

Vectors generated with python3 `datetime` (an independent implementation);
round-trip is checked property-style across seeded epoch values, and the
strictness rules (UTC-only, no leap seconds, month-aware day ranges, years
1970–9999) each have a discrete rejection row.
-/
import Tl.Format.Time
import Tests.Harness

namespace Tl.Tests

open Tl.Format

/-- `(iso, epoch ms)` oracle rows. -/
def timeVectors : List (String × Nat) :=
  [("1970-01-01T00:00:00Z", 0),
   ("1970-01-01T00:00:00.001Z", 1),
   ("1999-12-31T23:59:59.999Z", 946684799999),
   ("2000-02-29T00:00:00Z", 951782400000),
   ("2024-02-29T12:34:56.789Z", 1709210096789),
   ("2026-06-10T16:58:55.296Z", 1781110735296),
   ("2026-06-15T09:00:00Z", 1781514000000),
   ("2100-01-01T00:00:00Z", 4102444800000),
   ("9999-12-31T23:59:59.999Z", 253402300799999)]

def timeVectorTests : List Outcome :=
  timeVectors.map (fun (iso, ms) =>
    check s!"{iso} ↔ {ms}"
      (Time.epochMsOfIso? iso = some ms && Time.isoOfEpochMs ms = iso)
      s!"parse: {repr (Time.epochMsOfIso? iso)}; render: {Time.isoOfEpochMs ms}")

/-- Strict-parse rejections, one per documented rule. -/
def timeRejectTests : List Outcome :=
  let rejects : List (String × String) :=
    [("1969-12-31T23:59:59Z", "pre-epoch year"),
     ("2026-13-01T00:00:00Z", "month 13"),
     ("2026-00-10T00:00:00Z", "month 0"),
     ("2026-02-30T00:00:00Z", "Feb 30"),
     ("2025-02-29T00:00:00Z", "Feb 29 in a non-leap year"),
     ("2100-02-29T00:00:00Z", "Feb 29 in a century non-leap year"),
     ("2026-06-31T00:00:00Z", "June 31"),
     ("2026-06-00T00:00:00Z", "day 0"),
     ("2026-06-10T24:00:00Z", "hour 24"),
     ("2026-06-10T12:60:00Z", "minute 60"),
     ("2026-06-10T12:00:60Z", "leap second"),
     ("2026-06-10T12:00:00", "missing Z"),
     ("2026-06-10T12:00:00z", "lowercase z"),
     ("2026-06-10t12:00:00Z", "lowercase t"),
     ("2026-06-10 12:00:00Z", "space separator"),
     ("2026-06-10T12:00:00+00:00", "numeric offset"),
     ("2026-06-10T12:00:00.000Z", "zero fraction (non-canonical)"),
     ("2026-06-10T12:00:00.12Z", "two-digit fraction"),
     ("2026-06-10T12:00:00.1234Z", "four-digit fraction"),
     ("2026-6-10T12:00:00Z", "unpadded month"),
     ("10000-01-01T00:00:00Z", "five-digit year")]
  rejects.map (fun (s, why) =>
    check s!"rejects {why} ({s})" (Time.epochMsOfIso? s).isNone
      s!"parsed to {repr (Time.epochMsOfIso? s)}")

/-- Seeded round-trip across the representable range (cache the bound:
    10000-01-01 is the exclusive ceiling). -/
def timeRoundtripProp : List Outcome :=
  let ceiling := 253402300800000
  let samples := sample 0xdecade 200 (fun s =>
    let (s', v) := nextNat s ceiling
    (v, s'))
  [check "render ∘ parse = id on 200 seeded instants"
     (samples.all (fun ms => Time.epochMsOfIso? (Time.isoOfEpochMs ms) = some ms))]

/-- `parseDurationMs?` — compact relative durations (`tl.staleAfter`) and the
    rejection rules (no default unit, digits-only, lowercase units, ms-before-s). -/
def durationParseTests : List Outcome :=
  let oks : List (String × Nat) :=
    [("1h", 3600000), ("45m", 2700000), ("24h", 86400000), ("7d", 604800000),
     ("30s", 30000), ("500ms", 500), ("0h", 0), ("  1h  ", 3600000)]
  let bad : List (String × String) :=
    [("", "empty"), ("h", "unit only"), ("10", "no unit"), ("1.5h", "fractional"),
     ("10x", "unknown unit"), ("1hh", "doubled unit"), ("1H", "uppercase unit"),
     ("abc", "non-numeric"), ("-1h", "negative sign"), ("1 h", "internal space"),
     ("m500", "unit before number")]
  (oks.map (fun (s, ms) =>
    check s!"parseDurationMs? '{s}' = {ms}" (Time.parseDurationMs? s = some ms)
      s!"got {repr (Time.parseDurationMs? s)}"))
  ++ (bad.map (fun (s, why) =>
    check s!"parseDurationMs? rejects {why} ('{s}')" (Time.parseDurationMs? s).isNone
      s!"parsed to {repr (Time.parseDurationMs? s)}"))

def timeTests : List Outcome :=
  timeVectorTests ++ timeRejectTests ++ timeRoundtripProp ++ durationParseTests

end Tl.Tests
