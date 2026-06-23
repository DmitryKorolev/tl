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

/-- `parseCivilDate?` — the strict `YYYY-MM-DD` front-end for `--until <date>`
    (ADR-0010); month-aware ranges, padded fields only, no trailing time. -/
def civilDateTests : List Outcome :=
  let oks : List (String × (Nat × Nat × Nat)) :=
    [("2026-07-01", (2026, 7, 1)), ("1970-01-01", (1970, 1, 1)),
     ("2024-02-29", (2024, 2, 29)), ("9999-12-31", (9999, 12, 31))]
  let bad : List (String × String) :=
    [("2026-13-01", "month 13"), ("2026-00-10", "month 0"), ("2026-02-30", "Feb 30"),
     ("2025-02-29", "Feb 29 in a non-leap year"), ("2026-06-31", "June 31"),
     ("2026-06-00", "day 0"), ("2026-7-01", "unpadded month"), ("2026-07-1", "unpadded day"),
     ("2026/07/01", "slash separators"), ("2026-07-01T00:00:00Z", "trailing time"),
     ("", "empty"), ("not-a-date", "junk")]
  (oks.map (fun (s, ymd) =>
    check s!"parseCivilDate? '{s}'" (Time.parseCivilDate? s = some ymd)
      s!"got {repr (Time.parseCivilDate? s)}"))
  ++ (bad.map (fun (s, why) =>
    check s!"parseCivilDate? rejects {why} ('{s}')" (Time.parseCivilDate? s).isNone
      s!"parsed to {repr (Time.parseCivilDate? s)}"))

/-- `parseOffsetDateTime?` — a timestamp with an explicit `Z` / `±HH:MM` zone,
    normalized to UTC; a bare datetime (no zone) is rejected. Anchored on
    `2026-06-15T09:00:00Z = 1781514000000` (a `timeVectors` row). -/
def offsetDateTimeTests : List Outcome :=
  let anchor := 1781514000000
  let oks : List (String × Nat) :=
    [("2026-06-15T09:00:00Z", anchor),
     ("2026-06-15T09:00:00+00:00", anchor),
     ("2026-06-15T11:00:00+02:00", anchor),     -- 11:00 at +02:00 = 09:00 UTC
     ("2026-06-15T07:00:00-02:00", anchor),     -- 07:00 at −02:00 = 09:00 UTC
     ("2026-06-15T09:00:00.500Z", anchor + 500),
     ("1970-01-01T00:00:00Z", 0)]
  let bad : List (String × String) :=
    [("2026-06-15T09:00:00", "no zone designator"),
     ("2026-06-15T09:00:00z", "lowercase z"),
     ("2026-06-15T09:00:00+0200", "offset without a colon"),
     ("2026-06-15T09:00:00+15:00", "offset hour > 14"),
     ("2026-06-15T09:00:00+02:60", "offset minute 60"),
     ("2026-06-15T24:00:00Z", "hour 24"),
     ("2026-06-15 09:00:00Z", "space separator"),
     ("2026-06-15", "date only, no time"),
     ("1970-01-01T00:00:00+02:00", "pre-epoch once the offset is applied")]
  (oks.map (fun (s, ms) =>
    check s!"parseOffsetDateTime? '{s}' = {ms}" (Time.parseOffsetDateTime? s = some ms)
      s!"got {repr (Time.parseOffsetDateTime? s)}"))
  ++ (bad.map (fun (s, why) =>
    check s!"parseOffsetDateTime? rejects {why} ('{s}')" (Time.parseOffsetDateTime? s).isNone
      s!"parsed to {repr (Time.parseOffsetDateTime? s)}"))

/-- `startOfDayUtcMs` — local midnight as a UTC instant under an injected
    offset (local = UTC + offset), clamped at the epoch. `sod0` is
    `2026-06-15T00:00:00Z`. -/
def startOfDayTests : List Outcome :=
  let sod0 := 1781481600000
  let rows : List (Int × Nat × Nat × Nat × Nat) :=
    [(0, 2026, 6, 15, sod0),
     (120, 2026, 6, 15, sod0 - 7200000),    -- UTC+2: local midnight is 22:00 the prior UTC day
     (-300, 2026, 6, 15, sod0 + 18000000),  -- UTC−5: local midnight is 05:00 UTC
     (120, 1970, 1, 1, 0)]                   -- a pre-epoch result floors to 0
  rows.map (fun (off, y, m, d, expect) =>
    check s!"startOfDayUtcMs {off} {y}-{m}-{d} = {expect}"
      (Time.startOfDayUtcMs off y m d = expect)
      s!"got {Time.startOfDayUtcMs off y m d}")

/-- `parseUntilInstant?` — the shared dispatch: an offset-bearing timestamp
    ignores the injected offset, a bare date uses it, a bare datetime is
    rejected (ADR-0010 / ADR-0025 shared grammar). -/
def untilInstantTests : List Outcome :=
  [check "parseUntilInstant? — offset timestamp ignores the injected offset"
     (Time.parseUntilInstant? 999 "2026-06-15T09:00:00Z" = some 1781514000000)
     s!"got {repr (Time.parseUntilInstant? 999 "2026-06-15T09:00:00Z")}",
   check "parseUntilInstant? — bare date at UTC"
     (Time.parseUntilInstant? 0 "2026-06-15" = some 1781481600000)
     s!"got {repr (Time.parseUntilInstant? 0 "2026-06-15")}",
   check "parseUntilInstant? — bare date at +120 is local start-of-day"
     (Time.parseUntilInstant? 120 "2026-06-15" = some (1781481600000 - 7200000))
     s!"got {repr (Time.parseUntilInstant? 120 "2026-06-15")}",
   check "parseUntilInstant? — rejects a bare datetime (no offset)"
     (Time.parseUntilInstant? 0 "2026-06-15T09:00:00").isNone
     s!"got {repr (Time.parseUntilInstant? 0 "2026-06-15T09:00:00")}",
   check "parseUntilInstant? — rejects junk"
     (Time.parseUntilInstant? 0 "soon").isNone
     s!"got {repr (Time.parseUntilInstant? 0 "soon")}"]

def timeTests : List Outcome :=
  timeVectorTests ++ timeRejectTests ++ timeRoundtripProp ++ durationParseTests
  ++ civilDateTests ++ offsetDateTimeTests ++ startOfDayTests ++ untilInstantTests

end Tl.Tests
