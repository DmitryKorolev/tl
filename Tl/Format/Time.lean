/-
`Tl.Format.Time` — ISO-8601 UTC instants ↔ epoch milliseconds (ADR-0008/0010).

`deferUntil` is stored on disk as a normalized ISO-8601 UTC string and read by
the kernel as a plain `Instant` (ms since the Unix epoch, ADR-0010); the
ADR-0020 timestamp projections render the same way. This module is the strict
*canonical* codec for those stored/emitted forms: parse accepts exactly
`YYYY-MM-DDTHH:MM:SSZ` or `YYYY-MM-DDTHH:MM:SS.mmmZ` (uppercase `T`/`Z`, UTC
only, no leap seconds, years 1970–9999); render emits the same shape, with the
`.mmm` fraction exactly when the value has sub-second precision. The *lenient*
user-input parsing of `defer --until`/`--for` is a separate, backlogged
surface — it normalizes *to* this form, never widens it.

Civil-date conversion is the standard era/day-of-era algorithm (Hinnant's
`days_from_civil`/`civil_from_days`), `Nat`-only since the domain floor is the
epoch. Tested I/O shell (ADR-0004); no Mathlib (ADR-0009).
-/

namespace Tl.Format.Time

/-- Days since 1970-01-01 for a civil date (valid for dates ≥ 1970-01-01). -/
def daysFromCivil (y m d : Nat) : Nat :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- Civil date `(y, m, d)` from days since 1970-01-01. -/
def civilFromDays (z : Nat) : Nat × Nat × Nat :=
  let z' := z + 719468
  let era := z' / 146097
  let doe := z' - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m, d)

/-- Gregorian leap year. -/
def isLeap (y : Nat) : Bool := y % 4 = 0 && (y % 100 ≠ 0 || y % 400 = 0)

/-- Days in month `m` of year `y` (`m` is 1-based). -/
def daysInMonth (y m : Nat) : Nat :=
  if m = 2 then (if isLeap y then 29 else 28)
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30
  else 31

private def pad2 (n : Nat) : String :=
  if n < 10 then s!"0{n}" else s!"{n}"

private def pad3 (n : Nat) : String :=
  if n < 10 then s!"00{n}" else if n < 100 then s!"0{n}" else s!"{n}"

private def pad4 (n : Nat) : String :=
  if n < 10 then s!"000{n}" else if n < 100 then s!"00{n}"
  else if n < 1000 then s!"0{n}" else s!"{n}"

/-- Render epoch ms as the canonical ISO-8601 UTC instant: second precision,
    plus `.mmm` exactly when the value has sub-second precision (ADR-0008's
    `2026-06-15T09:00:00Z` and ADR-0020's `….296Z` forms).

    Round-trip precondition: `epochMsOfIso? ∘ isoOfEpochMs = some` only for
    `ms < 253402300800000` (year ≤ 9999) — above that `pad4` emits a 5-digit year
    the strict parser rejects. Latent today (every value enters via the clamped
    `epochMsOfIso?`; no defer-write surface or importer produces a larger `ms`),
    but a future write path must clamp before rendering. -/
def isoOfEpochMs (ms : Nat) : String :=
  let (secs, milli) := (ms / 1000, ms % 1000)
  let (days, daySecs) := (secs / 86400, secs % 86400)
  let (y, m, d) := civilFromDays days
  let frac := if milli = 0 then "" else "." ++ pad3 milli
  s!"{pad4 y}-{pad2 m}-{pad2 d}T{pad2 (daySecs / 3600)}:" ++
    s!"{pad2 (daySecs % 3600 / 60)}:{pad2 (daySecs % 60)}{frac}Z"

private def digits2? (cs : List Char) : Option Nat :=
  match cs with
  | [a, b] =>
    if a.isDigit && b.isDigit then some ((a.toNat - 48) * 10 + (b.toNat - 48)) else none
  | _ => none

private def digitsN? (cs : List Char) : Option Nat :=
  if cs.all Char.isDigit && cs ≠ [] then
    some (cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0)
  else none

/-- Parse a canonical ISO-8601 UTC instant to epoch ms. Strict: exactly
    `YYYY-MM-DDTHH:MM:SSZ` or with `.mmm`; field ranges checked (months,
    month-aware day-of-month, no hour 24, no leap second), years 1970–9999. -/
def epochMsOfIso? (s : String) : Option Nat := do
  let cs := s.toList
  -- split the fixed-position prefix YYYY-MM-DDTHH:MM:SS
  let (datePart, rest) := (cs.take 19, cs.drop 19)
  match datePart with
  | [y1, y2, y3, y4, '-', mo1, mo2, '-', d1, d2, 'T', h1, h2, ':', mi1, mi2, ':', s1, s2] => do
    let y ← digitsN? [y1, y2, y3, y4]
    let mo ← digits2? [mo1, mo2]
    let d ← digits2? [d1, d2]
    let h ← digits2? [h1, h2]
    let mi ← digits2? [mi1, mi2]
    let sec ← digits2? [s1, s2]
    let milli ← match rest with
      | ['Z'] => some 0
      | ['.', a, b, c, 'Z'] =>
        -- ".000Z" is non-canonical (the canonical form omits a zero
        -- fraction); rejecting it keeps decode/render symmetric
        match digitsN? [a, b, c] with
        | some 0 => none
        | m => m
      | _ => none
    if 1970 ≤ y && y ≤ 9999 && 1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ daysInMonth y mo
        && h < 24 && mi < 60 && sec < 60 then
      some (((daysFromCivil y mo d * 24 + h) * 60 + mi) * 60 * 1000
            + sec * 1000 + milli)
    else none
  | _ => none

/-- Parse a bare civil date `YYYY-MM-DD` (exactly 4-2-2 digits, no time, no
    separator beyond the two `-`), validating field ranges month-aware like
    `epochMsOfIso?`. The shared lenient front-end for a `--until <date>` value
    (ADR-0010) — distinct from the strict stored-instant codec above. -/
def parseCivilDate? (s : String) : Option (Nat × Nat × Nat) :=
  match s.toList with
  | [y1, y2, y3, y4, '-', mo1, mo2, '-', d1, d2] => do
    let y ← digitsN? [y1, y2, y3, y4]
    let mo ← digits2? [mo1, mo2]
    let d ← digits2? [d1, d2]
    if 1970 ≤ y && y ≤ 9999 && 1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ daysInMonth y mo then
      some (y, mo, d)
    else none
  | _ => none

/-- Local start-of-day (midnight) for a civil date as a UTC epoch-ms instant,
    given the injected UTC offset in minutes (local = UTC + offset; ADR-0010's
    one deliberate local-time use, threaded like `now` so parsing is
    deterministic). A pre-epoch result floors to `0`. -/
def startOfDayUtcMs (offsetMinutes : Int) (y mo d : Nat) : Nat :=
  -- a real UTC offset is within ±14h; clamp here — the one place the injected
  -- offset enters arithmetic — so a stray value (a typo'd `TL_UTC_OFFSET`, a
  -- corrupt tz read) shifts the day by at most that, never by days (review)
  let off := max (-840) (min 840 offsetMinutes)
  let dayMs : Int := (daysFromCivil y mo d : Int) * 86400000
  (max (dayMs - off * 60000) 0).toNat

/-- A zone designator at the end of a datetime: `Z` (UTC) or a numeric
    `±HH:MM` offset (`HH ≤ 14`, `MM < 60`), as signed minutes east of UTC. -/
private def parseZone? (cs : List Char) : Option Int :=
  match cs with
  | ['Z'] => some 0
  | [sgn, h1, h2, ':', m1, m2] =>
    if sgn = '+' || sgn = '-' then do
      let h ← digits2? [h1, h2]
      let m ← digits2? [m1, m2]
      if h ≤ 14 && m < 60 then
        let mag : Int := (h * 60 + m : Nat)
        some (if sgn = '-' then -mag else mag)
      else none
    else none
  | _ => none

/-- The suffix after `YYYY-MM-DDTHH:MM:SS`: an optional `.mmm` millisecond
    fraction (exactly three digits) then a required zone designator. Returns
    `(milliseconds, offsetMinutes)`. -/
private def parseFracZone? (rest : List Char) : Option (Nat × Int) :=
  match rest with
  | '.' :: more =>
    let frac := more.takeWhile Char.isDigit
    if frac.isEmpty then none  -- a dot with no fraction digits is malformed
    else do
      -- ISO fractional seconds → milliseconds: right-pad/truncate the digit run
      -- to exactly three (`.5`→500, `.05`→50, `.500`→500, `.5009`→500, sub-ms
      -- dropped), so a non-three-digit fraction is accepted, not rejected
      let ms3 := (frac.take 3) ++ List.replicate (3 - min frac.length 3) '0'
      let milli ← digitsN? ms3
      let off ← parseZone? (more.drop frac.length)
      some (milli, off)
  | zoneCs => do
    let off ← parseZone? zoneCs
    some (0, off)

/-- Parse an ISO-8601 datetime carrying an explicit zone designator — `Z` or a
    numeric `±HH:MM` offset — to a UTC epoch-ms instant. Fields are range-checked
    like `epochMsOfIso?`; the offset is subtracted to normalize to UTC. A bare
    datetime with no zone designator is rejected (`none`), so `--until` never
    silently guesses a zone (ADR-0010). The `.mmm` fraction is optional. -/
def parseOffsetDateTime? (s : String) : Option Nat := do
  let cs := s.toList
  let (datePart, rest) := (cs.take 19, cs.drop 19)
  match datePart with
  | [y1, y2, y3, y4, '-', mo1, mo2, '-', d1, d2, 'T', h1, h2, ':', mi1, mi2, ':', s1, s2] => do
    let y ← digitsN? [y1, y2, y3, y4]
    let mo ← digits2? [mo1, mo2]
    let d ← digits2? [d1, d2]
    let h ← digits2? [h1, h2]
    let mi ← digits2? [mi1, mi2]
    let sec ← digits2? [s1, s2]
    let (milli, offMin) ← parseFracZone? rest
    if 1970 ≤ y && y ≤ 9999 && 1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ daysInMonth y mo
        && h < 24 && mi < 60 && sec < 60 then
      let baseMs : Nat := ((daysFromCivil y mo d * 24 + h) * 60 + mi) * 60 * 1000 + sec * 1000 + milli
      let utc : Int := (baseMs : Int) - offMin * 60000
      if utc ≥ 0 then some utc.toNat else none
    else none
  | _ => none

/-- Resolve a `--until`-style absolute time value to a UTC instant: a timestamp
    with an explicit offset (`parseOffsetDateTime?`), or a bare date as local
    start-of-day under the injected offset. Any other shape — a bare datetime
    with no offset, junk — is `none` (the caller reports a teaching usage error).
    This is the shared *date/timestamp* resolver; relative durations go through
    `parseDurationMs?`. Together they are the one time-input grammar of ADR-0010,
    reused by the `tl log` selectors (ADR-0025) — not a second parser. -/
def parseUntilInstant? (offsetMinutes : Int) (s : String) : Option Nat :=
  match parseOffsetDateTime? s with
  | some ms => some ms
  | none => (parseCivilDate? s).map (fun (y, mo, d) => startOfDayUtcMs offsetMinutes y mo d)

/-- Parse a compact relative duration — `45m`, `1h`, `24h`, `7d`, `30s`, `500ms`
    — to milliseconds. The numeric part is digits-only and the unit is one of
    `ms`/`s`/`m`/`h`/`d` (lowercase). There is no default unit: a bare number,
    a fractional value, an unknown unit, or empty input all yield `none`. The
    `ms` unit is matched before `s` so `500ms` is not read as `500m` + `s`. -/
def parseDurationMs? (raw : String) : Option Nat :=
  let s := raw.trimAscii.toString
  let units : List (String × Nat) :=
    [("ms", 1), ("s", 1000), ("m", 60000), ("h", 3600000), ("d", 86400000)]
  units.findSome? (fun (u, mult) =>
    if s.endsWith u && s.length > u.length then
      let num := s.take (s.length - u.length)
      if num.all Char.isDigit then (· * mult) <$> num.toNat?
      else none
    else none)

end Tl.Format.Time
