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
    `2026-06-15T09:00:00Z` and ADR-0020's `….296Z` forms). -/
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

end Tl.Format.Time
