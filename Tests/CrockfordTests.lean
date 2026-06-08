/-
`Tests.CrockfordTests` — Crockford base32 and replica-id (ADR-0007): round-trip,
the case-insensitive decode aliases (`i`/`l`→1, `o`→0), the excluded `u`, and
replica format/validity.
-/
import Tl.Format.Crockford
import Tl.Clock.Replica
import Tests.Harness

open Tl.Format Tl.Clock Tl.Tests

def crockfordTests : List Outcome := [
  checkEq "zero × 13" (toCrockford 0 13) "0000000000000",
  checkEq "one" (toCrockford 1 1) "1",
  checkEq "ten is a" (toCrockford 10 1) "a",
  checkEq "31 is z" (toCrockford 31 1) "z",
  -- decode aliases / case-insensitivity
  checkEq "decode i → 1" (crockfordVal? 'i') (some 1),
  checkEq "decode L → 1" (crockfordVal? 'L') (some 1),
  checkEq "decode o → 0" (crockfordVal? 'o') (some 0),
  checkEq "decode uppercase A → 10" (crockfordVal? 'A') (some 10),
  check "reject excluded u" (crockfordVal? 'u').isNone,
  check "reject space" (crockfordVal? ' ').isNone,
  -- round-trip
  checkEq "round-trip 12345" (ofCrockford? (toCrockford 12345 13)) (some 12345),
  checkEq "round-trip 2^64-1" (ofCrockford? (toCrockford (2 ^ 64 - 1) 13)) (some (2 ^ 64 - 1)),
  -- replica id
  checkEq "replica round-trip" (Replica.ofNat 999999).toNat? (some 999999),
  checkEq "replica id length" (Replica.ofNat 42).id.length 13,
  check "replica valid" (Replica.ofNat 42).valid,
  check "reject bad replica" (¬ (Replica.mk "not-13-chars!").valid)
]

/-- Seeded property: `ofCrockford? ∘ (toCrockford · 13) = some` on random 64-bit ids. -/
def crockfordRoundtripProp : List Outcome :=
  (sample 0xc0de 64 (fun s => let (s1, v) := nextNat s (2 ^ 64); (v, s1))).map (fun v =>
    checkEq s!"crockford {v}" (ofCrockford? (toCrockford v 13)) (some v))
