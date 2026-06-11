/-
`Tests.Main` — the in-repo test runner for the tested I/O shell (ADR-0009).
Builds as the `tltest` executable; exits non-zero on any failed assertion.
-/
import Tests.HlcTests
import Tests.CrockfordTests
import Tests.RecordTests
import Tests.ErrorTests

open Tl.Tests

def main : IO UInt32 :=
  runAll [
    ("HLC update rules & encoding", hlcUnitTests),
    ("HLC hex round-trip (seeded property)", hlcRoundtripProp),
    ("HLC local-event monotonicity (seeded property)", hlcMonotoneProp),
    ("Crockford base32 & replica id", crockfordTests),
    ("Crockford round-trip (seeded property)", crockfordRoundtripProp),
    ("JSONL record round-trip & preserve-unknown", recordTests),
    ("Error codes, exit codes & --json envelope", errorCodeTests ++ envelopeTests)
  ]
