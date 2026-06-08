/-
`Tests.Main` — the in-repo test runner for the tested I/O shell (ADR-0009).
Builds as the `tltest` executable; exits non-zero on any failed assertion.
-/
import Tests.HlcTests

open Tl.Tests

def main : IO UInt32 :=
  runAll [
    ("HLC update rules & encoding", hlcUnitTests),
    ("HLC hex round-trip (seeded property)", hlcRoundtripProp),
    ("HLC local-event monotonicity (seeded property)", hlcMonotoneProp)
  ]
