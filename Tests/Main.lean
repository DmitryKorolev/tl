/-
`Tests.Main` — the in-repo test runner for the tested I/O shell (ADR-0009).
Builds as the `tltest` executable; exits non-zero on any failed assertion.
-/
import Tests.HlcTests
import Tests.CrockfordTests
import Tests.RecordTests
import Tests.ErrorTests
import Tests.Sha256Tests
import Tests.TimeTests
import Tests.CodecTests
import Tests.SysTests
import Tests.StoreTests
import Tests.CliTests
import Tests.CrossTests

open Tl.Tests

def main : IO UInt32 := do
  let sys ← sysTests
  let store ← storeTests
  let cli ← cliTests
  runAll [
    ("HLC update rules & encoding", hlcUnitTests),
    ("HLC hex round-trip (seeded property)", hlcRoundtripProp),
    ("HLC local-event monotonicity (seeded property)", hlcMonotoneProp),
    ("Crockford base32 & replica id", crockfordTests),
    ("Crockford round-trip (seeded property)", crockfordRoundtripProp),
    ("JSONL record round-trip & preserve-unknown", recordTests),
    ("Error codes, exit codes & --json envelope", errorCodeTests ++ envelopeTests),
    ("SHA-256 vectors, padding edges & the mint vector", sha256Tests),
    ("ISO-8601 UTC instant codec", timeTests),
    ("Record↔Op codec: canonical lines, escapes, fail-closed", codecTests),
    ("Native shim (ADR-0019): no-follow, sync, locks, entropy", sys),
    ("Store: discovery, transact, adversity, locking", store),
    ("CLI contract: verbs, guards, envelope, exit codes", cli),
    ("Cross-checks: encoding order, compiled kernel vs spec", crossTests)
  ]
