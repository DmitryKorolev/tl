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
import Tests.SanitizeTests
import Tests.GrammarTests
import Tests.SyncTests
import Tests.CacheTests
import Tests.PerfTests
import Tests.ImportsTests

open Tl.Tests

def main : IO UInt32 := do
  let sys ← sysTests
  let store ← storeTests
  let cli ← cliTests
  let grammar ← grammarTests
  let sync ← syncTests
  let cacheIo ← cacheIoTests
  let perf ← perfTests
  let perfPrim ← perfPrimitiveTests
  let perfBin ← perfBinaryTests
  let imports ← importsTests
  runAll [
    ("Root module imports every Tl/ source (AGENTS.md)", imports),
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
    ("Cross-checks: encoding order, compiled kernel vs spec", crossTests),
    ("Render sanitization (ADR-0014)", sanitizeTests),
    ("Grammar: tl help --json schema & parser agreement", grammar),
    ("Sync: line-union, ref I/O, local leg + read-time refresh", sync),
    ("Fold cache: codec round-trip & fail-closed decode", cacheCodecTests),
    ("Fold cache: validity branches (stale/refusal/deferral/skip-bad)", cacheFoldTests),
    ("Fold cache: cached fold ≡ fresh fold (seeded property)", cacheSuffixFoldProp),
    ("Fold cache: cacheVersion-bump guard (ADR-0022 §3)", cacheVersionGuardTests),
    ("Fold cache: file lifecycle, healing, doctor non-persist", cacheIo),
    ("Perf: ×4-op scaling stays near-linear on every fast path", perf),
    ("Perf: native-primitive fast paths (String compare, content hash)", perfPrim),
    ("Perf: end-to-end compiled-binary latency on a scaled repo", perfBin)
  ]
