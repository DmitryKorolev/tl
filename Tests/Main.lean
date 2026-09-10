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
import Tests.DocGrammarTests
import Tests.ReleaseTests
import Tests.ReleaseToolTests
import Tests.ReleaseDriftTests
import Tests.WorkflowCommandTests
import Tests.SyncTests
import Tests.CacheTests
import Tests.PerfTests
import Tests.ImportsTests
import Tests.VerifyTests
import Tests.VerifyLoadedTests
import Verify.Supervise

open Tl.Tests
open Tl.Verify

unsafe def main : IO UInt32 := do
  -- the suite drives `performSync` in-process against temp remotes; the default
  -- sink would spray "syncing with remote 'origin'…" onto the runner's stderr.
  -- Silence it — the sink's wiring is asserted with a recording sink in
  -- `cliSyncPostureTests`.
  Tl.Cli.syncProgressSink.set (fun _ => pure ())
  let sys ← sysTests
  let store ← storeTests
  let cli ← cliTests
  let grammar ← grammarTests
  let docGrammar ← docGrammarTests
  let crossEvidence ← crossEvidenceTests
  let releaseIdentity ← releaseIdentityTests
  let releasePlan ← releasePlanTests
  let releaseTool ← releaseToolTests
  let releaseDrift ← releaseDriftTests
  let workflowCommands ← workflowCommandTests
  let workflowRelease ← workflowReleaseTests
  let releaseWorkflowPrivilege ← releaseWorkflowPrivilegeTests
  let buildProvenance ← buildProvenanceTests
  let sync ← syncTests
  let cacheIo ← cacheIoTests
  let perf ← perfTests
  let perfPrim ← perfPrimitiveTests
  let perfBin ← perfBinaryTests
  let imports ← importsTests
  let verify ← verifyTests
  let verifyLoaded ← verifyLoadedTests
  let status ← runAll [
    ("Root module imports every Tl/ source (AGENTS.md)", imports),
    ("Lean-native trust verification: policy, inventory, kernel replay", verify),
    ("Lean-native trust verification: loaded environment selection", verifyLoaded),
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
    ("Cross-check evidence: the drift guard, and ADR-0004's list == the registry", crossEvidenceGuardTests ++ crossEvidence),
    ("Render sanitization (ADR-0014)", sanitizeTests),
    ("Grammar: tl help --json schema & parser agreement", grammar),
    ("Docs vs grammar: vision surface == commandSpecs", docGrammar),
    ("Release identity: repository/workflow/npm pins do not drift", releaseIdentity),
    ("Release plan: enabled channels, and the documents that state them", releasePlan),
    ("tlrelease: dispatch, usage, and the two refusals", releaseTool),
    ("Release drift: documented invocations, and one decision about a missing tool", releaseDrift),
    ("Typed workflow output producers", workflowCommands),
    ("Typed release orchestration", workflowRelease),
    ("Release workflow: privileged jobs need a pushed tag", releaseWorkflowPrivilege),
    ("Build provenance: tl version kinds, renderings, and stamp drift", buildProvenance),
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
  if status == 0 then IO.println testCompletionProtocol.verdict
  return status
