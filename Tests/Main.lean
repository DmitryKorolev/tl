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
import Tests.ShellInventoryTests
import Tests.HermeticTests
import Tests.InstallerProcessTests
import Tests.VerifierProcessTests
import Tests.ReleaseDriftTests
import Tests.WorkflowCommandTests
import Tests.WorkflowPolicyTests
import Tests.SyncTests
import Tests.CacheTests
import Tests.PerfTests
import Tests.ImportsTests
import Tests.VerifyTests
import Tests.VerifyLoadedTests
import Tests.Runner
import Tests.RunnerTests
import Verify.Supervise

open Tl.Tests
open Tl.Verify

/-- Every group is deferred; listing or selecting groups never constructs other fixtures. -/
unsafe def testGroups : List TestGroup := [
  { id := "hermetic", label := "Native local/CI hermetic validation", run := fun _ => hermeticTests },
  { id := "imports", label := "Root module imports every Tl/ source (AGENTS.md)", run := fun _ => importsTests },
  { id := "verify", label := "Lean-native trust verification: policy, inventory, kernel replay", run := fun _ => verifyTests },
  { id := "verify-loaded", label := "Lean-native trust verification: loaded environment selection", run := fun _ => verifyLoadedTests },
  { id := "hlc", label := "HLC update rules & encoding", run := fun _ => pure (hlcUnitTests) },
  { id := "hlc-roundtrip", label := "HLC hex round-trip (seeded property)", run := fun _ => pure (hlcRoundtripProp) },
  { id := "hlc-monotone", label := "HLC local-event monotonicity (seeded property)", run := fun _ => pure (hlcMonotoneProp) },
  { id := "crockford", label := "Crockford base32 & replica id", run := fun _ => pure (crockfordTests) },
  { id := "crockford-roundtrip", label := "Crockford round-trip (seeded property)", run := fun _ => pure (crockfordRoundtripProp) },
  { id := "record", label := "JSONL record round-trip & preserve-unknown", run := fun _ => pure (recordTests) },
  { id := "errors", label := "Error codes, exit codes & --json envelope", run := fun _ => pure (errorCodeTests ++ envelopeTests) },
  { id := "sha256", label := "SHA-256 vectors, padding edges & the mint vector", run := fun _ => pure (sha256Tests) },
  { id := "time", label := "ISO-8601 UTC instant codec", run := fun _ => pure (timeTests) },
  { id := "codec", label := "Record↔Op codec: canonical lines, escapes, fail-closed", run := fun _ => pure (codecTests) },
  { id := "sys", label := "Native shim (ADR-0019): no-follow, sync, locks, entropy", run := fun _ => sysTests },
  { id := "store", label := "Store: discovery, transact, adversity, locking", run := fun _ => storeTests },
  { id := "cli", label := "CLI contract: verbs, guards, envelope, exit codes", run := fun _ => cliTests },
  { id := "cross", label := "Cross-checks: encoding order, compiled kernel vs spec", run := fun _ => pure (crossTests) },
  { id := "cross-evidence", label := "Cross-check evidence: the drift guard, and ADR-0004's list == the registry", run := fun _ => do return crossEvidenceGuardTests ++ (← crossEvidenceTests) },
  { id := "sanitize", label := "Render sanitization (ADR-0014)", run := fun _ => pure (sanitizeTests) },
  { id := "grammar", label := "Grammar: tl help --json schema & parser agreement", run := fun _ => grammarTests },
  { id := "doc-grammar", label := "Docs vs grammar: vision surface == commandSpecs", run := fun _ => docGrammarTests },
  { id := "release-identity", label := "Release identity: repository/workflow/npm pins do not drift", run := fun _ => releaseIdentityTests },
  { id := "release-plan", label := "Release plan: enabled channels, and the documents that state them", run := fun _ => releasePlanTests },
  { id := "release-tool", label := "tlrelease: dispatch, usage, and the two refusals", run := fun _ => releaseToolTests },
  { id := "shell-inventory", label := "Exact three-program shell inventory", run := fun _ => shellInventoryTests },
  { id := "verifier-process", label := "Standalone verifier public-process probes — process", run := fun _ => verifierProcessTests },
  { id := "verifier-mutations", label := "Standalone verifier public-process probes — mutations", run := fun _ => verifierProcessMutationTests },
  { id := "verifier-command", label := "Standalone verifier public-process probes — command", run := fun _ => verifierSuiteCommandTests },
  { id := "installer-command", label := "Installer public-process probes — command", run := fun _ => installerSuiteCommandTests },
  { id := "installer-branches", label := "Installer public-process probes — branches", run := fun _ => installerBranchTests },
  { id := "installer-branch-mutations", label := "Installer public-process probes — branch-mutations", run := fun _ => installerBranchMutationTests },
  { id := "installer-process", label := "Installer public-process probes — process", run := fun _ => installerProcessTests },
  { id := "installer-process-mutations", label := "Installer public-process probes — process-mutations", run := fun _ => installerProcessMutationTests },
  { id := "release-drift", label := "Release drift: documented invocations, and one decision about a missing tool", run := fun _ => releaseDriftTests },
  { id := "workflow-commands", label := "Typed workflow output producers", run := fun _ => workflowCommandTests },
  { id := "workflow-release", label := "Typed release orchestration", run := fun _ => workflowReleaseTests },
  { id := "workflow-policy", label := "Workflow authority and invocation mutations", run := fun _ => workflowPolicyTests },
  { id := "release-privilege", label := "Release workflow: privileged jobs need a pushed tag", run := fun _ => releaseWorkflowPrivilegeTests },
  { id := "build-provenance", label := "Build provenance: tl version kinds, renderings, and stamp drift", run := fun _ => buildProvenanceTests },
  { id := "sync", label := "Sync: line-union, ref I/O, local leg + read-time refresh", run := fun _ => syncTests },
  { id := "cache-codec", label := "Fold cache: codec round-trip & fail-closed decode", run := fun _ => pure (cacheCodecTests) },
  { id := "cache-fold", label := "Fold cache: validity branches (stale/refusal/deferral/skip-bad)", run := fun _ => pure (cacheFoldTests) },
  { id := "cache-suffix", label := "Fold cache: cached fold ≡ fresh fold (seeded property)", run := fun _ => pure (cacheSuffixFoldProp) },
  { id := "cache-version", label := "Fold cache: cacheVersion-bump guard (ADR-0022 §3)", run := fun _ => pure (cacheVersionGuardTests) },
  { id := "cache-io", label := "Fold cache: file lifecycle, healing, doctor non-persist", run := fun _ => cacheIoTests },
  { id := "perf", label := "Perf: ×4-op scaling stays near-linear on every fast path", run := fun _ => perfTests },
  { id := "perf-primitives", label := "Perf: native-primitive fast paths (String compare, content hash)", run := fun _ => perfPrimitiveTests },
  { id := "perf-binary", label := "Perf: end-to-end compiled-binary latency on a scaled repo", run := fun _ => perfBinaryTests },
  { id := "runner", label := "Focused selection, progress, timing and worker supervision", run := fun _ => runnerTests }
]

unsafe def main (args : List String) : IO UInt32 := do
  -- The progress sink wiring is independently checked by cliSyncPostureTests.
  Tl.Cli.syncProgressSink.set (fun _ => pure ())
  let status ← runTestRequest testGroups args
  if status == 0 then testProgress (testRequestCompletionProtocol args).verdict
  return status
