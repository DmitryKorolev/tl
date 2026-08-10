/- Failure-path coverage for the Lean-native trust verifier. -/
import Tests.Harness
import Verify.Environment
import Verify.Proofs
import Verify.Report
import Verify.Supervise

namespace Tl.Tests

open Lean
open Tl.Verify

/-- Deletion guard for the verdict-logic theorems. They carry no landmark by
    design — landmarks guard the *product's* proved claims — so naming each one
    here is what makes retiring it a compile error rather than a silent
    deletion that leaves every gate green. Retire a name here only together
    with the theorem and the tier note in docs/codebase-map.md. -/
private def pinnedVerdictLogicTheorems : Unit :=
  let _ := @analyze_clean_iff
  let _ := @auditedReports_errors_eq_empty_iff
  let _ := @gateEvidence_errors_eq_empty_iff
  let _ := @analyzedGateEvidence_clean_iff
  let _ := @importViolations_isEmpty_iff
  let _ := @importViolations_size_eq
  let _ := @directImportAllowed_cases
  let _ := @completedSuccessfully_exitZero
  let _ := @completedSuccessfully_markerFinal
  let _ := @replayDependencies_superset
  let _ := @replayDependencies_inductiveSiblings
  let _ := @propagatedAxioms_sound
  let _ := @propagatedAxioms_complete
  let _ := @propagatedAxioms_closed
  let _ := @propagationFindings_eq_empty_iff
  let _ := @workerVerdict_status_zero_iff
  let _ := @workerVerdict_marker_iff
  let _ := @workerVerdict_marker_last
  let _ := @workerVerdict_report_empty
  let _ := @workerVerdict_diagnostics
  let _ := @workerVerdict_marker_iff_clean
  ()

private def cfg : Config :=
  { allowedAxioms := #[`propext, `Classical.choice, `Quot.sound] }

private def okDecl (name : Name) (kind := DeclKind.other) : Decl :=
  { name, «module» := `Tl.Kernel.Op, kind, axioms := #[`propext] }

private def clean : Observation :=
  { scope := "fixture"
    localModules := #[`Tl, `Tl.Kernel.Op, `Main]
    expectedModules := #[`Tl, `Tl.Kernel.Op, `Main]
    decls := #[okDecl `a .theoremDecl, okDecl `b]
    expectedLandmarks := #[`claimA]
    landmarks := #[{ name := `claimA, kind? := some .theoremDecl }]
    evidence := {
      importErrors := #[]
      replayError? := none
      propagationError? := none
      replayedConstants := 2
      importEdges := 3 } }

private def mentions (report : Report) (needle : String) : Bool :=
  report.errors.any fun error => error.contains needle

/-
What these rows are still for: the verdict *logic* — which conditions make a
scope clean, that every arm's silence is necessary and sufficient, and that the
ADR-0009 traversal reaches every edge and reports every rejected one — is proved
in `Verify/Proofs.lean` and is deliberately not re-asserted here on examples.
What stays is what those theorems cannot see: the wording each finding uses to
teach its fix, the truncation disclosure, the retention of concrete findings
through the aggregate, and — the first row below — that this file's own base
fixture really is clean. No theorem can supply that last one: `analyze_clean_iff`
is quantified over observations, so a fixture that quietly went dirty would keep
every `mentions` row green while stopping it from isolating the arm it names.
-/
private def reportTests : List Outcome :=
  let environmentFailure := analyze cfg {
    clean with evidence := { clean.evidence with
      replayError? := some "kernel replay rejected Bad.proof" } }
  let missing := analyze cfg {
    clean with expectedModules := clean.expectedModules.push `Tl.Kernel.Missing }
  let unexpected := analyze cfg {
    clean with localModules := clean.localModules.push `Tests.Accidental }
  let absentLandmark := analyze cfg {
    clean with landmarks := #[{ name := `claimA, kind? := none }] }
  let changedLandmark := analyze cfg {
    clean with landmarks := #[{ name := `claimA, kind? := some .other }] }
  let duplicateLandmark := analyze cfg {
    clean with
      expectedLandmarks := clean.expectedLandmarks ++ clean.expectedLandmarks
      landmarks := clean.landmarks ++ clean.landmarks }
  let localAxiom := analyze cfg {
    clean with decls := clean.decls.push {
      name := `unproved
      «module» := `Tl.Kernel.Op
      kind := .axiomDecl
      axioms := #[`unproved]
    } }
  let sorryDependency := analyze cfg {
    clean with decls := clean.decls.push {
      name := `unfinished
      «module» := `Tl.Kernel.Op
      kind := .theoremDecl
      axioms := #[`propext, `sorryAx]
    } }
  let propagationFailure := analyze cfg {
    clean with evidence := { clean.evidence with
      propagationError? := some "stored-body axiom propagation did not drain its \
        worklist within the bound, so this scope's transitive axiom rows are \
        incomplete and were discarded. Raise `propagationFuel`." } }
  let noDecls := analyze cfg { clean with decls := #[] }
  let noReplay := analyze cfg { clean with evidence := { clean.evidence with
    replayedConstants := 0 } }
  let noImportEdges := analyze cfg { clean with evidence := { clean.evidence with
    importEdges := 0 } }
  let emptyScope := analyze cfg {
    clean with localModules := #[], expectedModules := #[], decls := #[],
               expectedLandmarks := #[], landmarks := #[],
               evidence := { clean.evidence with replayedConstants := 0, importEdges := 0 } }
  let truncated := analyze cfg {
    clean with expectedModules := clean.expectedModules ++
      (Array.range 25).map fun index => Name.mkSimple s!"Absent{index}" }
  let axiomLandmark := analyze cfg {
    clean with landmarks := #[{ name := `claimA, kind? := some .axiomDecl }] }
  let droppedLandmarks := analyze cfg { clean with landmarks := #[] }
  let customRemedy := analyze cfg {
    clean with
      localModules := clean.localModules.push `Verify.Helper
      moduleRemedy := "edit the typed scope registry" }
  -- Assembled through `gateEvidenceOf`, the function the worker calls, so the
  -- rows exercise the shipped wiring rather than a hand-built `GateEvidence`.
  -- The split of labour with `analyzedGateEvidence_clean_iff` runs the other
  -- way from what it looks like: the theorem is *false* if a scope is audited
  -- twice or dropped from the assembly, since its right-hand side still demands
  -- a `GateClean` the verdict no longer depends on — that arm needs no row. Two
  -- things the theorem genuinely cannot see are covered here: it characterises
  -- only the empty verdict, where the two same-typed `Array String` arguments
  -- both reach it as `= #[]`, so nothing in it pins which becomes the inventory
  -- arm and which the unclaimed-source arm; and the findings themselves — that
  -- each observation reaches the verdict at all, labelled with its own scope.
  -- A pure permutation of the seven observations is invisible to both: each
  -- finding carries the scope from the observation it was built from, and the
  -- seven are only flattened, never read per field.
  let inventoryFinding :=
    ({ refusedSymlinks := #["Tl/Linked"] } : SourceInventory).errors "production"
      "Replace it with a regular in-tree directory or .lean file in the production source scope."
  let scopeFailure (scope : String) : Observation :=
    { clean with scope, evidence := { clean.evidence with
        replayError? := some s!"{scope} sentinel" } }
  let gateErrors := (gateEvidenceOf cfg
    (production := scopeFailure "production") (tests := scopeFailure "tests")
    (verifier := scopeFailure "verifier") (supervisor := scopeFailure "supervisor")
    (testSupervisor := scopeFailure "test supervisor")
    (tooling := scopeFailure "tooling")
    (release := scopeFailure "release")
    (inventoryErrors := #["inventory sentinel"])
    (unclaimedSources := #["Bench"])).errors
  [ checkEq "the base fixture is clean, so every row below isolates its own defect"
      (analyze cfg clean).errors.size 0,
    check "a scope that selected no declarations is not silently vacuous"
      (mentions noDecls "no declarations were selected"),
    check "a scope whose replay cone is empty is not silently vacuous"
      (mentions noReplay "nothing reached independent replay validation"),
    check "a scope whose stored import traversal read nothing is rejected"
      (mentions noImportEdges "no direct import edges were read"),
    check "vacuity guidance says the findings below cannot be trusted"
      (mentions noDecls "vacuous"),
    check "a vacuous scope says to restore the selection"
      (mentions noDecls "Restore the selection before trusting this run"),
    check "a named scope with no modules at all is rejected as vacuous"
      (mentions emptyScope "imported no first-party modules"),
    check "an empty scope says to restore its roots and inventory"
      (mentions emptyScope "Restore its registered roots and source inventory"),
    check "a long finding list keeps its first entries"
      (mentions truncated "Absent0"),
    check "a long finding list discloses the count it elided"
      (mentions truncated "… and 5 more"),
    check "a landmark degraded into an axiom is named as one"
      (mentions axiomLandmark "is an axiom"),
    check "a degraded landmark teaches the retire-together fix"
      (mentions axiomLandmark "Restore the theorem, or retire the proved claim and its landmark together"),
    check "dropping landmark observations cannot create an empty successful loop"
      (mentions droppedLandmarks "did not preserve the policy list"),
    check "a dropped landmark policy says to restore the one-for-one lookup"
      (mentions droppedLandmarks "Restore the one-for-one landmark lookup"),
    check "a scope mismatch uses its scope-specific repair instruction"
      (mentions customRemedy "edit the typed scope registry"),
    checkEq "the shipped assembly retains all scope, inventory, and claim findings"
      gateErrors.size 9,
    check "the shipped assembly audits each observation under its own scope name"
      (["production", "tests", "verifier", "supervisor", "test supervisor", "tooling",
        "release"].all fun scope =>
        gateErrors.any fun error =>
          error.contains s!"trust verification ({scope}): {scope} sentinel"),
    check "the shipped assembly retains inventory and unclaimed-source findings"
      (gateErrors.any (·.contains "inventory sentinel") &&
       gateErrors.any (·.contains "Bench")),
    check "the unclaimed-source arm, not the inventory arm, carries the sources"
      (gateErrors.any fun error =>
        error.contains "Bench" && error.contains "belong to no audited scope" &&
          error.contains "Move regular sources under an audited directory"),
    check "the inventory arm stays verbatim, unwrapped by the unclaimed-source message"
      (gateErrors.any fun error =>
        error == "inventory sentinel"),
    check "an environment/replay failure is retained"
      (mentions environmentFailure "kernel replay rejected Bad.proof"),
    -- The refusal must surface as its own finding. Without this arm a truncated
    -- axiom map would reach the verdict as an empty one, and every axiom arm
    -- below it would go quietly silent.
    check "a refused axiom propagation is reported, not read as no axioms"
      (mentions propagationFailure "did not drain its worklist"),
    check "a refused axiom propagation says how to fix it"
      (mentions propagationFailure "Raise `propagationFuel`"),
    check "an unimported source module is named" (mentions missing "Tl.Kernel.Missing"),
    check "missing-source guidance says how to fix it" (mentions missing "Import every source"),
    check "an unexpected cross-scope module is named"
      (mentions unexpected "Tests.Accidental"),
    check "an absent landmark is named" (mentions absentLandmark "claimA is absent"),
    check "an absent landmark teaches the retire-together fix"
      (mentions absentLandmark "Restore it, or retire the proved claim and its landmark together"),
    check "a changed landmark reports its actual kind"
      (mentions changedLandmark "non-theorem declaration"),
    check "a repeated landmark is rejected" (mentions duplicateLandmark "duplicate landmark"),
    check "a repeated landmark teaches the one-landmark-per-claim rule"
      (mentions duplicateLandmark "Give each documented proved claim its own landmark exactly once"),
    check "a first-party axiom is named" (mentions localAxiom "unproved"),
    check "a first-party axiom teaches the carried-assumption fix"
      (mentions localAxiom "record the residual as an explicit carried assumption"),
    check "a transitive forbidden axiom is named" (mentions sorryDependency "sorryAx"),
    check "a transitive forbidden axiom teaches the fix"
      (mentions sorryDependency "Finish the proof"),
    -- The inventory arm is the third finding class, produced outside `analyze`:
    -- `Verify/Main.lean` calls this once per source scope with that scope's own
    -- remedy, so the wording is production text and not test scaffolding.
    check "a refused symlink names its scope, its path and why it was refused"
      (inventoryFinding.any fun error =>
        error.startsWith "trust verification (production):" &&
          error.contains "Tl/Linked" && error.contains "refuses symbolic link"),
    check "a refused symlink carries its scope's own repair instruction"
      (inventoryFinding.any (·.contains "regular in-tree directory or .lean file in the production")),
    check "an inventory with nothing refused reports nothing"
      (({ modules := #[`Tl] } : SourceInventory).errors "production" "irrelevant").isEmpty ]

private def project : Std.HashSet Name :=
  (#[`Tl.Kernel.Op, `Tl.Kernel.Reach, `Tl.Kernel.Ready] : Array Name).foldl (·.insert ·) ∅

-- Traversal completeness and per-edge accumulation are proved
-- (`importViolations_isEmpty_iff`, `importViolations_size_eq`); these rows are
-- the message wording and the concrete allowlist decisions behind it.
private def importTests : List Outcome :=
  let violation := importViolations importPolicy "fixture" project
    #[(`Tl.Kernel.Ready, #[`Init.Data.List, `Mathlib.Data.Finset.Card, `Tl.Kernel.Op])]
  let allowlisted := importViolations importPolicy "fixture" project
    #[(`Tl.Kernel.Reach, #[`Mathlib.Data.Finset.Card])]
  let repackaged := importViolations importPolicy "fixture" project
    #[(`Tl.Kernel.Ready, #[`Aesop.Frontend])]
  [ checkEq "a disallowed direct import yields exactly one finding" violation.size 1,
    check "an ADR-0009 finding carries its audited scope"
      (violation.any fun error => error.startsWith "trust verification (fixture):"),
    check "the finding names both the importing and the imported module"
      (violation.any fun error =>
        error.contains "Tl.Kernel.Ready" && error.contains "Mathlib.Data.Finset.Card"),
    check "the finding teaches the ADR-0009 fix"
      (violation.any fun error => error.contains "amend ADR-0009"),
    check "an allowlisted module's Mathlib import yields nothing" allowlisted.isEmpty,
    checkEq "a Mathlib dependency package is a finding too" repackaged.size 1 ]

private def policyTests : List Outcome :=
  [ check "ordinary dependencies are unrestricted"
      (directImportAllowed importPolicy `Tests.Main `Batteries.Data.List),
    check "first-party dependencies are unrestricted"
      (directImportAllowed importPolicy `Tests.Main `Tl.Kernel.Op true),
    check "the three ADR-0009 modules may import Mathlib"
      (directImportAllowed importPolicy `Tl.Kernel.Reach `Mathlib.Data.Finset.Card),
    check "a direct Mathlib import elsewhere is rejected"
      (!directImportAllowed importPolicy `Tl.Kernel.Ready `Mathlib.Data.Finset.Card),
    check "a Mathlib dependency package cannot evade the package policy"
      (!directImportAllowed importPolicy `Tl.Kernel.Ready `Aesop),
    checkEq "the actual axiom allowance is pinned"
      allowedAxioms #[`propext, `Classical.choice, `Quot.sound],
    checkEq "the actual Mathlib-module allowance is pinned"
      importPolicy.mathlibModules
        #[`Tl.Kernel.Path, `Tl.Kernel.Reach, `Tl.Kernel.ReachBFS],
    -- The landmark list is what stops the proved-claim set from quietly
    -- shrinking, so retiring one must be a deliberate two-file edit rather
    -- than a single deletion that leaves every gate green.
    checkEq "the landmark set is pinned against a silent deletion"
      landmarkTheorems #[
        `Tl.Kernel.State.merge_comm,
        `Tl.Kernel.State.merge_assoc,
        `Tl.Kernel.State.merge_idem,
        `Tl.Kernel.fold_eq_of_mem_iff,
        `Tl.Kernel.fold_perm,
        `Tl.Kernel.fold_append,
        `Tl.Kernel.fold_append_self,
        `Tl.Kernel.mem_ready_iff,
        `Tl.Kernel.State.readyLe_total,
        `Tl.Kernel.State.ready_sorted,
        `Tl.Kernel.liveness,
        `Tl.Kernel.deadlock_exists,
        `Tl.Kernel.onCycle_kindSucc_iff,
        `Tl.Kernel.onCycle_precSucc_iff,
        `Tl.Kernel.State.sccWitnesses_same_witness_iff,
        `Tl.Kernel.effectiveStatus_epic,
        `Tl.Kernel.State.effStatusAux_epic_zero_ne_done,
        `Tl.Kernel.invariant_apply,
        `Tl.Kernel.close_cancel_monotone,
        `Tl.Kernel.effectiveStatus_metaSet,
        `Tl.Kernel.effectiveStatus_labelAdd,
        `Tl.Kernel.le_apply,
        `Tl.Kernel.fold_le_of_subset,
        `Tl.Kernel.apply_idem,
        `Tl.Kernel.ready_time_mono,
        `Tl.Kernel.mem_why_iff,
        `Tl.Kernel.State.mem_unblocks_iff,
        `Tl.Kernel.claimWonB_iff,
        `Tl.Kernel.claimWon_merge_iff,
        `Tl.Clock.Skew.skew_converges,
        `Tl.Kernel.foldFast_eq_fold,
        `Tl.Kernel.State.readyFast_eq,
        `Tl.Crdt.OrSet.presentElements_eq_ref,
        `Tl.Crdt.OrSet.entryLive_eq_ref,
        `Tl.Crdt.AssocList.ascending_of_sorted,
        `Tl.Cli.applyFacets_eq_filter,
        `Tl.Cli.mem_applyFacets_iff,
        `Tl.Cli.applyFacets_sublist,
        `Tl.Cli.readyFacets_cannot_widen,
        `Tl.Cli.readyRanked_cannot_widen,
        `Tl.Cli.mem_readyRanked_iff,
        `Tl.Cli.mem_readyRanked_ofLoaded_iff,
        `Tl.Cli.readyRanked_cannot_widen_ofLoaded,
        `Tl.Cli.View.rollup_ofLoaded,
        `Tl.Cli.View.issueData_ofLoaded,
        `Tl.Cli.readyPage_prefix,
        `Tl.Cli.readyPage_length,
        `Tl.Cli.labelFacet_pred_eq_true_iff,
        `Tl.Cli.assigneeFacet_pred_eq_true_iff ] ]

private def supervisorTests : List Outcome :=
  [ check "status zero without the final marker is rejected"
      (!completedSuccessfully verifierCompletionProtocol 0 ""),
    check "the exact final marker with status zero is accepted"
      (completedSuccessfully verifierCompletionProtocol 0
        s!"diagnostic\n{verifierCompletionProtocol.marker}\n"),
    check "a marker followed by later output is not final"
      (!completedSuccessfully verifierCompletionProtocol 0
        s!"{verifierCompletionProtocol.marker}\nlater work\n"),
    check "the test worker has a distinct accepted completion marker"
      (completedSuccessfully testCompletionProtocol 0
        s!"{testCompletionProtocol.marker}\n" &&
       !completedSuccessfully verifierCompletionProtocol 0
        s!"{testCompletionProtocol.marker}\n") ]

/-- Run a supervision, capturing the streams it forwards so a passing test does
    not print the gate's own failure diagnostics into the suite's output. -/
private def superviseCapturedWith
    (runWorker : System.FilePath → IO IO.Process.Output)
    (protocol : CompletionProtocol)
    (worker : System.FilePath) : IO (UInt32 × String × String) := do
  let out ← IO.mkRef { : IO.FS.Stream.Buffer }
  let err ← IO.mkRef { : IO.FS.Stream.Buffer }
  let status ← IO.withStdout (IO.FS.Stream.ofBuffer out) <|
    IO.withStderr (IO.FS.Stream.ofBuffer err) <|
      superviseWorkerWith runWorker protocol worker
  let stdout := String.fromUTF8! (← out.get).data
  let stderr := String.fromUTF8! (← err.get).data
  return (status, stdout, stderr)

private def superviseCaptured (worker : System.FilePath) :
    IO (UInt32 × String × String) :=
  superviseCapturedWith (fun path => IO.Process.output { cmd := path.toString })
    verifierCompletionProtocol worker

/-- Drive the supervision decision against real worker processes, plus an
    injected runner exception for the OS-error branch: the predicate above is
    only load-bearing if it is still applied to a worker's exit code/stdout and
    the worker's two diagnostic streams still reach the caller. -/
private def superviseTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let stub (name body : String) : IO System.FilePath := do
    let path := base / name
    IO.FS.writeFile path s!"#!/bin/sh\n{body}\n"
    let _ ← IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
    return path
  let (completed, completedOut, completedErr) ← superviseCaptured
    (← stub "completed"
      s!"echo worker-completed-stdout; echo worker-completed-stderr >&2; echo {verifierCompletionProtocol.marker}")
  let (trailingOutput, _, trailingErr) ← superviseCaptured
    (← stub "trailing"
      s!"echo {verifierCompletionProtocol.marker}; echo later-work; exit 0")
  let testCompletedWorker ← stub "test-completed" s!"echo {testCompletionProtocol.marker}"
  let (testCompleted, _, _) ← superviseCapturedWith
    (fun path => IO.Process.output { cmd := path.toString })
    testCompletionProtocol testCompletedWorker
  let (earlyExit, _, earlyErr) ←
    superviseCaptured (← stub "early" "echo working; exit 0")
  let (failedWithMarker, failedOut, failedErr) ← superviseCaptured
    (← stub "failed"
      s!"echo worker-failed-stdout; echo worker-failed-stderr >&2; echo {verifierCompletionProtocol.marker}; exit 1")
  let (missing, _, missingErr) ← superviseCaptured (base / "absent-worker")
  let nonExecutable := base / "not-executable"
  IO.FS.writeFile nonExecutable "not a process\n"
  let (execFailure, _, execFailureErr) ← superviseCaptured nonExecutable
  let spawnErrorWorker ← stub "spawn-error" "exit 0"
  let (spawnError, _, spawnErrorText) ← superviseCapturedWith
    (fun _ => throw (IO.userError "injected spawn failure"))
    verifierCompletionProtocol spawnErrorWorker
  IO.FS.removeDirAll base
  return [
    checkEq "a worker that completes and marks its verdict passes the gate" completed 0,
    check "the supervisor forwards a successful worker's stdout"
      (completedOut.contains "worker-completed-stdout"),
    check "the supervisor forwards a successful worker's stderr"
      (completedErr.contains "worker-completed-stderr"),
    checkEq "a worker with output after its marker fails the gate" trailingOutput 1,
    check "trailing work is diagnosed as an incomplete final verdict"
      (trailingErr.contains "last nonempty stdout line"),
    checkEq "the test completion protocol accepts a marked real worker" testCompleted 0,
    checkEq "a worker that exits zero without the marker fails the gate" earlyExit 1,
    check "an early exit is diagnosed as one" (earlyErr.contains "early-exit"),
    checkEq "a marker cannot rescue a worker that failed" failedWithMarker 1,
    check "the supervisor forwards a failed worker's stdout"
      (failedOut.contains "worker-failed-stdout"),
    check "the supervisor forwards a failed worker's stderr"
      (failedErr.contains "worker-failed-stderr"),
    check "a worker that exited non-zero is not diagnosed as an early exit"
      (failedErr.contains "exited with status 1" && !failedErr.contains "early-exit"),
    checkEq "a missing worker fails the gate" missing 1,
    check "a missing worker names the path and how to build it"
      (missingErr.contains "absent-worker" && missingErr.contains "lake build tlverify"),
    checkEq "an existing but unexecutable worker fails the gate" execFailure 1,
    check "a real exec failure teaches permissions and rebuild remedies"
      (execFailureErr.contains "could not execute" &&
       execFailureErr.contains "executable permission" &&
       execFailureErr.contains "lake build tlverify"),
    checkEq "a process-spawn exception fails the gate" spawnError 1,
    check "a process-spawn exception names the path, cause, and rebuild action"
      (spawnErrorText.contains "spawn-error" &&
       spawnErrorText.contains "injected spawn failure" &&
       spawnErrorText.contains "lake build tlverify")
  ]

private def inventoryScopeTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let targets ← IO.FS.createTempDir
  let layout := { auditLayout with
    sourceDirectories := #[
      { scope := .production, path := "Tl", modulePrefix := `Tl },
      { scope := .tests, path := "Tests", modulePrefix := `Tests }
    ]
    rootSources := #[
      { scope := .production, path := "Tl.lean", module := `Tl },
      { scope := .production, path := "Root.lean", module := `Root }
    ] }
  IO.FS.createDirAll (base / "Tl")
  IO.FS.createDirAll (base / "docs")
  IO.FS.createDirAll (base / "prose")
  IO.FS.writeFile (base / "Tl" / "Op.lean") "def x := 1\n"
  IO.FS.writeFile (base / "Tl.lean") "import Tl.Op\n"
  IO.FS.writeFile (base / "lakefile.lean") "import Lake\n"
  IO.FS.writeFile (base / "docs" / "notes.md") "prose, not a module\n"
  let claimed ← unclaimedSources base layout
  IO.FS.createDirAll (base / "Bench")
  IO.FS.writeFile (base / "Bench" / "Sneaky.lean") "def y := 2\n"
  IO.FS.writeFile (base / "Loose.lean") "def z := 3\n"
  -- A lowercase directory carrying both data and Lean, like the real
  -- `release/` and `scripts/`. Worth its own row: the claim's `path` is
  -- matched as a string, so a claim whose case does not match the directory
  -- on disk silently stops covering it.
  IO.FS.createDirAll (base / "release")
  IO.FS.writeFile (base / "release" / "Plan.lean") "def plan := 6\n"
  IO.FS.writeFile (base / "release" / "plan.json") "{}\n"
  IO.FS.createDirAll (targets / "linked-directory")
  IO.FS.writeFile (targets / "Linked.lean") "def linked := 4\n"
  IO.FS.writeFile (targets / "notes.md") "not a Lean module\n"
  let link (target path : System.FilePath) : IO Bool := do
    let result ← IO.Process.output {
      cmd := "ln", args := #["-s", target.toString, path.toString] }
    return result.exitCode == 0
  let directoryLink ← link (targets / "linked-directory") (base / "LinkedDirectory")
  let leanLink ← link (targets / "Linked.lean") (base / "Linked.lean")
  let danglingLeanLink ← link (targets / "absent.lean") (base / "Dangling.lean")
  let danglingUnknownLink ← link (targets / "absent") (base / "DanglingUnknown")
  let nonLeanLink ← link (targets / "notes.md") (base / "NOTES-link")
  let nestedNonLeanLink ← link (targets / "notes.md") (base / "docs" / "NOTES-link")
  let nestedDirectoryLink ← link (targets / "linked-directory") (base / "prose" / "vendor")
  let claimedRootLink ← link (targets / "Linked.lean") (base / "Root.lean")
  IO.FS.createDirAll (base / ".claude" / "worktrees" / "nested")
  IO.FS.writeFile (base / ".claude" / "worktrees" / "nested" / ".git")
    "gitdir: /tmp/example\n"
  IO.FS.writeFile (base / ".claude" / "worktrees" / "nested" / "Foreign.lean")
    "axiom foreign : False\n"
  let unclaimed ← unclaimedSources base layout
  let scopedLayout := { layout with
    sourceDirectories := layout.sourceDirectories.push
      { scope := .production, path := "Bench", modulePrefix := `Bench }
      |>.push { scope := .release, path := "release", modulePrefix := `release }
    rootSources := layout.rootSources.push
      { scope := .production, path := "Loose.lean", module := `Loose }
      |>.push { scope := .verifier, path := "VerifierRoot.lean", module := `VerifierRoot } }
  IO.FS.writeFile (base / "VerifierRoot.lean") "def verifierRoot := 5\n"
  let scopedInventories ← collectSourceInventories base scopedLayout
  let scopedExpected := scopedLayout.expectedSourceModules .production scopedInventories
  let verifierExpected := scopedLayout.expectedSourceModules .verifier scopedInventories
  let releaseExpected := scopedLayout.expectedSourceModules .release scopedInventories
  -- The wrong-case claim, checked rather than argued: on a case-insensitive
  -- filesystem `Release/` and `release/` are one directory, so this is the
  -- shape a `Release` claim would actually have taken.
  let miscasedLayout := { layout with
    sourceDirectories := layout.sourceDirectories.push
      { scope := .release, path := "Release", modulePrefix := `Release } }
  let miscasedInventories ← collectSourceInventories base miscasedLayout
  let miscasedExpected := miscasedLayout.expectedSourceModules .release miscasedInventories
  let miscasedUnclaimed ← unclaimedSources base miscasedLayout
  let scopedUnclaimed ← unclaimedSources base scopedLayout
  IO.FS.removeDirAll base
  IO.FS.removeDirAll targets
  return [
    check "an all-claimed checkout reports nothing" claimed.isEmpty,
    check "a new top-level directory of Lean sources is reported"
      (unclaimed.contains "Bench"),
    check "a new root-level Lean module is reported" (unclaimed.contains "Loose.lean"),
    check "an unclaimed symlink to a directory is reported fail-closed"
      (directoryLink && unclaimed.contains "LinkedDirectory"),
    check "an unclaimed symlink named .lean is reported"
      (leanLink && unclaimed.contains "Linked.lean"),
    check "a dangling unclaimed .lean symlink is still reported"
      (danglingLeanLink && unclaimed.contains "Dangling.lean"),
    check "an unclassifiable dangling symlink is reported fail-closed"
      (danglingUnknownLink && unclaimed.contains "DanglingUnknown"),
    check "an unclaimed regular non-Lean symlink is ignored"
      (nonLeanLink && !unclaimed.contains "NOTES-link"),
    check "a nested regular non-Lean symlink does not abort source inventory"
      (nestedNonLeanLink && !unclaimed.contains "docs"),
    check "a nested directory symlink becomes a diagnosed source-location finding"
      (nestedDirectoryLink && unclaimed.contains "prose"),
    check "a claimed root Lean source must still be a regular file"
      (claimedRootLink && unclaimed.contains "Root.lean"),
    check "a nested checkout boundary is not inventoried as this package's source"
      (!unclaimed.contains ".claude"),
    check "a typed directory claim feeds its scope's expected module set"
      (scopedExpected.contains `Bench.Sneaky),
    check "a typed root-source claim feeds its scope's expected module set"
      (scopedExpected.contains `Loose),
    check "a verifier root-source claim feeds the verifier expected module set"
      (verifierExpected.contains `VerifierRoot),
    check "a lowercase directory claim feeds its scope's expected module set"
      (releaseExpected.contains `release.Plan),
    check "a claimed directory's non-Lean data is not inventoried as a module"
      (!releaseExpected.any fun name => name.toString.endsWith "plan"),
    -- Stated as "never the name Lake builds", because the two filesystems
    -- fail differently and both must be covered: case-insensitively the claim
    -- reads the directory and derives `Release.Plan`, a module no target
    -- produces; case-sensitively it reads nothing at all. Asserting either
    -- specific outcome would pass on one CI leg and fail on the other.
    check "a directory claim whose case does not match the tree never derives the built module"
      (!miscasedExpected.contains `release.Plan)
      s!"a `Release` claim covered the `release` directory: {miscasedExpected}",
    check "a miscased claim leaves the real directory unclaimed rather than silently covered"
      (miscasedUnclaimed.contains "release")
      s!"unclaimed under the miscased layout: {miscasedUnclaimed}",
    check "typed source entries derive the corresponding top-level claims"
      (!scopedUnclaimed.contains "Bench" && !scopedUnclaimed.contains "Loose.lean" &&
       !scopedUnclaimed.contains "VerifierRoot.lean" && !scopedUnclaimed.contains "release"),
    check "Lake configuration is exempt without masquerading as an audited root module"
      (!layout.rootSources.any fun source => source.path == lakeConfigurationSource),
    checkEq "nothing else is reported" unclaimed.size 9,
    check "a directory carrying no Lean sources is not reported"
      (!unclaimed.contains "docs")
  ]

private def inventoryTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let root := base / "inventory"
  IO.FS.createDirAll (root / "Tl" / "Kernel")
  IO.FS.createDirAll (root / ".hidden")
  IO.FS.writeFile (root / "Tl" / "Kernel" / "Op.lean") "def x := 1\n"
  IO.FS.writeFile (root / "Tl.lean") "import Tl.Kernel.Op\n"
  IO.FS.writeFile (root / "lakefile.lean") "import Lake\n"
  IO.FS.writeFile (root / "notes.txt") "not a Lean module\n"
  IO.FS.writeFile (root / ".hidden" / "Canary.lean") "axiom hidden : False\n"
  let inventory ← modulesUnder root
  let foundRoot ← packageRoot? (root / "Tl" / "Kernel")
  let noRoot ← packageRoot? (base / "no-package" / "nested")
  let missingInventory ← modulesUnder (root / "missing")
  let linkPath := root / "cycle"
  let link ← IO.Process.output {
    cmd := "ln", args := #["-s", root.toString, linkPath.toString] }
  let danglingRootPath := root / "dangling-root"
  let danglingRootLink ← IO.Process.output {
    cmd := "ln", args := #["-s", (base / "absent-root").toString,
      danglingRootPath.toString] }
  let inventoryWithLink ← modulesUnder root
  let symlinkRootInventory ← modulesUnder linkPath
  let danglingRootInventory ← modulesUnder danglingRootPath
  IO.FS.removeDirAll base
  return [
    check "inventory finds a nested module" (inventory.modules.contains `Tl.Kernel.Op),
    check "inventory finds a root module" (inventory.modules.contains `Tl),
    check "generic inventory includes Lake's Lean configuration"
      (inventory.modules.contains `lakefile),
    check "inventory does not hide dot-prefixed Lean sources"
      (inventory.modules.any fun name => name.toString.contains "Canary"),
    checkEq "inventory contains exactly the fixture Lean files" inventory.modules.size 4,
    check "inventory classifies directory symlinks instead of throwing operationally"
      (link.exitCode == 0 && inventoryWithLink.refusedSymlinks.contains linkPath.toString),
    check "inventory classifies a symlinked root without following it"
      (link.exitCode == 0 && symlinkRootInventory.refusedSymlinks.contains linkPath.toString),
    check "inventory refuses a dangling symlink at the scope root"
      (danglingRootLink.exitCode == 0 &&
        danglingRootInventory.refusedSymlinks.contains danglingRootPath.toString),
    checkEq "package root is found from a nested working directory" foundRoot (some root),
    checkEq "package-root search reaches the filesystem root and fails closed" noRoot none,
    check "a missing source directory yields an empty inventory"
      (missingInventory.modules.isEmpty && missingInventory.refusedSymlinks.isEmpty),
    check "path containment compares components, not string prefixes"
      (!pathWithin "/repo/build" "/repo/build-other/Canary.olean"),
    check "a nested olean is within its project library root"
      (pathWithin "/repo/build" "/repo/build/Verify/Main.olean"),
    checkEq "the verifier scope excludes every registered supervisor root"
      (({ auditLayout with supervisorRoots :=
          #[`Verify.Launcher, `Verify.SecondSupervisor] }).verifierScopeModules
        #[`Verify.Main, `Verify.Launcher, `Verify.SecondSupervisor,
          `Verify.TestLauncher, `Verify.Supervise])
      #[`Verify.Main, `Verify.Supervise]
  ]

private def theoremInfo (name : Name) (type value : Expr) : ConstantInfo :=
  .thmInfo { name := name, levelParams := [], type := type, value := value }

private def axiomInfo (name : Name) (type : Expr) (isUnsafe := false) : ConstantInfo :=
  .axiomInfo { name := name, levelParams := [], type, isUnsafe }

private def mutualInductiveInfo : ConstantInfo :=
  .inductInfo {
    name := `VerifyFixture.Left
    levelParams := []
    type := .sort .zero
    numParams := 0
    numIndices := 0
    all := [`VerifyFixture.Left, `VerifyFixture.Right]
    ctors := []
    numNested := 0
    isRec := false
    isUnsafe := false
    isReflexive := false
  }

/-- A mutual inductive that also carries a constructor, so the edge seam and the
    replay cone can be told apart. -/
private def constructorBearingInductive : ConstantInfo :=
  .inductInfo {
    name := `VerifyFixture.Left
    levelParams := []
    type := .sort .zero
    numParams := 0
    numIndices := 0
    all := [`VerifyFixture.Left, `VerifyFixture.Right]
    ctors := [`VerifyFixture.mkLeft]
    numNested := 0
    isRec := false
    isUnsafe := false
    isReflexive := false
  }

private def identityType : Expr :=
  .forallE `p (.sort .zero)
    (.forallE `h (.bvar 0) (.bvar 1) .default) .default

private def validIdentity : Expr :=
  .lam `p (.sort .zero) (.lam `h (.bvar 0) (.bvar 0) .default) .default

private def invalidIdentity : Expr :=
  .lam `p (.sort .zero) (.lam `h (.bvar 0) (.bvar 1) .default) .default

private def replayTests : IO (List Outcome) := do
  let base ← mkEmptyEnvironment
  let valid := ({} : Std.HashMap Name ConstantInfo).insert `VerifyFixture.good
    (theoremInfo `VerifyFixture.good identityType validIdentity)
  let invalid := ({} : Std.HashMap Name ConstantInfo).insert `VerifyFixture.bad
    (theoremInfo `VerifyFixture.bad identityType invalidIdentity)
  let uncheckedDependency := invalid.insert `VerifyFixture.consumer
    (theoremInfo `VerifyFixture.consumer identityType (.const `VerifyFixture.bad []))
  let axiomDependency :=
    (({} : Std.HashMap Name ConstantInfo).insert `External.assumption
      (axiomInfo `External.assumption identityType)).insert `VerifyFixture.usesAssumption
      (theoremInfo `VerifyFixture.usesAssumption identityType
        (.const `External.assumption []))
  let replayCountFixture :=
    (({} : Std.HashMap Name ConstantInfo).insert `VerifyFixture.good
      (theoremInfo `VerifyFixture.good identityType validIdentity)).insert
      `VerifyFixture.unsafe (axiomInfo `VerifyFixture.unsafe identityType true)
  -- Two hops: the axiom is named only by `mid`, so `top` gets it only if the
  -- propagation is transitive rather than one-step.
  let twoHop :=
    ((axiomDependency.insert `VerifyFixture.mid
      (theoremInfo `VerifyFixture.mid identityType (.const `External.assumption []))).insert
      `VerifyFixture.top
      (theoremInfo `VerifyFixture.top identityType (.const `VerifyFixture.mid [])))
  -- Mutual recursion — the case the reverse worklist exists for. Each body
  -- names the other, and only one of them names the axiom.
  let mutualPair :=
    (({} : Std.HashMap Name ConstantInfo).insert `External.assumption
      (axiomInfo `External.assumption identityType)).insert `VerifyFixture.even
      (theoremInfo `VerifyFixture.even identityType (.const `VerifyFixture.odd []))
    |>.insert `VerifyFixture.odd
      (theoremInfo `VerifyFixture.odd identityType
        (.app (.const `VerifyFixture.even []) (.const `External.assumption [])))
  let mutualResult := propagatedAxioms mutualPair
  let twoHopResult := propagatedAxioms twoHop
  let axiomFree :=
    ({} : Std.HashMap Name ConstantInfo).insert `VerifyFixture.good
      (theoremInfo `VerifyFixture.good identityType validIdentity)
  let axiomFreeResult := propagatedAxioms axiomFree
  let seed := propagationSeed twoHop
  let rowOf (result : Option (Std.HashMap Name (Std.HashSet Name))) (name : Name) :
      Option (Std.HashSet Name) :=
    result.bind fun rows => rows[name]?
  let validError ← replayConstantsError? base valid
  let invalidError ← replayConstantsError? base invalid
  let dependencyError ← replayConstantsError? base uncheckedDependency
  let propagated := propagatedAxioms axiomDependency
  return [
    check "kernel replay accepts a valid stored theorem" validError.isNone,
    check "kernel replay rejects an unchecked ill-typed proof" invalidError.isSome
      "the semantic replay must close the unchecked-insertion class",
    check "kernel replay failure teaches the fix"
      (invalidError.any fun error => error.contains "Remove any kernel-checking bypass"),
    check "kernel replay rejects an unchecked external dependency artifact"
      dependencyError.isSome,
    check "replay dependencies include every mutual-inductive sibling"
      ((replayDependencies mutualInductiveInfo).contains `VerifyFixture.Right),
    checkEq "the replay count excludes constants the kernel replay skips"
      (replayedConstantCount replayCountFixture) 1,
    check "stored-body traversal finds a transitive external axiom"
      ((rowOf propagated `VerifyFixture.usesAssumption).any fun axioms =>
        axioms.contains `External.assumption),
    check "propagation crosses two hops, not just the direct user"
      ((rowOf twoHopResult `VerifyFixture.top).any fun axioms =>
        axioms.contains `External.assumption),
    check "propagation reaches both sides of a mutual pair"
      ((rowOf mutualResult `VerifyFixture.even).any (·.contains `External.assumption) &&
       (rowOf mutualResult `VerifyFixture.odd).any (·.contains `External.assumption)),
    check "a constant reaching no axiom gets no axiom"
      (axiomFreeResult.isSome &&
        !(rowOf axiomFreeResult `VerifyFixture.good).any (·.isEmpty == false)),
    -- Fail-closed: a truncated axiom map is the silent false negative this
    -- module exists to prevent, so the drain refuses instead of returning it.
    check "an exhausted worklist is refused, not truncated"
      ((drainWorklist seed.reverse 0 0 seed.axiomsByName seed.pending).isNone &&
       (drainWorklist seed.reverse 1 0 seed.axiomsByName seed.pending).isNone),
    check "the shipped fuel drains the same worklist"
      (propagatedAxioms twoHop).isSome,
    check "the edge seam keeps a declaration's stored constants"
      ((axiomEdges (theoremInfo `VerifyFixture.top identityType
        (.const `VerifyFixture.mid []))).contains `VerifyFixture.mid),
    -- The seam keeps an inductive's *constructors*; its mutual block is
    -- `replayDependencies`' addition for block reconstruction, not an
    -- axiom-dependency edge. Pinning both sides keeps the two from being
    -- conflated the next time one of them is edited.
    check "the edge seam keeps an inductive's constructors"
      ((axiomEdges constructorBearingInductive).contains `VerifyFixture.mkLeft),
    check "the edge seam is not the replay cone"
      (!(axiomEdges constructorBearingInductive).contains `VerifyFixture.Right &&
        (replayDependencies constructorBearingInductive).contains `VerifyFixture.Right)
  ]

def verifyTests : IO (List Outcome) := do
  return reportTests ++ importTests ++ policyTests ++ supervisorTests ++
    (← superviseTests) ++ (← inventoryTests) ++ (← inventoryScopeTests) ++
    (← replayTests)

end Tl.Tests
