/-
`Tests.VerifyLoadedTests` — loaded-environment coverage for the verifier's
selection, provenance, and semantic-observation wiring.

The ordinary CI legs run `tltest` with the toolchain and project `.olean`s
present, so these assertions exercise Lean's real stored module/declaration
tables. The git-floor leg ships only the compiled worker and skips on the
observed absence of a toolchain; no environment/setup branch may return an
empty group.
-/
import Tests.Harness
import Verify.Environment

open Lean
open Tl.Verify

namespace Tl.Tests

private def hasNamePrefix (prefixName : Name)
    (entries : Std.HashMap Name ConstantInfo) : Bool :=
  entries.toList.any fun (name, _) => Name.isPrefixOf prefixName name

/-- A proof of `False` produced by the *real* kernel-checking bypass, not by
    hand-assembling a `ConstantInfo`. `Lean.Kernel.Environment.addDecl` honours
    `debug.skipKernelTC` by routing to `addDeclWithoutChecking`, so what this
    returns is byte-identical to what a module compiled under that option would
    serialize into its `.olean`.

    This closes the gap the in-memory fixture in `Tests/VerifyTests.lean`
    leaves open. That one asserts replay rejects an ill-typed value the test
    itself invented; this one asserts replay rejects the artifact Lean's own
    bypass actually produces. It also cannot be checked in as a compiled
    fixture module: any audited scope containing it would fail the gate by
    design, which is the point. -/
private def forgeUncheckedFalse (env : Environment) :
    Except String ConstantInfo :=
  let forged : Declaration := .thmDecl {
    name := `ForgedFixture.provesFalse, levelParams := []
    type := .const ``False [], value := .const ``True.intro [] }
  match Lean.Kernel.Environment.addDecl env.toKernelEnv
      (Lean.debug.skipKernelTC.set ({} : Options) true) forged with
  | .error _ =>
    -- Not a pass: if the bypass ever stops accepting this, the regression below
    -- would silently test nothing.
    .error "addDecl refused the declaration even with debug.skipKernelTC set"
  | .ok bypassed =>
    match bypassed.find? `ForgedFixture.provesFalse with
    | some info => .ok info
    | none => .error "the bypass reported success but stored no constant"

/-- Exercise the exact environment tables used by `observeEnvironment`.
    Unsafe only because Lean's no-initializer module loader is unsafe; the
    assertions themselves are read-only. -/
private unsafe def verifyLoadedTestsRequired (sysroot : System.FilePath) :
    IO (List Outcome) := do
  initSearchPath sysroot
  let env ← loadEnvironmentNoInitializers #[`Verify.Environment]
  let production ← loadEnvironmentNoInitializers #[`Tl]
  let imported := modulesInEnvironment env #[`Verify.Report, `Verify.Policy, `Absent.Module]
  let projectModules ← projectModulesIn env
  let productionModules ← projectModulesIn production
  -- This must go through `observeEnvironment`, not manually compose its
  -- helpers: it pins the production wiring from replay closure through
  -- `propagatedAxioms` into each reported declaration. Injected audit findings
  -- make both mandatory evidence fields non-clean, so dropping either result is
  -- observable without checking a bad artifact into the repository.
  let stateObservation ← observeEnvironment "loaded transitive-axiom wiring"
    production #[`Tl.Kernel.State] #[`Tl.Kernel.State] productionModules
    #[`Tl.Kernel.State.merge_comm, `Absent.Landmark]
    (importAudit := fun _ _ _ => #["injected import-audit finding"])
    (replayAudit := fun _ _ => pure (some "injected replay-audit finding"))
  let reportNames := declarationNamesOf env #[`Verify.Report]
  let reportDecls ← declarationsOf env #[`Verify.Report] {}
  let reportRows := directImportRows env #[`Verify.Report]
  let analyzeClosure := replayClosure env #[`Tl.Verify.analyze]
  let projectRoot ← projectOLeanRoot
  let reportOLean ← realPathNormalized (← findOLean `Verify.Report)
  -- The bypass artifact is replayed alongside the genuine cone of the constants
  -- it names, so the rejection has to be the kernel's type mismatch and cannot
  -- be an incidental "unknown constant False" from an underpopulated input.
  let forged := forgeUncheckedFalse env
  let forgedError? ← match forged with
    | .error _ => pure none
    | .ok info =>
      replayConstantsError? (← mkEmptyEnvironment)
        ((replayClosure env #[``False, ``True.intro]).insert info.name info)
  return [
    check "Lean's kernel-checking bypass still accepts a forged proof of False"
      forged.toOption.isSome
      (match forged with | .error e => e | .ok _ => ""),
    check "independent replay rejects a real skipKernelTC-forged theorem"
      (forgedError?.isSome)
      "a declaration that reached the environment without kernel checking must not survive replay",
    check "the rejection names the forged declaration and the type mismatch"
      (forgedError?.any fun error =>
        error.contains "ForgedFixture.provesFalse" && error.contains "type mismatch"),
    check "the rejection teaches the fix"
      (forgedError?.any fun error => error.contains "Remove any kernel-checking bypass"),
    check "loaded module selection keeps the requested imported modules"
      (imported == #[`Verify.Report, `Verify.Policy]),
    check "project provenance includes a verifier module"
      (projectModules.contains `Verify.Report),
    check "project provenance excludes an external Std module"
      (!projectModules.contains `Std),
    check "project olean root contains the selected verifier artifact"
      (pathWithin projectRoot reportOLean),
    check "loaded declaration selection finds analyze in Verify.Report"
      (reportNames.contains `Tl.Verify.analyze),
    check "loaded declaration selection excludes another selected package module"
      (!reportNames.contains `Tl.Verify.importViolations),
    check "loaded declaration records retain their defining module"
      (reportDecls.any fun decl =>
        decl.name == `Tl.Verify.analyze && decl.module == `Verify.Report),
    check "loaded observation wires transitive axioms into declarations"
      (stateObservation.decls.any fun decl =>
        decl.name == `Tl.Kernel.State.merge_comm && decl.axioms.contains `propext),
    check "loaded observation retains the import-audit result"
      (stateObservation.evidence.importErrors.contains "injected import-audit finding"),
    check "loaded observation retains the replay-audit result"
      (stateObservation.evidence.replayError? == some "injected replay-audit finding"),
    check "loaded observation maps every policy landmark one-for-one"
      (stateObservation.landmarks.map (·.name) == stateObservation.expectedLandmarks),
    check "loaded landmark lookup distinguishes present and absent names"
      ((stateObservation.landmarks.any fun landmark =>
          landmark.name == `Tl.Kernel.State.merge_comm &&
          landmark.kind? == some .theoremDecl) &&
        (stateObservation.landmarks.any fun landmark =>
          landmark.name == `Absent.Landmark && landmark.kind?.isNone)),
    check "stored direct-import traversal reads Verify.Report's Std edge"
      (reportRows.any fun (name, imports) => name == `Verify.Report && imports.contains `Std),
    check "stored direct-import traversal does not leak an unselected row"
      (!reportRows.any fun (name, _) => name == `Verify.Policy),
    check "replay closure keeps its selected root"
      (analyzeClosure.contains `Tl.Verify.analyze),
    check "replay closure crosses from project declarations into Std"
      (hasNamePrefix `Std analyzeClosure)
  ]

/-- These checks need a Lean toolchain and the project `.olean`s, which the
    binary-only git-floor job does not ship. Whether one is present is an
    *observed fact* — `findSysroot` reads `LEAN_SYSROOT` or runs
    `lean --print-prefix` — so the skip is decided here rather than by a
    caller-supplied opt-out flag. A flag would let any environment turn this
    group into a green row whose stated reason is false, which is the
    silently-green class the trust gate exists to prevent; a fact cannot be
    asserted from outside, so no assertion that the ordinary legs left a
    variable unset is needed. A host that *does* resolve a toolchain must load
    the real modules: failure is one visible failing assertion, never an empty
    group or an uncaught exception that discards the suite report. -/
unsafe def verifyLoadedTests : IO (List Outcome) := do
  match ← (findSysroot : IO System.FilePath).toBaseIO with
  | .error _ =>
    return [check "loaded-environment checks skipped: no Lean toolchain on this host" true]
  | .ok sysroot =>
    try verifyLoadedTestsRequired sysroot
    catch error =>
      return [{
        name := "loaded-environment checks can resolve the project modules"
        passed := false
        msg := s!"{error}; run `lake exe tltest` from the repository root after `lake build`"
      }]

end Tl.Tests
