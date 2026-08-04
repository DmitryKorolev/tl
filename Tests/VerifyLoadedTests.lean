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

/-- A module's direct imports as *written*, parsed from its own source header by
    Lean's own header parser.

    This is a second, independent path to the fact `directImportRows` reads out
    of the compiled `.olean` header table, which is what makes it usable as a
    pin: the two are produced by different code from different artifacts, so
    they disagree exactly when the collector drops, reorders, or invents an
    edge. Both include the implicit prelude imports a non-`prelude` module
    carries, so the rows compare equal element for element. -/
private def writtenImports (root : System.FilePath) (module : Name) : IO (Array Name) := do
  let path := (Name.components module).foldl
    (fun (dir : System.FilePath) part => dir / part.toString) root |>.addExtension "lean"
  let (imports, _, _) ← Lean.Elab.parseImports (← IO.FS.readFile path) path.toString
  return imports.map (·.module)

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
  -- The gate's own production roots, not a hand-written `#[`Tl]`: `Main` is a
  -- production root too, so selecting only the library root would leave it and
  -- anything reachable only from it outside every pin below.
  let production ← loadEnvironmentNoInitializers auditLayout.productionRoots
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
  -- The refusal arm, through the shipped wiring: a propagation that declines to
  -- answer must reach the verdict as a *finding*, never as an empty axiom map,
  -- which would read as clean and silence every axiom arm below it.
  let refusedObservation ← observeEnvironment "loaded propagation refusal"
    production #[`Tl.Kernel.State] #[`Tl.Kernel.State] productionModules
    #[`Tl.Kernel.State.merge_comm]
    (propagationAudit := fun _ => none)
  let reportNames := declarationNamesOf env #[`Verify.Report]
  let reportDecls ← declarationsOf env #[`Verify.Report] {}
  let reportRows := directImportRows env #[`Verify.Report]
  -- Truncation and early exit are what the ADR-0009 proofs cannot see: they
  -- characterise the traversal over the rows it is *handed*, so the collector
  -- that produces those rows has to be pinned separately. A truncating
  -- collector still returns one well-formed row per selected module and still
  -- reports a nonzero `importEdges`, so neither the vacuity arm nor a row-count
  -- assertion can catch it — the row *contents* are what has to be pinned, and
  -- pinning them against the table they were read from would prove nothing.
  -- `writtenImports` is the independent source of truth: the same fact taken
  -- from the module's own source header instead of its compiled `.olean`.
  let multiSel := #[`Verify.Report, `Verify.Policy, `Verify.Environment]
  let multiRows := directImportRows env multiSel
  -- Local to this test, never the shipped policy: it forbids everything the
  -- first selected module happens not to import, so the violation is
  -- contributed by a row that is not the first.
  let laterRowPolicy : ImportPolicy := { ordinaryPrefixes := #[`Init, `Std], mathlibModules := #[] }
  let laterRowFindings := importViolations laterRowPolicy "collector sentinel"
    (#[`Verify.Report].foldl (·.insert ·) (∅ : Std.HashSet Name)) multiRows
  let analyzeClosure := replayClosure env #[`Tl.Verify.analyze]
  let projectRoot ← projectOLeanRoot
  -- Resolved from the compiled artifact, not the working directory, so this
  -- reads the sources that produced the `.olean`s under audit whatever
  -- directory the suite was launched from.
  let packageDir? ← packageRoot? projectRoot
  -- Expectations are keyed off the collector's *own* rows, so each comparison
  -- below is about row contents alone and cannot fail merely because the
  -- collector returns rows in the environment's module order while a selection
  -- is written in another. Which modules get a row is the separate count and
  -- per-module arms' job, and between them nothing is left uncovered: a
  -- dropped, duplicated or substituted row breaks one of those, and a row whose
  -- edges were truncated breaks the equality.
  --
  -- An unreadable source degrades to an empty row so the rest of the group
  -- still reports, but the reason is kept rather than thrown away: without it
  -- the arms would accuse the collector of disagreeing with a header they in
  -- fact never read.
  let mut sourceReadErrors : Array String := #[]
  let writtenRowsOf (rows : Array (Name × Array Name)) :
      IO (Array (Name × Array Name) × Array String) := do
    match packageDir? with
    | none => return (#[], #[])
    | some dir =>
      let mut written := #[]
      let mut errors := #[]
      for (module, _) in rows do
        match ← (writtenImports dir module).toBaseIO with
        | .ok imports => written := written.push (module, imports)
        | .error error =>
          written := written.push (module, #[])
          errors := errors.push s!"{module}: {error}"
      return (written, errors)
  let (writtenRows, multiReadErrors) ← writtenRowsOf multiRows
  sourceReadErrors := sourceReadErrors ++ multiReadErrors
  -- The verifier rows above are three hand-picked modules, six stored edges at
  -- the widest, so on their own they pin the collector only that deep and only
  -- three rows wide — a cap at either bound would match all three. The whole
  -- production scope is the pin that has neither ceiling: every module the gate
  -- actually audits, every edge each one declares, and it widens by itself as
  -- the project grows.
  let scopeRows := directImportRows production productionModules
  let (scopeWritten, scopeReadErrors) ← writtenRowsOf scopeRows
  sourceReadErrors := sourceReadErrors ++ scopeReadErrors
  let scopeEdges := scopeRows.foldl (fun total (_, imports) => total + imports.size) 0
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
    checkEq "the stored import traversal returns one row per selected module"
      multiRows.size multiSel.size,
    check "every selected module contributes a row"
      (multiSel.all fun name => multiRows.any fun (rowName, _) => rowName == name),
    check "the verifier's own sources are reachable from the compiled artifact"
      packageDir?.isSome
      "no lakefile above the project olean root, so the header cross-check below reads nothing",
    check "every cross-checked source is readable at the resolved path"
      sourceReadErrors.isEmpty
      (String.intercalate "; " sourceReadErrors.toList),
    -- Guards the pin against passing because *both* sides came back empty: this
    -- names two edges that a first-row-only or drop-the-tail collector loses.
    check "the header cross-check is non-vacuous: a multi-import module parses to its later edges"
      ((writtenRows.find? (·.1 == `Verify.Environment)).any fun (_, imports) =>
        imports.contains `Lean.Replay && imports.contains `Verify.Report),
    checkEq "every collected row is its module's own written header, edge for edge"
      multiRows writtenRows,
    -- Row count and edge count, each pinned against something outside the table
    -- they come from: a collector that capped rows, or edges within a row, is
    -- caught by one or the other however high it set the cap.
    checkEq "the collector returns a row for every module of a whole audited scope"
      scopeRows.size productionModules.size,
    -- With the count above, this forces a bijection: 74 distinct audited modules
    -- each appearing among 74 rows leaves no room for a duplicate or a
    -- substitution. It is the arm the header equality cannot supply, because
    -- expectations are keyed off the collector's own row names — a collector
    -- that repeated one row's *name* would have its expectation repeat with it.
    check "every audited module of that scope contributes its own row"
      (productionModules.all fun module => scopeRows.any fun (rowName, _) => rowName == module)
      s!"{scopeRows.size} rows cover {(scopeRows.map (·.1)).toList.eraseDups.length} distinct modules",
    checkEq "every row of that scope is its module's own written header too"
      scopeRows scopeWritten,
    check "the whole-scope cross-check is wider and deeper than the hand-picked one"
      (productionModules.size ≥ 20 && scopeEdges ≥ 100)
      s!"{productionModules.size} modules and {scopeEdges} edges cross-checked",
    check "a forbidden edge after an allowed row is still reported"
      (laterRowFindings.any fun error => (error.splitOn "Verify.Policy").length > 1),
    check "loaded observation retains the import-audit result"
      (stateObservation.evidence.importErrors.contains "injected import-audit finding"),
    check "loaded observation retains the replay-audit result"
      (stateObservation.evidence.replayError? == some "injected replay-audit finding"),
    check "a refused propagation is reported rather than read as no axioms"
      (refusedObservation.evidence.propagationError?.isSome &&
        refusedObservation.decls.all (·.axioms.isEmpty)),
    check "the refusal teaches the fix at the shipped wiring"
      (refusedObservation.evidence.propagationError?.any fun message =>
        (message.splitOn "did not drain its worklist").length > 1 &&
          (message.splitOn "Raise `propagationFuel`").length > 1),
    check "a propagation that answers leaves the arm silent"
      (stateObservation.evidence.propagationError?.isNone),
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
