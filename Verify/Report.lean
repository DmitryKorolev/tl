/- Pure decision logic for the Lean-native trust verifier. -/
import Std

open Lean (Name)

namespace Tl.Verify

/-- The seven environments one run audits, each loaded and inspected on its own.

    This is deliberately not `Verify.Environment.AuditScope`, which owns
    *filesystem locations*: the two supervisors have no sources of their own,
    and three of these scopes are inspected out of the one `Verify/` source
    claim. A gate scope names an environment; a source scope names a directory.

    Every observation is indexed by one of these, so the scope an observation
    belongs to is fixed when it is built and cannot be reassigned by where it is
    passed. Adding a case here is a compile error in `GateScope.label` and in
    `AuditLayout.gateRoots`, which is where a new environment's name and roots
    are decided. Reaching the verdict additionally needs a field in
    `ScopeObservations`, and nothing forces that: a case added here and nowhere
    else names an environment the gate never audits. -/
inductive GateScope where
  | production
  | tests
  | verifier
  | supervisor
  | testSupervisor
  | tooling
  | release
  deriving DecidableEq, Repr, Inhabited

/-- How a finding names its scope, and how the summary line lists it. Derived
    from the constructor rather than carried alongside it, so no observation can
    report itself under another scope's name. -/
def GateScope.label : GateScope → String
  | .production => "production"
  | .tests => "tests"
  | .verifier => "verifier"
  | .supervisor => "verifier supervisor"
  | .testSupervisor => "test supervisor"
  | .tooling => "tooling"
  | .release => "release"

inductive DeclKind where
  | axiomDecl
  | theoremDecl
  | other
  deriving DecidableEq, Repr, Inhabited

structure Decl where
  name : Name
  «module» : Name
  kind : DeclKind
  axioms : Array Name
  deriving Repr, Inhabited

structure Landmark where
  name : Name
  kind? : Option DeclKind
  deriving Repr, Inhabited

def defaultModuleRemedy : String :=
  "Import every source in the scope's root module; an unimported file is neither built nor verified."

/-- Mandatory semantic evidence for one scope. Keeping the import audit and
    replay verdict as named fields prevents either result from disappearing
    into clean-path array plumbing. -/
structure SemanticEvidence where
  importErrors : Array String
  replayError? : Option String
  /-- Set when stored-body axiom propagation refused to answer. Its own field
      rather than folded into the replay error: a truncated axiom map is a
      distinct failure with a distinct fix, and above all it must not reach the
      verdict as an *empty* axiom set, which would read as clean. -/
  propagationError? : Option String
  replayedConstants : Nat
  importEdges : Nat
  deriving Inhabited

/-- One scope's collected evidence. The scope is the structure's parameter, not
    a field: `Observation .production` and `Observation .tests` are different
    types, so an observation cannot be passed where another scope's is expected,
    and the scope name every finding below carries is read off the type. -/
structure Observation (scope : GateScope) where
  localModules : Array Name
  expectedModules : Array Name
  decls : Array Decl
  /-- Scope-specific repair for a source/import-closure mismatch. -/
  moduleRemedy : String := defaultModuleRemedy
  /-- Policy names and observed kinds stay separate so dropping the lookup
      cannot turn a nonempty landmark policy into an empty successful loop. -/
  expectedLandmarks : Array Name
  landmarks : Array Landmark
  evidence : SemanticEvidence
  deriving Inhabited

structure Config where
  allowedAxioms : Array Name
  deriving Inhabited

structure Report where
  errors : Array String
  deriving Repr, Inhabited

def declKindName : DeclKind → String
  | .axiomDecl => "an axiom"
  | .theoremDecl => "a theorem"
  | .other => "a non-theorem declaration"

def summarize (xs : Array String) (limit : Nat := 20) : String :=
  let shown := xs.extract 0 (min limit xs.size)
  let rest := xs.size - shown.size
  String.intercalate "\n"
    (shown.toList ++ if rest == 0 then [] else [s!"  … and {rest} more"])

/-- The seven independently audited worker scopes, one report each. Named fields
    make silently dropping one from the final verdict a type error rather than an
    array edit. -/
structure AuditedReports where
  production : Report
  tests : Report
  verifier : Report
  supervisor : Report
  testSupervisor : Report
  tooling : Report
  release : Report

def AuditedReports.errors (reports : AuditedReports) : Array String :=
  #[reports.production, reports.tests, reports.verifier, reports.supervisor,
    reports.testSupervisor, reports.tooling, reports.release].flatMap (·.errors)

def unclaimedSourceError? (unclaimed : Array String) : Option String :=
  if unclaimed.isEmpty then none else
    some s!"trust verification: {unclaimed.size} Lean source location(s) belong to no audited scope:\n\
      {summarize (unclaimed.map fun name => s!"  {name}")}\n\
      Move regular sources under an audited directory (Tl/, Tests/, Verify/, VerifyFixture/, scripts/, release/), register an in-tree location with its owning typed source scope in Verify/Environment.lean, or replace a symbolic-link source location with regular in-tree files; a source no scope loads is built but never inspected, and a linked directory cannot be audited without following paths outside the checkout."

/-- Every class of evidence required for the worker's final verdict. New audit
    classes must become fields here, so the final decision cannot forget to
    aggregate them through an anonymous mutable array. -/
structure GateEvidence where
  reports : AuditedReports
  inventoryErrors : Array String
  unclaimedSources : Array String

def GateEvidence.errors (evidence : GateEvidence) : Array String :=
  let errors := evidence.reports.errors ++ evidence.inventoryErrors
  match unclaimedSourceError? evidence.unclaimedSources with
  | none => errors
  | some error => errors.push error

/-
`analyze` is the whole verdict: one named arm per audited condition, each
returning the findings it reports and nothing else. The arms are separate
definitions rather than pushes into one mutable accumulator so that each
condition is stated — and proved equivalent to its finding being absent — in
`Verify.Proofs` without restating any message text.
-/

def replayFindings {scope : GateScope} (o : Observation scope) : Array String :=
  match o.evidence.replayError? with
  | none => #[]
  | some replayError => #[s!"trust verification ({scope.label}): {replayError}"]

/-- Axiom propagation refused to answer, so the axiom rows below it are
    incomplete and were discarded. Its own arm: silence here is what lets the
    axiom-dependency arm's silence mean anything. -/
def propagationFindings {scope : GateScope} (o : Observation scope) : Array String :=
  match o.evidence.propagationError? with
  | none => #[]
  | some propagationError => #[s!"trust verification ({scope.label}): {propagationError}"]

/-- Expected source modules the inspected environment did not import. -/
def missingModules {scope : GateScope} (o : Observation scope) : Array Name :=
  let localSet := o.localModules.foldl (·.insert ·) (∅ : Std.HashSet Name)
  o.expectedModules.filter fun name => !localSet.contains name

def missingModuleFindings {scope : GateScope} (o : Observation scope) : Array String :=
  let missing := missingModules o
  if missing.isEmpty then #[] else
    #[s!"trust verification ({scope.label}): {missing.size} source module(s) are absent from the imported environment:\n\
      {summarize (missing.map fun name => s!"  {name}")}\n\
      {o.moduleRemedy}"]

/-- Imported first-party modules the scope never declared. -/
def unexpectedModules {scope : GateScope} (o : Observation scope) : Array Name :=
  let expectedSet := o.expectedModules.foldl (·.insert ·) (∅ : Std.HashSet Name)
  o.localModules.filter fun name => !expectedSet.contains name

def unexpectedModuleFindings {scope : GateScope} (o : Observation scope) : Array String :=
  let unexpected := unexpectedModules o
  if unexpected.isEmpty then #[] else
    #[s!"trust verification ({scope.label}): {unexpected.size} imported first-party module(s) are outside the declared scope:\n\
      {summarize (unexpected.map fun name => s!"  {name}")}\n\
      {o.moduleRemedy}"]

/-- Why a nonempty scope's findings would be vacuous. -/
def vacuityReasons {scope : GateScope} (o : Observation scope) : List String :=
  (if o.decls.isEmpty then ["no declarations were selected from them"] else []) ++
  (if o.evidence.replayedConstants == 0 then ["nothing reached independent replay validation"] else []) ++
  (if o.evidence.importEdges == 0 then ["no direct import edges were read"] else [])

/-- Every semantic arm is silent when nothing was selected. All seven named
    scopes are mandatory, so an empty module set is itself vacuous; otherwise
    declarations, replay validation, and import traversal must each have
    observable evidence. -/
def vacuityFindings {scope : GateScope} (o : Observation scope) : Array String :=
  if o.localModules.isEmpty then
    #[s!"trust verification ({scope.label}): the named scope imported no first-party modules. Restore its registered roots and source inventory before trusting this run."]
  else
    let vacuous := vacuityReasons o
    if vacuous.isEmpty then #[] else
      #[s!"trust verification ({scope.label}): {o.localModules.size} module(s) were inspected but {String.intercalate ", and " vacuous}. Declaration ownership, the replay cone, or the stored import traversal has regressed, so the axiom and kernel-replay findings below are vacuous. Restore the selection before trusting this run."]

def landmarkPolicyFindings {scope : GateScope} (o : Observation scope) : Array String :=
  if o.landmarks.map (·.name) != o.expectedLandmarks then
    #[s!"trust verification ({scope.label}): landmark observation did not preserve the policy list. Restore the one-for-one landmark lookup before trusting this run."]
  else #[]

def landmarkKindFindings {scope : GateScope} (o : Observation scope) : Array String :=
  o.landmarks.filterMap fun landmark =>
    match landmark.kind? with
    | some .theoremDecl => none
    | some kind =>
      some s!"trust verification ({scope.label}): landmark {landmark.name} is {declKindName kind}, not a theorem. Restore the theorem, or retire the proved claim and its landmark together."
    | none =>
      some s!"trust verification ({scope.label}): landmark theorem {landmark.name} is absent. Restore it, or retire the proved claim and its landmark together."

/-- One pass of the duplicate-landmark scan: the names seen so far, and the
    names seen more than once. -/
def repeatedLandmarkStep (state : Std.HashSet Name × Array Name)
    (landmark : Landmark) : Std.HashSet Name × Array Name :=
  let (seen, repeated) := state
  if seen.contains landmark.name then (seen, repeated.push landmark.name)
  else (seen.insert landmark.name, repeated)

def repeatedLandmarks (landmarks : Array Landmark) : Array Name :=
  (landmarks.foldl repeatedLandmarkStep (∅, #[])).2

def duplicateLandmarkFindings {scope : GateScope} (o : Observation scope) : Array String :=
  let repeated := repeatedLandmarks o.landmarks
  if repeated.isEmpty then #[] else
    #[s!"trust verification ({scope.label}): duplicate landmark(s):\n\
      {summarize (repeated.map fun name => s!"  {name}")}\n\
      Give each documented proved claim its own landmark exactly once."]

def axiomDeclarations {scope : GateScope} (o : Observation scope) : Array Decl :=
  o.decls.filter (·.kind == .axiomDecl)

def axiomDeclarationFindings {scope : GateScope} (o : Observation scope) : Array String :=
  let axiomDecls := axiomDeclarations o
  if axiomDecls.isEmpty then #[] else
    #[s!"trust verification ({scope.label}): {axiomDecls.size} first-party axiom declaration(s):\n\
      {summarize (axiomDecls.map fun decl => s!"  {decl.name}  ({decl.module})")}\n\
      Prove the claim or record the residual as an explicit carried assumption; do not extend the kernel trust boundary locally."]

/-- Inspected declarations whose stored axiom dependencies leave the allowance.
    A first-party axiom is reported by its own arm, never also as depending on
    itself. -/
def axiomDependencyOffenders (cfg : Config) {scope : GateScope} (o : Observation scope) : Array String :=
  o.decls.filterMap fun decl =>
    if decl.kind == .axiomDecl then none
    else
      let bad := decl.axioms.filter fun name => !cfg.allowedAxioms.contains name
      if bad.isEmpty then none
      else some s!"  {decl.name}  ({decl.module})  depends on: {String.intercalate ", " (bad.toList.map toString)}"

def axiomDependencyFindings (cfg : Config) {scope : GateScope} (o : Observation scope) : Array String :=
  let offenders := axiomDependencyOffenders cfg o
  if offenders.isEmpty then #[] else
    #[s!"trust verification ({scope.label}): {offenders.size} declaration(s) depend on axioms outside {cfg.allowedAxioms.toList}:\n\
      {summarize offenders}\n\
      Finish the proof without `sorry` or native evaluation. If a residual is genuinely unprovable, decompose it and document the carried assumption."]

def analyze (cfg : Config) {scope : GateScope} (o : Observation scope) : Report :=
  { errors :=
      o.evidence.importErrors
        ++ replayFindings o
        ++ propagationFindings o
        ++ missingModuleFindings o
        ++ unexpectedModuleFindings o
        ++ vacuityFindings o
        ++ landmarkPolicyFindings o
        ++ landmarkKindFindings o
        ++ duplicateLandmarkFindings o
        ++ axiomDeclarationFindings o
        ++ axiomDependencyFindings cfg o }

/-- What the worker sends to each stream, and what it returns. -/
structure WorkerVerdict where
  diagnostics : Array String
  report : Array String
  status : UInt32
  deriving DecidableEq

/-- The whole verdict-to-exit decision, as a pure total function.

    Naming it is what removes the last unproved branch from the worker: with
    the decision here, `runChecked` emits `diagnostics`, emits `report`, and
    returns `status` unconditionally, so the lines CI exercises on every clean
    run are the same lines that run on a failure. A branch there would be the
    one arm no test reaches, guarding the outcome the project can least afford
    to get wrong — a silently green trust gate.

    The `marker` this takes is the supervising launcher's
    `CompletionProtocol.verdict` — the exact line it accepts as proof the worker
    reached the end. Passed in rather than imported so this module stays
    independent of the supervision protocol. -/
def workerVerdict (summary marker : String) (evidence : GateEvidence) : WorkerVerdict :=
  let errors := evidence.errors
  if errors.isEmpty then { diagnostics := #[], report := #[summary, marker], status := 0 }
  else { diagnostics := errors, report := #[], status := 1 }

/-- The seven observations one run produces, one per audited environment.

    Every field has a *different* type, so this is what closes the call-site
    hole seven same-typed parameters left open: passing the tests observation as
    `production` no longer compiles, and neither does duplicating one scope while
    dropping another. Field names are how the structure is written, but they are
    no longer the only thing standing between a swapped argument and a scope that
    is never audited. -/
structure ScopeObservations where
  production : Observation .production
  tests : Observation .tests
  verifier : Observation .verifier
  supervisor : Observation .supervisor
  testSupervisor : Observation .testSupervisor
  tooling : Observation .tooling
  release : Observation .release

/-- One scope's entry in the clean-run summary line. Label and count are one
    expression over one field, so a count cannot end up filed under another
    scope's name. -/
def Observation.summaryEntry {scope : GateScope} (o : Observation scope) : String :=
  s!"{scope.label}={o.decls.size}"

/-- What a clean run prints before its completion marker: what was inspected, in
    the scopes it was inspected under. -/
def ScopeObservations.summary (observations : ScopeObservations) : String :=
  let inspected := String.intercalate ", "
    [observations.production.summaryEntry, observations.tests.summaryEntry,
      observations.verifier.summaryEntry, observations.supervisor.summaryEntry,
      observations.testSupervisor.summaryEntry, observations.tooling.summaryEntry,
      observations.release.summaryEntry]
  s!"trust verification: ok; inspected {inspected} declarations; safe total \
    dependency cones independently replay-validated; \
    landmarks={observations.production.landmarks.size}"

/-- Assemble the whole run's evidence from the seven scope observations and the
    two inventory scans. The worker calls exactly this, so the verdict the
    theorems in `Verify.Proofs` characterise is the verdict it ships: a scope
    audited twice, or one left out *of this function*, makes
    `analyzedGateEvidence_clean_iff` false rather than merely unproved, so the
    build cannot go green on it.

    The call site is covered by the argument types rather than by convention:
    each field of `ScopeObservations` accepts one scope's observation and no
    other, and `observeEnvironment` mints an `Observation scope` only from an
    environment loaded under that same scope. What remains is the registry those
    two read — which roots and which sources belong to a scope — and a mismatch
    there is reported by the module arms rather than passed over. -/
def gateEvidenceOf (cfg : Config) (observations : ScopeObservations)
    (inventoryErrors unclaimedSources : Array String) : GateEvidence :=
  { reports :=
      { production := analyze cfg observations.production
        tests := analyze cfg observations.tests
        verifier := analyze cfg observations.verifier
        supervisor := analyze cfg observations.supervisor
        testSupervisor := analyze cfg observations.testSupervisor
        tooling := analyze cfg observations.tooling
        release := analyze cfg observations.release }
    inventoryErrors
    unclaimedSources }

end Tl.Verify
