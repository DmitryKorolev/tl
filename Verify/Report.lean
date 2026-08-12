/- Pure decision logic for the Lean-native trust verifier. -/
import Std

open Lean (Name)

namespace Tl.Verify

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

structure Observation where
  scope : String
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

/-- The six independently audited worker scopes. Named fields make silently
    dropping one from the final verdict a type error rather than an array edit. -/
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

def replayFindings (o : Observation) : Array String :=
  match o.evidence.replayError? with
  | none => #[]
  | some replayError => #[s!"trust verification ({o.scope}): {replayError}"]

/-- Axiom propagation refused to answer, so the axiom rows below it are
    incomplete and were discarded. Its own arm: silence here is what lets the
    axiom-dependency arm's silence mean anything. -/
def propagationFindings (o : Observation) : Array String :=
  match o.evidence.propagationError? with
  | none => #[]
  | some propagationError => #[s!"trust verification ({o.scope}): {propagationError}"]

/-- Expected source modules the inspected environment did not import. -/
def missingModules (o : Observation) : Array Name :=
  let localSet := o.localModules.foldl (·.insert ·) (∅ : Std.HashSet Name)
  o.expectedModules.filter fun name => !localSet.contains name

def missingModuleFindings (o : Observation) : Array String :=
  let missing := missingModules o
  if missing.isEmpty then #[] else
    #[s!"trust verification ({o.scope}): {missing.size} source module(s) are absent from the imported environment:\n\
      {summarize (missing.map fun name => s!"  {name}")}\n\
      {o.moduleRemedy}"]

/-- Imported first-party modules the scope never declared. -/
def unexpectedModules (o : Observation) : Array Name :=
  let expectedSet := o.expectedModules.foldl (·.insert ·) (∅ : Std.HashSet Name)
  o.localModules.filter fun name => !expectedSet.contains name

def unexpectedModuleFindings (o : Observation) : Array String :=
  let unexpected := unexpectedModules o
  if unexpected.isEmpty then #[] else
    #[s!"trust verification ({o.scope}): {unexpected.size} imported first-party module(s) are outside the declared scope:\n\
      {summarize (unexpected.map fun name => s!"  {name}")}\n\
      {o.moduleRemedy}"]

/-- Why a nonempty scope's findings would be vacuous. -/
def vacuityReasons (o : Observation) : List String :=
  (if o.decls.isEmpty then ["no declarations were selected from them"] else []) ++
  (if o.evidence.replayedConstants == 0 then ["nothing reached independent replay validation"] else []) ++
  (if o.evidence.importEdges == 0 then ["no direct import edges were read"] else [])

/-- Every semantic arm is silent when nothing was selected. All six named
    scopes are mandatory, so an empty module set is itself vacuous; otherwise
    declarations, replay validation, and import traversal must each have
    observable evidence. -/
def vacuityFindings (o : Observation) : Array String :=
  if o.localModules.isEmpty then
    #[s!"trust verification ({o.scope}): the named scope imported no first-party modules. Restore its registered roots and source inventory before trusting this run."]
  else
    let vacuous := vacuityReasons o
    if vacuous.isEmpty then #[] else
      #[s!"trust verification ({o.scope}): {o.localModules.size} module(s) were inspected but {String.intercalate ", and " vacuous}. Declaration ownership, the replay cone, or the stored import traversal has regressed, so the axiom and kernel-replay findings below are vacuous. Restore the selection before trusting this run."]

def landmarkPolicyFindings (o : Observation) : Array String :=
  if o.landmarks.map (·.name) != o.expectedLandmarks then
    #[s!"trust verification ({o.scope}): landmark observation did not preserve the policy list. Restore the one-for-one landmark lookup before trusting this run."]
  else #[]

def landmarkKindFindings (o : Observation) : Array String :=
  o.landmarks.filterMap fun landmark =>
    match landmark.kind? with
    | some .theoremDecl => none
    | some kind =>
      some s!"trust verification ({o.scope}): landmark {landmark.name} is {declKindName kind}, not a theorem. Restore the theorem, or retire the proved claim and its landmark together."
    | none =>
      some s!"trust verification ({o.scope}): landmark theorem {landmark.name} is absent. Restore it, or retire the proved claim and its landmark together."

/-- One pass of the duplicate-landmark scan: the names seen so far, and the
    names seen more than once. -/
def repeatedLandmarkStep (state : Std.HashSet Name × Array Name)
    (landmark : Landmark) : Std.HashSet Name × Array Name :=
  let (seen, repeated) := state
  if seen.contains landmark.name then (seen, repeated.push landmark.name)
  else (seen.insert landmark.name, repeated)

def repeatedLandmarks (landmarks : Array Landmark) : Array Name :=
  (landmarks.foldl repeatedLandmarkStep (∅, #[])).2

def duplicateLandmarkFindings (o : Observation) : Array String :=
  let repeated := repeatedLandmarks o.landmarks
  if repeated.isEmpty then #[] else
    #[s!"trust verification ({o.scope}): duplicate landmark(s):\n\
      {summarize (repeated.map fun name => s!"  {name}")}\n\
      Give each documented proved claim its own landmark exactly once."]

def axiomDeclarations (o : Observation) : Array Decl :=
  o.decls.filter (·.kind == .axiomDecl)

def axiomDeclarationFindings (o : Observation) : Array String :=
  let axiomDecls := axiomDeclarations o
  if axiomDecls.isEmpty then #[] else
    #[s!"trust verification ({o.scope}): {axiomDecls.size} first-party axiom declaration(s):\n\
      {summarize (axiomDecls.map fun decl => s!"  {decl.name}  ({decl.module})")}\n\
      Prove the claim or record the residual as an explicit carried assumption; do not extend the kernel trust boundary locally."]

/-- Inspected declarations whose stored axiom dependencies leave the allowance.
    A first-party axiom is reported by its own arm, never also as depending on
    itself. -/
def axiomDependencyOffenders (cfg : Config) (o : Observation) : Array String :=
  o.decls.filterMap fun decl =>
    if decl.kind == .axiomDecl then none
    else
      let bad := decl.axioms.filter fun name => !cfg.allowedAxioms.contains name
      if bad.isEmpty then none
      else some s!"  {decl.name}  ({decl.module})  depends on: {String.intercalate ", " (bad.toList.map toString)}"

def axiomDependencyFindings (cfg : Config) (o : Observation) : Array String :=
  let offenders := axiomDependencyOffenders cfg o
  if offenders.isEmpty then #[] else
    #[s!"trust verification ({o.scope}): {offenders.size} declaration(s) depend on axioms outside {cfg.allowedAxioms.toList}:\n\
      {summarize offenders}\n\
      Finish the proof without `sorry` or native evaluation. If a residual is genuinely unprovable, decompose it and document the carried assumption."]

def analyze (cfg : Config) (o : Observation) : Report :=
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

/-- Assemble the whole run's evidence from the seven scope observations and the
    two inventory scans. The worker calls exactly this, so the verdict the
    theorems in `Verify.Proofs` characterise is the verdict it ships: a scope
    audited twice, or one left out *of this function*, makes
    `analyzedGateEvidence_clean_iff` false rather than merely unproved, so the
    build cannot go green on it.

    What that does not cover is the call site. The seven parameters share a type,
    so passing `testObservation` into `production` compiles, leaves a scope
    unaudited, and no theorem or test sees it — named arguments at the call site
    are the mitigation, and the residual is the recorded verifier-bootstrap
    assumption in docs/overview.md, not something proved here. -/
def gateEvidenceOf (cfg : Config)
    (production tests verifier supervisor testSupervisor tooling release : Observation)
    (inventoryErrors unclaimedSources : Array String) : GateEvidence :=
  { reports :=
      { production := analyze cfg production
        tests := analyze cfg tests
        verifier := analyze cfg verifier
        supervisor := analyze cfg supervisor
        testSupervisor := analyze cfg testSupervisor
        tooling := analyze cfg tooling
        release := analyze cfg release }
    inventoryErrors
    unclaimedSources }

end Tl.Verify
