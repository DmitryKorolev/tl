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

def AuditedReports.errors (reports : AuditedReports) : Array String :=
  #[reports.production, reports.tests, reports.verifier, reports.supervisor,
    reports.testSupervisor, reports.tooling].flatMap (·.errors)

def unclaimedSourceError? (unclaimed : Array String) : Option String :=
  if unclaimed.isEmpty then none else
    some s!"trust verification: {unclaimed.size} Lean source location(s) belong to no audited scope:\n\
      {summarize (unclaimed.map fun name => s!"  {name}")}\n\
      Move regular sources under an audited directory (Tl/, Tests/, Verify/, VerifyFixture/, scripts/), register an in-tree location with its owning typed source scope in Verify/Environment.lean, or replace a symbolic-link source location with regular in-tree files; a source no scope loads is built but never inspected, and a linked directory cannot be audited without following paths outside the checkout."

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

def analyze (cfg : Config) (o : Observation) : Report := Id.run do
  let mut errors := o.evidence.importErrors
  if let some replayError := o.evidence.replayError? then
    errors := errors.push s!"trust verification ({o.scope}): {replayError}"
  let localSet := o.localModules.foldl (·.insert ·) (∅ : Std.HashSet Name)
  let missing := o.expectedModules.filter fun name => !localSet.contains name
  if !missing.isEmpty then
    errors := errors.push s!"trust verification ({o.scope}): {missing.size} source module(s) are absent from the imported environment:\n\
      {summarize (missing.map fun name => s!"  {name}")}\n\
      {o.moduleRemedy}"
  let expectedSet := o.expectedModules.foldl (·.insert ·) (∅ : Std.HashSet Name)
  let unexpected := o.localModules.filter fun name => !expectedSet.contains name
  if !unexpected.isEmpty then
    errors := errors.push s!"trust verification ({o.scope}): {unexpected.size} imported first-party module(s) are outside the declared scope:\n\
      {summarize (unexpected.map fun name => s!"  {name}")}\n\
      {o.moduleRemedy}"

  -- Every semantic arm below is silent when nothing was selected. All six
  -- named scopes are mandatory, so an empty module set is itself vacuous;
  -- otherwise declarations, replay validation, and import traversal must each
  -- have observable evidence.
  if o.localModules.isEmpty then
    errors := errors.push s!"trust verification ({o.scope}): the named scope imported no first-party modules. Restore its registered roots and source inventory before trusting this run."
  else
    let vacuous :=
      (if o.decls.isEmpty then ["no declarations were selected from them"] else []) ++
      (if o.evidence.replayedConstants == 0 then ["nothing reached independent replay validation"] else []) ++
      (if o.evidence.importEdges == 0 then ["no direct import edges were read"] else [])
    if !vacuous.isEmpty then
      errors := errors.push s!"trust verification ({o.scope}): {o.localModules.size} module(s) were inspected but {String.intercalate ", and " vacuous}. Declaration ownership, the replay cone, or the stored import traversal has regressed, so the axiom and kernel-replay findings below are vacuous. Restore the selection before trusting this run."

  if o.landmarks.map (·.name) != o.expectedLandmarks then
    errors := errors.push s!"trust verification ({o.scope}): landmark observation did not preserve the policy list. Restore the one-for-one landmark lookup before trusting this run."

  for landmark in o.landmarks do
    match landmark.kind? with
    | some .theoremDecl => pure ()
    | some kind =>
      errors := errors.push s!"trust verification ({o.scope}): landmark {landmark.name} is {declKindName kind}, not a theorem. Restore the theorem, or retire the proved claim and its landmark together."
    | none =>
      errors := errors.push s!"trust verification ({o.scope}): landmark theorem {landmark.name} is absent. Restore it, or retire the proved claim and its landmark together."

  let mut seen : Std.HashSet Name := ∅
  let mut repeated : Array Name := #[]
  for landmark in o.landmarks do
    if seen.contains landmark.name then
      repeated := repeated.push landmark.name
    else
      seen := seen.insert landmark.name
  if !repeated.isEmpty then
    errors := errors.push s!"trust verification ({o.scope}): duplicate landmark(s):\n\
      {summarize (repeated.map fun name => s!"  {name}")}\n\
      Give each documented proved claim its own landmark exactly once."

  let axiomDecls := o.decls.filter (·.kind == .axiomDecl)
  if !axiomDecls.isEmpty then
    errors := errors.push s!"trust verification ({o.scope}): {axiomDecls.size} first-party axiom declaration(s):\n\
      {summarize (axiomDecls.map fun decl => s!"  {decl.name}  ({decl.module})")}\n\
      Prove the claim or record the residual as an explicit carried assumption; do not extend the kernel trust boundary locally."

  let offenders := o.decls.filterMap fun decl =>
    if decl.kind == .axiomDecl then none
    else
      let bad := decl.axioms.filter fun name => !cfg.allowedAxioms.contains name
      if bad.isEmpty then none
      else some s!"  {decl.name}  ({decl.module})  depends on: {String.intercalate ", " (bad.toList.map toString)}"
  if !offenders.isEmpty then
    errors := errors.push s!"trust verification ({o.scope}): {offenders.size} declaration(s) depend on axioms outside {cfg.allowedAxioms.toList}:\n\
      {summarize offenders}\n\
      Finish the proof without `sorry` or native evaluation. If a residual is genuinely unprovable, decompose it and document the carried assumption."

  return { errors }

end Tl.Verify
