/- Exact module/declaration inspection and independent kernel replay. -/
import Lean
import Lean.Replay
import Verify.Policy
import Verify.Report

open Lean

namespace Tl.Verify

/-- The semantic scope that owns a source location.  Source locations carry this
    tag so claiming a new path also adds its modules to one scope's exact expected
    set; there is no string-only claim that can hide an unaudited Lake target. -/
inductive AuditScope where
  | production
  | tests
  | verifier
  | tooling
  /-- Release administration: the `tlrelease` decision layer. Its own scope
      rather than a corner of `tooling` because its root defines `main`, and
      roots inside one array load into one environment where two `main`s
      collide. Deliberately not under `Tl/` — satisfying the root-import rule
      that way would import release administration into the shipped product. -/
  | release
  deriving DecidableEq, Repr, Inhabited

/-- How a source-inventory finding names the scope it came from, and the scope
    word its repair instruction uses. Derived from the constructor for the same
    reason `GateScope.label` is: the alternative is a scope word written out
    beside each call, which is one more thing that can name the wrong scope. -/
def AuditScope.label : AuditScope → String
  | .production => "production"
  | .tests => "tests"
  | .verifier => "verifier"
  | .tooling => "tooling"
  | .release => "release"

structure ScopedSourceDirectory where
  scope : AuditScope
  path : String
  modulePrefix : Name
  deriving Inhabited

structure ScopedRootSource where
  scope : AuditScope
  path : String
  «module» : Name
  deriving Inhabited

/-- Single registry for every dynamically loaded root and every filesystem
    location claimed by the trust gate. Lake target roots remain the independent
    build-graph declaration; a new executable script must update both registries,
    and the scope-specific error names those edit sites. -/
structure AuditLayout where
  productionRoots : Array Name
  testRoots : Array Name
  verifierRoots : Array Name
  supervisorRoots : Array Name
  testSupervisorRoots : Array Name
  toolingRoots : Array Name
  releaseRoots : Array Name
  supervisorModules : Array Name
  testSupervisorModules : Array Name
  sourceDirectories : Array ScopedSourceDirectory
  rootSources : Array ScopedRootSource

def auditLayout : AuditLayout := {
  productionRoots := #[`Tl, `Main]
  testRoots := #[`Tests, `VerifyFixture.EarlyExit]
  verifierRoots := #[`Verify.Main]
  supervisorRoots := #[`Verify.Launcher]
  testSupervisorRoots := #[`Verify.TestLauncher]
  toolingRoots := #[`scripts.GenLicenses]
  releaseRoots := #[`release.Main]
  supervisorModules := #[`Verify.Launcher, `Verify.Supervise]
  testSupervisorModules := #[`Verify.TestLauncher, `Verify.Supervise]
  sourceDirectories := #[
    { scope := .production, path := "Tl", modulePrefix := `Tl },
    { scope := .tests, path := "Tests", modulePrefix := `Tests },
    { scope := .verifier, path := "Verify", modulePrefix := `Verify },
    { scope := .tests, path := "VerifyFixture", modulePrefix := `VerifyFixture },
    { scope := .tooling, path := "scripts", modulePrefix := `scripts },
    -- Lowercase, like `scripts`, and the same reason: the directory predates
    -- the Lean in it and already holds this release's machine-readable data.
    -- On a case-insensitive filesystem a `Release/` claim would not match the
    -- `release` this scan reports, so every module here would be an unclaimed
    -- source on macOS and claimed on Linux.
    { scope := .release, path := "release", modulePrefix := `release }
  ]
  rootSources := #[
    { scope := .production, path := "Tl.lean", module := `Tl },
    { scope := .production, path := "Main.lean", module := `Main },
    { scope := .tests, path := "Tests.lean", module := `Tests }
  ]
}

/-- Lake's configuration is elaborated before the audit target exists.  Keep
    this bootstrap exemption visibly separate from audited root modules. -/
def lakeConfigurationSource : String := "lakefile.lean"

unsafe def loadEnvironmentNoInitializers (moduleNames : Array Name) : IO Environment :=
  importModules (moduleNames.map fun name =>
      { module := name, importAll := true, isMeta := true }) {}
    (loadExts := false)

/-- The roots each audited environment is loaded from. A `match`, so a new
    `GateScope` case cannot be added without deciding what it loads — and the
    decision is here, next to the registry, rather than at a call site that
    happened to name it. -/
def AuditLayout.gateRoots (layout : AuditLayout) : GateScope → Array Name
  | .production => layout.productionRoots
  | .tests => layout.testRoots
  | .verifier => layout.verifierRoots
  | .supervisor => layout.supervisorRoots
  | .testSupervisor => layout.testSupervisorRoots
  | .tooling => layout.toolingRoots
  | .release => layout.releaseRoots

/-- An environment together with the scope it was loaded for.

    The constructor is private, so the only way to obtain one is `loadScope`,
    which reads the roots out of the registry under the same scope. That is what
    makes the scope on an `Observation` mean something: an observation tagged
    `.production` cannot have been built from the tests environment, because
    `observeEnvironment` accepts only a matching `ScopedEnvironment`. Without
    this, tagging the observation alone would leave the identical hole one step
    earlier — the tests environment observed twice, once under each name, with
    every field of both observations internally consistent. -/
structure ScopedEnvironment (scope : GateScope) where
  private mk ::
  env : Environment

/-- Load one audited scope from its registered roots, with initializers
    unexecuted. -/
unsafe def loadScope (layout : AuditLayout) (scope : GateScope) :
    IO (ScopedEnvironment scope) :=
  return ⟨← loadEnvironmentNoInitializers (layout.gateRoots scope)⟩

def declarationKind : ConstantInfo → DeclKind
  | .axiomInfo _ => .axiomDecl
  | .thmInfo _ => .theoremDecl
  | _ => .other

partial def packageRoot? (start : System.FilePath) : IO (Option System.FilePath) := do
  if ← (start / "lakefile.lean").pathExists then return some start
  match start.parent with
  | some parent => packageRoot? parent
  | none => return none

/-- Whether a symlink must be treated as a possible Lean source location.
    `.lean` names stay fail-closed even when dangling; directory targets may
    contain arbitrary modules; regular non-Lean targets cannot contribute one;
    and any metadata failure stays fail-closed because it cannot establish the
    regular-file exception. -/
def symlinkMayContainLean (path : System.FilePath) : IO Bool := do
  if path.extension == some "lean" then return true
  try return (← path.metadata).type == .dir
  catch _ => return true

structure SourceInventory where
  modules : Array Name := #[]
  refusedSymlinks : Array String := #[]
  deriving Inhabited

def SourceInventory.append (left right : SourceInventory) : SourceInventory :=
  { modules := left.modules ++ right.modules
    refusedSymlinks := left.refusedSymlinks ++ right.refusedSymlinks }

structure ScopedSourceInventory where
  source : ScopedSourceDirectory
  inventory : SourceInventory
  deriving Inhabited

def SourceInventory.errors (inventory : SourceInventory) (scope : AuditScope) : Array String :=
  inventory.refusedSymlinks.map fun path =>
    s!"trust verification ({scope.label}): source inventory refuses symbolic link {path} because it is a .lean path, a directory, or could not be classified safely. Replace it with a regular in-tree directory or .lean file in the {scope.label} source scope."

/-- Inventory importable Lean modules without crossing a nested checkout or a
    symbolic-link source boundary. Semantic refusals are returned as data, not
    thrown as operational IO errors, so the final verdict can give the source
    remedy rather than an unrelated `.olean` rebuild remedy. -/
partial def modulesUnder (dir : System.FilePath) (parts : List String := []) :
    IO SourceInventory := do
  let rootMetadata? ← try
      pure (some (← dir.symlinkMetadata))
    catch error =>
      if ← dir.pathExists then throw error else pure none
  let some rootMetadata := rootMetadata? | return {}
  if rootMetadata.type == .symlink then
    return { refusedSymlinks := #[dir.toString] }
  unless rootMetadata.type == .dir do return {}
  -- A nested checkout is a separate source authority. This covers ordinary
  -- clones and git worktrees (`.git` may be a directory or a file) wherever a
  -- harness or editor stores them, without special-casing `.claude`. It also
  -- means a new top-level directory containing both `.git` and Lean sources is
  -- intentionally invisible to `unclaimedSources`; making Lake build that
  -- separate authority requires a protected-review lakefile change (ADR-0026).
  if ← (dir / ".git").pathExists then return {}
  let mut found : SourceInventory := {}
  let entries := (← dir.readDir).qsort fun left right => left.fileName < right.fileName
  for entry in entries do
    let metadata ← entry.path.symlinkMetadata
    if metadata.type == .symlink then
      -- A regular non-Lean link cannot contribute a module and is safe to
      -- ignore. A `.lean`-named link (including a dangling one) or a directory
      -- link may hide out-of-tree sources, so inventory stays fail-closed.
      if ← symlinkMayContainLean entry.path then
        found := { found with
          refusedSymlinks := found.refusedSymlinks.push entry.path.toString }
      else
        continue
    if metadata.type == .dir then
      found := found.append (← modulesUnder entry.path (parts ++ [entry.fileName]))
    else if metadata.type == .file && entry.path.extension == some "lean" then
      if let some stem := entry.path.fileStem then
        found := { found with
          modules := found.modules.push ((parts ++ [stem]).foldl Name.str .anonymous) }
  return found

def collectSourceInventories (root : System.FilePath)
    (layout : AuditLayout) : IO (Array ScopedSourceInventory) :=
  layout.sourceDirectories.mapM fun source => do
    let parts := source.modulePrefix.components.map toString
    return { source, inventory := ← modulesUnder (root / source.path) parts }

/-- Every source-inventory refusal of the run, taken from the registry itself.
    A scope added to `auditLayout.sourceDirectories` reports through this with no
    second edit; the five hand-paired calls this replaces were a list a new scope
    could be left off, leaving a scan whose findings nobody read. -/
def scopedInventoryErrors (inventories : Array ScopedSourceInventory) : Array String :=
  inventories.flatMap fun entry => entry.inventory.errors entry.source.scope

def sourceInventoryFor (scope : AuditScope)
    (inventories : Array ScopedSourceInventory) : SourceInventory :=
  inventories.foldl (fun inventory scopedInventory =>
    if scopedInventory.source.scope == scope then
      inventory.append scopedInventory.inventory
    else inventory) {}

def AuditLayout.rootModulesFor (layout : AuditLayout) (scope : AuditScope) : Array Name :=
  layout.rootSources.filterMap fun source =>
    if source.scope == scope then some source.module else none

def AuditLayout.expectedSourceModules (layout : AuditLayout) (scope : AuditScope)
    (inventories : Array ScopedSourceInventory) : Array Name :=
  (sourceInventoryFor scope inventories).modules ++ layout.rootModulesFor scope

/-- Lean sources in the checkout that no typed source scope in `auditLayout`
    claims. The same entries feed each scope's exact expected-module set, so a
    new top-level directory or root module cannot be hidden merely by naming it
    as claimed. `.git` and `.lake` are not repository sources;
    `lakefile.lean` is the distinct fixed configuration exemption, elaborated
    rather than imported, and stays a review obligation (ADR-0026). -/
def unclaimedSources (root : System.FilePath) (layout : AuditLayout) : IO (Array String) := do
  let claimedDirs := layout.sourceDirectories.foldl
    (fun names source => names.insert source.path) (∅ : Std.HashSet String)
  let claimedFiles := layout.rootSources.foldl
    (fun names source => names.insert source.path)
    ((∅ : Std.HashSet String).insert lakeConfigurationSource)
  let skipped := (#[".git", ".lake"] : Array String).foldl (·.insert ·) (∅ : Std.HashSet String)
  let mut unclaimed := #[]
  let entries := (← root.readDir).qsort fun left right => left.fileName < right.fileName
  for entry in entries do
    let name := entry.fileName
    if skipped.contains name || claimedDirs.contains name then continue
    let metadata ← entry.path.symlinkMetadata
    if claimedFiles.contains name then
      -- Claimed root modules do not pass through `modulesUnder`; validate their
      -- placement here so `Tl.lean`, `Main.lean`, and `Tests.lean` cannot be
      -- symbolic links while nested `.lean` links are refused.
      if metadata.type != .file then unclaimed := unclaimed.push name
    else if metadata.type == .symlink then
      -- Nothing can be inventoried through a directory/`.lean` link
      -- (`modulesUnder` refuses them), so a link that may reach Lean sources
      -- counts as unclaimed. The extension check is independent of resolution:
      -- a dangling `Loose.lean` must not disappear from the fail-closed scan.
      if ← symlinkMayContainLean entry.path then unclaimed := unclaimed.push name
    else if metadata.type == .dir then
      let inventory ← modulesUnder entry.path
      unless inventory.modules.isEmpty && inventory.refusedSymlinks.isEmpty do
        unclaimed := unclaimed.push name
    else if entry.path.extension == some "lean" then
      unclaimed := unclaimed.push name
  return unclaimed

def modulesInEnvironment (env : Environment) (candidates : Array Name) : Array Name :=
  let imported := env.allImportedModuleNames.foldl (·.insert ·) (∅ : Std.HashSet Name)
  candidates.filter imported.contains

/-- Remove every registered root from a broader module inventory. Kept pure so
    multi-root scope subtraction cannot regress to a one-off literal. -/
def without (names excluded : Array Name) : Array Name :=
  let excluded := excluded.foldl (·.insert ·) (∅ : Std.HashSet Name)
  names.filter fun name => !excluded.contains name

/-- The verifier scope is the complete Verify/ inventory minus only the roots
    loaded exclusively through the supervisor executable. Shared helpers remain
    in the verifier scope even when listed in `supervisorModules`. -/
def AuditLayout.verifierScopeModules (layout : AuditLayout)
    (verifierInventory : Array Name) : Array Name :=
  without verifierInventory (layout.supervisorRoots ++ layout.testSupervisorRoots)

def pathWithin (root path : System.FilePath) : Bool :=
  root.normalize.components.isPrefixOf path.normalize.components

def ascend? (path : System.FilePath) : Nat → Option System.FilePath
  | 0 => some path
  | steps + 1 => path.parent >>= fun parent => ascend? parent steps

def projectOLeanRoot : IO System.FilePath := do
  let verifierOLean ← realPathNormalized (← findOLean `Verify.Environment)
  let some buildLib := ascend? verifierOLean (Name.components `Verify.Environment).length |
    throw <| IO.userError s!"cannot resolve the project olean root above {verifierOLean}"
  return buildLib

def projectModulesIn (env : Environment) : IO (Array Name) := do
  let projectLib ← projectOLeanRoot
  env.allImportedModuleNames.filterM fun name => do
    let olean ← realPathNormalized (← findOLean name)
    return pathWithin projectLib olean

def ScopedEnvironment.projectModules {scope : GateScope}
    (env : ScopedEnvironment scope) : IO (Array Name) :=
  projectModulesIn env.env

def declarationsOf (env : Environment) (modulesToInspect : Array Name)
    (axiomsByName : Std.HashMap Name (Std.HashSet Name)) :
    IO (Array Decl) := do
  let modules := env.allImportedModuleNames
  let selected := modulesToInspect.foldl (·.insert ·) (∅ : Std.HashSet Name)
  return env.constants.fold (init := #[]) fun decls name info =>
    match env.getModuleIdxFor? name with
    | none => decls
    | some idx =>
      if h : idx.toNat < modules.size then
        let definingModule := modules[idx.toNat]
        if selected.contains definingModule then
          let kind := declarationKind info
          let axioms := if kind == .axiomDecl then #[] else
            (axiomsByName[name]?.getD {}).toArray.qsort Name.lt
          decls.push { name, «module» := definingModule, kind, axioms }
        else decls
      else decls

def declarationNamesOf (env : Environment) (modulesToInspect : Array Name) :
    Array Name :=
  let selected := modulesToInspect.foldl (·.insert ·) (∅ : Std.HashSet Name)
  let moduleNames := env.allImportedModuleNames
  env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | none => names
    | some idx =>
      if h : idx.toNat < moduleNames.size then
        if selected.contains moduleNames[idx.toNat] then names.push name else names
      else names

/-- Stored dependencies a replay step must enqueue.  Mutual-inductive siblings
    are required even when only one member was selected: replay reconstructs the
    complete block together.  Kept as a pure seam so that requirement is tested
    independently of a loaded environment. -/
def replayDependencies (info : ConstantInfo) : Array Name :=
  let used := info.getUsedConstantsAsSet.toArray
  match info with
  | .inductInfo inductiveInfo => used ++ inductiveInfo.all.toArray
  | _ => used

/-- The complete stored dependency cone of the selected declarations.  This
    deliberately crosses package boundaries: a dependency `.olean` is data to
    recheck, not part of the trusted base. -/
partial def replayClosure (env : Environment) (roots : Array Name) :
    Std.HashMap Name ConstantInfo := Id.run do
  let mut pending := roots
  let mut constants : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if constants.contains name then continue
    let some info := env.find? name | continue
    constants := constants.insert name info
    for dependency in replayDependencies info do
      pending := pending.push dependency
  return constants

/-! ### Stored-body axiom propagation

Transitive axiom dependencies are computed from stored constant bodies rather
than read from Lean's serialized `collectAxioms` extension summaries: those
summaries are data produced by the same compilation this gate is auditing. That
makes the propagation load-bearing on its own — a bug in it is a *silent* false
negative, a green run with an axiom sitting unreported in a theorem's cone — so
it is written as a fold and a fuel-structural recursion, and its soundness and
completeness are proved in `Verify.Proofs`.

A `while` loop would rule that out: it elaborates through `Lean.Loop.forIn` to
an opaque worklist combinator carrying a one-step unfolding lemma and no
induction principle, so nothing about the result could be proved at all. -/

/-- The stored edges axiom propagation follows: every constant a declaration's
    stored type or value mentions. For a declaration carrying no value,
    `ConstantInfo.getUsedConstantsAsSet` still yields structural neighbours — an
    inductive's constructors, a constructor's own name, a recursor's mutual
    block. Against Lean's own `collectAxioms` this edge set is never narrower:
    the two agree on axioms, definitions, theorems, opaques and inductives, and
    for quotients, constructors and recursors this one is strictly broader,
    which is the safe direction.

    It is deliberately *not* `replayDependencies`, which additionally enqueues
    an inductive's whole mutual block — a requirement of reconstructing the
    block for kernel replay, not an axiom-dependency edge. A named seam, so the
    spec in `Verify.Proofs` quantifies over exactly the relation the code
    walks. -/
def axiomEdges (info : ConstantInfo) : Array Name :=
  info.getUsedConstantsAsSet.toArray

/-- The reverse edge map, the seeded axiom rows, and the initial worklist. -/
structure PropagationSeed where
  /-- Each constant mapped to the declarations whose stored body mentions it. -/
  reverse : Std.HashMap Name (Array Name) := {}
  axiomsByName : Std.HashMap Name (Std.HashSet Name) := {}
  pending : Array (Name × Name) := #[]
  deriving Inhabited

def seedStep (seed : PropagationSeed) (name : Name) (info : ConstantInfo) :
    PropagationSeed :=
  -- `alter` keeps the stored array uniquely referenced, so the push stays
  -- amortized O(1); a get-then-insert would copy it once per edge, making
  -- this pass quadratic in a constant's in-degree.
  let reverse := (axiomEdges info).foldl (init := seed.reverse) fun reverse dependency =>
    reverse.alter dependency fun dependents => some ((dependents.getD #[]).push name)
  match info with
  | .axiomInfo _ =>
    -- `alter` rather than `insert`: a constant is visited once, so the row is
    -- empty here either way, but adding to it keeps the seed *monotone* — which
    -- is what lets `Verify.Proofs` carry a growth invariant through the fold
    -- without first proving that a `Std.HashMap`'s keys are distinct.
    { reverse
      axiomsByName := seed.axiomsByName.alter name fun row =>
        some ((row.getD {}).insert name)
      pending := seed.pending.push (name, name) }
  | _ => { seed with reverse }

def propagationSeed (constants : Std.HashMap Name ConstantInfo) : PropagationSeed :=
  constants.fold seedStep {}

/-- Give one axiom to one dependent, enqueuing it only when the row actually
    grew. Pairing that guard with the insert is what bounds the worklist. -/
def propagateStep (axiomName : Name)
    (state : Std.HashMap Name (Std.HashSet Name) × Array (Name × Name))
    (dependent : Name) :
    Std.HashMap Name (Std.HashSet Name) × Array (Name × Name) :=
  let (axiomsByName, pending) := state
  let existing := axiomsByName[dependent]?.getD {}
  if existing.contains axiomName then (axiomsByName, pending)
  else
    (axiomsByName.insert dependent (existing.insert axiomName),
      pending.push (dependent, axiomName))

/-- Drain the worklist, propagating each pair back along the reverse edges.
    `none` means the fuel ran out before the cursor reached the end, so the
    axiom map is *truncated* — precisely the silent false negative this module
    exists to prevent — and it is refused rather than returned. `some`
    witnesses that the loop reached a drained worklist, which is what makes the
    closure property in `Verify.Proofs` observable rather than something a
    counting argument would have to establish. -/
def drainWorklist (reverse : Std.HashMap Name (Array Name)) :
    Nat → Nat → Std.HashMap Name (Std.HashSet Name) → Array (Name × Name) →
      Option (Std.HashMap Name (Std.HashSet Name))
  | 0, _, _, _ => none
  | fuel + 1, cursor, axiomsByName, pending =>
    if h : cursor < pending.size then
      -- Plain `let`s, not a destructuring one: a pattern `let` elaborates to a
      -- `match`, which makes the recursive step opaque to `split` and puts the
      -- proofs in `Verify.Proofs` out of reach. The pair is read by `.1`/`.2`
      -- for the same reason.
      let entry := pending[cursor]'h
      let stepped :=
        (reverse[entry.1]?.getD #[]).foldl (propagateStep entry.2) (axiomsByName, pending)
      drainWorklist reverse fuel (cursor + 1) stepped.1 stepped.2
    else some axiomsByName

/-- Every enqueued pair is a distinct `(dependent, axiom)` whose dependent is a
    key of `constants` and whose axiom is one of the seeds, so the worklist
    cannot outgrow this. Exhausting it means a bug in this module rather than a
    large input, and `drainWorklist` then refuses. Do not answer an exhaustion
    by returning the partial map: the theorems in `Verify.Proofs` would go
    vacuous exactly where they matter, and the gate would be silently green
    again. -/
def propagationFuel (constants : Std.HashMap Name ConstantInfo)
    (seed : PropagationSeed) : Nat :=
  (constants.size + 1) * seed.pending.size + 1

/-- Exact transitive axiom dependencies from stored constant bodies. The
    reverse worklist handles mutual recursion; `none` is a refusal, never an
    empty answer. -/
def propagatedAxioms (constants : Std.HashMap Name ConstantInfo) :
    Option (Std.HashMap Name (Std.HashSet Name)) :=
  let seed := propagationSeed constants
  drainWorklist seed.reverse (propagationFuel constants seed) 0 seed.axiomsByName seed.pending

def replayConstantsError? (base : Environment)
    (constants : Std.HashMap Name ConstantInfo) : IO (Option String) := do
  try
    let _ ← Lean.Kernel.Environment.replay constants base.toKernelEnv
    return none
  catch error =>
    return some s!"independent kernel replay rejected the stored environment: {error}. Remove any kernel-checking bypass and fix the declaration the kernel names."

/-- Number of safe, total stored constants independently validated by
    `Environment.replay`. Lean submits ordinary declarations to the kernel;
    constructors and recursors are regenerated from their inductive block and
    compared with the stored metadata. Unsafe and partial executable code is
    deliberately skipped. -/
def replayedConstantCount (constants : Std.HashMap Name ConstantInfo) : Nat :=
  constants.fold (init := 0) fun count _ info =>
    if !info.isUnsafe && !info.isPartial then count + 1 else count

/-- The stored direct-import rows of the inspected modules, in header order. -/
def directImportRows (env : Environment) (modulesToInspect : Array Name) :
    Array (Name × Array Name) := Id.run do
  let selected := modulesToInspect.foldl (·.insert ·) (∅ : Std.HashSet Name)
  let mut rows := #[]
  for h : idx in [:env.header.moduleNames.size] do
    let name := env.header.moduleNames[idx]
    unless selected.contains name do continue
    rows := rows.push (name, env.header.moduleData[idx]!.imports.map (·.module))
  return rows

abbrev ImportAudit :=
  String → Std.HashSet Name → Array (Name × Array Name) → Array String

abbrev ReplayAudit :=
  Environment → Std.HashMap Name ConstantInfo → IO (Option String)

/-- The propagation seam, alongside the import and replay ones. Its refusal is
    unreachable from real input — the shipped fuel always suffices — so without
    an injectable seam the `none` arm below could not be exercised at all, and
    a later edit collapsing it (a `.getD {}`, say) would leave every gate
    green while a discarded axiom map reached the verdict as an empty one. -/
abbrev PropagationAudit :=
  Std.HashMap Name ConstantInfo → Option (Std.HashMap Name (Std.HashSet Name))

/-- The three module sets one observation is built from. All three are
    `Array Name` and were three adjacent positional parameters, so a swap
    compiled; a call site now has to name each set it supplies. A set that
    disagrees with the registry is not silent the way a swapped scope was: it is
    what the missing- and unexpected-module arms report. The one thing those arms
    cannot see is an `expected` read out of the environment itself, since the two
    sides would then agree by construction — which is why every call site derives
    it from the source inventory or the registered module list. -/
structure ScopeModules where
  /-- Every source the registry says this scope owns; the environment is
      required to have imported all of them and nothing else first-party. -/
  expected : Array Name
  /-- The modules whose declarations and stored import rows this scope
      inspects. -/
  inspected : Array Name
  /-- Every first-party module in the environment, so the import audit can tell
      a project import from an external dependency. -/
  project : Array Name

def observeEnvironment {scope : GateScope} (environment : ScopedEnvironment scope)
    (modules : ScopeModules)
    (landmarkNames : Array Name := #[])
    (moduleRemedy : String := defaultModuleRemedy)
    (importAudit : ImportAudit := importViolations importPolicy)
    (replayAudit : ReplayAudit := replayConstantsError?)
    (propagationAudit : PropagationAudit := propagatedAxioms) :
    IO (Observation scope) := do
  let env := environment.env
  let imported := modulesInEnvironment env modules.inspected
  let replayConstants := replayClosure env (declarationNamesOf env imported)
  -- A refusal must not degrade into "no axioms found", which reads as clean.
  -- The empty map silences the axiom-dependency arm, and `propagationError?`
  -- fires its own arm in its place, so the verdict stays fail-closed.
  let (axiomsByName, propagationError?) :=
    match propagationAudit replayConstants with
    | some axiomsByName => (axiomsByName, none)
    | none =>
      ({}, some "stored-body axiom propagation did not drain its worklist within \
        the bound, so this scope's transitive axiom rows are incomplete and were \
        discarded. Raise `propagationFuel` in Verify/Environment.lean and rerun \
        `lake exe tlverify`; the bound assumes one worklist entry per \
        (declaration, axiom) pair, so needing more of it means the propagation \
        itself is enqueuing duplicates.")
  let project := modules.project.foldl (·.insert ·) (∅ : Std.HashSet Name)
  let importRows := directImportRows env imported
  let importErrors := importAudit scope.label project importRows
  let replayError? ← replayAudit (← mkEmptyEnvironment) replayConstants
  let landmarks := landmarkNames.map fun name =>
    { name, kind? := (env.find? name).map declarationKind : Landmark }
  return {
    localModules := imported
    expectedModules := modules.expected
    moduleRemedy
    decls := ← declarationsOf env imported axiomsByName
    expectedLandmarks := landmarkNames
    landmarks
    evidence := {
      importErrors
      replayError?
      propagationError?
      replayedConstants := replayedConstantCount replayConstants
      importEdges := importRows.foldl (fun total (_, importedModules) =>
        total + importedModules.size) 0
    }
  }

end Tl.Verify
