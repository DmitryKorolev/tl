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
  deriving DecidableEq, Repr, Inhabited

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
  supervisorModules := #[`Verify.Launcher, `Verify.Supervise]
  testSupervisorModules := #[`Verify.TestLauncher, `Verify.Supervise]
  sourceDirectories := #[
    { scope := .production, path := "Tl", modulePrefix := `Tl },
    { scope := .tests, path := "Tests", modulePrefix := `Tests },
    { scope := .verifier, path := "Verify", modulePrefix := `Verify },
    { scope := .tests, path := "VerifyFixture", modulePrefix := `VerifyFixture },
    { scope := .tooling, path := "scripts", modulePrefix := `scripts }
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

def SourceInventory.errors (inventory : SourceInventory) (scope remedy : String) : Array String :=
  inventory.refusedSymlinks.map fun path =>
    s!"trust verification ({scope}): source inventory refuses symbolic link {path} because it is a .lean path, a directory, or could not be classified safely. {remedy}"

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

/-- Compute exact transitive axiom dependencies from stored constant bodies.
    The reverse worklist handles mutual recursion without trusting Lean's
    serialized `collectAxioms` extension summaries. -/
def propagatedAxioms (constants : Std.HashMap Name ConstantInfo) :
    Std.HashMap Name (Std.HashSet Name) := Id.run do
  let mut reverse : Std.HashMap Name (Array Name) := {}
  let mut axiomsByName : Std.HashMap Name (Std.HashSet Name) := {}
  let mut pending : Array (Name × Name) := #[]
  for (name, info) in constants do
    for dependency in info.getUsedConstantsAsSet do
      -- `alter` keeps the stored array uniquely referenced, so the push stays
      -- amortized O(1); a get-then-insert would copy it once per edge, making
      -- this pass quadratic in a constant's in-degree.
      reverse := reverse.alter dependency fun dependents =>
        some ((dependents.getD #[]).push name)
    if info matches .axiomInfo _ then
      axiomsByName := axiomsByName.insert name (({} : Std.HashSet Name).insert name)
      pending := pending.push (name, name)
  let mut cursor := 0
  while h : cursor < pending.size do
    let (dependency, axiomName) := pending[cursor]
    cursor := cursor + 1
    for dependent in reverse[dependency]?.getD #[] do
      let existing := axiomsByName[dependent]?.getD {}
      unless existing.contains axiomName do
        axiomsByName := axiomsByName.insert dependent (existing.insert axiomName)
        pending := pending.push (dependent, axiomName)
  return axiomsByName

def replayConstantsError? (base : Environment)
    (constants : Std.HashMap Name ConstantInfo) : IO (Option String) := do
  try
    let _ ← Lean.Environment.replay constants base
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

def observeEnvironment (scope : String) (env : Environment)
    (expectedModules modulesToInspect projectModules : Array Name)
    (landmarkNames : Array Name := #[])
    (moduleRemedy : String := defaultModuleRemedy)
    (importAudit : ImportAudit := importViolations importPolicy)
    (replayAudit : ReplayAudit := replayConstantsError?) :
    IO Observation := do
  let imported := modulesInEnvironment env modulesToInspect
  let replayConstants := replayClosure env (declarationNamesOf env imported)
  let axiomsByName := propagatedAxioms replayConstants
  let project := projectModules.foldl (·.insert ·) (∅ : Std.HashSet Name)
  let importRows := directImportRows env imported
  let importErrors := importAudit scope project importRows
  let replayError? ← replayAudit (← mkEmptyEnvironment) replayConstants
  let landmarks := landmarkNames.map fun name =>
    { name, kind? := (env.find? name).map declarationKind : Landmark }
  return {
    scope
    localModules := imported
    expectedModules
    moduleRemedy
    decls := ← declarationsOf env imported axiomsByName
    expectedLandmarks := landmarkNames
    landmarks
    evidence := {
      importErrors
      replayError?
      replayedConstants := replayedConstantCount replayConstants
      importEdges := importRows.foldl (fun total (_, importedModules) =>
        total + importedModules.size) 0
    }
  }

end Tl.Verify
