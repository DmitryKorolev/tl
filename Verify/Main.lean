/-
`tlverifyWorker` dynamically loads separately compiled scopes. This avoids the
global `main` names shared by executables and inspects production, tests, the
verifier/supervisor, and executable Lean tooling without running initializers.
-/
import Lean
import Verify.Environment
import Verify.Policy
-- The verdict-logic theorems are not used by the worker at runtime; the import
-- keeps them inside the audited verifier scope, so they are kernel-replayed by
-- the very gate they are about.
import Verify.Proofs
import Verify.Supervise

open Lean

namespace Tl.Verify

def supervisorModuleRemedy : String :=
  "Keep the supervisor closure minimal; if Verify.Launcher intentionally imports another helper, add that module to auditLayout.supervisorModules in Verify/Environment.lean."

def testSupervisorModuleRemedy : String :=
  "Keep the test supervisor closure minimal; if Verify.TestLauncher intentionally imports another helper, add that module to auditLayout.testSupervisorModules in Verify/Environment.lean."

def toolingModuleRemedy : String :=
  "Add each executable script root to Tooling.roots in lakefile.lean and to auditLayout.toolingRoots in Verify/Environment.lean, or move non-executable Lean support under an existing audited scope."

unsafe def runChecked : IO UInt32 := do
  initSearchPath (← findSysroot)
  let cwd ← IO.currentDir
  let some root ← packageRoot? cwd | do
    IO.eprintln s!"trust verification: could not find lakefile.lean above {cwd}; run this command inside the tl checkout"
    return 1
  let sourceInventories ← collectSourceInventories root auditLayout
  let productionInventory := sourceInventoryFor .production sourceInventories
  let testsInventory := sourceInventoryFor .tests sourceInventories
  let verifierInventory := sourceInventoryFor .verifier sourceInventories
  let toolingInventory := sourceInventoryFor .tooling sourceInventories
  let production ← loadEnvironmentNoInitializers auditLayout.productionRoots
  let productionModules ← projectModulesIn production
  let expectedProduction := auditLayout.expectedSourceModules .production sourceInventories
  let productionObservation ← observeEnvironment "production" production
    expectedProduction productionModules productionModules landmarkTheorems

  let expectedVerifierAll := auditLayout.expectedSourceModules .verifier sourceInventories
  let expectedSupervisor := auditLayout.supervisorModules
  let expectedVerifier := auditLayout.verifierScopeModules expectedVerifierAll
  let tests ← loadEnvironmentNoInitializers auditLayout.testRoots
  let testProjectModules ← projectModulesIn tests
  let testModules := without
    (without testProjectModules productionModules) expectedVerifierAll
  let expectedTests := auditLayout.expectedSourceModules .tests sourceInventories
  let testObservation ← observeEnvironment "tests" tests expectedTests testModules
    testProjectModules

  let verifier ← loadEnvironmentNoInitializers auditLayout.verifierRoots
  let verifierProjectModules ← projectModulesIn verifier
  let verifierModules := without verifierProjectModules productionModules
  let verifierObservation ← observeEnvironment "verifier" verifier
    expectedVerifier verifierModules verifierProjectModules

  let launcher ← loadEnvironmentNoInitializers auditLayout.supervisorRoots
  let launcherModules ← projectModulesIn launcher
  let launcherObservation ← observeEnvironment "verifier supervisor" launcher
    expectedSupervisor launcherModules launcherModules (moduleRemedy := supervisorModuleRemedy)

  let testLauncher ← loadEnvironmentNoInitializers auditLayout.testSupervisorRoots
  let testLauncherModules ← projectModulesIn testLauncher
  let testLauncherObservation ← observeEnvironment "test supervisor" testLauncher
    auditLayout.testSupervisorModules testLauncherModules testLauncherModules
    (moduleRemedy := testSupervisorModuleRemedy)

  let tooling ← loadEnvironmentNoInitializers auditLayout.toolingRoots
  let toolingModules ← projectModulesIn tooling
  let toolingObservation ← observeEnvironment "tooling" tooling
    (auditLayout.expectedSourceModules .tooling sourceInventories)
    toolingModules toolingModules (moduleRemedy := toolingModuleRemedy)

  let unclaimed ← unclaimedSources root auditLayout
  let inventoryErrors :=
    productionInventory.errors "production"
      "Replace it with a regular in-tree directory or .lean file in the production source scope." ++
    testsInventory.errors "tests"
      "Replace it with a regular in-tree directory or .lean file in the test source scope." ++
    verifierInventory.errors "verifier"
      "Replace it with a regular in-tree directory or .lean file in the verifier source scope." ++
    toolingInventory.errors "tooling"
      "Replace it with a regular in-tree directory or .lean file in the tooling source scope."
  -- Named arguments: six same-typed observations are otherwise swappable, and a
  -- scope audited twice would leave another entirely uninspected.
  let evidence : GateEvidence := gateEvidenceOf config
    (production := productionObservation) (tests := testObservation)
    (verifier := verifierObservation) (supervisor := launcherObservation)
    (testSupervisor := testLauncherObservation) (tooling := toolingObservation)
    (inventoryErrors := inventoryErrors) (unclaimedSources := unclaimed)
  let errors := evidence.errors
  if !errors.isEmpty then
    for error in errors do IO.eprintln error
    return 1

  IO.println s!"trust verification: ok; inspected production={productionObservation.decls.size}, tests={testObservation.decls.size}, verifier={verifierObservation.decls.size}, verifier-supervisor={launcherObservation.decls.size}, test-supervisor={testLauncherObservation.decls.size}, tooling={toolingObservation.decls.size} declarations; safe total dependency cones independently replay-validated; landmarks={productionObservation.landmarks.size}"
  IO.println verifierCompletionProtocol.marker
  return 0

def operationalError (error : IO.Error) : String :=
  s!"trust verification: could not complete semantic inspection: {error}. Fix the named module/path or rebuild its .olean, then rerun `lake build tlverify --wfail` and `lake exe tlverify`."

unsafe def run : IO UInt32 := do
  try runChecked
  catch error =>
    IO.eprintln (operationalError error)
    return 1

end Tl.Verify

unsafe def main : IO UInt32 := Tl.Verify.run
