/- Process-completion protocol and supervision decision shared by the minimal
   verifier launcher and its tests. -/
import Lean

namespace Tl.Verify

/-- A supervised worker's completion contract. The launcher stays independent
    of the worker's imports and selects one of these protocols from its own
    executable name. -/
structure CompletionProtocol where
  label : String
  marker : String
  workerFile : String
  buildCommand : String
  runCommand : String
  deriving DecidableEq, Repr

def verifierCompletionProtocol : CompletionProtocol := {
  label := "trust verification"
  marker := "TL_VERIFY_COMPLETED_V1"
  workerFile := "tlverifyWorker"
  buildCommand := "lake build tlverify"
  runCommand := "lake exe tlverify"
}

def testCompletionProtocol : CompletionProtocol := {
  label := "test suite"
  marker := "TL_TESTS_COMPLETED_V1"
  workerFile := "tltestWorker"
  buildCommand := "lake build tltest"
  runCommand := "lake exe tltest"
}

/-- Status zero is accepted only when the marker is the final nonempty stdout
    line. This detects both an early exit before the marker and later work
    accidentally moved after it. Deliberate in-worker forgery remains outside
    what an in-band protocol can authenticate. -/
def completedSuccessfully (protocol : CompletionProtocol)
    (exitCode : UInt32) (stdout : String) : Bool :=
  let lastNonempty := (stdout.splitOn "\n").foldl (fun latest line =>
    if line.trimAscii.isEmpty then latest else some line) none
  exitCode == 0 && lastNonempty == some protocol.marker

/-- Run the audited worker through `runWorker` and decide the gate's status.
    The injected runner keeps the process-spawn exception path testable; the
    shipped `superviseWorker` below supplies `IO.Process.output`. -/
def superviseWorkerWith
    (runWorker : System.FilePath → IO IO.Process.Output)
    (protocol : CompletionProtocol)
    (worker : System.FilePath) : IO UInt32 := do
  -- A missing worker does not raise: `IO.Process.output` reports the failed
  -- exec as status 255, which would otherwise be diagnosed as trust findings.
  unless ← worker.pathExists do
    IO.eprintln s!"{protocol.label} supervisor: no worker at {worker}. Build it with `{protocol.buildCommand}`, then run it as `{protocol.runCommand}` from the tl checkout."
    return 1
  let spawned ← try
      pure (some (← runWorker worker))
    catch error => do
      IO.eprintln s!"{protocol.label} supervisor: could not run the worker at {worker}: {error}. Rebuild it with `{protocol.buildCommand}`, then rerun `{protocol.runCommand}` from the tl checkout."
      pure none
  let some result := spawned | return 1
  IO.print result.stdout
  IO.eprint result.stderr
  if completedSuccessfully protocol result.exitCode result.stdout then return 0
  -- The two failures need opposite next actions: a worker that exited non-zero
  -- has already said what is wrong, while status zero without the marker is the
  -- unmarked early-exit case this protocol exists to catch.
  if result.exitCode == 255 then
    IO.eprintln s!"{protocol.label} supervisor: could not execute the worker at {worker}; restore its executable permission or rebuild it with `{protocol.buildCommand}`, then rerun `{protocol.runCommand}`"
  else if result.exitCode != 0 then
    IO.eprintln s!"{protocol.label} supervisor: the worker exited with status {result.exitCode}; fix what it reported above and rerun `{protocol.runCommand}`"
  else
    IO.eprintln s!"{protocol.label} supervisor: the worker exited successfully without its final completion verdict as the last nonempty stdout line; fix an early-exit/initialization failure or work left after the marker, then rerun `{protocol.runCommand}`"
  return 1

/-- Run the audited worker and decide the gate's status: forward its streams,
    then accept only a run that both succeeded and reached its final marker.
    Lives here rather than in `Verify.Launcher` so the decision — not just the
    `completedSuccessfully` predicate — is exercised against real processes by
    `Tests/VerifyTests.lean`. -/
def superviseWorker (protocol : CompletionProtocol) (worker : System.FilePath) : IO UInt32 :=
  superviseWorkerWith (fun path => IO.Process.output { cmd := path.toString }) protocol worker

/-- Minimal executable entry shared by the two distinct launcher roots. -/
def launchSiblingWorker (protocol : CompletionProtocol) : IO UInt32 := do
  let appPath ← IO.appPath
  let some appDir := appPath.parent | do
    IO.eprintln s!"{protocol.label} supervisor: cannot locate the executable directory above {appPath}; run it as `{protocol.runCommand}` from the tl checkout"
    return 1
  superviseWorker protocol (appDir / protocol.workerFile)

end Tl.Verify
