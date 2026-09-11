/- Process-completion protocol and supervision decision shared by the minimal
   verifier launcher and its tests. -/
import Lean

namespace Tl.Verify

/-- A supervised worker's completion contract. The launcher stays independent
    of the worker's imports and selects one of these protocols from its own
    executable name. -/
structure CompletionProtocol where
  /-- The gate's product name, spelled the way a reader invokes it. It opens
      the verdict line so a log tells you which of the two gates finished. -/
  tool : String
  label : String
  /-- Bumped when the verdict's shape or meaning changes. A worker and a
      launcher built at different revisions then disagree on the exact string
      and the run is refused, rather than one accepting the other's line
      because it happens to look finished. -/
  protocolVersion : Nat
  workerFile : String
  buildCommand : String
  runCommand : String
  deriving DecidableEq, Repr

/-- The line a completed worker prints last, and the only one its supervisor
    accepts as evidence that it reached the end.

    Derived from the fields above rather than stored beside them: a second
    constant would be one more thing to keep in step, and the copy it drifted
    from would be the one the launcher compares against. Two protocols
    therefore differ in this line by construction — they already differ in
    `tool` and in `label`.

    A sentence rather than an opaque token, because whoever meets it is reading
    a CI log: a bare constant is a question ("what is this, and did it pass?")
    that the line can answer itself for the cost of a few words. Readability
    does not weaken the contract — the string is still matched exactly, in
    full, and as the last nonempty line — and it never authenticated a worker
    that deliberately forges it, which is outside what any in-band protocol can
    establish. -/
def CompletionProtocol.verdict (protocol : CompletionProtocol) : String :=
  s!"{protocol.tool}: {protocol.label} completed (completion protocol v{protocol.protocolVersion})"

def verifierCompletionProtocol : CompletionProtocol := {
  tool := "tlverify"
  label := "trust verification"
  protocolVersion := 1
  workerFile := "tlverifyWorker"
  buildCommand := "lake build tlverify"
  runCommand := "lake exe tlverify"
}

def testCompletionProtocol : CompletionProtocol := {
  tool := "tltest"
  label := "test suite"
  protocolVersion := 1
  workerFile := "tltestWorker"
  buildCommand := "lake build tltest"
  runCommand := "lake exe tltest"
}

/-- A selected run or a discovery request must never emit the full-suite verdict. -/
def testRequestCompletionProtocol (args : List String) : CompletionProtocol :=
  if args.isEmpty then testCompletionProtocol
  else { testCompletionProtocol with label := "test runner request" }

/-- Status zero is accepted only when the protocol's verdict is the final
    nonempty stdout line. This detects both an early exit before the verdict
    and later work accidentally moved after it. Deliberate in-worker forgery
    remains outside what an in-band protocol can authenticate. -/
def completedSuccessfully (protocol : CompletionProtocol)
    (exitCode : UInt32) (stdout : String) : Bool :=
  let lastNonempty := (stdout.splitOn "\n").foldl (fun latest line =>
    if line.trimAscii.isEmpty then latest else some line) none
  exitCode == 0 && lastNonempty == some protocol.verdict

/-- Run the audited worker through `runWorker` and decide the gate's status.
    The injected runner keeps the process-spawn exception path testable; the
    shipped `superviseWorker` below supplies `IO.Process.output`. -/
def superviseWorkerWith
    (runWorker : System.FilePath → IO IO.Process.Output)
    (protocol : CompletionProtocol)
    (worker : System.FilePath) (forwardOutput : Bool := true) : IO UInt32 := do
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
  if forwardOutput then
    IO.print result.stdout
    IO.eprint result.stderr
  if completedSuccessfully protocol result.exitCode result.stdout then return 0
  -- The two failures need opposite next actions: a worker that exited non-zero
  -- has already said what is wrong, while status zero without the verdict is
  -- the unannounced early-exit case this protocol exists to catch.
  if result.exitCode == 255 then
    IO.eprintln s!"{protocol.label} supervisor: could not execute the worker at {worker}; restore its executable permission or rebuild it with `{protocol.buildCommand}`, then rerun `{protocol.runCommand}`"
  else if result.exitCode != 0 then
    IO.eprintln s!"{protocol.label} supervisor: the worker exited with status {result.exitCode}; fix what it reported above and rerun `{protocol.runCommand}`"
  else
    IO.eprintln s!"{protocol.label} supervisor: the worker exited successfully without its final completion verdict as the last nonempty stdout line — expected exactly `{protocol.verdict}`; fix an early-exit/initialization failure, or work left after the verdict, then rerun `{protocol.runCommand}`"
  return 1

/-- Run the audited worker and decide the gate's status: forward its streams,
    then accept only a run that both succeeded and reached its final marker.
    Lives here rather than in `Verify.Launcher` so the decision — not just the
    `completedSuccessfully` predicate — is exercised against real processes by
    `Tests/VerifyTests.lean`. -/
def superviseWorker (protocol : CompletionProtocol) (worker : System.FilePath) : IO UInt32 :=
  superviseWorkerWith (fun path => IO.Process.output { cmd := path.toString }) protocol worker

/-- Drain a pipe as it arrives, retaining only the last nonempty line needed
    for the completion check. Memory does not grow with the assertion log. -/
partial def forwardWorkerStream (source : IO.FS.Handle) (target : IO.FS.Stream)
    (stopped : IO.Ref Bool) : IO String := do
  let rec loop (last : String) : IO String := do
    let line ← source.getLine
    if line.isEmpty || (← stopped.get) then return last
    target.putStr line
    target.flush
    loop (if line.trimAscii.isEmpty then last else line)
  loop ""

/-- Both pipes are drained concurrently; a full stderr pipe cannot block stdout
    progress. The caller's streams are captured before starting the reader task. -/
def streamingWorkerOutput (worker : System.FilePath) (args : Array String) :
    IO IO.Process.Output := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  let child ← IO.Process.spawn {
    cmd := worker.toString, args, stdin := .null, stdout := .piped, stderr := .piped }
  let stopped ← IO.mkRef false
  let stdout ← IO.asTask (forwardWorkerStream child.stdout out stopped) Task.Priority.dedicated
  let stderr ← IO.asTask (forwardWorkerStream child.stderr err stopped) Task.Priority.dedicated
  -- Observe either reader's failure without first joining the other: a fixture
  -- descendant can inherit its pipe and keep it open after the worker exits.
  -- Keep the terminal's process group so Ctrl+C still reaches worker fixtures.
  try
    let (first, remaining) ← IO.waitAny' [stdout, stderr]
    let _ ← IO.ofExcept first
    for reader in remaining do
      let _ ← IO.ofExcept (← IO.wait reader)
    let exitCode ← child.wait
    let last ← IO.ofExcept (← IO.wait stdout)
    return { exitCode, stdout := last, stderr := "" }
  catch error =>
    stopped.set true
    try child.kill catch _ => pure ()
    -- Reap asynchronously: termination is best-effort and neither a worker
    -- ignoring it nor a descendant retaining a pipe may hide this failure.
    -- The public launcher exits after reporting the error. This is not process
    -- containment; callers embedding this helper must own descendant cleanup.
    let _ ← IO.asTask child.wait Task.Priority.dedicated
    throw error

def superviseStreamingWorker (protocol : CompletionProtocol) (worker : System.FilePath)
    (args : Array String := #[]) : IO UInt32 :=
  superviseWorkerWith (fun path => streamingWorkerOutput path args) protocol worker false

/-- Minimal executable entry shared by the two distinct launcher roots. -/
def launchSiblingWorker (protocol : CompletionProtocol) (args : Array String := #[])
    (streaming : Bool := false) : IO UInt32 := do
  let appPath ← IO.appPath
  let some appDir := appPath.parent | do
    IO.eprintln s!"{protocol.label} supervisor: cannot locate the executable directory above {appPath}; run it as `{protocol.runCommand}` from the tl checkout"
    return 1
  if streaming then
    superviseStreamingWorker protocol (appDir / protocol.workerFile) args
  else
    superviseWorkerWith (fun path => IO.Process.output { cmd := path.toString, args })
      protocol (appDir / protocol.workerFile)

end Tl.Verify
