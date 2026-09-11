import Tests.Runner
import Verify.Supervise

namespace Tl.Tests

open Tl.Verify

private def captureRunner (action : IO UInt32) : IO (UInt32 × String × String) := do
  let out ← IO.mkRef { : IO.FS.Stream.Buffer }
  let err ← IO.mkRef { : IO.FS.Stream.Buffer }
  let status ← IO.withStdout (IO.FS.Stream.ofBuffer out) <|
    IO.withStderr (IO.FS.Stream.ofBuffer err) action
  return (status, String.fromUTF8! (← out.get).data, String.fromUTF8! (← err.get).data)

private def runnerSelectionTests : IO (List Outcome) := do
  let visited ← IO.mkRef ([] : List String)
  let group (id : String) : TestGroup := {
    id, label := s!"label {id}", run := fun _ => do
      visited.modify (· ++ [id])
      return [check id true] }
  let registry := [group "first", group "second", group "third"]
  let mut rows := [
    checkOk "no arguments select the complete suite" (parseTestRequest []) (.run []),
    checkOk "help request" (parseTestRequest ["--help"]) .help,
    checkOk "list request" (parseTestRequest ["--list"]) .list,
    checkOk "repeated selectors parse without losing order"
      (parseTestRequest ["--group", "second", "--group", "first"])
      (.run ["second", "first"])]
  for args in [["--group"], ["--group", ""], ["--group", "  "],
      ["--group", "--list"], ["unknown"], ["--list", "--group", "first"],
      ["--group", "first", "--help"], ["--help", "--list"]] do
    let (status, _, err) ← captureRunner (runTestRequest registry args)
    rows := rows ++ [checkEq s!"invalid selection {args}: usage status" status 2,
      check s!"invalid selection {args}: remedy" (err.contains "--help" || err.contains "--list")]
  let (unknown, _, unknownErr) ← captureRunner
    (runTestRequest registry ["--group", "first", "--group", "absent"])
  rows := rows ++ [checkEq "unknown selection refuses before valid prefix runs" unknown 2,
    check "unknown name is diagnosed" (unknownErr.contains "absent" && unknownErr.contains "--list"),
    checkEq "invalid requests never execute a group" (← visited.get) []]
  let (listed, listOut, _) ← captureRunner (runTestRequest registry ["--list"])
  let (helped, helpOut, _) ← captureRunner (runTestRequest registry ["--help"])
  rows := rows ++ [checkEq "list succeeds" listed 0,
    check "list includes every id and label" (registry.all fun g => listOut.contains s!"{g.id}\t{g.label}"),
    checkEq "help succeeds" helped 0,
    check "help documents full versus focused runs" (helpOut.contains "complete CI suite"),
    checkEq "discovery never runs fixtures" (← visited.get) []]
  let (focused, focusedOut, _) ← captureRunner
    (runTestRequest registry ["--group", "third", "--group", "first", "--group", "third"])
  rows := rows ++ [checkEq "focused run succeeds" focused 0,
    checkEq "selected groups run once in registry order" (← visited.get) ["first", "third"],
    check "focused report is explicit and timed"
      (focusedOut.contains "selected test groups only" && focusedOut.contains "END third:" &&
       focusedOut.contains " ms" && focusedOut.contains "All 2 assertions passed.")]
  visited.set []
  let (full, fullOut, _) ← captureRunner (runTestRequest registry [])
  rows := rows ++ [checkEq "default full run succeeds" full 0,
    checkEq "default visits every group exactly once" (← visited.get) ["first", "second", "third"],
    check "full report identifies complete coverage"
      (fullOut.contains "complete test suite" && fullOut.contains "All 3 assertions passed.")]
  for (name, invalid) in [("empty", []), ("duplicate", [group "same", group "same"]),
      ("unnamed", [group " "])] do
    let (status, _, err) ← captureRunner (runTestRequest invalid [])
    rows := rows ++ [checkEq s!"{name} registry refuses" status 2,
      check s!"{name} registry teaches repair" (err.contains "restore" || err.contains "give")]
  let (noGroups, _, noGroupsErr) ← captureRunner (runTestGroups [])
  rows := rows ++ [checkEq "direct empty run is not success" noGroups 1,
    check "empty run teaches selection" (noGroupsErr.contains "--list")]
  let failed : TestGroup := { id := "failed", label := "failed", run := fun _ => do
    return [check "deliberate failure" false "repair assertion"] }
  let empty : TestGroup := { id := "empty", label := "empty", run := fun _ => pure [] }
  let crashed : TestGroup := { id := "crashed", label := "crashed", run := fun _ => do
    throw (IO.userError "fixture exception") }
  visited.set []
  let (bad, badOut, badErr) ← captureRunner (runTestGroups [failed, empty, crashed, group "after"])
  rows := rows ++ [checkEq "assertion, empty group and exception fail run" bad 1,
    check "all failure kinds reach the log"
      (badOut.contains "repair assertion" && badOut.contains "test group is nonempty" &&
       badOut.contains "fixture exception" && badOut.contains "--group crashed"),
    check "summary counts synthetic failures" (badErr.contains "3/4 assertions FAILED"),
    checkEq "later groups still execute after failures" (← visited.get) ["after"]]
  -- The START line must be flushed before entering setup, not merely collected
  -- and printed at the end of the group.
  let output ← IO.mkRef { : IO.FS.Stream.Buffer }
  let flushed ← IO.mkRef false
  let stream := { IO.FS.Stream.ofBuffer output with flush := flushed.set true }
  let progressGroup : TestGroup := { id := "progress", label := "progress", run := fun _ => do
    let started := (String.fromUTF8! (← output.get).data).contains "START progress:"
    return [check "progress precedes setup" (started && (← flushed.get))] }
  let progressStatus ← IO.withStdout stream (runTestGroups [progressGroup])
  rows := rows ++ [checkEq "START is observable and flushed before setup" progressStatus 0]
  let (fixtureStatus, fixtureOut, _) ← captureRunner do
    let value ← measureTestFixture "success" (pure (7 : Nat))
    let failure ← (measureTestFixture "exception" (throw (IO.userError "fixture failure") : IO Nat)).toBaseIO
    return if value == 7 && (match failure with | .error _ => true | .ok _ => false) then 0 else 1
  return rows ++ [checkEq "fixture timing preserves values and exceptions" fixtureStatus 0,
    check "fixture timing reports success and failure boundaries"
      (["FIXTURE START success", "FIXTURE END success:", "FIXTURE START exception",
        "FIXTURE END exception:"].all (fun text => fixtureOut.contains text))]

private def streamingSupervisorTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  try
    let stub (name body : String) : IO System.FilePath := do
      let path := base / name
      IO.FS.writeFile path s!"#!/bin/sh\n{body}\n"
      let result ← IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
      unless result.exitCode == 0 do throw (IO.userError "could not make worker fixture executable")
      return path
    let args := ["--group", "literal name"]
    let protocol := testRequestCompletionProtocol args
    let verdict := s!"printf '%s\\n' '{protocol.verdict}'"
    let success ← stub "success" s!"printf '%s\\n' \"$1\" \"$2\"; echo diagnostic >&2; {verdict}"
    let (status, stdout, stderr) ← captureRunner (superviseStreamingWorker protocol success args.toArray)
    let mut rows := [checkEq "streamed worker passes" status 0,
      check "arguments are forwarded literally" (stdout.startsWith "--group\nliteral name\n"),
      check "stdout is forwarded exactly once" ((stdout.splitOn protocol.verdict).length == 2),
      checkEq "stderr is forwarded" stderr "diagnostic\n",
      check "focused verdict cannot certify the full suite"
        (!completedSuccessfully testCompletionProtocol 0 stdout),
      checkEq "no arguments preserve full-suite protocol" (testRequestCompletionProtocol []) testCompletionProtocol]
    for (name, body, expected, diagnostic) in [
        ("early", "echo working; exit 0", 1, "early-exit"),
        ("trailing", s!"{verdict}; echo later", 1, "last nonempty stdout line"),
        ("failed", s!"{verdict}; exit 7", 1, "status 7"),
        ("blank-tail", s!"{verdict}; printf '\\n  \\n'", 0, ""),
        ("no-newline", s!"printf '%s' '{protocol.verdict}'", 0, ""),
        ("wrong-protocol", s!"echo '{testCompletionProtocol.verdict}'", 1, "early-exit"),
        ("truncated", "printf 'tltest: test runner request'", 1, "early-exit"),
        ("nul-tail", s!"{verdict}; printf '\\000after\\n'", 1, "last nonempty stdout line"),
        ("nul-verdict", s!"printf '%s\\000hidden\\n' '{protocol.verdict}'", 1, "early-exit"),
        ("invalid-utf8-tail", s!"{verdict}; printf '\\377after\\n'", 1, "last nonempty stdout line") ] do
      let worker ← stub name body
      let (code, _, err) ← captureRunner (superviseStreamingWorker protocol worker)
      rows := rows ++ [checkEq s!"streamed {name}: status" code expected,
        check s!"streamed {name}: diagnostic" (err.contains diagnostic)]
    let missing := base / "missing"
    let (missingCode, _, missingErr) ← captureRunner (superviseStreamingWorker protocol missing)
    IO.FS.writeFile missing "not executable"
    let (execCode, _, execErr) ← captureRunner (superviseStreamingWorker protocol missing)
    rows := rows ++ [checkEq "streamed missing worker refuses" missingCode 1,
      check "missing worker gives build remedy" (missingErr.contains "lake build tltest"),
      checkEq "streamed unexecutable worker refuses" execCode 1,
      check "exec failure gives permission remedy" (execErr.contains "executable permission")]
    -- A handshake, not a speed assertion: the worker cannot complete until
    -- both stdout and stderr have been forwarded and flushed by its supervisor.
    let ackOut := base / "ack-out"
    let ackErr := base / "ack-err"
    let worker ← stub "handshake" s!"echo stdout-ready; echo stderr-ready >&2\n\
      i=0\nwhile [ ! -f '{ackOut}' ] || [ ! -f '{ackErr}' ]; do\n\
      i=$((i + 1)); [ \"$i\" -lt 500 ] || exit 9; sleep 0.01\ndone\n\
      i=0\nwhile [ \"$i\" -lt 3000 ]; do\n\
      echo 'stderr burst makes more than one pipe buffer of diagnostic output' >&2\n\
      i=$((i + 1))\ndone\necho 'UTF-8: λ ✓'; {verdict}"
    let out ← IO.mkRef { : IO.FS.Stream.Buffer }
    let err ← IO.mkRef { : IO.FS.Stream.Buffer }
    let acknowledge (path : System.FilePath) : IO (IO Unit) := do
      let sent ← IO.mkRef false
      return do
        unless ← sent.get do
          IO.FS.writeFile path "seen"
          sent.set true
    let outFlush ← acknowledge ackOut
    let errFlush ← acknowledge ackErr
    let outStream := { IO.FS.Stream.ofBuffer out with flush := outFlush }
    let errStream := { IO.FS.Stream.ofBuffer err with flush := errFlush }
    let code ← IO.withStdout outStream <| IO.withStderr errStream <|
      superviseStreamingWorker protocol worker
    rows := rows ++ [checkEq "both streams reach consumer before worker exit" code 0,
      check "streaming preserves Unicode" ((String.fromUTF8! (← out.get).data).contains "λ ✓"),
      check "stderr burst drains without deadlock" ((← err.get).data.size > 65536)]
    -- A broken consumer must request termination of the direct worker,
    -- including when the error happens on the background stdout reader.
    let brokenWorker ← stub "broken-consumer" "while :; do echo line; echo line >&2; done"
    for breakStdout in [true, false] do
      let sink := IO.FS.Stream.ofBuffer (← IO.mkRef { : IO.FS.Stream.Buffer })
      let broken := { sink with flush := throw (IO.userError "injected consumer failure") }
      let result ← (IO.withStdout (if breakStdout then broken else sink) <|
        IO.withStderr (if breakStdout then sink else broken) <|
          streamingWorkerOutput brokenWorker #[]).toBaseIO
      rows := rows ++ [check s!"consumer error propagates after cleanup (stdout={breakStdout})"
        (match result with
         | .error error => error.toString.contains "injected consumer failure"
         | .ok _ => false)]
    -- The descendant keeps both pipes open until the caller releases it.
    -- Failure must return before that release, for either reader; the bounded
    -- fallback makes a regression fail an assertion instead of hanging tests.
    let ready := base / "descendant-ready"
    let release := base / "descendant-release"
    let expired := base / "descendant-expired"
    let stopped := base / "descendant-stopped"
    let descendant ← stub "descendant" s!"echo ready > '{ready}'\n\
      i=0\nwhile [ ! -f '{release}' ]; do\n\
      i=$((i + 1)); if [ \"$i\" -ge 200 ]; then echo expired > '{expired}'; break; fi\n\
      sleep 0.01\ndone\necho stopped > '{stopped}'"
    let parent ← stub "parent" s!"'{descendant}' &\n\
      i=0\nwhile [ ! -f '{ready}' ]; do\n\
      i=$((i + 1)); [ \"$i\" -lt 500 ] || exit 9; sleep 0.01\ndone\n\
      echo stdout-ready; echo stderr-ready >&2\nwait"
    for breakStdout in [true, false] do
      for path in [ready, release, expired, stopped] do
        if ← path.pathExists then IO.FS.removeFile path
      let sink := IO.FS.Stream.ofBuffer (← IO.mkRef { : IO.FS.Stream.Buffer })
      let broken := { sink with flush := throw (IO.userError "descendant consumer failure") }
      let result ← (IO.withStdout (if breakStdout then broken else sink) <|
        IO.withStderr (if breakStdout then sink else broken) <|
          streamingWorkerOutput parent #[]).toBaseIO
      let returnedBeforeRelease := !(← expired.pathExists)
      IO.FS.writeFile release "release"
      for _ in [:500] do
        if ← stopped.pathExists then break
        IO.sleep 10
      rows := rows ++ [
        check s!"descendant cleanup preserves consumer error (stdout={breakStdout})"
          (match result with
           | .error error => error.toString.contains "descendant consumer failure"
           | .ok _ => false),
        check s!"consumer failure returns while descendant retains pipes (stdout={breakStdout})"
          returnedBeforeRelease,
        check s!"descendant fixture completes after release (stdout={breakStdout})"
          (← stopped.pathExists)]
    return rows
  finally IO.FS.removeDirAll base

/-- Pin the public registry and drive actual launcher-to-worker argument flow.
    The selected HLC group has no subprocess fixtures and cannot recurse here. -/
private def runnerCommandTests : IO (List Outcome) := do
  let expected := ["hermetic", "imports", "verify", "verify-loaded", "hlc", "hlc-roundtrip",
    "hlc-monotone", "crockford", "crockford-roundtrip", "record", "errors", "sha256", "time",
    "codec", "sys", "store", "cli", "cross", "cross-evidence", "sanitize", "grammar",
    "doc-grammar", "release-identity", "release-plan", "release-tool", "shell-inventory",
    "verifier-process", "verifier-mutations", "verifier-command", "installer-command",
    "installer-branches", "installer-branch-mutations", "installer-process",
    "installer-process-mutations", "release-drift", "workflow-commands", "workflow-release",
    "workflow-policy", "release-privilege", "build-provenance", "sync", "cache-codec",
    "cache-fold", "cache-suffix", "cache-version", "cache-io", "perf", "perf-primitives",
    "perf-binary", "runner"]
  let list ← IO.Process.output { cmd := ".lake/build/bin/tltest", args := #["--list"] }
  let ids := (list.stdout.splitOn "\n").filterMap fun line =>
    if line.contains "\t" then (line.splitOn "\t").head? else none
  let mut rows := [checkEq "public list preserves every registered group" ids expected,
    checkEq "public list succeeds" list.exitCode 0,
    check "public list runs no group" (!list.stdout.contains "START ")]
  for (args, expectedStatus, text) in [
      (#["--help"], 0, "Usage: lake exe tltest"),
      (#["--group", "hlc"], 0, "END hlc:"),
      (#["--group", "hlc", "--group", "absent"], 1, "unknown group 'absent'"),
      (#["--group", ""], 1, "nonempty group name"),
      (#["--group"], 1, "needs a group name")] do
    let result ← IO.Process.output { cmd := ".lake/build/bin/tltest", args }
    rows := rows ++ [checkEq s!"public runner {args}: status" result.exitCode expectedStatus,
      check s!"public runner {args}: report" ((result.stdout ++ result.stderr).contains text),
      check s!"public runner {args}: never certifies full suite"
        (!result.stdout.contains testCompletionProtocol.verdict)]
    if expectedStatus == 0 then
      rows := rows ++ [check s!"public runner {args}: request completion"
        (completedSuccessfully (testRequestCompletionProtocol args.toList) result.exitCode result.stdout)]
    else
      rows := rows ++ [check s!"public runner {args}: no fixtures or completion on invalid request"
        (!result.stdout.contains "START " && !result.stdout.contains "completed (completion protocol")]
  return rows

def runnerTests : IO (List Outcome) := do
  return (← runnerSelectionTests) ++ (← streamingSupervisorTests) ++ (← runnerCommandTests)

end Tl.Tests
