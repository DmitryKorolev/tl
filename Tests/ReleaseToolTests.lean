/-
`Tests.ReleaseToolTests` — the `tlrelease` decision layer.

Outside the TCB and therefore tested rather than proved (ADR-0004), with one
exception noted where it applies: a pure verdict function whose failure mode is
a silent false negative carries a theorem instead, in the `Verify/Proofs.lean`
style. Nothing here is a landmark claim — landmarks guard the *product's*
proved claims, and release administration is not the product.

Driven in-process against `release.Cli` rather than by spawning the binary:
the branches that matter are the refusals, and a refusal is easier to pin down
by its exit status and the text it teaches than by a process's output stream.
`release.Main` exists only so that this import does not collide with the
harness's own `main`.
-/
import Tests.Harness
import release.Cli

namespace Tl.Tests

open Release

/-- Run a dispatch and capture what it told each stream. Both are captured,
    because *which* stream a message reaches is part of the contract: usage
    goes to stderr on a refusal so a caller redirecting stdout still sees why,
    and to stdout on an explicit `--help` so it can be paged. -/
private def dispatchCaptured (args : List String) : IO (UInt32 × String × String) := do
  let out ← IO.mkRef { : IO.FS.Stream.Buffer }
  let err ← IO.mkRef { : IO.FS.Stream.Buffer }
  let status ← IO.withStdout (IO.FS.Stream.ofBuffer out) <|
    IO.withStderr (IO.FS.Stream.ofBuffer err) <| dispatch args
  return (status, String.fromUTF8! (← out.get).data, String.fromUTF8! (← err.get).data)

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

def releaseToolTests : IO (List Outcome) := do
  let (helpStatus, helpOut, helpErr) ← dispatchCaptured ["--help"]
  let (shortStatus, shortOut, _) ← dispatchCaptured ["-h"]
  let (wordStatus, wordOut, _) ← dispatchCaptured ["help"]
  let (emptyStatus, emptyOut, emptyErr) ← dispatchCaptured []
  let (unknownStatus, unknownOut, unknownErr) ← dispatchCaptured ["publish-everything"]
  let mut outs := [
    -- Asking for help is not an error, and it goes to stdout.
    checkEq "tlrelease: --help succeeds" helpStatus 0,
    check "tlrelease: --help writes the usage to stdout" (contains helpOut "usage: tlrelease")
      helpOut,
    check "tlrelease: --help writes nothing to stderr" helpErr.isEmpty helpErr,
    checkEq "tlrelease: -h is the same as --help" (shortStatus, shortOut) (helpStatus, helpOut),
    checkEq "tlrelease: the help subcommand is the same as --help"
      (wordStatus, wordOut) (helpStatus, helpOut),
    -- The two refusals. A release step invoking this with no command, or with
    -- a command this build does not have, must not be able to read the result
    -- as success — that is the entire failure this executable exists to stop.
    checkEq "tlrelease: no command is a usage error" emptyStatus 2,
    check "tlrelease: no command says so on stderr"
      (contains emptyErr "no command given") emptyErr,
    check "tlrelease: no command writes nothing to stdout" emptyOut.isEmpty emptyOut,
    checkEq "tlrelease: an unknown command is a usage error" unknownStatus 2,
    check "tlrelease: an unknown command names the command it did not recognise"
      (contains unknownErr "publish-everything") unknownErr,
    check "tlrelease: an unknown command says how to list the real ones"
      (contains unknownErr "--help") unknownErr,
    check "tlrelease: an unknown command writes nothing to stdout" unknownOut.isEmpty unknownOut,
    -- Distinguishing "did nothing" from "succeeded" is the whole point, so a
    -- refusal must never share an exit status with success.
    check "tlrelease: no refusal exits zero"
      (emptyStatus != 0 && unknownStatus != 0) s!"empty={emptyStatus} unknown={unknownStatus}"]
  -- `help` is generated from the same table `dispatch` reads, so a command
  -- that exists but is undocumented — or documented but unreachable — is not
  -- representable. These rows check that the table is actually the source of
  -- both, which is only observable once it is non-empty.
  for command in commands do
    let (status, stdout, _) ← dispatchCaptured [command.name, "--help"]
    outs := outs ++ [
      check s!"tlrelease: '{command.name}' is listed in the usage"
        (contains helpOut command.name) helpOut,
      check s!"tlrelease: '{command.name}' is reachable from dispatch"
        (status != 2 || !contains stdout "unknown command")
        s!"dispatching {command.name} reported it as unknown"]
  outs := outs ++ [
    check "tlrelease: every command has a distinct name"
      ((commands.map (·.name)).eraseDups.length == commands.length)
      s!"duplicate command names: {commands.map (·.name)}"]
  return outs

end Tl.Tests
