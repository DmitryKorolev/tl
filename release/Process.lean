/-
Running another program, with its exit status as a value.

This is the seam the whole port turns on. The recurring defect across three
review rounds was not that anyone forgot to check a status — it was that POSIX
shell offers several spellings that *discard* one while looking like they carry
it: `sha256sum "$f" | cut -d' ' -f1` returns `cut`'s status, `VAR="$(f)" prog`
returns `prog`'s, `$(gh api … || echo '')` turns an error into an absent value,
and `$(cmd; echo $?)` returns the `echo`. Every one of those reported success
for a check that could not run.

There is no spelling here that drops one. `run` returns a `RunOutcome` a caller
has to `match` on, and the three cases are the three genuinely different things
that can happen — the program ran and said something, the program is not there
to run, the program is there and did not finish. Collapsing the last two into
the first is the `AuditOutcome` mistake one level down: "I could not look" is
not "I looked and it was fine".

Three properties every run gets, so no caller can forget one:

- **Both pipes drain on their own tasks, before the wait.** A child writing
  more than a pipe buffer holds blocks in `write` while the parent blocks in
  `wait`, and neither ever moves. The digest of a large file is small output,
  but `gh` returns pages of JSON and this helper is written once for both.
- **Standard input is `/dev/null`.** Nothing here has anything to send, and a
  program that decides to prompt — a credential helper, a pager, an
  `are you sure?` — reads EOF and gives up immediately instead of hanging until
  the bound expires. The bound is the backstop, not the mechanism.
- **A bound, always.** `0` is not accepted as "unbounded" the way the git
  helper accepts it: this tool runs inside a release job whose own timeout is
  the only other thing that would stop it, and a release that hangs in the
  signing step until GitHub kills it is a release with no diagnosis.

Deliberately not modelled on `Tl/Sync/Ref.lean`'s environment scrub. That one
exists because a `git` subprocess reads repository routing out of the
environment; the programs here read none, and inheriting the environment is
what lets a release job point at a tool it installed.
-/

namespace Release

/-- What a program that ran said, and how it ended. Both streams are captured
    and kept apart: a tool's diagnosis belongs in a refusal message, and its
    answer belongs in the value being computed, and reading one for the other
    is how a digest becomes an error string. -/
structure ProcessOutput where
  exitCode : UInt32
  stdout : String
  stderr : String
  deriving Repr

/-- Whether a program ended by succeeding. A named function rather than
    `== 0` at each call site, so that the one convention every caller depends
    on is written down once. -/
def ProcessOutput.succeeded (output : ProcessOutput) : Bool := output.exitCode == 0

/-- What became of an attempt to run a program.

    Three cases because there are three answers, and only the first is a
    result. `unavailable` is "there is nothing on PATH by that name, or it is
    not executable"; `timedOut` is "it is there, it started, and it did not
    finish". Both are refusals with different remedies — install the tool
    versus find out why it hung — and neither may ever be read as an answer. -/
inductive RunOutcome where
  | completed (output : ProcessOutput)
  | unavailable (command : String) (detail : String)
  | timedOut (command : String) (afterMs : Nat)
  deriving Repr

/-- The default bound. Generous, because the one long-running call is hashing a
    release binary — a hundred megabytes or so, which every digest tool does in
    well under a second, but on a cold artifact download from a network
    filesystem the read dominates and a tight bound would turn a slow disk into
    a failed release. It is a backstop against a hang, not a performance
    budget. -/
def defaultTimeoutMs : Nat := 120000

/-- The poll step. Ten milliseconds is the same figure `Tl/Sync/Ref.lean`
    settled on: short enough that a fast program adds no perceptible latency,
    long enough that waiting is not a busy-spin. -/
private def pollStepMs : Nat := 10

/-- Lean's own message when the child stub cannot exec the named program.

    `IO.Process.spawn` does not fail on a name that is not on PATH — the fork
    succeeds and the *child* discovers there is nothing to exec, prints this,
    and exits. So "there is no such program" arrives looking exactly like "the
    program ran and failed", which is the conflation this module exists to
    remove, and it is recovered here rather than left to each caller.

    Matching a runtime message is not a thing to be pleased about, and it is
    kept honest by what depends on it: nothing. Both readings refuse, and the
    only difference is which remedy the operator is shown — install the tool, or
    find out why it failed. If a later toolchain changes the wording the worst
    outcome is a less helpful sentence, never an acceptance. -/
private def notExecutableMarker : String := "could not execute external process"

/-- The conventional POSIX status for "command not found", which a shell in the
    chain would produce even where the message above does not appear. -/
private def commandNotFoundStatus : UInt32 := 127

private def looksUnexecutable (output : ProcessOutput) : Bool :=
  output.exitCode == commandNotFoundStatus
    || (output.exitCode != 0 && (output.stderr.splitOn notExecutableMarker).length > 1)

/-- Run `command` with `args`, waiting at most `timeoutMs`.

    The bound is enforced by polling rather than by a second thread: `tryWait`
    on the calling thread costs nothing while the child runs and needs no
    coordination to tear down. On expiry the child is killed, so a hung tool
    cannot outlive the command that started it.

    A `timeoutMs` of `0` would make the loop below run once and then report a
    timeout the child never had a chance to miss, which is a bound that refuses
    everything rather than nothing. It is raised to one step instead — the
    caller asked for "as little as possible", and that is what a single poll
    is. -/
def run (command : String) (args : Array String)
    (timeoutMs : Nat := defaultTimeoutMs) : IO RunOutcome := do
  let bound := if timeoutMs == 0 then pollStepMs else timeoutMs
  let spawned ← (IO.Process.spawn {
    cmd := command, args := args,
    stdin := .null, stdout := .piped, stderr := .piped }).toBaseIO
  match spawned with
  | .error error =>
      -- Not "the program failed": the program was never entered. Everything
      -- that reaches here — no such file, not executable, a directory on PATH
      -- under that name — is a statement about the machine rather than about
      -- what was being checked.
      return .unavailable command (toString error)
  | .ok child =>
      -- Before the wait, and on tasks: see the header. The reads are started
      -- here so a child that fills a pipe keeps moving while this thread polls.
      let outTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
      let errTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
      let mut code? : Option UInt32 := none
      for _ in [0 : bound / pollStepMs + 1] do
        code? ← child.tryWait
        if code?.isSome then break
        IO.sleep (UInt32.ofNat pollStepMs)
      match code? with
      | some exitCode =>
          -- The child has exited, but the pipes are not necessarily closed: a
          -- grandchild that inherited them keeps `readToEnd` waiting, and a
          -- bound that covered only the wait would leave this blocked forever
          -- in a release job whose own timeout is then the only thing that
          -- stops it. The reads get the same bound as the run.
          let mut drained := false
          for _ in [0 : bound / pollStepMs + 1] do
            if (← IO.hasFinished outTask) && (← IO.hasFinished errTask) then
              drained := true
              break
            IO.sleep (UInt32.ofNat pollStepMs)
          if !drained then
            return .timedOut command bound
          -- A stream that could not be read is not an empty stream. Reading it
          -- as one would turn a broken pipe into a digest tool that printed
          -- nothing, which is a different refusal with a different remedy.
          match outTask.get, errTask.get with
          | .ok stdout, .ok stderr =>
              let output : ProcessOutput := { exitCode, stdout, stderr }
              if looksUnexecutable output then
                return .unavailable command output.stderr.trimAscii.toString
              else return .completed output
          | .error error, _ | _, .error error =>
              return .unavailable command
                s!"it ran, but its output could not be read ({error})"
      | none =>
          child.kill
          return .timedOut command bound

/-- What to tell whoever has to fix a run that produced no answer.

    One wording for each case, here rather than at each call site: these are the
    two ways every external tool in this pipeline can fail, and a reader who saw
    a different sentence for the same condition in two commands would look for
    two problems. The caller adds what it was trying to establish; this says
    what happened to the program. -/
def RunOutcome.failureMessage : RunOutcome → Option String
  | .completed _ => none
  | .unavailable command detail =>
      some s!"'{command}' could not be run ({detail}). It is not on PATH, or it is there and not executable. This check is mandatory and cannot be skipped, so a tool that is not there is a refusal rather than a check that quietly does not happen — install it, or run this where it is installed."
  | .timedOut command afterMs =>
      some s!"'{command}' did not finish within {afterMs}ms and was killed. A tool that is present and does not return has established nothing, which is not the same as having found nothing; find out why it hung rather than raising the bound to cover it."

/-- The output of a run that both happened and succeeded, or a message saying
    which of the three ways it did not.

    Most callers want exactly this, and writing it once is what stops the
    non-zero-status case from being the one a caller forgets: there is no way to
    reach a `ProcessOutput` through this function without the status having been
    checked. A caller that genuinely needs to branch on a particular non-zero
    status — a `gh` call where "not found" is an answer — matches `run` directly
    and says so. -/
def succeeded (command : String) (args : Array String)
    (timeoutMs : Nat := defaultTimeoutMs) : IO (Except String ProcessOutput) := do
  let outcome ← run command args timeoutMs
  match outcome, outcome.failureMessage with
  | _, some message => return .error message
  | .completed output, none =>
      if output.succeeded then return .ok output
      else
        let detail := if output.stderr.trimAscii.isEmpty then output.stdout else output.stderr
        return .error
          s!"'{command}' exited {output.exitCode}: {detail.trimAscii.toString}"
  -- `failureMessage` is `none` only on `completed`, so this is unreachable for
  -- any value `run` returns. It is a refusal rather than a `panic!` because
  -- this executable's contract is that every path ends in a decision, and
  -- "the impossible happened" is a refusal like any other.
  | _, none => return .error s!"'{command}': the run produced neither an outcome nor a reason."

end Release
