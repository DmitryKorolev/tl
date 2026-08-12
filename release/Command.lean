/-
What a `tlrelease` subcommand is.

Its own module because the dependency runs both ways otherwise: `release/Cli.lean`
assembles the table from the modules that own each decision, and each of those
modules needs this type to describe what it contributes. Keeping the type here
and the table there lets a new decision be a new module plus one name in the
table, with nothing importing backwards.
-/

namespace Release

/-- One subcommand: how it is invoked, what it decides, and the process exit
    status it produces.

    `run` returns the status rather than throwing, because every caller is a
    release step reading `$?`. The three statuses are fixed across the tool:
    `0` the decision was made and it was yes, `1` a refusal — the decision was
    made and it was no, `2` a usage error — no decision was made at all. The
    third exists so that "you invoked me wrongly" can never be mistaken for
    "I checked, and it is fine", which is the whole failure this executable
    was written to remove. -/
structure Command where
  name : String
  arguments : String
  summary : String
  run : List String → IO UInt32

/-- Read a file, with the failure as a value rather than an exception.

    Every read in this tool goes through here so that "could not read it" is a
    refusal carrying the path, and never an unhandled exception or — worse —
    an empty string that the next step treats as content. The shell's
    equivalents did the latter routinely: `$(cat missing 2>/dev/null)` is the
    empty string and a zero status. -/
def readTextFile (path : String) : IO (Except String String) := do
  try
    return .ok (← IO.FS.readFile path)
  catch error =>
    return .error s!"could not read {path}: {error}"

/-- Write a file, with a failed write as a refusal rather than an exception and
    without leaving a partial file where a complete one had been.

    Written beside the target and renamed over it: `rename` within a directory
    is atomic, so a reader sees either the old contents or the new. Every caller
    here writes something another tool then trusts — the signing pin the shell
    verifier reads, and an SBOM that is hashed into `SHA256SUMS` and signed — and
    a truncated write leaves behind something that still parses as a file, which
    the next reader has no way to tell from a complete one.

    An unreadable directory or a full disk is a refusal carrying the path, never
    an escaping backtrace.

    The staging path is derived from the target rather than randomised, so it is
    predictable, and a write through it would follow whatever is already there —
    a symbolic link pointing somewhere else, or another run's half-written file.
    An existing one is therefore refused rather than written through. What
    remains is the window between that check and the write, which this cannot
    close: Lean's `IO.FS` offers no exclusive, no-follow create, and `release/`
    has no access to the native shim. Both callers write into a directory the
    same process has just been given — a release job's workspace, or a checkout
    the operator owns — so the residue is a race an attacker who already has
    that directory would win more directly. -/
def writeFileAtomically (path : String) (contents : String) : IO (Except String Unit) := do
  let temporary := path ++ ".tmp"
  if ← System.FilePath.pathExists temporary then
    return .error s!"could not write {path}: {temporary} already exists. The new contents are staged there and renamed over the target, so writing through it would follow whatever it is — a link to somewhere else, or a half-written file another run left behind. Remove it once you know which, rather than letting this write decide."
  try
    IO.FS.writeFile temporary contents
    IO.FS.rename temporary path
    return .ok ()
  catch error =>
    try IO.FS.removeFile temporary catch _ => pure ()
    return .error s!"could not write {path}: {error}"

/-- Report a refusal and produce the refusal status. Every decision in this
    tool ends here or at `0`; there is no path that reports a problem and then
    exits successfully anyway. -/
def refuse (message : String) : IO UInt32 := do
  IO.eprintln message
  return 1

/-- Report a usage error. Distinct from `refuse` because no decision was made:
    a caller must not be able to read "you invoked me wrongly" as "I checked,
    and it is fine". -/
def misuse (message : String) : IO UInt32 := do
  IO.eprintln message
  return 2

end Release
