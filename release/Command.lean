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

/-! ## A decision, as a monad

Every command has the same shape: read some of the world, refuse on the first
thing that is wrong, and otherwise say what it established. Written as nested
`match ← …` that shape becomes a staircase eight levels deep, and the depth is
not a readability complaint — it is where a branch gets forgotten, because the
`.error` arms are far from each other and from the top.

`Decision` is `Except String` over `IO`, so a refusal short-circuits the rest
and each step reads as one line. The two lifts are named rather than left to
instance resolution so that it is visible at each step whether it touches the
world: `ofExcept` is a pure check, `ofIO` is a read that can fail. -/

/-- A step that can refuse, carrying the message a refusal would print. -/
abbrev Decision := ExceptT String IO

/-- A pure check, as a step. -/
def ofExcept (result : Except String α) : Decision α := ExceptT.mk (pure result)

/-- A read of the world that can refuse, as a step. -/
def ofIO (action : IO (Except String α)) : Decision α := ExceptT.mk action

/-- Refuse here, with this message. -/
def decline (message : String) : Decision α := ofExcept (.error message)

/-- Read a file and parse it, as one step.

    Every parser in this tool takes the document's path first, so that a refusal
    names the file rather than describing a shape. Passing the path once, here,
    is what stops a message from naming the file a *different* read opened. -/
def readParsed (path : String) (parse : String → String → Except String α) :
    Decision α := do
  let text ← ofIO (readTextFile path)
  ofExcept (parse path text)

/-- Run a decision as a subcommand.

    The success value is what the command tells the operator it established,
    which is a required argument rather than an optional flourish: a release
    step that prints nothing on success gives a reader of a pipeline log no way
    to tell it from a step that was skipped.

    Every message, either way, is prefixed with the command's own name. A
    release log interleaves the output of a dozen tools and an unattributed
    sentence sends the reader to the wrong one. -/
def decide (name : String) (action : Decision String) : IO UInt32 := do
  match ← action.run with
  | .error message => refuse s!"{name}: {message}"
  | .ok established =>
      IO.println s!"{name}: {established}"
      return 0

/-! ## Named options

Commands that carry more than three or four values take them as `--name value`
rather than positionally, because a release step is read far more often than it
is written and `tlrelease build-metadata x64 abc123 supported ubuntu-latest …`
says nothing about which is which.

Named options bring their own way to fail silently, and each is closed here
rather than at the call sites:

- **An option whose value is missing** takes the next word. Written naively,
  `--commit --tier supported` binds `commit` to `"--tier"`, and a commit that
  is not a commit is caught later while a *free-text* field would simply carry
  it. Anything beginning with `--` is refused as a value.
- **An option given twice** silently keeps one of them. Which one depends on
  whether the reader takes the first match or the last, and a run identity or a
  digest given twice means two callers disagree about it. Refused.
- **An option nobody declared** is accepted and ignored, so a typo (`--comit`)
  removes the value and the command runs with whatever default the reader
  substituted. Refused.

The declaration is the whole mechanism: a name that is not in it cannot be read
and cannot be passed. -/

/-- One declared option: its name without the leading `--`, and whether it
    carries a value. -/
structure OptionSpec where
  name : String
  takesValue : Bool
  deriving Repr

/-- What an invocation supplied, after checking it against a declaration.

    Private constructor: the only way to one is `parseOptions`, so a value of
    this type has already been checked for unknown names, repeats and missing
    values. -/
structure Options where
  private mk ::
  named : List (String × String)
  present : List String
  positional : List String

private def declaredNames (specs : List OptionSpec) : String :=
  String.intercalate ", " (specs.map fun spec => "--" ++ spec.name)

/-- The accumulating half of `parseOptions`.

    Written as recursion over the remaining words rather than as a loop with
    mutable state, because one branch consumes *two* words and the other one,
    and a loop that advances by a variable amount is the shape in which an
    off-by-one hides. Each list is built by prepending and reversed once at the
    end: appending inside the recursion would make parsing an argument list
    quadratic in its length. -/
private def collectOptions (specs : List OptionSpec) :
    (remaining : List String) → (afterSeparator : Bool) →
    (named : List (String × String)) → (present : List String) →
    (positional : List String) → Except String Options
  | [], _, named, present, positional =>
      .ok ⟨named.reverse, present.reverse, positional.reverse⟩
  | word :: rest, true, named, present, positional =>
      collectOptions specs rest true named present (word :: positional)
  | word :: rest, false, named, present, positional =>
      if word == "--" then
        collectOptions specs rest true named present positional
      else if !word.startsWith "--" then
        collectOptions specs rest false named present (word :: positional)
      else
        let name := (word.drop 2).toString
        match specs.find? (·.name == name) with
        | none =>
            .error s!"'{word}' is not an option this command takes. It takes {declaredNames specs}. An option nobody declared would otherwise be accepted and ignored, so a typo would remove the value and leave the command running on whatever stood in for it."
        | some spec =>
            if present.contains name then
              .error s!"'{word}' was given more than once. Two values for one option means two callers disagree about it, and taking either one would make the answer depend on argument order."
            else if !spec.takesValue then
              collectOptions specs rest false named (name :: present) positional
            else
              match rest with
              | [] =>
                  .error s!"'{word}' takes a value and was given none — it is the last argument, so there is nothing it could have taken."
              | value :: afterValue =>
                  if value.startsWith "--" then
                    .error s!"'{word}' takes a value and the next argument is '{value}', which is another option. Bound to it, the option would carry the name of the next one as its value — which a free-text field would go on to record as though it were the thing asked for."
                  else
                    collectOptions specs afterValue false ((name, value) :: named)
                      (name :: present) positional
  termination_by remaining => remaining.length

/-- Split `args` against a declaration. Everything that is not an option, and
    everything after a bare `--`, is positional. -/
def parseOptions (specs : List OptionSpec) (args : List String) :
    Except String Options :=
  collectOptions specs args false [] [] []

/-- A declared option's value, or a usage message naming it.

    Every reader of a required option goes through here, so "the caller did not
    pass it" is a usage error rather than an empty string that reaches a
    comparison and matches nothing. -/
def Options.required (options : Options) (name : String) : Except String String :=
  match options.named.find? (·.1 == name) with
  | some (_, value) => .ok value
  | none => .error s!"--{name} is required and was not given."

/-- A declared option's value, when the command has something sensible to do
    without it. `none` is a stated absence: nothing here substitutes a default
    that a later comparison would silently satisfy. -/
def Options.value? (options : Options) (name : String) : Option String :=
  (options.named.find? (·.1 == name)).map (·.2)

/-- A declared option's value, or the empty string.

    For the descriptive fields only — the ones recorded for a human and read by
    no verdict. Named `describing` rather than `valueD` so that using it where a
    decision is made reads wrong. -/
def Options.describing (options : Options) (name : String) : String :=
  (options.value? name).getD ""

/-- Whether a declared valueless option was given. -/
def Options.given (options : Options) (name : String) : Bool :=
  options.present.contains name

end Release
