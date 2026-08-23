/-
The v0.1 dependency boundary: no path the GitHub-only release reaches may
invoke python, python3, ruby, brew, node or npm.

Why it is a gate rather than a rule. The boundary is a claim about a *set of
files* — the ones an operator's release actually runs — and that set changes
whenever a script learns to call another one. Reviewed by eye, it holds until
someone adds one line to a script two levels down from the installer. The
inventory below is the claim, this scan is what keeps it true, and the two
failure modes it exists to prevent are equally quiet: an interpreter that is
present on the runner today and absent on the operator's machine tomorrow, and a
release that stops for a runtime it deliberately does not publish through.

Enforced twice, deliberately. This arm is lexical: it reads the reachable files
and refuses on an invocation in command position, and on one of the six written
as a path anywhere on a line. The second arm is
`scripts/check-release-runtimes.sh`, which runs the release profile, the
installer and the verifier with all six commands shimmed to fail on PATH.

What each arm sees is narrower than "says" and "executes", and the difference is
where a bypass lived. A PATH shim intercepts a command *resolved through PATH*;
it cannot shadow `/usr/bin/python3`, so an absolute path is invisible to it
however it is spelled. This arm cannot see a command name that is not a literal
word — `"$tool" publish`, or a name inside the string `sh -c` runs. Compose
those two and there is a shape neither arm covered: an absolute path held in a
variable. That is why paths are read wherever they are written rather than only
in command position, and why a backslash escape is a lexer concern rather than a
curiosity — `/usr/bin/pyt\hon3` executes, and matched neither the six nor a shim.

The residual, stated rather than implied: an interpreter path *assembled* at
runtime — pieced together from fragments, or read out of a file — is a literal
word to nobody and resolves through PATH for nobody, so neither arm sees it. A
runtime with no interpreter installed is what closes that by construction, and
it is tracked as its own task rather than described here as covered.

Deferred channels are excluded by name, never by directory. npm and Homebrew
publish through their own runtimes by nature, and their machinery keeps running
on every commit (ADR-0006) — but it is not on the release path while
release/plan.json defers them, and the exclusion says which file, for which
channel, rather than exempting a directory that would go on absorbing new
scripts nobody looked at.
-/
import release.Command
import release.Model

namespace Release

/-- The commands the v0.1 release path may not invoke.

    `python` and `python3` are separate entries because they are separate
    commands: a boundary written as one of them is a boundary the other walks
    through. -/
def forbiddenCommands : List String :=
  ["python", "python3", "ruby", "brew", "node", "npm"]

inductive SourceKind where
  /-- Read as shell: `#` outside quotes begins a comment. -/
  | shell
  /-- Read as a GitHub workflow: `#` comments too, and jobs can be excluded by
      name, which is how a deferred channel's publish job leaves the scan. -/
  | workflow
  deriving DecidableEq, Repr

/-- One place a v0.1 release begins. Each is entered by something outside this
    repository — a tag push, a piped `curl`, an operator following VERIFYING.md,
    or a CI job — so the set cannot be derived from the code and is stated. -/
structure EntryPoint where
  path : String
  kind : SourceKind
  /-- What enters here. Part of the refusal, because "this file is on the
      release path" is the half of the message a reader needs first. -/
  entered : String
  deriving Repr

def entryPoints : List EntryPoint :=
  [{ path := "install.sh", kind := .shell,
     entered := "piped into a shell from curl by a user installing tl" },
   { path := "scripts/verify-release-artifacts.sh", kind := .shell,
     entered := "run by a user following VERIFYING.md, and by the release workflow before it publishes" },
   { path := "scripts/check-release-policy.sh", kind := .shell,
     entered := "the release profile of the policy, which the release workflow's gates job runs on the tagged commit" },
   { path := ".github/workflows/release.yml", kind := .workflow,
     entered := "the workflow a SemVer tag push starts" }]

/-- A file the scan does not enter, and why it is not on the release path.

    Naming the channel is the point: when `release/plan.json` enables one, its
    rows come off this list, its scripts join the scan, and the interpreter
    reads behind them have to move into this executable first. -/
structure DeferredPath where
  path : String
  /-- The channel that owns the runtime this file needs. Typed, so an exclusion
      names a channel `release/plan.json` has an opinion about rather than a
      word; the check below refuses if that channel is no longer deferred. -/
  channels : List Channel
  why : String
  deriving Repr

def deferredPaths : List DeferredPath :=
  [{ path := "scripts/check-channel-policy.sh", channels := [.npm, .homebrew],
     why := "the deferred channels' own gates; the ci profile runs the Homebrew one on every commit and the npm one runs from --npm-only where the tool is built, and the release profile has neither" },
   { path := "npm/tl/bin/tl", channels := [.npm],
     why := "the launcher inside the npm package, which npm execs" }]

/-- A workflow job the scan does not read, and why it does not run.

    A deferred channel's publish job is gated on `release/plan.json` through the
    `gates` job's outputs, so it does not run for a release that defers the
    channel — it is not skipped, it has no job. Excluded here by name for the
    same reason its file is: a *new* publish job is not covered by an exclusion
    written for an old one. -/
structure DeferredJob where
  job : String
  channel : Channel
  deriving Repr

def deferredJobs : List DeferredJob :=
  [{ job := "publish-npm", channel := .npm },
   { job := "publish-homebrew", channel := .homebrew }]

/-- Every exclusion this run is entitled to, checked against the plan that
    decides which channels publish.

    An exclusion says "this file is not on the release path *because* its channel
    is deferred", and until now nothing connected that clause to the switch it
    depends on. Enabling npm puts its scripts and its publish job back on the
    release path, and the scan would have gone on removing them by name — a gate
    reporting a clean path it no longer describes.

    The two directions are not symmetric, deliberately. A deferred channel whose
    file is excluded is the intended state. An *enabled* channel with an
    exclusion still standing is a refusal here, naming the file and the edit,
    because that is the moment the boundary silently stops meaning anything. -/
def staleExclusions (plan : ReleasePlan) : List String :=
  let livePaths := deferredPaths.filterMap fun deferred =>
    let live := deferred.channels.filter (plan.enabled ·)
    if live.isEmpty then none
    else some s!"  {deferred.path} is excluded for {String.intercalate ", " (live.map (·.wire))}, which this release publishes through"
  let liveJobs := deferredJobs.filterMap fun deferred =>
    if plan.enabled deferred.channel then
      some s!"  the '{deferred.job}' job is excluded for {deferred.channel.wire}, which this release publishes through"
    else none
  livePaths ++ liveJobs

/-! ## Reading one line

Comments first, because every one of these files explains itself at length and
the words `npm`, `brew` and `ruby` appear throughout that prose. A scan that
counted those would be answered by rewording a comment, which teaches exactly
the wrong lesson. -/

/-- The code half of one line: everything before an unquoted `#` that begins a
    word. `${x#y}` and `foo#bar` are not comments, and a `#` inside quotes is
    text — both matter here, since these scripts contain digests, format strings
    and `printf` patterns.

    A `#!` line never reaches here: `readLine` recognises it first and hands it
    to the parser its own syntax has. This function is about shell, and a shebang
    is not shell. -/
def codeOf (line : String) : String :=
  let rec walk : List Char → Bool → Bool → Bool → List Char → List Char
    | [], _, _, _, acc => acc.reverse
    | c :: rest, single, double, afterSpace, acc =>
      if c == '\'' && !double then walk rest (!single) double false (c :: acc)
      else if c == '"' && !single then walk rest single (!double) false (c :: acc)
      else if c == '#' && !single && !double && afterSpace then acc.reverse
      else walk rest single double (c == ' ' || c == '\t') (c :: acc)
  String.ofList (walk line.toList false false true [])

/-- The program a command word names.

    A release step can spell an interpreter as a path — `/usr/bin/python3`,
    `$HOME/.local/bin/npm`, `./tool/node` — and comparing the whole word would
    read those as different commands. That spelling is the one *neither* arm
    would otherwise catch: PATH shims cannot shadow an absolute path either, so
    a lexical check on the last segment is the only place it is visible.
    `./scripts/npm-pack.sh` stays a script, because its last segment is. -/
def commandName (word : String) : String := (word.splitOn "/").getLast!

/-- One command word, as the file writes it and as this scan identifies it.

    Both halves are kept because both are read. The basename is what a rule about
    `python3` can compare against; the written form is what an operator needs in
    order to find the thing, and `/usr/bin/python3` and `python3` are the same
    finding while being very different lines to go and look at.

    Every word this scan judges is normalized through `identify` — the words in
    command position on a shell line, and the interpreter a `#!` line names — so
    a spelling understood in one of those places cannot be misread in the
    other. That is not a tidiness argument: the two paths *had* diverged, and a
    `#!` followed by a space is what walked through the gap. -/
structure CommandIdentity where
  written : String
  basename : String
  deriving Repr, DecidableEq

/-- The one normalization. -/
def identify (word : String) : CommandIdentity :=
  { written := word, basename := commandName word }

/-- Words that hold the command position open rather than taking it: the shell
    keywords a command can follow, and the wrappers that run their argument.
    Matched on the program name, so `/usr/bin/env python3` reaches `python3`. -/
private def keepsCommandPosition (word : String) : Bool :=
  ["if", "then", "elif", "else", "do", "while", "until", "!", "&&", "||",
    "exec", "env", "sudo", "command", "time", "nohup", "xargs", "builtin"].contains
      (commandName word)
    || word.startsWith "-"
    -- `VAR=value cmd …`: an assignment prefix, not a command. `=` before any
    -- `/` distinguishes it from a path that happens to contain one.
    || (word.takeWhile (· != '/') |>.any (· == '='))

private structure Lexer where
  single : Bool := false
  double : Bool := false
  atCommand : Bool := true
  token : List Char := []
  found : List String := []
  /-- Every word on the line, command position or not. A path is worth reading
      wherever it is written: `tool=/usr/bin/python3` puts an interpreter on the
      release path in a word no notion of command position covers. -/
  words : List String := []

private def Lexer.endToken (state : Lexer) (separator : Bool) : Lexer :=
  let word := String.ofList state.token.reverse
  let atCommand :=
    if word.isEmpty then state.atCommand || separator
    else if state.atCommand && keepsCommandPosition word then true
    else separator
  { state with
      token := []
      atCommand
      words := if word.isEmpty then state.words else word :: state.words
      found := if !word.isEmpty && state.atCommand && !keepsCommandPosition word
        then word :: state.found else state.found }

/-- One line of shell, lexed into words: those in command position, and all of
    them.

    Quote characters are dropped rather than kept in the token, so `'npm' i`
    reads as an invocation of `npm`; a word is only ever compared whole, so
    `npm-pack.sh` and `nodes` are not.

    A backslash escapes the character after it, everywhere but inside single
    quotes. That is the shell's own rule and it had to be the lexer's: `pyt\hon3`
    is one word naming `python3`, the shell runs it, and a lexer that kept the
    backslash compared `pyt\hon3` against the six and matched nothing. Written
    as `/usr/bin/pyt\hon3` it was invisible to the PATH-shim arm as well, because
    a shim cannot shadow an absolute path.

    What this still cannot see is a command name that is not a literal word —
    `"$tool" publish`, or `npm` inside the string `sh -c` runs. The PATH-shim arm
    sees those when the name resolves through PATH; when it does not, the
    remaining case is the one `words` exists for, and past that it is the
    residual recorded at the top of this file. -/
private def lexLine (line : String) : Lexer :=
  let rec walk : List Char → Lexer → Lexer
    | [], state => state.endToken false
    -- The escape, before anything reads the character it protects. Inside single
    -- quotes a backslash is an ordinary character and the quote it precedes
    -- still closes, so there the next character is left to be read again.
    | '\\' :: next :: rest, state =>
      if state.single then walk (next :: rest) { state with token := '\\' :: state.token }
      else walk rest { state with token := next :: state.token }
    -- A line ending in a backslash is continued, and the marker is not a word.
    | ['\\'], state => state.endToken false
    | c :: rest, state =>
      if c == '\'' && !state.double then walk rest { state with single := !state.single }
      else if c == '"' && !state.single then walk rest { state with double := !state.double }
      else if state.single || state.double then
        walk rest { state with token := c :: state.token }
      -- `\r` is whitespace here: a file with CRLF endings otherwise leaves the
      -- carriage return glued to the last token on the line, so a step whose
      -- whole line is one command — `npm\r` — would be read as a command named
      -- `npm\r` and matched against nothing.
      else if c == ' ' || c == '\t' || c == '\r' then walk rest (state.endToken false)
      else if c == ';' || c == '|' || c == '&' || c == '(' || c == ')'
          || c == '{' || c == '}' || c == '`' || c == '<' || c == '>' then
        walk rest (state.endToken true)
      else walk rest { state with token := c :: state.token }
  walk line.toList {}

/-- The words in command position on one line of shell. -/
def commandWords (line : String) : List String := (lexLine line).found.reverse

/-- Every word on one line of shell, whatever position it is in. -/
def lineWords (line : String) : List String := (lexLine line).words.reverse

/-! ### The interpreter a file runs under

A `#!` line is the one line in these files whose meaning the kernel decides
rather than the shell, and it does not obey the shell's spelling rules. It is
also the line with the most reach: it chooses the interpreter for everything
below it, so a helper written in one of the six is a Python or Ruby dependency
on the release path no matter what its body says.

Its syntax admits whitespace after the marker — `#! /usr/bin/python3` is
executed by every platform this project ships to — and that is exactly what the
shell lexer cannot read. Given the whole line, it takes `#!` for the command and
the interpreter path for an argument, finds no invocation, and returns the same
answer a clean line returns. The repair is not another special case in the
lexer: it is parsing the line with the syntax it actually has, and refusing when
that parser cannot. -/

/-- The characters an interpreter path is written with. Deliberately narrow: a
    `#!` line is taken literally by the kernel, so anything outside this is not
    a path that will be executed, and this scan says so rather than guessing. -/
private def interpreterPathChar (c : Char) : Bool :=
  c.isAlphanum || c == '.' || c == '/' || c == '_' || c == '-' || c == '+' || c == '~'

/-- The command line a `#!` names — everything after the marker and the optional
    whitespace behind it — or why this scan will not read it.

    Refusing is the point of the `Except`. Both malformed shapes are cases where
    answering "no interpreter" would be indistinguishable from a file that runs
    under `/bin/sh`, and the second — a `#!` carrying something that is not a
    literal word — is what a script generated by another script looks like when
    its substitution did not happen.

    Every word is held to that, not only the first. The kernel expands nothing on
    this line, so `#!/usr/bin/env $INTERPRETER` names a program called
    `$INTERPRETER`; reading it as a clean `env` invocation would be this scan
    inventing a meaning the line does not have. -/
def shebangBody (line : String) : Except String String :=
  let body := (line.drop 2).trimAscii.toString
  if body.isEmpty then
    .error "the line begins with #! and names no interpreter"
  else
    let words := (body.splitOn " ").flatMap (·.splitOn "\t") |>.filter (!·.isEmpty)
    match words.find? (fun word => !word.all interpreterPathChar) with
    | some word =>
        .error s!"'{word}' on the #! line is not a literal word, and the kernel expands nothing there"
    | none => .ok body

/-- The shell a workflow line runs, if it runs any.

    A step written on one line — `- run: brew install coreutils` — puts the
    command after a YAML key, and a shell lexer reads that key as the command and
    everything after it as arguments. Stripping it is what makes those steps
    scannable at all.

    `run:` is the only key stripped, because it is the only one whose value is
    shell. `name:` and `if:` carry prose and expressions, and stripping those
    would put an English sentence in command position — `- name: npm publish the
    packages` would become a finding about a step title. A `run: |` block needs
    nothing here: its lines are already shell, one per line. -/
def workflowShell (line : String) : String :=
  let body := line.trimAsciiStart.toString
  let body := if body.startsWith "- " then (body.drop 2).toString else body
  if body.startsWith "run:" then (body.drop 4).toString else line

/-- How a command reaches the release path: as a word the line runs, or as the
    interpreter the whole file runs under. Kept because the refusals read
    differently — "invokes python3" and "runs under python3" send an operator to
    different repairs. -/
inductive InvocationSite where
  | commandPosition
  | shebang
  /-- Written as a path somewhere on the line, in no particular position.

      The class neither arm otherwise covers. A PATH shim cannot shadow
      `/usr/bin/python3`, and `tool=/usr/bin/python3` followed by `"$tool"` puts
      the command position out of a lexer's reach — so the release path can
      reach an interpreter with nothing to see it. What is still visible is the
      path itself, wherever it is written, and a first-party release script has
      no business naming one. -/
  | writtenAsPath
  deriving Repr, DecidableEq

/-- What one line was read as.

    `unsupported` is the constructor that did not exist, and its absence was a
    defect rather than a simplification. A scanner that meets a line it cannot
    parse has two ways to answer: report no invocation — which is the same answer
    a clean line gives, and therefore a silent pass — or say that it could not
    read it. Only the second is evidence. Every omission in the parsers above is
    now a refusal naming the line rather than a verdict about a file this gate
    did not entirely understand.

    What is deliberately *not* `unsupported`: a command name that is not a
    literal word — `"$tool" publish`, or a name inside the string `sh -c` runs.
    Those are beyond a lexical scan, and the PATH-shim arm sees them whenever the
    name resolves through PATH; where it does not, the path form is caught by
    `writtenAsPath` above.

    Refusing on them instead was considered and measured. The lexer's notion of
    command position is necessarily broad — a flag keeps the position open, so
    the *value* of `--bundle "$bundle"` lands in it, as does a redirect target —
    and 236 words on the current release path sit in that position with a `$` in
    them. A rule refusing those would refuse this repository's own release,
    every edit would move the set, and the exception list would be the files
    themselves: a gate nobody can maintain, which is a gate that gets disabled.
    The distinction that remains is between a shape this scan is *supposed* to
    read and cannot, and a shape no lexical scan can read. -/
inductive ScanLine where
  | understood (reached : List (InvocationSite × CommandIdentity))
  | unsupported (reason : String)
  deriving Repr

/-- What one piece of shell reaches: the words in command position, and then
    every *other* word that is written as a path.

    The second half is not a second guess at command position. It is the reading
    that survives a command position no lexer can see: a path is runnable from a
    variable, from a string another shell evaluates, or from a line this scan
    read as an argument, and none of those is shadowed by a PATH shim either.
    A word already reported in command position is not reported twice. -/
def reachedBy (site : InvocationSite) (code : String) :
    List (InvocationSite × CommandIdentity) :=
  -- Lexed once, read twice: the two views are the same pass over the line.
  let lexed := lexLine code
  let commands := lexed.found.reverse.map identify
  let paths := lexed.words.reverse.filterMap fun word =>
    let identity := identify word
    if (word.splitOn "/").length > 1 && !commands.contains identity then
      some (InvocationSite.writtenAsPath, identity)
    else none
  commands.map (fun identity => (site, identity)) ++ paths

/-- One line, read as what it is.

    The shebang test comes first and is not conditioned on the line number: `#!`
    at the start of a line inside a heredoc is the first line of the script that
    heredoc writes, and a release step that writes a Python helper and runs it is
    the same dependency as one that invokes Python directly.

    Where "the start" is depends on the file. A shell line is taken as written,
    because the kernel honours a `#!` only at the first byte and a heredoc that
    indents its content produces a file that does not have one there. A workflow
    line is trimmed first: YAML strips a block scalar's common indentation, so
    the `#!` that is ten spaces in here is at the first byte of the script the
    step actually runs. The cost of trimming is that a YAML comment beginning
    `#!` reads as a shebang — a loud false finding rather than a quiet false
    pass, which is the direction this gate is allowed to be wrong in. -/
def readLine (kind : SourceKind) (line : String) : ScanLine :=
  let bare := match kind with
    | .shell => line
    | .workflow => line.trimAsciiStart.toString
  if bare.startsWith "#!" then
    match shebangBody bare with
    | .error reason => .unsupported reason
    | .ok body => .understood (reachedBy .shebang body)
  else
    let code := match kind with
      | .shell => codeOf line
      | .workflow => workflowShell (codeOf line)
    .understood (reachedBy .commandPosition code)

/-- Line number, the command, how it got there, and the line it is on. The line
    travels with the finding because the fix is almost never "delete this
    word". -/
structure Invocation where
  line : Nat
  command : CommandIdentity
  site : InvocationSite
  text : String
  deriving Repr, DecidableEq

/-- A line this scan is shaped to read and would not guess at. -/
structure UnsupportedLine where
  line : Nat
  reason : String
  text : String
  deriving Repr, DecidableEq

/-- What one file's text amounts to: the forbidden commands it reaches, and the
    lines that were not read. Both halves reach the verdict; a scan that produced
    only the first would report a clean file it had not finished reading. -/
structure TextScan where
  invocations : List Invocation
  unsupported : List UnsupportedLine
  deriving Repr

/-- Read every line of one file. The line is reported as written, whatever had to
    be stripped from it to find the command. -/
def scanLines (kind : SourceKind) (text : String) : TextScan :=
  let read := (text.splitOn "\n").zipIdx 1 |>.map fun (line, number) =>
    (number, line.trimAscii.toString, readLine kind line)
  { invocations := read.flatMap fun (number, text, scanned) =>
      match scanned with
      | .understood reached =>
        reached.filterMap fun (site, command) =>
          if forbiddenCommands.contains command.basename then
            some { line := number, command, site, text }
          else none
      | .unsupported _ => []
    unsupported := read.filterMap fun (number, text, scanned) =>
      match scanned with
      | .understood _ => none
      | .unsupported reason => some { line := number, reason, text } }

/-! ## Reachability

A first-party script names the scripts it runs, so the reachable set is the
transitive closure of those references. Read from the code half of each line for
the same reason the invocations are: every one of these files discusses the
scripts it does *not* run. -/

private def pathChar (c : Char) : Bool :=
  c.isAlphanum || c == '.' || c == '/' || c == '_' || c == '-'

/-- Where first-party scripts live, as written in a reference. A path outside
    these is a fixture, a temporary directory or a downloaded artifact — not a
    file in this repository, and not something this scan can read. -/
private def firstPartyPrefixes : List String := ["scripts/", "npm/", ".github/"]

/-- Repository-root scripts, which have no directory to recognise them by. -/
private def rootScripts : List String := ["install.sh"]

/-- The repository path a reference token names, if it names one.

    Scripts write each other's paths through a variable —
    `"$repo_root/scripts/lib/release-common.sh"` — and `$` is not part of a path
    token, so what arrives here is a tail with an unknown head. Taking the path
    from its first-party directory is what makes that the same file as the plain
    `./scripts/lib/release-common.sh` written elsewhere. A tail that begins below
    one of those directories, as `"$script_dir/lib/x.sh"` does, carries nothing
    to anchor it and is not resolved. A token with a directory this does not
    recognise is deliberately not a reference: it is a path in a temporary
    fixture, and treating it as one would make this gate refuse because a file it
    invented is missing. -/
def normalizeReference (token : String) : Option String :=
  let token := if token.startsWith "./" then (token.drop 2).toString else token
  match firstPartyPrefixes.find? (fun prefixed => (token.splitOn prefixed).length > 1) with
  | some prefixed =>
    match (token.splitOn prefixed) with
    | _ :: rest => some (prefixed ++ String.intercalate prefixed rest)
    | [] => none
  | none =>
    let basename := (token.splitOn "/").getLast!
    if rootScripts.contains basename then some basename
    else if (token.splitOn "/").length > 1 then none
    else none

/-- Every first-party script one file names. A token is a reference when it ends
    in `.sh` with a non-empty stem, or is the npm launcher, which has no
    extension. -/
def referencedScripts (text : String) : List String :=
  let tokens := (text.splitOn "\n").flatMap fun line =>
    let code := codeOf line
    let rec split : List Char → List Char → List String → List String
      | [], current, acc =>
        if current.isEmpty then acc.reverse else (String.ofList current.reverse :: acc).reverse
      | c :: rest, current, acc =>
        if pathChar c then split rest (c :: current) acc
        else if current.isEmpty then split rest [] acc
        else split rest [] (String.ofList current.reverse :: acc)
    split code.toList [] []
  let scriptTokens := tokens.filter fun token =>
    (token.endsWith ".sh" && (token.splitOn "/").getLast!.length > 3)
      || token.endsWith "npm/tl/bin/tl"
  scriptTokens.filterMap normalizeReference |>.eraseDups

/-! ## Reading one workflow

Only the jobs that run. A workflow is scanned as a whole file except for the
jobs a deferred channel owns, which are removed by name — the `gates` job
publishes `release/plan.json`'s channel switches as outputs and each of those
jobs gates on its own, so for a release that defers the channel there is no job
to run. -/

/-- Whether a line opens a job: exactly two spaces, a name, a colon, nothing
    else. The workflow's own two-space indentation is what makes this
    unambiguous, and a `jobs:` key at column zero cannot match it. -/
def jobOpener? (line : String) : Option String :=
  if !(line.startsWith "  ") || line.startsWith "   " then none
  else
    let rest := (line.drop 2).trimAsciiEnd
    if !rest.endsWith ":" then none
    else
      let name := (rest.dropEnd 1).toString
      if name.isEmpty || !name.all (fun c => c.isAlphanum || c == '-' || c == '_') then none
      else some name

/-- A workflow with the deferred channels' jobs removed, ready to scan.
    Everything else is kept, including the lines outside every job — the
    triggers and the top-level environment run whatever publishes.

    A deferred job ends at the next job, or at any content that is not indented
    inside one. Without that second condition a deferred job at the end of the
    file would swallow whatever followed it, which is the direction that hides a
    finding rather than inventing one. -/
def workflowRunningText (text : String) : String :=
  let deferred := deferredJobs.map (·.job)
  let rec walk : List String → Bool → List String → List String
    | [], _, kept => kept.reverse
    | line :: rest, inDeferred, kept =>
      match jobOpener? line with
      | some name =>
        if deferred.contains name then walk rest true kept
        else walk rest false (line :: kept)
      | none =>
        let stillInside :=
          inDeferred && (line.trimAscii.isEmpty || line.startsWith "    " || line.startsWith "   -")
        if stillInside then walk rest true kept else walk rest false (line :: kept)
  String.intercalate "\n" (walk (text.splitOn "\n") false [])

/-! ## The scan -/

/-- One file the scan read, and what it found in it.

    The constructor is private, so a value of this type is evidence the scanner
    actually produced. That is not ceremony: the first version of this module
    was covered by rows that built a `ScannedFile` by hand, and one of them
    described a state the scanner could not reach — a file whose line count was
    zero — so the guard it exercised was unreachable in production and an empty
    entry point passed the real gate. A test can no longer describe a scan that
    did not happen. -/
structure ScannedFile where
  private mk ::
  path : String
  reachedFrom : String
  invocations : List Invocation
  /-- The lines the scan refused to guess at. Carried per file rather than
      counted across the run, because the refusal has to name one. -/
  unsupported : List UnsupportedLine
  /-- What the file contained, in bytes, rather than a count derived from it.
      The question this answers is "was there anything here to read at all",
      and a derived number invites a shape — no lines — that no file has. -/
  bytesRead : Nat
  deriving Repr

def scanText (kind : SourceKind) (text : String) : String :=
  match kind with
  | .shell => text
  | .workflow => workflowRunningText text

/-- The refusal lines for one file's findings.

    The written spelling is named when it differs from the command it resolves
    to. `python3` says which rule was broken and `/usr/bin/python3` says which
    word to go and change, and a finding that carried only the first sent the
    reader looking for a word the file does not contain. -/
def fileFindings (scanned : ScannedFile) : List String :=
  scanned.invocations.map fun invocation =>
    let how := match invocation.site with
      | .commandPosition => "invokes"
      | .shebang => "runs under"
      | .writtenAsPath => "names the path of"
    let named :=
      if invocation.command.written == invocation.command.basename then
        invocation.command.basename
      else s!"{invocation.command.basename}, written {invocation.command.written}"
    s!"  {scanned.path}:{invocation.line}: {how} {named} — {invocation.text}"

/-- The refusal lines for the lines one file did not yield to the scan. -/
def fileUnsupported (scanned : ScannedFile) : List String :=
  scanned.unsupported.map fun line =>
    s!"  {scanned.path}:{line.line}: {line.reason} — {line.text}"

/-- How many files one walk may read. The whole tracked shell surface several
    times over; reaching it means the closure is walking in circles, which is a
    defect here rather than a large repository. -/
def closureBound : Nat := 500

/-- What a walk of the closure came back with.

    Completion is a constructor rather than a convention. The bound exists so a
    walk cannot loop forever, and the first version returned the files it had
    read when it hit that bound — which reported a clean verdict over a *prefix*
    of the release path, the one answer this gate must never give. Only
    `complete` reaches the verdict now, so a walk that stopped early cannot be
    mistaken for one that finished. -/
inductive ClosureResult where
  | complete (files : List ScannedFile)
  | exhausted (pending : List String) (read : List ScannedFile)

/-- The verdict over a walk that finished. `exhausted` refuses here rather than
    at the walk, so the reason a release stopped is written in one place with
    every other reason it can stop. -/
def boundaryVerdict : ClosureResult → Except String String
  | .exhausted pending read =>
    .error s!"the reachability walk stopped at its bound of {closureBound} file(s) with {pending.length} still queued, having read {read.length}: {String.intercalate ", " (pending.take 5)}{if pending.length > 5 then ", …" else ""}. What it did not reach is unchecked, so this is a refusal rather than a shorter verdict. Either the closure is walking in circles — a defect in this gate — or the release path has outgrown the bound, and raising `closureBound` in release/Boundary.lean is the deliberate answer to the second."
  | .complete scanned =>
  let findings := scanned.flatMap fileFindings
  let unread := scanned.flatMap fileUnsupported
  let missedEntry := entryPoints.filterMap fun entry =>
    if scanned.any (·.path == entry.path) then none else some entry.path
  let empty := scanned.filter (·.bytesRead == 0) |>.map (·.path)
  if !missedEntry.isEmpty then
    -- By identity, not by count: a walk that read four files none of which was
    -- an entry point would satisfy a count.
    .error s!"did not read {String.intercalate ", " missedEntry}. An entry point this gate did not read is a release path it did not check."
  else if !empty.isEmpty then
    .error s!"read nothing from {String.intercalate ", " empty}. A file with no content produces no findings for the same reason a clean one does, so this is reported rather than counted as a pass — an entry point that was emptied, or a reference to a file that is a placeholder, is not a release path that was checked."
  else if findings.isEmpty && unread.isEmpty then
    -- The files are named, not counted. A closure that stopped following
    -- references still reports a plausible number, and the reader of a release
    -- log is the only one who can notice that the script they just added is not
    -- in the list.
    .ok s!"{scanned.length} file(s) reachable from {entryPoints.length} v0.1 entry point(s) invoke none of {String.intercalate ", " forbiddenCommands}, and every line of them was read: {String.intercalate ", " (scanned.map (·.path))}"
  else
    -- Both sections when both apply. A refusal that reported only the lines it
    -- could not read would hide the invocation it *did* find, and one that
    -- reported only the findings would let the unread lines through on the
    -- next run that happens to have no findings.
    let invocationSection :=
      if findings.isEmpty then [] else
        ["the v0.1 release path invokes a command it must not."] ++ findings
          ++ [s!"ADR-0026 keeps {String.intercalate ", " forbiddenCommands} off every path a release reaches: an operator's machine is not a GitHub runner, and a release must not stop for a runtime it does not publish through. Move the decision into tlrelease, or — if this belongs to a channel release/plan.json defers — move the file behind that channel's own script and name it in deferredPaths."]
    let unreadSection :=
      if unread.isEmpty then [] else
        ["the scan could not read a line it is shaped to read."] ++ unread
          ++ ["A line this gate cannot parse is not a clean line: whatever it names would go unreported, and a verdict over the rest of the file would read as a verdict over all of it. Either write the line in a form release/Boundary.lean states it can read, or teach it the spelling — and add the spelling to the corpus in Tests/ReleaseToolTests.lean, so the next one that is not understood fails here rather than passing."]
    .error (String.intercalate "\n" (invocationSection ++ unreadSection))

/-! ## The command -/

private def boundaryOptions : List OptionSpec :=
  [{ name := "root", takesValue := true }, { name := "plan", takesValue := true }]

private structure BoundaryArgs where
  root : String
  planPath : String

private def deferredNames : List String := deferredPaths.map (·.path)

/-- Walk the closure breadth-first, entry points first. `fuel` is the visited
    bound: every step either consumes a queued path or stops, and the queue only
    ever grows by paths not yet visited, so the file count bounds it. Running out
    of it produces `exhausted`, which the verdict refuses — the walk does not get
    to decide that what it managed to read is enough. -/
private def walkClosure (root : String) : Nat → List (String × String) → List String →
    List ScannedFile → Decision ClosureResult
  | 0, queue, _, scanned =>
    if queue.isEmpty then pure (.complete scanned)
    else pure (.exhausted (queue.map (·.1)) scanned)
  | _ + 1, [], _, scanned => pure (.complete scanned)
  | fuel + 1, (path, reachedFrom) :: queue, visited, scanned =>
    if visited.contains path || deferredNames.contains path then
      walkClosure root fuel queue visited scanned
    else do
      let entry := entryPoints.find? (·.path == path)
      let full := if root == "." then path else root ++ "/" ++ path
      let text ← ofIO (readTextFile full)
      let kind := entry.map (·.kind) |>.getD .shell
      let scanText := scanText kind text
      let scan := scanLines kind scanText
      let found : ScannedFile :=
        { path, reachedFrom, invocations := scan.invocations,
          unsupported := scan.unsupported,
          bytesRead := text.trimAscii.toString.length }
      let next := (referencedScripts scanText).filterMap fun reference =>
        if visited.contains reference || deferredNames.contains reference then none
        else some (reference, path)
      walkClosure root fuel (queue ++ next) (path :: visited) (scanned ++ [found])

private def boundaryDecision (args : BoundaryArgs) : Decision String := do
  let plan ← readParsed args.planPath ReleasePlan.parse
  -- Before the scan, not after: if an exclusion has gone stale the scan below
  -- is reading a smaller release path than the one this release publishes, and
  -- its verdict would be about the wrong set of files.
  match staleExclusions plan with
  | [] => pure ()
  | stale =>
      decline ("an exclusion no longer matches release/plan.json.\n"
        ++ String.intercalate "\n" stale
        ++ "\nA file or job is excluded from this scan because the channel that needs its runtime is deferred. Enabling that channel puts it back on the release path: take its row out of deferredPaths/deferredJobs in release/Boundary.lean, and move the interpreter reads behind it into tlrelease, in the change that enables the channel.")
  let queue := entryPoints.map fun entry => (entry.path, entry.entered)
  let result ← walkClosure args.root closureBound queue [] []
  ofExcept (boundaryVerdict result)

def boundaryCommand : Command :=
  optionCommand "dependency-boundary" "--root <checkout> --plan <plan.json>"
    "Refuse unless every script the v0.1 release path reaches is free of python, ruby, brew, node and npm."
    ["--root", ".", "--plan", "release/plan.json"]
    boundaryOptions
    (fun options => do
      return { root := ← options.required "root", planPath := ← options.required "plan" })
    boundaryDecision

def boundaryCommands : List Command := [boundaryCommand]

end Release
