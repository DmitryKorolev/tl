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
and refuses on an invocation in command position. It cannot see through
`sh -c "npm publish"`, through a command name held in a variable, or through a
tool a *dependency* shells out to. The second arm is
`scripts/check-release-runtimes.sh`, which runs the release profile, the
installer and the verifier with all six commands shimmed to fail on PATH — it
sees anything that actually executes, whatever it is spelled like, and sees
nothing about a branch this run did not take. Neither arm subsumes the other.

Deferred channels are excluded by name, never by directory. npm and Homebrew
publish through their own runtimes by nature, and their machinery keeps running
on every commit (ADR-0006) — but it is not on the release path while
release/plan.json defers them, and the exclusion says which file, for which
channel, rather than exempting a directory that would go on absorbing new
scripts nobody looked at.
-/
import release.Command

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
  channel : String
  why : String
  deriving Repr

def deferredPaths : List DeferredPath :=
  [{ path := "scripts/check-channel-policy.sh", channel := "npm, homebrew",
     why := "the deferred channels' own gates; the ci profile runs them on every commit and the release profile does not have them" },
   { path := "scripts/npm-pack.sh", channel := "npm",
     why := "stages the packages and drives npm pack/install over them" },
   { path := "scripts/npm-publish.sh", channel := "npm",
     why := "publishes the packages with npm" },
   { path := "scripts/npm-bootstrap.sh", channel := "npm",
     why := "the one-time manual npm bootstrap before the channel can authenticate" },
   { path := "npm/tl/bin/tl", channel := "npm",
     why := "the launcher inside the npm package, run by node" },
   { path := "scripts/gen-homebrew-formula.sh", channel := "homebrew",
     why := "generates Formula/tl.rb and parses it with ruby" },
   { path := "scripts/lib/channel-common.sh", channel := "npm, homebrew",
     why := "the release-data reads those four scripts share, which use python3" }]

/-- A workflow job the scan does not read, and why it does not run.

    A deferred channel's publish job is gated on `release/plan.json` through the
    `gates` job's outputs, so it does not run for a release that defers the
    channel — it is not skipped, it has no job. Excluded here by name for the
    same reason its file is: a *new* publish job is not covered by an exclusion
    written for an old one. -/
structure DeferredJob where
  job : String
  channel : String
  deriving Repr

def deferredJobs : List DeferredJob :=
  [{ job := "publish-npm", channel := "npm" },
   { job := "publish-homebrew", channel := "homebrew" }]

/-! ## Reading one line

Comments first, because every one of these files explains itself at length and
the words `npm`, `brew` and `ruby` appear throughout that prose. A scan that
counted those would be answered by rewording a comment, which teaches exactly
the wrong lesson. -/

/-- The code half of one line: everything before an unquoted `#` that begins a
    word. `${x#y}` and `foo#bar` are not comments, and a `#` inside quotes is
    text — both matter here, since these scripts contain digests, format strings
    and `printf` patterns. -/
def codeOf (line : String) : String :=
  let rec walk : List Char → Bool → Bool → Bool → List Char → List Char
    | [], _, _, _, acc => acc.reverse
    | c :: rest, single, double, afterSpace, acc =>
      if c == '\'' && !double then walk rest (!single) double false (c :: acc)
      else if c == '"' && !single then walk rest single (!double) false (c :: acc)
      else if c == '#' && !single && !double && afterSpace then acc.reverse
      else walk rest single double (c == ' ' || c == '\t') (c :: acc)
  String.ofList (walk line.toList false false true [])

/-- Words that hold the command position open rather than taking it: the shell
    keywords a command can follow, and the wrappers that run their argument. -/
private def keepsCommandPosition (word : String) : Bool :=
  ["if", "then", "elif", "else", "do", "while", "until", "!", "&&", "||",
    "exec", "env", "sudo", "command", "time", "nohup", "xargs", "builtin"].contains word
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

private def Lexer.endToken (state : Lexer) (separator : Bool) : Lexer :=
  let word := String.ofList state.token.reverse
  let atCommand :=
    if word.isEmpty then state.atCommand || separator
    else if state.atCommand && keepsCommandPosition word then true
    else separator
  { state with
      token := []
      atCommand
      found := if !word.isEmpty && state.atCommand && !keepsCommandPosition word
        then word :: state.found else state.found }

/-- The words in command position on one line of shell.

    Quote characters are dropped rather than kept in the token, so `'npm' i`
    reads as an invocation of `npm`; a word is only ever compared whole, so
    `npm-pack.sh` and `nodes` are not. What this cannot see is a command name
    that is not a literal word — `"$tool" publish`, or `npm` inside the string
    `sh -c` runs — which is why the PATH-shim arm exists. -/
def commandWords (line : String) : List String :=
  let rec walk : List Char → Lexer → Lexer
    | [], state => state.endToken false
    | c :: rest, state =>
      if c == '\'' && !state.double then walk rest { state with single := !state.single }
      else if c == '"' && !state.single then walk rest { state with double := !state.double }
      else if state.single || state.double then
        walk rest { state with token := c :: state.token }
      else if c == ' ' || c == '\t' then walk rest (state.endToken false)
      else if c == ';' || c == '|' || c == '&' || c == '(' || c == ')'
          || c == '{' || c == '}' || c == '`' || c == '<' || c == '>' then
        walk rest (state.endToken true)
      else walk rest { state with token := c :: state.token }
  (walk line.toList {}).found.reverse

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

/-- Line number, the command, and the line it is on. The line travels with the
    finding because the fix is almost never "delete this word". -/
structure Invocation where
  line : Nat
  command : String
  text : String
  deriving Repr, DecidableEq

/-- Every forbidden command one file invokes. The line is reported as written,
    whatever had to be stripped from it to find the command. -/
def invocationsIn (kind : SourceKind) (text : String) : List Invocation :=
  let lines := (text.splitOn "\n").zipIdx 1
  lines.flatMap fun (line, number) =>
    let code := match kind with
      | .shell => codeOf line
      | .workflow => workflowShell (codeOf line)
    (commandWords code).filterMap fun word =>
      if forbiddenCommands.contains word then
        some { line := number, command := word, text := line.trimAscii.toString }
      else none

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

/-- One file the scan read, and what it found in it. -/
structure ScannedFile where
  path : String
  reachedFrom : String
  invocations : List Invocation
  lines : Nat
  deriving Repr

def scanText (kind : SourceKind) (text : String) : String :=
  match kind with
  | .shell => text
  | .workflow => workflowRunningText text

/-- The refusal lines for one file's findings. -/
def fileFindings (scanned : ScannedFile) : List String :=
  scanned.invocations.map fun invocation =>
    s!"  {scanned.path}:{invocation.line}: invokes {invocation.command} — {invocation.text}"

/-- Every finding of a whole run, and the counts that make silence meaningful.
    A scan that read nothing, or that reached only the entry points it was
    handed, is reported rather than returned as a clean verdict: the shape this
    gate exists to catch is a check that stopped looking. -/
def boundaryVerdict (scanned : List ScannedFile) : Except String String :=
  let findings := scanned.flatMap fileFindings
  let empty := scanned.filter (·.lines == 0) |>.map (·.path)
  if !empty.isEmpty then
    .error s!"read no lines from {String.intercalate ", " empty}. A file that scans as empty produces no findings for the same reason a clean one does, so this is reported rather than counted as a pass."
  else if findings.isEmpty then
    -- The files are named, not counted. A closure that stopped following
    -- references still reports a plausible number, and the reader of a release
    -- log is the only one who can notice that the script they just added is not
    -- in the list.
    .ok s!"{scanned.length} file(s) reachable from {entryPoints.length} v0.1 entry point(s) invoke none of {String.intercalate ", " forbiddenCommands}: {String.intercalate ", " (scanned.map (·.path))}"
  else
    .error ("the v0.1 release path invokes a command it must not.\n"
      ++ String.intercalate "\n" findings
      ++ s!"\nADR-0026 keeps {String.intercalate ", " forbiddenCommands} off every path a release reaches: an operator's machine is not a GitHub runner, and a release must not stop for a runtime it does not publish through. Move the decision into tlrelease, or — if this belongs to a channel release/plan.json defers — move the file behind that channel's own script and name it in deferredPaths.")

/-! ## The command -/

private def boundaryUsage : String :=
  "usage: tlrelease dependency-boundary --root <checkout>"

private def boundaryOptions : List OptionSpec :=
  [{ name := "root", takesValue := true }]

private def deferredNames : List String := deferredPaths.map (·.path)

/-- Walk the closure breadth-first, entry points first. `fuel` is the visited
    bound: every step either consumes a queued path or stops, and the queue only
    ever grows by paths not yet visited, so the file count bounds it. -/
private def walkClosure (root : String) : Nat → List (String × String) → List String →
    List ScannedFile → Decision (List ScannedFile)
  | 0, _, _, scanned => pure scanned
  | _ + 1, [], _, scanned => pure scanned
  | fuel + 1, (path, reachedFrom) :: queue, visited, scanned =>
    if visited.contains path || deferredNames.contains path then
      walkClosure root fuel queue visited scanned
    else do
      let entry := entryPoints.find? (·.path == path)
      let full := if root == "." then path else root ++ "/" ++ path
      let text ← ofIO (readTextFile full)
      let kind := entry.map (·.kind) |>.getD .shell
      let scanText := scanText kind text
      let found : ScannedFile :=
        { path, reachedFrom, invocations := invocationsIn kind scanText,
          lines := (scanText.splitOn "\n").length }
      let next := (referencedScripts scanText).filterMap fun reference =>
        if visited.contains reference || deferredNames.contains reference then none
        else some (reference, path)
      walkClosure root fuel (queue ++ next) (path :: visited) (scanned ++ [found])

private def boundaryDecision (root : String) : Decision String := do
  let queue := entryPoints.map fun entry => (entry.path, entry.entered)
  -- The bound is the whole tracked shell surface several times over; reaching
  -- it means the closure is walking in circles, which is a defect here rather
  -- than a large repository.
  let scanned ← walkClosure root 500 queue [] []
  if scanned.length < entryPoints.length then
    decline s!"read {scanned.length} file(s) for {entryPoints.length} entry point(s). An entry point that is not read is one this gate did not check."
  else
    ofExcept (boundaryVerdict scanned)

def boundaryCommand : Command := {
  name := "dependency-boundary"
  arguments := "--root <checkout>"
  summary := "Refuse unless every script the v0.1 release path reaches is free of python, ruby, brew, node and npm."
  run := runWithOptions "tlrelease dependency-boundary" boundaryOptions boundaryUsage
    (fun options => options.required "root") boundaryDecision }

def boundaryCommands : List Command := [boundaryCommand]

end Release
