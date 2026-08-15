/-
`Tests.ReleaseDriftTests` — the two guards over statements kept beside the
release layer rather than inside it.

Both exist for the same failure, in two materials. `--plan` became mandatory on
`tlrelease dependency-boundary`, and three sentences went on showing
`--root .` alone: a documented invocation that exits 2 for anyone who copies it,
in a repository whose own rule is that artifacts stand on their own. And the
decision "a missing tool is a skip, unless the run is strict, in which case it
is a failure" was written out at four gates, so the rule lived in four places
and was tested at none of them.

Neither guard reads a copy of what it checks. The documentation rows run the
command's own `accepts` — the same function its `run` goes through, so an
invocation accepted here is one the tool accepts. The shell rows read the policy
scripts with `release/Boundary.lean`'s own lexer, which is the one that already
knows what a comment is and what command position means.

Tested I/O shell (ADR-0004): both guards read tracked files and decide, and
neither is part of the product. What they protect is the thing a reader of the
documentation, or of one policy script, cannot check for themselves.
-/
import Tests.Harness
import release.Cli

namespace Tl.Tests

open System (FilePath)
open Release

/-! ## Reading the tree -/

/-- Every file under `dir` with one of these extensions, recursively.

    Directories rather than a list of files, deliberately. A list would go on
    passing after somebody added a document it does not name, and "the check
    covers everything it was told about" is the shape of gate this repository
    keeps removing. -/
private partial def filesUnder (dir : FilePath) (extensions : List String) :
    IO (Array FilePath) := do
  let mut found : Array FilePath := #[]
  for entry in ← dir.readDir do
    if [".git", ".lake", ".tl", "dist", "node_modules"].contains entry.fileName then
      continue
    if ← entry.path.isDir then
      found := found ++ (← filesUnder entry.path extensions)
    else if extensions.any (fun extension => entry.path.extension == some extension) then
      found := found.push entry.path
  return found

/-! ## Documented invocations

The rule is one sentence: inside backticks, either name a command or write an
invocation that works. A fragment — a command with some of its options — is the
form that rots, because it is specific enough to be copied and incomplete enough
to stop being true.

What is checked is acceptance at the usage layer, not the decision: a documented
`--plan release/plan.json` is required to *parse* here, and whether that file
says what the sentence claims is a matter for the command itself. That is the
line between a documentation guard and a second copy of the release policy. -/

/-- The backticked spans on one line: the odd segments of a split on the
    backtick. A line whose backticks do not pair leaves its last segment
    unclosed, and that segment is read as a span rather than dropped — the
    conservative direction, since a documented invocation missing its closing
    backtick is still a documented invocation.

    A trailing backslash comes off the span. Two of these documents are written
    *by* shell, inside a quoted heredoc where a backtick has to be escaped, and
    the escape belongs to the closing backtick rather than to the invocation in
    front of it. -/
private def codeSpans (line : String) : List String :=
  ((line.splitOn "`").zipIdx 0).filterMap fun (segment, index) =>
    if index % 2 == 1 then
      some (if segment.endsWith "\\" then (segment.dropEnd 1).toString else segment)
    else none

/-- Words, on real whitespace. Splitting on the space alone left a span written
    with a tab as one token that matched nothing, which is a documented
    invocation this guard read as prose. -/
private def wordsOf (text : String) : List String :=
  ((text.splitOn " ").flatMap (·.splitOn "\t")).filterMap fun word =>
    let word := word.trimAscii.toString
    if word.isEmpty then none else some word

/-- The tokens of a documented span, with the ways a reader is told to run this
    executable removed: a `lake exe` prefix, and a path to the built binary.

    Normalizing by basename is the same rule the dependency boundary uses on a
    command word, and for the same reason — `./.lake/build/bin/tlrelease` and
    `tlrelease` are one command, and a guard that only knew the second was a
    guard three copyable spellings walked around. -/
private def invocationTokens (span : String) : List String :=
  let words := wordsOf span
  let words := match words with
    | "lake" :: "exe" :: rest => rest
    | _ => words
  match words with
  | executable :: rest => commandName executable :: rest
  | [] => []

/-- What one documented span has to be.

    A bare `tlrelease`, or `tlrelease <command>` with no arguments, is a
    reference to the tool or the command and is left alone: prose has to be able
    to name a thing without invoking it. Everything else is an invocation, and is
    held to what the command's own parser accepts. -/
def documentedVerdict (span : String) : Except String Unit :=
  match invocationTokens span with
  | "tlrelease" :: name :: argv =>
      if ["--help", "-h", "help"].contains name then .ok ()
      else match commands.find? (·.name == name) with
        | none =>
            .error s!"names '{name}', which is not a command this build offers"
        | some command =>
            if argv.isEmpty then .ok () else command.accepts argv
  | _ => .ok ()

/-- Every span in one file that is not what it claims to be. -/
private def documentedFailures (path : String) (text : String) : List String :=
  ((text.splitOn "\n").zipIdx 1).flatMap fun (line, number) =>
    (codeSpans line).filterMap fun span =>
      match documentedVerdict span with
      | .ok () => none
      | .error message => some s!"  {path}:{number}: `{span}` {message}"

/-- How many documented invocations one file carries — the half of the evidence
    that says the check had something to read. -/
private def documentedCount (text : String) : Nat :=
  ((text.splitOn "\n").flatMap codeSpans).countP fun span =>
    match invocationTokens span with
    | "tlrelease" :: _ :: _ :: _ => true
    | _ => false

/-- The option names one usage line mentions, without the punctuation the
    syntax carries: `(--workflow-ref <ref> … | --outside-workflow)` names two. -/
def usageOptions (usage : String) : List String :=
  (wordsOf usage).filterMap fun word =>
    let word := (word.dropWhile fun c => c == '(' || c == '[' || c == '{').toString
    let word := (word.takeWhile fun c =>
      c != ')' && c != ']' && c != '}' && c != '|' && c != ',').toString
    if word.startsWith "--" && word.length > 2 then some (word.drop 2).toString else none

/-! ## One decision about a missing tool

`command -v` and `rc_skip_gate` belong to `scripts/lib/release-common.sh`. A
policy script that reaches for either is writing its own answer to "what happens
when the tool is absent", and the four that did had already produced two
spellings of it. -/

/-- The builtins that answer "is this tool here" on their own. `command`
    is not among them: it takes a flag, and `command npm publish` is an
    invocation rather than a probe. -/
private def presenceProbes : List String := ["type", "which", "hash"]

/-- Does this line probe for a command's presence?

    Read from the code half of the line with the boundary's own lexer, so the
    sentence explaining this rule in a comment is prose and a quoted gate name
    containing one of these words is one token rather than several.

    Every word is normalized to its program name first. A guard that compared
    whole words forbade a spelling rather than a decision: `type shellcheck` and
    `/usr/bin/command -v shellcheck` both branch on tool presence, and both were
    invisible to a rule written for the literal string `command -v`. -/
def probesForTool (line : String) : Bool :=
  let code := codeOf line
  let named := (lineWords code).map commandName
  let commanded := (commandWords code).map commandName
  (named.zip (named.drop 1)).any (fun (word, next) =>
      word == "command" && next.startsWith "-" && next.any (· == 'v'))
    || commanded.any presenceProbes.contains

/-- Does this line call `name` in command position? -/
def callsDirectly (line : String) (name : String) : Bool :=
  (commandWords (codeOf line)).any fun word => commandName word == name

/-- The library that owns the decision, by what it defines rather than by where
    it sits: the file carrying `rc_tool_gate` is the one place entitled to the
    two constructs below it. -/
private def definesToolGate (text : String) : Bool :=
  (text.splitOn "rc_tool_gate()").length > 1

/-- A script that runs gates, which is what puts it under this rule. Found by
    what it does — it opens a policy run — so a third policy script is covered
    the day it is written rather than the day somebody remembers it. -/
private def runsGates (text : String) : Bool :=
  (text.splitOn "rc_policy_begin").length > 1

private def hygieneFailures (path : String) (text : String) : List String :=
  ((text.splitOn "\n").zipIdx 1).filterMap fun (line, number) =>
    if probesForTool line then
      some s!"  {path}:{number}: decides for itself whether a tool is present — {line.trimAscii}"
    else if callsDirectly line "rc_skip_gate" then
      some s!"  {path}:{number}: calls rc_skip_gate directly — {line.trimAscii}"
    else none

/-! ## The current release-tool artifact handoff

`upload-artifact` excludes files below a dot-directory by default. The release
tool used to be uploaded directly from `.lake/`, so the action found no file
even though the preceding build and digest succeeded. Until ADR-0028 replaces
this raw-digest handoff with its typed file-set-hash form, pin the three paths
that must denote the same staged bytes. -/

private def occursExactlyOnce (text needle : String) : Bool :=
  (text.splitOn needle).length == 2

def releaseToolHandoffShape (workflow : String) : Except String Unit := do
  let stage := "install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease"
  let digest := "line=$(sha256sum release-tool/tlrelease)"
  let upload := "path: release-tool/tlrelease"
  if !occursExactlyOnce workflow stage then
    throw "the release tool must be staged once from the gated binary into a non-hidden artifact path"
  if !occursExactlyOnce workflow digest then
    throw "the raw transition digest must hash exactly the staged artifact bytes"
  if !occursExactlyOnce workflow upload then
    throw "upload-artifact must upload exactly the staged non-hidden release-tool path"
  if workflow.contains "path: .lake/build/bin/tlrelease" then
    throw "upload-artifact excludes the hidden .lake path by default"

/-! ## The rows -/

def releaseDriftTests : IO (List Outcome) := do
  let documents ← filesUnder "." ["md", "sh", "yml"]
  let mut documentFailures : List String := []
  let mut documented := 0
  for path in documents do
    let text ← IO.FS.readFile path
    documented := documented + documentedCount text
    documentFailures := documentFailures ++ documentedFailures path.toString text
  let documentRows : List Outcome :=
    [check "release docs: every documented tlrelease invocation is one the tool accepts"
      documentFailures.isEmpty (String.intercalate "\n" documentFailures ++
        "\nInside backticks, name the command or write an invocation that works: a fragment is specific enough to be copied and incomplete enough to stop being true. The command's own parser decides this, so a required option added to it fails here in the same build.")]
  let scripts ← filesUnder "scripts" ["sh"]
  let releaseWorkflow ← IO.FS.readFile ".github/workflows/release.yml"
  let mut library := 0
  let mut policies : List (FilePath × String) := []
  for path in scripts do
    let text ← IO.FS.readFile path
    if definesToolGate text then library := library + 1
    else if runsGates text then policies := policies ++ [(path, text)]
  let mut hygieneRows : List Outcome := []
  for (path, text) in policies do
    let failures := hygieneFailures path.toString text
    hygieneRows := hygieneRows ++
      [check s!"release policy: {path} decides a missing tool through rc_tool_gate alone"
        failures.isEmpty (String.intercalate "\n" failures ++
          "\nrc_tool_gate in scripts/lib/release-common.sh crosses the three inputs — present or absent, strict or not, passed or failed — and its selftest matrix is what proves the crossing. A branch written here is a second answer to the same question, tested by nothing.")]
  return documentRows ++ hygieneRows ++ [
    check "release workflow: the current release-tool upload hashes and uploads one staged path"
      (releaseToolHandoffShape releaseWorkflow).toOption.isSome
      (match releaseToolHandoffShape releaseWorkflow with
       | .ok () => ""
       | .error message => message),
    -- Non-vacuity, both halves. A walk that found no documents, or no script
    -- under the rule, reports the same clean result as a repository that
    -- satisfies it.
    check "release docs: the scan read documented invocations to check"
      (documented ≥ 4) s!"found {documented} documented invocation(s) with arguments",
    check "release policy: the library that owns the decision was found exactly once"
      (library == 1) s!"{library} file(s) define rc_tool_gate",
    check "release policy: the scripts that run gates were found"
      (policies.length ≥ 2) s!"{policies.length} policy script(s)",
    -- The checker itself, on the drift it exists to catch and on the shapes it
    -- must leave alone. Without these rows a guard that accepted everything
    -- would report the same clean result as the repository being clean.
    check "release docs: the stale form this guard was written for is rejected"
      ((documentedVerdict "tlrelease dependency-boundary --root .").toOption.isNone),
    check "release docs: the complete form is accepted"
      ((documentedVerdict "tlrelease dependency-boundary --root . --plan release/plan.json").toOption.isSome),
    check "release docs: naming a command without invoking it is prose"
      ((documentedVerdict "tlrelease prereqs").toOption.isSome),
    check "release docs: naming the tool alone is prose"
      ((documentedVerdict "tlrelease").toOption.isSome),
    check "release docs: a command this build does not offer is rejected"
      ((documentedVerdict "tlrelease depenency-boundary --root .").toOption.isNone),
    -- The wrapper forms a reader can copy. Each is the same command, and a
    -- guard that only knew the bare name let three stale spellings through.
    check "release docs: a stale invocation behind `lake exe` is rejected"
      ((documentedVerdict "lake exe tlrelease dependency-boundary --root .").toOption.isNone),
    check "release docs: a stale invocation behind the built path is rejected"
      ((documentedVerdict "./.lake/build/bin/tlrelease dependency-boundary --root .").toOption.isNone),
    check "release docs: a stale invocation separated by a tab is rejected"
      ((documentedVerdict "tlrelease\tdependency-boundary --root .").toOption.isNone),
    check "release docs: naming the built path without arguments is prose"
      ((documentedVerdict "./.lake/build/bin/tlrelease").toOption.isSome),
    check "release docs: another executable's span is not read as one of these"
      ((documentedVerdict "lake exe tltest --root .").toOption.isSome),
    check "release policy: a presence probe is recognised"
      (probesForTool "if command -v npm >/dev/null 2>&1; then"),
    check "release policy: spacing does not decide it"
      (probesForTool "command   -v ruby > /dev/null"),
    -- The spellings that are the same decision. A guard that forbade the string
    -- `command -v` forbade a spelling, and a policy script could keep its own
    -- present/strict/passed logic by writing any of these instead.
    check "release policy: the probe reached through a path is recognised"
      (probesForTool "if /usr/bin/command -v shellcheck >/dev/null 2>&1; then"),
    check "release policy: type is a presence probe"
      (probesForTool "if type shellcheck >/dev/null 2>&1; then"),
    check "release policy: which is a presence probe"
      (probesForTool "which actionlint >/dev/null || exit 1"),
    check "release policy: hash is a presence probe"
      (probesForTool "hash ruby 2>/dev/null"),
    check "release policy: a gate name that contains one of those words is not one"
      (!probesForTool "rc_gate \"the type check\" ./scripts/x.sh"),
    check "release policy: the same words in a comment are prose"
      (!probesForTool "# command -v belongs to the library"),
    check "release policy: a direct skip is recognised"
      (callsDirectly "  rc_skip_gate \"workflow lint\" \"actionlint is not on PATH\"" "rc_skip_gate"),
    check "release policy: going through the helper is not one"
      (!callsDirectly "rc_tool_gate \"workflow lint\" --tool actionlint -- actionlint" "rc_skip_gate"),
    check "release workflow: a hidden upload source is refused"
      (releaseToolHandoffShape
        "install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease\nline=$(sha256sum release-tool/tlrelease)\npath: .lake/build/bin/tlrelease").toOption.isNone,
    check "release workflow: hashing the build path instead of the upload source is refused"
      (releaseToolHandoffShape
        "install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease\nline=$(sha256sum .lake/build/bin/tlrelease)\npath: release-tool/tlrelease").toOption.isNone,
    check "release workflow: an unstaged upload is refused"
      (releaseToolHandoffShape
        "line=$(sha256sum release-tool/tlrelease)\npath: release-tool/tlrelease").toOption.isNone,
    check "release workflow: the canonical staged handoff is accepted"
      (releaseToolHandoffShape
        "install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease\nline=$(sha256sum release-tool/tlrelease)\npath: release-tool/tlrelease").toOption.isSome,
    -- The commands' own examples. `arguments` is the shape and `invocation` is
    -- an instance of it, and the second is what makes the first checkable.
    check "tlrelease: every command's canonical invocation is one it accepts"
      (commands.all fun command => (command.accepts command.invocation).toOption.isSome)
      (String.intercalate "; " (commands.filterMap fun command =>
        match command.accepts command.invocation with
        | .ok () => none
        | .error message => some s!"{command.name}: {message}")),
    check "tlrelease: every option in a canonical invocation is one the usage line names"
      (commands.all fun command =>
        command.invocation.all fun word =>
          !word.startsWith "--" || (command.usage.splitOn word).length > 1)
      (String.intercalate "; " (commands.filterMap fun command =>
        let missing := command.invocation.filter fun word =>
          word.startsWith "--" && (command.usage.splitOn word).length == 1
        if missing.isEmpty then none else some s!"{command.name}: {missing}")),
    check "tlrelease: a canonical invocation is the argv after the name, not with it"
      (commands.all fun command => !command.invocation.contains "tlrelease"),
    -- The declaration against the sentence describing it, both ways. One
    -- direction catches an option nobody documented — which is how an optional
    -- option can exist, be accepted, and appear in nothing a reader sees; the
    -- other catches a documented option the parser would refuse.
    check "tlrelease: every declared option is named in the usage line"
      (commands.all fun command =>
        command.optionNames.all fun named => (command.usage.splitOn s!"--{named}").length > 1)
      (String.intercalate "; " (commands.filterMap fun command =>
        let missing := command.optionNames.filter fun named =>
          (command.usage.splitOn s!"--{named}").length == 1
        if missing.isEmpty then none else some s!"{command.name}: {missing}")),
    check "tlrelease: every option the usage line names is one the parser declares"
      (commands.all fun command =>
        (usageOptions command.usage).all command.optionNames.contains)
      (String.intercalate "; " (commands.filterMap fun command =>
        let undeclared := (usageOptions command.usage).filter fun named =>
          !command.optionNames.contains named
        if undeclared.isEmpty then none else some s!"{command.name}: {undeclared}")),
    -- The help table's entry against the usage line, including the two that
    -- elide. An elision is allowed to stop early and not to say something else:
    -- what precedes the ellipsis has to be what the usage line starts with, or
    -- the table is describing a syntax the command does not have.
    check "tlrelease: the help table's argument line agrees with the usage line"
      (commands.all fun command =>
        let full := s!"usage: tlrelease {command.name} {command.arguments}"
        if command.arguments.endsWith "…" then
          command.usage.startsWith (full.dropEnd 1).trimAsciiEnd.toString
        else command.usage == full)
      (String.intercalate "; " (commands.filterMap fun command =>
        let full := s!"usage: tlrelease {command.name} {command.arguments}"
        let agrees :=
          if command.arguments.endsWith "…" then
            command.usage.startsWith (full.dropEnd 1).trimAsciiEnd.toString
          else command.usage == full
        if agrees then none else some s!"{command.name}: {command.usage} vs {full}"))]

end Tl.Tests
