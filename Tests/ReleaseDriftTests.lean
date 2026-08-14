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

private def wordsOf (text : String) : List String :=
  (text.splitOn " ").filterMap fun word =>
    let word := word.trimAscii.toString
    if word.isEmpty then none else some word

/-- What one documented span has to be.

    A bare `tlrelease`, or `tlrelease <command>` with no arguments, is a
    reference to the tool or the command and is left alone: prose has to be able
    to name a thing without invoking it. Everything else is an invocation, and is
    held to what the command's own parser accepts. -/
def documentedVerdict (span : String) : Except String Unit :=
  match wordsOf span with
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
    match wordsOf span with
    | "tlrelease" :: _ :: _ :: _ => true
    | _ => false

/-! ## One decision about a missing tool

`command -v` and `rc_skip_gate` belong to `scripts/lib/release-common.sh`. A
policy script that reaches for either is writing its own answer to "what happens
when the tool is absent", and the four that did had already produced two
spellings of it. -/

/-- Does this line probe for a command's presence?

    Read from the code half of the line, so the sentence explaining the rule in
    a comment is prose. Matched as adjacent words — `command` followed by a flag
    carrying `v` — rather than as the string `command -v`, so the spacing does
    not decide the verdict. -/
def probesForTool (line : String) : Bool :=
  let words := wordsOf (codeOf line)
  (words.zip (words.drop 1)).any fun (word, next) =>
    word == "command" && next.startsWith "-" && next.any (· == 'v')

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
      some s!"  {path}:{number}: probes for a tool with `command -v` — {line.trimAscii}"
    else if callsDirectly line "rc_skip_gate" then
      some s!"  {path}:{number}: calls rc_skip_gate directly — {line.trimAscii}"
    else none

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
    check "release docs: an unrelated span is not read as an invocation"
      ((documentedVerdict "lake exe tlrelease").toOption.isSome),
    check "release policy: a presence probe is recognised"
      (probesForTool "if command -v npm >/dev/null 2>&1; then"),
    check "release policy: spacing does not decide it"
      (probesForTool "command   -v ruby > /dev/null"),
    check "release policy: the same words in a comment are prose"
      (!probesForTool "# command -v belongs to the library"),
    check "release policy: a direct skip is recognised"
      (callsDirectly "  rc_skip_gate \"workflow lint\" \"actionlint is not on PATH\"" "rc_skip_gate"),
    check "release policy: going through the helper is not one"
      (!callsDirectly "rc_tool_gate \"workflow lint\" --tool actionlint -- actionlint" "rc_skip_gate"),
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
