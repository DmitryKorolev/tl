/- Guards over documented invocations, workflow authority and release-native wiring. -/
import Tests.Harness
import Tests.WorkflowTests
import Verify.Environment
import release.Cli
import release.Workflow

namespace Tl.Tests

open Lean
open System (FilePath)
open Release
open Tl.Verify

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

    Normalizing by basename keeps equivalent documented spellings together — `./.lake/build/bin/tlrelease` and
    `tlrelease` are one command, and a guard that only knew the second was a
    guard three copyable spellings walked around. -/
private def invocationTokens (span : String) : List String :=
  let words := wordsOf span
  let words := match words with
    | "lake" :: "exe" :: rest => rest
    | _ => words
  match words with
  | executable :: rest => (executable.splitOn "/").getLast! :: rest
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

/-! ## The release-tool artifact handoff, structurally

The tool the privileged jobs run is built once, in the unprivileged `gates` job,
and carried to each of them through an artifact. Everything about that carriage
is what this models: where the bytes are staged from, what is hashed, what is
uploaded under which name, and — on the receiving side — that each consumer
validates the bytes it received *before* running them, with nothing in between.

The previous guard counted substrings over the whole file. Three of its four
rows would have been satisfied by a comment, and the fourth by a decoy step in
any job at all; nothing in it could tell a consumer that had dropped its
comparison from a consumer that never existed, because it never looked at
consumers. This reads the workflow as jobs and steps and binds each fact to the
place that must carry it.

The canonical file-set prefix is shared by every consumer and the capability-free
rehearsal. Its complete steps are pinned, including the first invocation, and
mutation rows exercise each real consumer independently of the rehearsal. A
hosted run established the upload/hash-expression behavior before the raw-digest
handoff was removed; local parsing does not establish hosted file selection.
The remaining arbitrary publication commands are outside this model and await
ADR-0028's separate typed-policy cutover. -/

open Release.Workflow (Step stepsOf jobsOf)

/-- The binary-only Git-floor job must receive every executable its suite runs.
    Artifact downloads do not preserve executable permissions. -/
private def gitFloorReleaseToolShape (workflow : String) : Bool := Id.run do
  let jobs := jobsOf workflow
  let some (_, buildLines) := jobs.find? (fun (name, _) => name == "build-and-test")
    | return false
  let some (_, floorLines) := jobs.find? (fun (name, _) => name == "git-floor")
    | return false
  let some upload := (stepsOf buildLines).find?
      (fun step => step.name == "upload binaries for the git-floor job")
    | return false
  let some run := (stepsOf floorLines).find?
      (fun step => step.name == "run the suite under git 2.17")
    | return false
  return (upload.code.map (fun line => line.trimAscii.toString)).contains
      ".lake/build/bin/tlrelease"
    && (run.code.map (fun line => line.trimAscii.toString)).contains
      "chmod +x .lake/build/bin/tl .lake/build/bin/tltest .lake/build/bin/tltestWorker .lake/build/bin/tlrelease"

/-! ## The shared native hermetic invocation
The complete job shape is pinned here. Process arguments and evidence branches
are now exercised in HermeticTests, where the executable owns them. -/

private def canonicalHermeticWorkflow : String :=
  "jobs:\n" ++
  "  hermetic-release:\n" ++
  "    runs-on: ubuntu-latest\n" ++
  "    timeout-minutes: 20\n" ++
  "    steps:\n" ++
  "      - uses: actions/checkout@9c091bb21b7c1c1d1991bb908d89e4e9dddfe3e0 # v7.0.0\n" ++
  "      - name: install the pinned Lean toolchain\n" ++
  "        uses: leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9 # v1.5.0\n" ++
  "        with:\n" ++
  "          auto-config: \"false\"\n" ++
  "          build: \"false\"\n" ++
  "          test: \"false\"\n" ++
  "          lint: \"false\"\n" ++
  "          use-mathlib-cache: \"false\"\n" ++
  "          use-github-cache: \"false\"\n" ++
  "      - name: build the native hermetic runner\n" ++
  "        run: lake build tlrelease --wfail\n" ++
  "      - name: runtime-stripped release policy and retained-adapter suites\n" ++
  "        run: ./.lake/build/bin/tlrelease hermetic --root .\n"

def hermeticReleaseShape (workflow : String) : Except String Unit := do
  let jobs := (jobsOf workflow).filter (fun (name, _) => name == "hermetic-release")
  let [(_, lines)] := jobs | throw "Restore exactly one hermetic-release job."
  let expected := ((jobsOf canonicalHermeticWorkflow).head!).2
  let code (ls : List String) := ls.filter (fun l =>
    !l.trimAscii.isEmpty && !l.trimAscii.toString.startsWith "#")
  if code lines != code expected then
    throw "Restore the pinned checkout, toolchain, native build and shared hermetic invocation."
  pure ()

/-! ### The canonical one-file transport boundary -/

private def consumerToolPath : String := "tool/tlrelease"
private def toolArtifactName : String := "release-tool"
private def uploadAction : String := "actions/upload-artifact@"
private def downloadAction : String := "actions/download-artifact@"

/-- Whether a step runs the downloaded tool. -/
private def stepUsesTool (step : Step) : Bool :=
  step.code.any fun line =>
    let text := line.trimAscii.toString
    (text.splitOn s!"./{consumerToolPath}").length > 1
      || (text.splitOn s!" {consumerToolPath} ").length > 1

/-- Whether a step is the download of the tool artifact. -/
private def stepDownloadsTool (step : Step) : Bool :=
  (step.uses.getD "").startsWith downloadAction && step.hasInput "name" toolArtifactName

/-- The jobs this scan reads as consumers, for a test that says which. -/
def releaseToolConsumers (workflow : String) : List String :=
  (jobsOf workflow).filterMap fun (job, lines) =>
    if (stepsOf lines).any stepDownloadsTool then some job else none

/-- Replace every occurrence, for building one mutation out of the canonical
    workflow. -/
private def swap (text : String) (before after : String) : String :=
  String.intercalate after (text.splitOn before)

/-- The exact ADR-0028 prefix. Help is a real, side-effect-free first invocation
    shared by the rehearsal and, after cutover, every publication consumer. -/
private def fileSetPrefix : String :=
  "      - name: download the release tool\n" ++
  "        uses: actions/download-artifact@3e5f45b2cfb9172054b4087a40e8e0b5a5461e7c # v8.0.1\n" ++
  "        with:\n" ++
  "          name: release-tool\n" ++
  "          path: tool\n" ++
  "      - name: refuse a missing or changed release tool\n" ++
  "        if: needs.gates.outputs.releaseToolFileSetHash == '' || hashFiles('tool/tlrelease') == '' || needs.gates.outputs.releaseToolFileSetHash != hashFiles('tool/tlrelease')\n" ++
  "        run: /usr/bin/false\n" ++
  "      - name: make the validated release tool executable\n" ++
  "        run: /bin/chmod 0755 tool/tlrelease\n" ++
  "      - name: enter the validated release tool\n" ++
  "        run: ./tool/tlrelease --help\n"

private def fileSetProducer : String :=
  "      - name: hash the staged release tool file set\n" ++
  "        id: tool_file_set_hash\n" ++
  "        env:\n" ++
  "          RELEASE_TOOL_FILE_SET_HASH: ${{ hashFiles('release-tool/tlrelease') }}\n" ++
  "        run: printf '%s\\n' \"fileSetHash=$RELEASE_TOOL_FILE_SET_HASH\" >> \"$GITHUB_OUTPUT\"\n"

private def fileSetRehearsal : String :=
  "    if: github.event_name == 'workflow_dispatch' && github.ref_type == 'branch'\n" ++
  "    needs: [gates]\n" ++
  "    runs-on: ubuntu-latest\n" ++
  "    timeout-minutes: 5\n" ++
  "    permissions: {}\n" ++
  "    steps:\n" ++ fileSetPrefix

/-- Preserve indentation: trimming would let a property under the wrong YAML
    parent impersonate the required one. Comments and blank lines are inert. -/
private def codeLines (lines : List String) : List String :=
  lines.filter (fun line => !line.trimAscii.isEmpty && !line.trimAscii.toString.startsWith "#")

private def fileSetStage : String :=
  "      - name: stage the release tool\n" ++
  "        run: install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease\n"

private def handoffOnlyInput : String :=
  "  workflow_dispatch:\n" ++
  "    inputs:\n" ++
  "      handoff_only:\n" ++
  "        description: Run the gates and capability-free tool handoff without the release matrix\n" ++
  "        type: boolean\n" ++
  "        default: false\n"

private def fileSetRehearsalShape (workflow : String) : Bool := Id.run do
  let jobs := jobsOf workflow
  let [(_, rehearsal)] := jobs.filter (fun (name, _) => name == "handoff-rehearsal")
    | return false
  let [(_, gates)] := jobs.filter (fun (name, _) => name == "gates")
    | return false
  let producers := (stepsOf gates).filter (fun step => step.hasField "id" "tool_file_set_hash")
  let [producer] := producers | return false
  let steps := stepsOf gates
  let some staging := (steps.zipIdx).find? (fun (step, _) => step.name == "stage the release tool")
    | return false
  let (stage, stageAt) := staging
  let some uploadAt := (steps.zipIdx).find? (fun (step, _) =>
    (step.uses.getD "").startsWith uploadAction && step.hasInput "name" "release-tool")
    | return false
  let (_, uploadIndex) := uploadAt
  let outputLines := ((codeLines gates).dropWhile (· != "    outputs:")).drop 1
    |>.takeWhile (·.startsWith "      ")
  let some stamp := jobs.lookup "stamp" | return false
  return codeLines rehearsal == codeLines (fileSetRehearsal.splitOn "\n")
    && codeLines producer.lines == codeLines (fileSetProducer.splitOn "\n")
    && codeLines stage.lines == codeLines (fileSetStage.splitOn "\n")
    && (steps[stageAt + 1]?).map (fun step => codeLines step.lines) == some (codeLines producer.lines)
    && uploadIndex == stageAt + 2
    && outputLines.contains "      releaseToolFileSetHash: ${{ steps.tool_file_set_hash.outputs.fileSetHash }}"
    && (gates.filter (· == "      releaseToolFileSetHash: ${{ steps.tool_file_set_hash.outputs.fileSetHash }}")).length == 1
    && (workflow.splitOn handoffOnlyInput).length == 2
    && (stamp.filter (· == "    if: github.event_name != 'workflow_dispatch' || !inputs.handoff_only")).length == 1

private def fileSetUpload : String :=
  "      - name: upload the release tool for the signing job\n" ++
  "        uses: actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a # v7.0.1\n" ++
  "        with:\n" ++
  "          name: release-tool\n" ++
  "          path: release-tool/tlrelease\n" ++
  "          if-no-files-found: error\n" ++
  "          retention-days: 7\n"

private def fileSetConsumers : List String :=
  ["handoff-rehearsal", "stamp", "sign", "publish-release", "publish-homebrew", "publish-npm"]

/-- Read a YAML control key, not a shell line in a block scalar. Quoting a
    control key does not change what GitHub does with it. -/
private def handoffControl (line : String) : String × String :=
  let body := line.trimAscii.toString
  let body := if body.startsWith "- " then (body.drop 2).toString else body
  let parts := body.splitOn ":"
  let key := (parts.headD "").trimAscii.toString
  let key := key.replace "\"" "" |>.replace "'" ""
  (key, String.intercalate ":" (parts.drop 1))

/-- Conditions can be folded or literal YAML scalars. Read their complete
    indented value, including a condition that is the first key of a step. -/
private def handoffStatusOverride (lines : List String) : Bool := Id.run do
  let mut active : Option Nat := none
  let mut conditions : List String := []
  for line in codeLines lines do
    let width := (line.toList.takeWhile (· == ' ')).length
    if active.any (width > ·) then
      conditions := line :: conditions
      continue
    let (key, value) := handoffControl line
    if key == "continue-on-error" then return true
    if key == "if" then
      let value := value.trimAscii.toString
      if value.startsWith "*" || value.startsWith "&" then return true
      active := some (width + if line.trimAscii.toString.startsWith "- " then 2 else 0)
      conditions := value :: conditions
    else active := none
  let compact := (String.ofList ((String.intercalate " " conditions.reverse).toList.filter (! ·.isWhitespace))).toLower
  return ["always(", "failure(", "cancelled(", "success("].any fun name =>
    (compact.splitOn name).length > 1

private def fileSetDefaults : String := "defaults:\n  run:\n    shell: bash\n"

private def handoffInheritedExecution (workflow : String) : Bool :=
  let header := codeLines ((workflow.splitOn "\n").takeWhile (· != "jobs:"))
  let defaults := ((header.dropWhile (· != "defaults:")).drop 1).takeWhile (·.startsWith " ")
  let env := ((header.dropWhile (· != "env:")).drop 1).takeWhile (·.startsWith " ")
  defaults == ["  run:", "    shell: bash"]
    && (header.filter (fun line => (handoffControl line).1 == "defaults")).length == 1
    && (header.filter (fun line => (handoffControl line).1 == "env")).all (· == "env:")
    && env.all (fun line => line.startsWith "  " && !line.startsWith "   " &&
      ["GLIBC_FLOOR_IMAGE", "GLIBC_FLOOR", "ELAN_VERSION"].contains (handoffControl line).1)

/-- Exact file-set transport shape, deliberately separate from the later
    migration of arbitrary publication commands into the typed policy grammar.
    This guard owns the producer and handoff, not the meaning of every shell
    command that follows. It keeps implicit success sequencing for the entire
    job and keeps the first domain command next to the uniform help entry. -/
def releaseToolHandoffShape (workflow : String) : Except String Unit := do
  let jobs := jobsOf workflow
  if !handoffInheritedExecution workflow then
    throw "restore the inherited bash shell and build-only environment keys for the handoff"
  if !fileSetRehearsalShape workflow then
    throw "restore the canonical producer, output mapping, and capability-free rehearsal"
  if releaseToolConsumers workflow != fileSetConsumers then
    throw "restore every release-tool consumer, exactly once"
  for (job, lines) in jobs do
    let fields := Release.Workflow.fieldsOf lines 1 4
    if !fields.readable || (fields.fields.any (·.key == "steps") && (stepsOf lines).isEmpty) then
      throw s!"write the `{job}` job's fields and steps in readable block form so an upload cannot disappear from the scan"
  if (jobs.flatMap (fun (_, lines) => stepsOf lines)).any (fun step => !step.readable) then
    throw "write every step with readable direct fields so unsupported metadata cannot hide an artifact upload"
  if (jobs.flatMap (fun (_, lines) => stepsOf lines)).any (fun step =>
      step.fields.any (·.key == "uses") &&
        ((step.scalar? "uses").bind Release.Workflow.plainScalar?).isNone) then
    throw "write every action reference as one plain scalar so an artifact uploader cannot be hidden by YAML metadata"
  if (jobs.flatMap (fun (_, lines) => stepsOf lines)).any (fun step =>
      (step.uses.getD "").startsWith uploadAction && (step.input? "name").isNone) then
    throw "give every artifact upload one readable plain name input so the release-tool uploader cannot be hidden"
  if ((jobs.flatMap (fun (_, lines) => stepsOf lines)).filter (fun step =>
      (step.uses.getD "").startsWith uploadAction && step.hasInput "name" "release-tool")).length != 1 then
    throw "only gates may upload the single release-tool artifact"
  let code := codeLines (workflow.splitOn "\n")
  if code.any (fun line => (line.splitOn "releaseToolDigest").length > 1) then
    throw "remove the obsolete raw-digest handoff atomically"
  for (job, lines) in jobs do
    if job != "gates" && !fileSetConsumers.contains job then
      if (stepsOf lines).any stepUsesTool then
        throw s!"the `{job}` job runs the tool without a modeled handoff; add its consumer explicitly"
      continue
    let header := (codeLines lines).takeWhile (· != "    steps:")
    if header.any (fun line => ["defaults", "container", "env", "continue-on-error"].contains (handoffControl line).1) then
      throw s!"remove the `{job}` job's handoff execution override"
    if handoffStatusOverride lines then
      throw s!"remove the `{job}` job's error or status override; handoff failure must stop later steps"
    let steps := stepsOf lines
    if job == "gates" then
      let tail := steps.dropWhile (fun step => step.name != "stage the release tool")
      if codeLines (tail.flatMap (·.lines)) != codeLines ((fileSetStage ++ fileSetProducer ++ fileSetUpload).splitOn "\n") then
        throw "end gates with exactly staging, file-set hashing, and the pinned single-file upload"
      if (steps.filter (fun step => step.runs "install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease")).length != 1 then
        throw "stage the gated binary exactly once"
      if (steps.filter (fun step => step.hasField "id" "tool_file_set_hash")).length != 1 then
        throw "produce the file-set hash exactly once"
      if (steps.filter (fun step => (step.uses.getD "").startsWith uploadAction && step.hasInput "name" "release-tool")).length != 1 then
        throw "upload the single release-tool artifact exactly once"
    else
      let before := steps.takeWhile (fun step => !stepDownloadsTool step)
      let after := steps.drop before.length
      if before.any stepUsesTool then
        throw s!"move the `{job}` job's early tool execution after its handoff"
      if codeLines ((after.take 4).flatMap (·.lines)) != codeLines (fileSetPrefix.splitOn "\n") then
        throw s!"restore the `{job}` job's exact contiguous download/refusal/chmod/entry prefix"
      if (steps.filter stepDownloadsTool).length != 1 then
        throw s!"download the `{job}` job's release tool exactly once"
      if job != "handoff-rehearsal" && !(after[4]?).any stepUsesTool then
        throw s!"keep the `{job}` job's first domain invocation immediately after the validated entry"
      if job != "handoff-rehearsal" && (after[4]?).any (fun step =>
          (codeLines step.lines).any (fun line =>
            ["if", "shell", "working-directory", "env"].contains (handoffControl line).1)) then
        throw s!"keep the `{job}` job's first domain invocation unconditional, with inherited execution settings"
  pure ()

/-- A six-consumer fixture exercises the entire handoff shape independently of
    the live workflow. Its publication effects are inert; its handoff is exact. -/
private def canonicalFileSetHandoff : String :=
  "on:\n" ++ handoffOnlyInput ++ fileSetDefaults ++ "jobs:\n" ++
  "  gates:\n    outputs:\n" ++
  "      releaseToolFileSetHash: ${{ steps.tool_file_set_hash.outputs.fileSetHash }}\n" ++
  "    steps:\n" ++ fileSetStage ++ fileSetProducer ++ fileSetUpload ++
  "  handoff-rehearsal:\n" ++ fileSetRehearsal ++
  String.join ((fileSetConsumers.drop 1).map fun job =>
    s!"  {job}:\n" ++
    (if job == "stamp" then "    if: github.event_name != 'workflow_dispatch' || !inputs.handoff_only\n" else "") ++
    "    needs: [gates]\n    steps:\n" ++ fileSetPrefix ++
    "      - name: verify the domain input\n        run: ./tool/tlrelease manifest-verify --dist dist\n")

private def fileSetRefuses (workflow : String) : Bool :=
  (releaseToolHandoffShape workflow).toOption.isNone

/-- Change one consumer without damaging the rehearsal oracle beside it. -/
private def mutateFileSetJob (job before after : String) : String := Id.run do
  let jobs := jobsOf canonicalFileSetHandoff
  let some lines := jobs.lookup job | return canonicalFileSetHandoff
  let body := String.intercalate "\n" lines
  let changed := swap body before after
  if body == changed then return canonicalFileSetHandoff
  return (canonicalFileSetHandoff.splitOn "jobs:\n").headD "" ++ "jobs:\n" ++
    String.join (jobs.map fun (name, lines) =>
      s!"  {name}:\n" ++ (if name == job then changed else String.intercalate "\n" lines) ++ "\n")

def fileSetMutationTests : List Outcome :=
  let mutations : List (String × String × String) := [
    ("absent staging", fileSetStage, ""),
    ("staging only in a comment", "        run: install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease", "        # install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease\n        run: true"),
    ("duplicate staging", fileSetStage, fileSetStage ++ fileSetStage),
    ("stage source drift", "install -D -m 0755 .lake/build/bin/tlrelease", "install -D -m 0755 other/tlrelease"),
    ("stage destination drift", "tlrelease release-tool/tlrelease", "tlrelease other/tlrelease"),
    ("duplicate producer", fileSetProducer, fileSetProducer ++ fileSetProducer),
    ("no recognized producer id", "        id: tool_file_set_hash", "        id: other_hash"),
    ("absent gates job", "  gates:\n", "  other-gates:\n"),
    ("hash before staging", fileSetStage ++ fileSetProducer, fileSetProducer ++ fileSetStage),
    ("upload before hashing", fileSetProducer ++ fileSetUpload, fileSetUpload ++ fileSetProducer),
    ("upload source drift", "path: release-tool/tlrelease", "path: .lake/build/bin/tlrelease"),
    ("duplicate upload", fileSetUpload, fileSetUpload ++ fileSetUpload),
    ("post-upload overwrite", fileSetUpload, fileSetUpload ++ "      - run: cp other release-tool/tlrelease\n"),
    ("producer empty set", "hashFiles('release-tool/tlrelease')", "hashFiles('absent')"),
    ("producer multiple files", "hashFiles('release-tool/tlrelease')", "hashFiles('release-tool/*')"),
    ("producer output key", "fileSetHash=$", "digest=$"),
    ("producer output mapping", "steps.tool_file_set_hash.outputs.fileSetHash", "steps.other.outputs.fileSetHash"),
    ("absent output mapping", "      releaseToolFileSetHash: ${{ steps.tool_file_set_hash.outputs.fileSetHash }}\n", ""),
    ("mapping wrong parent", "    outputs:", "    env:"),
    ("download missing", "      - name: download the release tool\n", "      - name: download something else\n"),
    ("nested download action", "uses: actions/download-artifact@", "uses: actions/checkout@decoy\n        with:\n          uses: actions/download-artifact@"),
    ("nested producer id", "        id: tool_file_set_hash", "        env:\n          id: tool_file_set_hash"),
    ("download wildcard", "          name: release-tool\n          path: tool", "          pattern: release-*\n          path: tool"),
    ("download destination", "          path: tool", "          path: other"),
    ("empty expected value allowed", "needs.gates.outputs.releaseToolFileSetHash == '' || ", ""),
    ("empty received value allowed", "hashFiles('tool/tlrelease') == '' || ", ""),
    ("unequal values allowed", " || needs.gates.outputs.releaseToolFileSetHash != hashFiles('tool/tlrelease')", ""),
    ("received multiple files", "hashFiles('tool/tlrelease')", "hashFiles('tool/*')"),
    ("mismatch ignored", "run: /usr/bin/false", "run: /usr/bin/true"),
    ("prefix truncated at chmod", "      - name: enter the validated release tool\n        run: ./tool/tlrelease --help\n", ""),
    ("domain invocation removed", "      - name: verify the domain input\n        run: ./tool/tlrelease manifest-verify --dist dist", ""),
    ("step before entry", "      - name: enter the validated release tool", "      - run: cp replacement tool/tlrelease\n      - name: enter the validated release tool"),
    ("step before domain invocation", "      - name: verify the domain input", "      - run: cp replacement tool/tlrelease\n      - name: verify the domain input"),
    ("early tool execution", "      - name: download the release tool", "      - run: ./tool/tlrelease --help\n      - name: download the release tool"),
    ("handoff status override", "run: /bin/chmod 0755 tool/tlrelease", "run: /bin/chmod 0755 tool/tlrelease\n        if: always()"),
    ("later status override", "      - name: verify the domain input", "      - name: verify the domain input\n        if: Always ()"),
    ("later quoted status override", "      - name: verify the domain input", "      - name: verify the domain input\n        'if': failure()"),
    ("later error override", "      - name: verify the domain input", "      - name: verify the domain input\n        continue-on-error: true"),
    ("domain skipped", "      - name: verify the domain input", "      - name: verify the domain input\n        if: false"),
    ("quoted domain skipped", "      - name: verify the domain input", "      - name: verify the domain input\n        'if': false"),
    ("domain shell override", "      - name: verify the domain input", "      - name: verify the domain input\n        shell: bash -c 'true' {0}"),
    ("domain working directory", "      - name: verify the domain input", "      - name: verify the domain input\n        working-directory: other"),
    ("domain shell startup file", "      - name: verify the domain input", "      - name: verify the domain input\n        env:\n          BASH_ENV: other"),
    ("folded step status override", "      - name: verify the domain input", "      - name: verify the domain input\n        if: >-\n          always()"),
    ("literal step status override", "      - name: verify the domain input", "      - name: verify the domain input\n        if: |\n          failure()"),
    ("folded job status override", "  sign:\n", "  sign:\n    if: >-\n      always()\n"),
    ("literal job status override", "  sign:\n", "  sign:\n    if: |\n      failure()\n"),
    ("job error override", "  sign:\n", "  sign:\n    continue-on-error: true\n"),
    ("job shell override", "  sign:\n", "  sign:\n    defaults:\n      run:\n        shell: bash {0}\n"),
    ("inherited shell override", "    shell: bash", "    shell: bash -c 'true' {0}"),
    ("inherited working directory", "    shell: bash", "    shell: bash\n    working-directory: other"),
    ("inherited shell startup file", fileSetDefaults, fileSetDefaults ++ "env:\n  BASH_ENV: other\n"),
    ("job shell startup file", "  sign:\n", "  sign:\n    env:\n      BASH_ENV: other\n"),
    ("another job uploads the tool", "  sign:\n", "  replacement:\n    steps:\n" ++ fileSetUpload ++ "  sign:\n"),
    ("another upload uses wider input indentation", "  sign:\n", "  replacement:\n    steps:\n      - uses: actions/upload-artifact@v4\n        with:\n            name: release-tool\n            path: other\n  sign:\n"),
    ("another upload uses a commented name", "  sign:\n", "  replacement:\n    steps:\n      - uses: actions/upload-artifact@v4\n        with:\n          name: release-tool # comment\n          path: other\n  sign:\n"),
    ("another upload hides its name in flow syntax", "  sign:\n", "  replacement:\n    steps:\n      - uses: actions/upload-artifact@v4\n        with: {name: release-tool, path: other}\n  sign:\n"),
    ("another upload has an unreadable field", "  sign:\n", "  replacement:\n    steps:\n      - uses: actions/upload-artifact@v4\n        'continue-on-error': false\n        with:\n          name: release-tool\n          path: other\n  sign:\n"),
    ("another upload has a quoted steps key", "  sign:\n", "  replacement:\n    'steps':\n      - uses: actions/upload-artifact@v4\n        with:\n          name: release-tool\n          path: other\n  sign:\n"),
    ("another upload has a quoted action", "  sign:\n", "  replacement:\n    steps:\n      - uses: 'actions/upload-artifact@v4'\n        with:\n          name: release-tool\n          path: other\n  sign:\n"),
    ("another upload has an anchored action", "  sign:\n", "  replacement:\n    steps:\n      - uses: &upload actions/upload-artifact@v4\n        with:\n          name: release-tool\n          path: other\n  sign:\n"),
    ("another upload follows duplicate steps", "  sign:\n", "  replacement:\n    steps:\n      - run: true\n    steps:\n      - uses: actions/upload-artifact@v4\n        with:\n          name: release-tool\n          path: other\n  sign:\n"),
    ("missing real consumer", "  publish-npm:", "  unexpected:"),
    ("unmodeled tool execution", "  sign:\n", "  extra-job:\n    steps:\n      - run: ./tool/tlrelease --help\n  sign:\n"),
    ("rehearsal permissions", "    permissions: {}", "    permissions: write-all"),
    ("rehearsal secrets", "    permissions: {}", "    permissions: {}\n    secrets: inherit"),
    ("rehearsal environment", "    permissions: {}", "    permissions: {}\n    environment: release"),
    ("rehearsal credentials", "    permissions: {}", "    permissions: {}\n    env:\n      GH_TOKEN: ${{ github.token }}"),
    ("rehearsal trigger", "github.ref_type == 'branch'", "github.ref_type == 'tag'"),
    ("handoff-only bypass", "    if: github.event_name != 'workflow_dispatch' || !inputs.handoff_only", "")]
  let independent := mutations.filter fun (name, _, _) =>
    ["nested download action", "download destination", "empty expected value allowed", "empty received value allowed",
     "unequal values allowed", "received multiple files", "mismatch ignored",
     "prefix truncated at chmod", "step before entry", "step before domain invocation",
     "early tool execution", "handoff status override", "domain skipped",
     "quoted domain skipped", "domain invocation removed", "domain shell override", "domain working directory",
     "domain shell startup file", "folded step status override", "literal step status override"].contains name
  let withoutRealConsumers :=
    (canonicalFileSetHandoff.splitOn "jobs:\n").headD "" ++ "jobs:\n" ++
    String.join ((jobsOf canonicalFileSetHandoff).map fun (job, lines) =>
      s!"  {job}:\n" ++
      (if job == "gates" || job == "handoff-rehearsal" then String.intercalate "\n" lines else
        (if job == "stamp" then "    if: github.event_name != 'workflow_dispatch' || !inputs.handoff_only\n" else "") ++
        "    steps:\n      - run: true\n") ++ "\n")
  [check "file-set model: zero real consumers cannot satisfy the guard"
    (fileSetRehearsalShape withoutRealConsumers && fileSetRefuses withoutRealConsumers),
   check "file-set model: accepts the complete six-consumer fixture"
    (releaseToolHandoffShape canonicalFileSetHandoff).toOption.isSome
    (match releaseToolHandoffShape canonicalFileSetHandoff with | .ok () => "" | .error message => message)] ++
  (mutations.map fun (name, before, after) =>
    let mutant := swap canonicalFileSetHandoff before after
    check s!"file-set model: refuses {name}"
      (mutant != canonicalFileSetHandoff && fileSetRefuses mutant)) ++
  ((fileSetConsumers.drop 1).flatMap fun job => independent.map fun (name, before, after) =>
    let mutant := mutateFileSetJob job before after
    check s!"file-set model: independently refuses {name} in {job}"
      (mutant != canonicalFileSetHandoff && fileSetRehearsalShape mutant && fileSetRefuses mutant)) ++
  (fileSetConsumers.drop 1).flatMap fun job =>
    let first := "        run: ./tool/tlrelease manifest-verify --dist dist"
    let later := fun condition => first ++ "\n      - name: later domain invocation\n" ++
      "        if: " ++ condition ++ "\n        run: ./tool/tlrelease --help\n"
    let ordinary := mutateFileSetJob job first (later ">-\n          !contains(github.ref_name, '-')")
    [check s!"file-set model: keeps ordinary later conditions in {job}"
      (ordinary != canonicalFileSetHandoff && (releaseToolHandoffShape ordinary).toOption.isSome)] ++
    ["always()", ">-\n          Always ()", "|\n          failure()", ">-\n          !cancelled()"].map fun condition =>
      let mutant := mutateFileSetJob job first (later condition)
      check s!"file-set model: refuses later {condition.trimAscii} in {job}"
        (mutant != canonicalFileSetHandoff && fileSetRehearsalShape mutant && fileSetRefuses mutant)

/-! ## Native errors stay structured

The release writer's phase and errno are values (`release/Write.lean`), and this
row is why they stay values. The prototype recovered the error class by matching
the shim's formatted prose — `":EEXIST:"` inside the message the C side builds —
which quietly makes a sentence part of the contract: reword the message and the
classification stops matching, with nothing failing to say so.

Deliberately lexical, and deliberately about one shape: an errno *name* between
colons is what a formatted `tlsys:<op>:<ERRNO>:` line looks like, and matching
one is the only way to read a class back out of prose. Printing a name is not
this — `Errno.name` renders `"EACCES"` with no colons and nothing reads it
back. -/

/-- The characters an errno name is made of, after the leading `E`. -/
private def isErrnoTail (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- Does the text contain a formatted errno token — `:E` followed by two or
    more capitals and a closing colon?

    Scanned over the whole line rather than only inside string literals: a line
    that mentions the shape in a comment is describing this rule, and the two
    places that do live in `Tests/` and `docs/`, outside what this reads. -/
def classifiesFormattedErrno (line : String) : Bool :=
  ((line.splitOn ":E").drop 1).any fun tail =>
    let name := (tail.takeWhile isErrnoTail).toString
    name.length ≥ 2 && (tail.drop name.length).startsWith ":"

private def formattedErrnoFailures (path : String) (text : String) : List String :=
  ((text.splitOn "\n").zipIdx 1).filterMap fun (line, number) =>
    if classifiesFormattedErrno line then
      some s!"  {path}:{number}: reads a native error class out of formatted text — {line.trimAscii}"
    else none


/-! ## The release scope's native boundary

`release/` may reach exactly one native primitive, and ADR-0028 makes that a
registry rather than a habit: a second FFI declaration, an extra linker input,
or a build recipe reading a different source is a widening of the release
surface, and each of those is invisible to the trust verifier's import audit —
it reads Lean imports and cannot observe a linked object.

Three separate facts, because checking one leaves a substitution gap in the
others. What the release environment *declares*; what the executable *links*;
and what the recipe *compiles* from. -/

/-- One extern declaration: where it is, what it is called, which native symbol
    it binds, and its complete Lean type. -/
private structure ExternRow where
  «module» : Name
  name : Name
  symbols : List String
  signature : String
  deriving DecidableEq, Repr

private def externSymbols (data : Lean.ExternAttrData) : List String :=
  data.entries.filterMap fun entry =>
    match entry with
    | .standard _ symbol => some symbol
    | .inline _ pattern => some pattern
    | .adhoc backend => some s!"adhoc:{backend}"
    | .opaque => some "opaque"

/-- Every extern declaration defined by one of `modules`, read out of the loaded
    environment rather than out of the sources: what the executable binds is
    what was compiled, and a declaration reached through an import this file did
    not think to read would be invisible to a source scan. -/
private def externRowsOf (env : Environment) (modules : Array Name) : Array ExternRow :=
  let imported := env.allImportedModuleNames
  let selected := modules.foldl (·.insert ·) (∅ : Std.HashSet Name)
  let rows := env.constants.fold (init := #[]) fun rows name info =>
    match env.getModuleIdxFor? name with
    | none => rows
    | some idx =>
      if h : idx.toNat < imported.size then
        let definingModule := imported[idx.toNat]
        if selected.contains definingModule then
          match Lean.getExternAttrData? env name with
          | none => rows
          | some data =>
              rows.push {
                «module» := definingModule
                name := name
                symbols := externSymbols data
                signature := toString info.type }
        else rows
      else rows
  rows.qsort fun left right => Name.lt left.name right.name

/-- The complete release FFI registry. One row, and widening it is a deliberate
    change to this list, ADR-0019 and ADR-0028 together — not a new
    `@[extern]` somebody added to a release module. -/
private def pinnedReleaseExterns : List ExternRow :=
  [{ «module» := `release.Sys,
     -- The raw array-taking declaration is private: release code can reach
     -- the symbol only through `Release.Sys.mechanism`, whose arguments are
     -- the sealed base and component-list types. Pin the compiled private name
     -- too, so making that unsafe wire public is itself a registry change.
     name := Name.mkStr
       (Name.mkStr (Name.mkStr (Name.mkNum `_private.release.Sys 0) "Release") "Sys")
       "releaseWriteAtomic",
     symbols := ["tl_release_write_atomic"],
     signature :=
       "([mdata borrowed:1 String]) -> ([mdata borrowed:1 Array.{0} String]) -> " ++
       "([mdata borrowed:1 ByteArray]) -> (IO (Array.{0} UInt32))" }]

/-- A symbol belonging to the product's own primitives. Release administration
    is not part of the product TCB, so a release binding to one of these is that
    boundary crossed in the one direction nothing else observes. -/
private def isProductSymbol (symbol : String) : Bool := symbol.startsWith "tl_sys_"

private unsafe def releaseExternRows : IO (List Outcome) := do
  let release ← loadScope auditLayout .release
  let modules ← release.projectModules
  let rows := externRowsOf release.env modules
  let offRegistry := rows.toList.filter fun row => !pinnedReleaseExterns.contains row
  let productBound := rows.toList.filter fun row => row.symbols.any isProductSymbol
  let elsewhere := rows.toList.filter fun row => row.«module» != `release.Sys
  return [
    check "release natives: the scan read the release scope's modules"
      (modules.size ≥ 10) s!"the loaded release scope had {modules.size} project module(s)",
    checkEq "release natives: the release scope declares exactly the pinned externs"
      rows.toList pinnedReleaseExterns,
    check "release natives: no extern outside the registry"
      offRegistry.isEmpty
      (s!"{repr offRegistry}\nAn FFI declaration is a widening of the release surface the trust verifier cannot see: it audits Lean imports and cannot observe a linked symbol. Add it to pinnedReleaseExterns, state its release contract, and amend ADR-0019 in the same change."),
    check "release natives: no release binding to a product primitive"
      productBound.isEmpty
      (s!"{repr productBound}\nrelease/ is not part of the product TCB. Bind a tl_release_* symbol, or move the code that needs the product under Tl/."),
    check "release natives: every extern lives in the one module that is the wire"
      elsewhere.isEmpty
      (s!"{repr elsewhere}\nrelease/Sys.lean is release administration's whole native boundary; a binding anywhere else is a second one nothing reads together with the first.")]

/-! ### What the executable links, and what the recipe compiles

Read from `lakefile.lean` lexically, because that is where both facts are
written. Pinning only the source bindings would leave the object free to be
swapped; pinning only the object would leave the recipe free to compile it from
somewhere else. -/

private def linesOf (text : String) : List String := text.splitOn "\n"

/-- The lines that actually attach a native object, which is the assignment and
    not the sentence in the header explaining why it is the one Lake still
    supports. -/
private def linkObjectLines (lakefile : String) : List String :=
  (linesOf lakefile).filterMap fun line =>
    let line := line.trimAscii.toString
    if line.startsWith "moreLinkObjs" then some line else none

private def occurrences (text needle : String) : Nat := (text.splitOn needle).length - 1

private def staticReleaseRecipe : String := r#"pkg : System.FilePath := do
  let some exe := pkg.findLeanExe? `tlrelease
    | error "Restore the tlrelease executable before building its static package."
  let infoJob ← exe.root.linkInfoNoExport.fetch
  infoJob.mapM fun info => do
    let lean ← getLeanInstall
    let objects ← mkLinkArgs info.objs info.libs (linkDeps := true)
    let flags := lean.linkStaticFlags.map fun flag =>
      if flag == "-Wl,-Bdynamic" then "-Wl,-Bstatic" else flag
    let args := objects ++ exe.exeOnlyLinkArgs ++ info.args ++
      #["-static", "-L", lean.leanLibDir.toString, "-L", lean.systemLibDir.toString] ++ flags
    addLeanTrace
    addPlatformTrace
    addPureTrace args "static release linker arguments"
    let output := pkg.buildDir / "bin" / "tlrelease-static"
    let artifact ← buildArtifactUnlessUpToDate output (exe := true) do
      compileExe output args "gcc"
    return artifact.path"#

private def staticReleaseRecipeAllowed (lakefile : String) : Bool :=
  match lakefile.splitOn "\ntarget tlreleaseStatic " with
  | [_, suffix] => ((suffix.splitOn "\n/--").headD "").trimAsciiEnd.toString == staticReleaseRecipe
  | _ => false

private def staticReleaseRecipeRows (lakefile : String) : List Outcome :=
  [check "static release: the complete packaging recipe is pinned" (staticReleaseRecipeAllowed lakefile)] ++
  [ ("wrong executable", "pkg.findLeanExe? `tlrelease", "pkg.findLeanExe? `tl"),
    ("missing native graph", "mkLinkArgs info.objs info.libs", "mkLinkArgs #[] info.libs"),
    ("dynamic runtime", "then \"-Wl,-Bstatic\"", "then \"-Wl,-Bdynamic\""),
    ("bundled compiler sysroot", "lean.linkStaticFlags.map", "lean.ccLinkStaticFlags.map"),
    ("dynamic executable", "#[\"-static\", \"-L\"", "#[\"-L\""),
    ("bundled library path", "lean.systemLibDir.toString", "\"/tmp/unreviewed\""),
    ("untraced recipe", "addPureTrace args", "addPureTrace (#[] : Array String)"),
    ("wrong compiler", "compileExe output args \"gcc\"", "compileExe output args \"clang\"") ].flatMap fun (label, before, after) =>
      let mutated := lakefile.replace before after
      [check s!"static release: {label} mutation is real" (mutated != lakefile),
       check s!"static release: {label} is refused" (!staticReleaseRecipeAllowed mutated)]

private def nativeBuildRows (lakefile : String) : List Outcome :=
  let objects := linkObjectLines lakefile
  [ -- Every executable that links a native object links the same one, and it is
    -- the in-repository shim ADR-0019 records.
    check "release natives: every linked native object is the in-repository shim"
      (objects.all fun line => line == "moreLinkObjs := #[`@/tlsys.o]")
      s!"{objects}",
    check "release natives: the three executables that need the shim link it"
      (objects.length == 3) s!"{objects.length} target(s) declare moreLinkObjs: {objects}",
    -- The recipe. One custom target, compiling exactly one source.
    check "release natives: the shim is compiled from exactly ffi/tlsys.c"
      (occurrences lakefile "inputTextFile <| pkg.dir / \"ffi\" / \"tlsys.c\"" == 1)
      "the tlsys.o recipe must read exactly one source, and it is ffi/tlsys.c",
    check "release natives: only the shim and static packaging targets exist"
      (occurrences lakefile "\ntarget " == 2 &&
        occurrences lakefile "\ntarget tlreleaseStatic pkg : System.FilePath := do" == 1)
      "pin every custom target; static packaging must reuse the existing object graph",
    check "release natives: and it is tlsys.o"
      (occurrences lakefile "\ntarget tlsys.o pkg : System.FilePath := do" == 1)
      "the custom target's name and shape are part of what the release links",
    -- `extern_lib` is the other way to attach native code, and it is the one
    -- that would not show up as a `moreLinkObjs` line at all.
    check "release natives: no external library is attached another way"
      (occurrences lakefile "extern_lib " == 0)
      "extern_lib attaches native code without a moreLinkObjs line, so it would pass every row above"]

/-! ## The rows -/

unsafe def releaseDriftTests : IO (List Outcome) := do
  let nativeRows ←
    match ← (findSysroot : IO FilePath).toBaseIO with
    | .error _ =>
        pure [check "release natives: extern registry skipped — no Lean toolchain on this host" true]
    | .ok sysroot => do
        initSearchPath sysroot
        try releaseExternRows
        catch error =>
          pure [check "release natives: the release scope can be loaded" false
            s!"{error}; run `lake exe tltest` from the repository root after `lake build`"]
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
  let releaseSources ← filesUnder "release" ["lean"]
  let mut formattedErrnoFailureRows : List String := []
  for path in releaseSources do
    let text ← IO.FS.readFile path
    formattedErrnoFailureRows :=
      formattedErrnoFailureRows ++ formattedErrnoFailures path.toString text
  let formattedErrnoRows : List Outcome :=
    [check "release errors: no release source classifies a native error by its formatted text"
      formattedErrnoFailureRows.isEmpty
      (String.intercalate "\n" formattedErrnoFailureRows ++
        "\nThe native side reports a phase and an errno as numbers, decoded by release/Write.lean. Matching the formatted message instead makes a sentence part of the contract, so rewording it silently stops the classification without failing a build."),
     check "release errors: the scan read release sources to check"
       (releaseSources.size ≥ 10) s!"found {releaseSources.size} release source(s)"]
  let releaseWorkflow ← IO.FS.readFile ".github/workflows/release.yml"
  let ciWorkflow ← IO.FS.readFile ".github/workflows/ci.yml"
  let lakefile ← IO.FS.readFile "lakefile.lean"
  let hermeticExecutionRows := ["if: false", "continue-on-error: true", "container: alpine", "environment: release"].flatMap fun field =>
    [check s!"hermetic release: job-level `{field}` is refused"
       ((hermeticReleaseShape (swap canonicalHermeticWorkflow "    timeout-minutes: 20\n"
         s!"    timeout-minutes: 20\n    {field}\n")).toOption.isNone),
     check s!"hermetic release: step-level `{field}` is refused"
       ((hermeticReleaseShape (swap canonicalHermeticWorkflow "        run: ./.lake/build/bin/tlrelease hermetic"
         s!"        {field}\n        run: ./.lake/build/bin/tlrelease hermetic")).toOption.isNone)]
  return workflowParserTests ++ fileSetMutationTests ++ documentRows ++ formattedErrnoRows ++ nativeRows ++ nativeBuildRows lakefile ++ staticReleaseRecipeRows lakefile
    ++ hermeticExecutionRows ++ [
    -- The detector, on the shape it exists to catch and on the shapes it must
    -- leave alone. Without these a detector that matched nothing would report
    -- the same clean result as a release layer that classifies nothing.
    check "release errors: the prototype's own classification is recognised"
      (classifiesFormattedErrno "    if (error.toString.splitOn \":EEXIST:\").length > 1 then"),
    check "release errors: another errno spelled the same way is recognised"
      (classifiesFormattedErrno "  let occupied := message.splitOn \":ENOTOWNED:\""),
    check "release errors: the shim's whole formatted prefix is recognised"
      (classifiesFormattedErrno "  if message.startsWith \"tlsys:rename:EIO: \" then"),
    check "release errors: rendering an errno name is not classifying one"
      (!classifiesFormattedErrno "  | .eacces => \"EACCES\""),
    check "release errors: a ratio written with a colon is not one"
      (!classifiesFormattedErrno "-- the 3:1 ratio the perf rows pin"),
    check "release errors: a single capital after a colon is not an errno name"
      (!classifiesFormattedErrno "  s!\"{what}:E: something\""),
    check "release errors: a name with no closing colon is not the formatted shape"
      (!classifiesFormattedErrno "  -- ENOSPC and EDQUOT both mean the same fix"),
    check "release workflow: every consumer instantiates the release-tool handoff prefix"
      (releaseToolHandoffShape releaseWorkflow).toOption.isSome
      (match releaseToolHandoffShape releaseWorkflow with
       | .ok () => ""
       | .error message => message),
    check "git floor: the release command is uploaded and made executable"
      (gitFloorReleaseToolShape ciWorkflow),
    check "git floor: omitting the release command from the artifact is refused"
      (!gitFloorReleaseToolShape
        (swap ciWorkflow "            .lake/build/bin/tlrelease\n" "")),
    check "git floor: omitting the release command's executable permission is refused"
      (!gitFloorReleaseToolShape
        (swap ciWorkflow "tltestWorker .lake/build/bin/tlrelease" "tltestWorker")),
    check "git floor: a missing producer job cannot pass the handoff guard"
      (!gitFloorReleaseToolShape (swap ciWorkflow "  build-and-test:" "  renamed-build:")),
    check "git floor: a missing consumer job cannot pass the handoff guard"
      (!gitFloorReleaseToolShape (swap ciWorkflow "  git-floor:" "  renamed-floor:")),
    check "git floor: a missing upload step cannot pass the handoff guard"
      (!gitFloorReleaseToolShape
        (swap ciWorkflow "name: upload binaries for the git-floor job" "name: renamed upload")),
    check "git floor: a missing test step cannot pass the handoff guard"
      (!gitFloorReleaseToolShape
        (swap ciWorkflow "name: run the suite under git 2.17" "name: renamed test")),
    -- Non-vacuity against the live file, which the fixtures cannot give: the
    -- scan finds consumers by what they do, so a parser that stopped reading
    -- the download step would report a clean workflow having checked one job.
    -- Five is what release.yml has — stamp, sign and the three publish jobs —
    -- and a sixth is a change to make deliberately. `stamp` joined when the
    -- build provenance moved into `tlrelease`: it runs the tool, so it
    -- validates the bytes it received like every other consumer.
    checkEq "release workflow: the scan reads all five real consumers and the rehearsal"
      (releaseToolConsumers releaseWorkflow)
      ["handoff-rehearsal", "stamp", "sign", "publish-release", "publish-homebrew", "publish-npm"],
    check "file-set handoff: the capability-free rehearsal and producer are pinned"
      (fileSetRehearsalShape releaseWorkflow),
    check "file-set handoff: a publication-capable rehearsal is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow "    permissions: {}" "    permissions: write-all")),
    check "file-set handoff: a producer reading a wildcard is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow "hashFiles('release-tool/tlrelease')" "hashFiles('release-tool/*')")),
    check "file-set handoff: changing the producer mapping is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow "steps.tool_file_set_hash.outputs.fileSetHash" "steps.tool.outputs.digest")),
    check "file-set handoff: an output mapping under env is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow "    outputs:" "    env:")),
    check "file-set handoff: hashing before staging is refused"
      (!fileSetRehearsalShape (swap (swap releaseWorkflow fileSetProducer "") fileSetStage (fileSetProducer ++ fileSetStage))),
    check "file-set handoff: a step inserted after staging is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow fileSetStage (fileSetStage ++ "      - run: true\n"))),
    check "file-set handoff: removing the dispatch input is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow handoffOnlyInput "  workflow_dispatch:\n")),
    check "file-set handoff: running the matrix on a handoff-only dispatch is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow "    if: github.event_name != 'workflow_dispatch' || !inputs.handoff_only" "")),
    check "file-set handoff: skipping the empty expectation refusal is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow "needs.gates.outputs.releaseToolFileSetHash == '' || " "")),
    check "file-set handoff: skipping the empty download refusal is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow "hashFiles('tool/tlrelease') == '' || " "")),
    check "file-set handoff: swallowing a mismatch is refused"
      (!fileSetRehearsalShape (swap releaseWorkflow "run: /usr/bin/false" "run: /usr/bin/true")),
    check "file-set handoff: stopping at chmod is not a complete prefix"
      (!fileSetRehearsalShape (swap releaseWorkflow "        run: ./tool/tlrelease --help" "        run: true")),
    check "file-set handoff: a status override cannot enter the rehearsal"
      (!fileSetRehearsalShape (swap releaseWorkflow "run: /bin/chmod 0755 tool/tlrelease" "run: /bin/chmod 0755 tool/tlrelease\n        if: always()")),
    -- Non-vacuity, both halves. A walk that found no documents, or no script
    -- under the rule, reports the same clean result as a repository that
    -- satisfies it.
    check "release docs: the scan read documented invocations to check"
      (documented ≥ 4) s!"found {documented} documented invocation(s) with arguments",
    check "hermetic release: the live CI workflow has the pinned job shape"
      (hermeticReleaseShape ciWorkflow).toOption.isSome
      (match hermeticReleaseShape ciWorkflow with
       | .ok () => ""
       | .error message => message),
    check "hermetic release: the canonical fixture is accepted"
      (hermeticReleaseShape canonicalHermeticWorkflow).toOption.isSome
      (match hermeticReleaseShape canonicalHermeticWorkflow with
       | .ok () => ""
       | .error message => message),
    check "hermetic release: a missing job is refused"
      (hermeticReleaseShape "jobs:\n").toOption.isNone,
    check "hermetic release: duplicate jobs are refused"
      (hermeticReleaseShape (canonicalHermeticWorkflow ++ "  hermetic-release:\n")).toOption.isNone,
    check "hermetic release: an unpinned checkout is refused"
      (hermeticReleaseShape (swap canonicalHermeticWorkflow
        "actions/checkout@9c091bb21b7c1c1d1991bb908d89e4e9dddfe3e0" "actions/checkout@main")).toOption.isNone,
    check "hermetic release: an unpinned toolchain action is refused"
      (hermeticReleaseShape (swap canonicalHermeticWorkflow
        "leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9" "leanprover/lean-action@main")).toOption.isNone,
    check "hermetic release: no-op build is refused"
      (hermeticReleaseShape (swap canonicalHermeticWorkflow "lake build tlrelease --wfail" "true")).toOption.isNone,
    check "hermetic release: no-op runner is refused"
      (hermeticReleaseShape (swap canonicalHermeticWorkflow
        "./.lake/build/bin/tlrelease hermetic --root ." "true")).toOption.isNone,
    check "hermetic release: swallowed failure is refused"
      (hermeticReleaseShape (swap canonicalHermeticWorkflow
        "hermetic --root ." "hermetic --root . || true")).toOption.isNone,
    check "hermetic release: a second outer step is refused"
      (hermeticReleaseShape (canonicalHermeticWorkflow ++
        "      - name: after the boundary\n        run: true\n")).toOption.isNone,
    -- The checker itself, on the drift it exists to catch and on the shapes it
    -- must leave alone. Without these rows a guard that accepted everything
    -- would report the same clean result as the repository being clean.
    check "release docs: the stale form this guard was written for is rejected"
      ((documentedVerdict "tlrelease policy --strict").toOption.isNone),
    check "release docs: the complete form is accepted"
      ((documentedVerdict "tlrelease policy --profile ci --strict").toOption.isSome),
    check "release docs: naming a command without invoking it is prose"
      ((documentedVerdict "tlrelease prereqs").toOption.isSome),
    check "release docs: naming the tool alone is prose"
      ((documentedVerdict "tlrelease").toOption.isSome),
    check "release docs: a command this build does not offer is rejected"
      ((documentedVerdict "tlrelease unknown-policy --root .").toOption.isNone),
    -- The wrapper forms a reader can copy. Each is the same command, and a
    -- guard that only knew the bare name let three stale spellings through.
    check "release docs: a stale invocation behind `lake exe` is rejected"
      ((documentedVerdict "lake exe tlrelease policy --strict").toOption.isNone),
    check "release docs: a stale invocation behind the built path is rejected"
      ((documentedVerdict "./.lake/build/bin/tlrelease policy --strict").toOption.isNone),
    check "release docs: a stale invocation separated by a tab is rejected"
      ((documentedVerdict "tlrelease\tpolicy --strict").toOption.isNone),
    check "release docs: naming the built path without arguments is prose"
      ((documentedVerdict "./.lake/build/bin/tlrelease").toOption.isSome),
    check "release docs: another executable's span is not read as one of these"
      ((documentedVerdict "lake exe tltest --root .").toOption.isSome),
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
