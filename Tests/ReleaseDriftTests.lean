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
import Verify.Environment
import release.Cli

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

What is deliberately *not* here: ADR-0028's end-state prefix, whose comparison
is `releaseToolFileSetHash` against `hashFiles`, whose mismatch arm is the
canonical `/usr/bin/false` step, and which a dedicated capability-free rehearsal
consumer also instantiates. That lands with the workflow cutover, and it needs a
real hosted run first — `hashFiles`' file-selection semantics are not something
local parsing can establish. The model below is written over the migration
shape and names the transition in one place, so the cutover edits a value rather
than a scan. -/

/-- One step of a job, as much of it as this model reads. -/
private structure Step where
  /-- Its `name:`, or the empty string for a bare `uses:` step. -/
  name : String
  /-- The `uses:` reference, if it is an action step. -/
  uses : Option String
  /-- Every line of the step, so a `run:` body can be read as text. -/
  lines : List String

/-- Whether the step's body mentions the text — its `run:` script and `with:`
    block included. -/
private def Step.mentions (step : Step) (needle : String) : Bool :=
  step.lines.any fun line => (line.splitOn needle).length > 1

/-- The step's body with comment lines dropped.

    The distinction the old guard could not make: a canonical string inside a
    `#` comment describes the rule, and one in a command obeys it. A guard that
    reads both alike can be satisfied by writing the sentence down. -/
private def Step.code (step : Step) : List String :=
  step.lines.filter fun line => !(line.trimAscii.toString.startsWith "#")

private def Step.runs (step : Step) (needle : String) : Bool :=
  step.code.any fun line => (line.splitOn needle).length > 1

/-- Split one job's lines into its steps. A step begins at a `- name:` or
    `- uses:` item under `steps:`; everything up to the next one is its body. -/
private def stepsOf (jobLines : List String) : List Step := Id.run do
  let mut steps : List Step := []
  let mut current : Option Step := none
  let mut inSteps := false
  for line in jobLines do
    let body := line.trimAscii.toString
    if body == "steps:" then
      inSteps := true
      continue
    if !inSteps then continue
    if body.startsWith "- " then
      if let some step := current then steps := steps ++ [{ step with lines := step.lines.reverse }]
      let head := (body.drop 2).toString
      let named := if head.startsWith "name:" then (head.drop 5).toString.trimAscii.toString else ""
      let used := if head.startsWith "uses:" then some (head.drop 5).toString.trimAscii.toString
                  else none
      current := some { name := named, uses := used, lines := [line] }
    else if let some step := current then
      -- A `uses:` on its own line belongs to the step being read.
      let used := if body.startsWith "uses:" then some (body.drop 5).toString.trimAscii.toString
                  else step.uses
      current := some { step with uses := used, lines := line :: step.lines }
  if let some step := current then steps := steps ++ [{ step with lines := step.lines.reverse }]
  return steps

/-- The workflow's top-level jobs, each with its lines. -/
private def jobsOf (workflow : String) : List (String × List String) := Id.run do
  let mut jobs : List (String × List String) := []
  let mut current : Option (String × List String) := none
  let mut inJobs := false
  for line in workflow.splitOn "\n" do
    if !inJobs then
      if line == "jobs:" then inJobs := true
      continue
    if line != "" && !line.startsWith " " && !line.startsWith "#" then break
    let isHeader := line.startsWith "  " && !line.startsWith "   "
      && (line.trimAscii.toString.splitOn ":").length > 1
      && !line.trimAscii.toString.startsWith "#"
      && !line.trimAscii.toString.startsWith "- "
    if isHeader then
      if let some (name, ls) := current then jobs := jobs ++ [(name, ls.reverse)]
      let name := ((line.trimAscii.toString.splitOn ":").headD "")
      current := some (name, [])
    else if let some (name, ls) := current then
      current := some (name, line :: ls)
  if let some (name, ls) := current then jobs := jobs ++ [(name, ls.reverse)]
  return jobs

/-! ## The nested hermetic release job

The inner container is evidence only because the outer invocation gives it no
authority. Its image, mounts, identity, network, capabilities, entry point and
environment are therefore one exact argv rather than individually interesting
substrings. The command body has a smaller structural contract: it must prove
the negative and positive inventories before running the release profile and
all retained-adapter suites. -/

private def hermeticImage : String :=
  "docker.io/alpine/git@sha256:53a6239398162098fed2f49a46512f9cbba9e3f31b9f2cea4fa90129ee069a99"

private def hermeticEnvironment : List String :=
  [s!"HERMETIC_IMAGE: {hermeticImage}",
   "ACTIONLINT_VERSION: \"1.7.12\"",
   "ACTIONLINT_SHA256: \"8aca8db96f1b94770f1b0d72b6dddcb1ebb8123cb3712530b08cc387b349a3d8\"",
   "SHELLCHECK_VERSION: \"0.11.0\"",
   "SHELLCHECK_SHA256: \"8c3be12b05d5c177a04c29e3c78ce89ac86f1595681cab149b65b97c4e227198\"",
   "HERMETIC_REQUIRED_TOOLS: \"awk basename cat chmod cp cut dirname env find git grep head id ln ls mkdir mktemp mv pwd readlink rm sed sha256sum sh shellcheck sleep sort stat tail tar touch tr uname wc actionlint\"",
   "HERMETIC_FORBIDDEN_RUNTIMES: \"python python3 ruby brew node npm\""]

/-- The complete Podman configuration argv, through the start of the one
    inner command argument. An insertion anywhere before the image changes
    this list; after the image, words belong to `/bin/sh`, not Podman. -/
private def hermeticPodmanPrefix : List String :=
  ["podman run --rm \\",
   "--platform linux/amd64 \\",
   "--network none \\",
   "--read-only \\",
   "--read-only-tmpfs=false \\",
   "--cap-drop ALL \\",
   "--security-opt no-new-privileges \\",
   "--uidmap 0:0:1 \\",
   "--gidmap 0:0:1 \\",
   "--user 0:0 \\",
   "--mount \"type=bind,source=$GITHUB_WORKSPACE,target=/workspace,readonly\" \\",
   "--mount \"type=bind,source=$scratch,target=/scratch\" \\",
   "--mount \"type=bind,source=$scratch/lib64,target=/lib64\" \\",
   "--workdir /workspace \\",
   "--env HOME=/scratch/home \\",
   "--env TMPDIR=/scratch/tmp \\",
   "--env HERMETIC_CURL_LOG=/scratch/curl-reached \\",
   "--env \"HERMETIC_REQUIRED_TOOLS=$HERMETIC_REQUIRED_TOOLS\" \\",
   "--env \"HERMETIC_FORBIDDEN_RUNTIMES=$HERMETIC_FORBIDDEN_RUNTIMES\" \\",
   "--env PATH=/scratch/tools:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \\",
   "--entrypoint /bin/sh \\",
   "\"$HERMETIC_IMAGE\" -eu -c '"]

private def hermeticBodyFragments : List String :=
  ["[ \"$(podman info --format '{{.Host.Security.Rootless}}')\" = true ]",
   "pack ./npm/tl --ignore-scripts --pack-destination \"$scratch/packed\"",
   "tar -xzf \"$scratch/packed/taskloop-tl-0.0.0.tgz\" -C \"$scratch/packed\" package/bin/tl",
   "cmp npm/tl/bin/tl \"$scratch/packed/package/bin/tl\"",
   "source_launcher=/scratch/packed/package/bin/tl",
   "sha256sum \"$scratch/packed/package/bin/tl\"",
   "echo \"${ACTIONLINT_SHA256}  $scratch/actionlint.tar.gz\" | sha256sum -c -",
   "echo \"${SHELLCHECK_SHA256}  $scratch/shellcheck.tar.xz\" | sha256sum -c -"]

/-- The complete inner program, including each refusal and final invocation.
    Exact lines and ordering prevent a lint argument or a swallowed failure
    from standing in for execution. -/
private def hermeticInnerBody : List String :=
  ["[ \"$(id -u)\" = \"$(stat -c %u /scratch)\" ]",
   "[ \"$(id -g)\" = \"$(stat -c %g /scratch)\" ]",
   ": > /scratch/write-probe",
   "if ( : > /workspace/.hermetic-write-probe ) 2>/dev/null; then",
   "echo \"hermetic release: the checkout mount is writable\" >&2",
   "exit 1",
   "fi",
   "[ ! -e /var/run/docker.sock ] || {",
   "echo \"hermetic release: a container-engine socket entered the inner container\" >&2",
   "exit 1",
   "}",
   "[ ! -e /run/podman/podman.sock ]",
   "[ ! -e /run/user/0/podman/podman.sock ]",
   "for runtime in $HERMETIC_FORBIDDEN_RUNTIMES; do",
   "if command -v \"$runtime\" >/dev/null 2>&1; then",
   "echo \"hermetic release: forbidden runtime $runtime is on PATH\" >&2",
   "exit 1",
   "fi",
   "hits=$(find / -xdev \\( -type f -o -type l \\) \\( -name \"$runtime\" -o -name \"$runtime[0-9]*\" -o -name nodejs \\) -print)",
   "[ -z \"$hits\" ] || {",
   "echo \"hermetic release: forbidden runtime $runtime exists in the image: $hits\" >&2",
   "exit 1",
   "}",
   "done",
   "for tool in $HERMETIC_REQUIRED_TOOLS curl; do",
   "command -v \"$tool\" >/dev/null 2>&1 || {",
   "echo \"hermetic release: required input $tool is absent\" >&2",
   "exit 1",
   "}",
   "printf \"hermetic input: %s=%s\\n\" \"$tool\" \"$(command -v \"$tool\")\"",
   "done",
   "sha256sum -c /scratch/positive-inputs.sha256",
   "git --version",
   "shellcheck --version",
   "actionlint -version",
   "shellcheck -S warning -s sh /scratch/tools/curl /scratch/launcher-suite",
   "./scripts/check-release-policy.sh --profile release --strict",
   "[ -s \"$HERMETIC_CURL_LOG\" ] || {",
   "echo \"hermetic release: the declared curl fixture was never reached\" >&2",
   "exit 1",
   "}",
   "/scratch/launcher-suite",
   "echo \"hermetic release: policy and all three retained-adapter suites passed\""]

private def suffixAt (needle : String) : List String → Option (List String)
  | [] => none
  | line :: rest => if line == needle then some (line :: rest) else suffixAt needle rest

private def hermeticOccurrences (text needle : String) : Nat :=
  (text.splitOn needle).length - 1

def hermeticReleaseShape (workflow : String) : Except String Unit := do
  let jobs := jobsOf workflow
  let matching := jobs.filter fun (name, _) => name == "hermetic-release"
  if matching.length != 1 then
    throw s!"the workflow has {matching.length} hermetic-release jobs; exactly one owns the dependency-budget evidence"
  let (_, jobLines) := matching.head!
  let normalized := jobLines.map (·.trimAscii.toString)
  for forbidden in ["if:", "continue-on-error:", "container:", "environment:"] do
    if normalized.any (·.startsWith forbidden) then
      throw s!"the hermetic-release job must not override execution with `{forbidden}`"
  for expected in ["runs-on: ubuntu-latest", "timeout-minutes: 20"] ++ hermeticEnvironment do
    if !normalized.contains expected then
      throw s!"the hermetic-release job does not pin `{expected}`"
  let steps := stepsOf jobLines
  if steps.length != 2 then
    throw s!"the hermetic-release job has {steps.length} steps; it must be one pinned checkout action and one ordinary run step"
  let checkoutSteps := steps.filter fun step =>
    step.uses.any (· == "actions/checkout@9c091bb21b7c1c1d1991bb908d89e4e9dddfe3e0 # v7.0.0")
  if checkoutSteps.length != 1 then
    throw "the hermetic-release job does not have exactly one pinned checkout action"
  let runSteps := steps.filter fun step => step.runs "podman run --rm"
  let [step] := runSteps
    | throw s!"the hermetic-release job has {runSteps.length} steps launching Podman; exactly one ordinary run step must own the complete invocation"
  if hermeticOccurrences (String.intercalate "\n" step.code) "podman run" != 1 then
    throw "the hermetic-release run step launches Podman more than once"
  let code := step.code.map (·.trimAscii.toString)
  let some suffix := suffixAt hermeticPodmanPrefix.head! code
    | throw "the hermetic-release run step has no canonical Podman invocation"
  let actual := suffix.take hermeticPodmanPrefix.length
  if actual != hermeticPodmanPrefix then
    throw s!"the hermetic Podman argv drifted; expected {hermeticPodmanPrefix}, got {actual}"
  for fragment in hermeticBodyFragments do
    if !code.contains fragment then
      throw s!"the hermetic-release run step no longer executes `{fragment}`"
  if (suffix.drop hermeticPodmanPrefix.length).filter (· != "") != hermeticInnerBody ++ ["'"] then
    throw "the hermetic-release inner evidence program drifted; preserve its checks, refusal arms and suite invocations in order"
  pure ()

private def canonicalHermeticWorkflow : String :=
  "jobs:\n" ++
  "  hermetic-release:\n" ++
  "    runs-on: ubuntu-latest\n" ++
  "    timeout-minutes: 20\n" ++
  "    env:\n" ++
  String.join (hermeticEnvironment.map fun line => s!"      {line}\n") ++
  "    steps:\n" ++
  "      - uses: actions/checkout@9c091bb21b7c1c1d1991bb908d89e4e9dddfe3e0 # v7.0.0\n" ++
  "      - name: runtime-stripped release policy and retained-adapter suites\n" ++
  "        run: |\n" ++
  String.join ((hermeticBodyFragments ++ hermeticPodmanPrefix ++ hermeticInnerBody ++ ["'"]).map fun line => s!"          {line}\n")

private def hermeticRefuses (workflow needle : String) : Bool :=
  match hermeticReleaseShape workflow with
  | .ok () => false
  | .error message => (message.splitOn needle).length > 1

/-! ### The names this handoff is made of

Every literal the model matches on, in one place. The cutover replaces the
digest transition below with the file-set hash and this list is where it is
edited; a scan spread through the rows would be edited in six. -/

/-- Where the gated binary is staged to, and therefore what is hashed and
    uploaded. Non-hidden deliberately: `upload-artifact` excludes files below a
    dot-directory, so uploading from `.lake/` found no file at all while the
    build and the digest before it both succeeded. -/
private def stagedToolPath : String := "release-tool/tlrelease"

private def gatedToolPath : String := ".lake/build/bin/tlrelease"

/-- The artifact the tool travels in. -/
private def toolArtifactName : String := "release-tool"

/-- Where a consumer receives it. Necessarily different from the staging path:
    the producer stages into the workspace it built in, and the consumer
    downloads into its own. -/
private def consumerToolPath : String := "tool/tlrelease"

/-- The job output carrying the expectation, and the step that produces it.

    `releaseToolDigest` is a raw SHA-256 throughout the migration and keeps that
    meaning until it is removed; ADR-0028's `releaseToolFileSetHash` is a
    `hashFiles` result over a one-file set and is deliberately a *different*
    name, because the two are not comparable values. -/
private def toolDigestOutput : String := "releaseToolDigest"

private def toolDigestProducer : String := "tool"

private def uploadAction : String := "actions/upload-artifact@"

private def downloadAction : String := "actions/download-artifact@"

/-! ### The producer

One job stages the gated binary, one step hashes exactly those bytes into one
named output, and one pinned action uploads exactly that path under the artifact
name every consumer downloads. -/

private def producerFailures (jobs : List (String × List String)) : List String := Id.run do
  let mut failures : List String := []
  let some gates := jobs.lookup "gates"
    | return ["the workflow has no `gates` job, which is where the release tool is built and handed off"]
  let steps := stepsOf gates
  -- Staged from the gated binary into the non-hidden artifact path, in code
  -- rather than in a comment describing it. Counted over the job's command
  -- lines rather than over the steps carrying them, so a second copy inside one
  -- step is the same finding as a second step: what must be true is that one
  -- command decides what the uploaded bytes are.
  let staging := (steps.flatMap (·.code)).filter fun line =>
    (line.splitOn s!"install -D -m 0755 {gatedToolPath} {stagedToolPath}").length > 1
  if staging.length != 1 then
    failures := failures ++
      [s!"the gates job stages the release tool {staging.length} time(s); exactly one command must copy {gatedToolPath} to {stagedToolPath}, because that path is what is hashed and what is uploaded"]
  -- Hashed, by the step whose id the job output names, over the staged path.
  let producers := steps.filter fun step =>
    step.mentions s!"id: {toolDigestProducer}" && step.runs s!"sha256sum {stagedToolPath}"
  if producers.length != 1 then
    failures := failures ++
      [s!"the gates job has {producers.length} step(s) with `id: {toolDigestProducer}` hashing {stagedToolPath}; the expectation every consumer compares against must be produced once, from the bytes that were staged"]
  -- Published as the job output the consumers read, from that step.
  let mapping := toolDigestOutput ++ ": ${{ steps." ++ toolDigestProducer ++ ".outputs.digest }}"
  if !gates.any fun line => (line.splitOn mapping).length > 1 then
    failures := failures ++
      ["the gates job does not map `" ++ toolDigestOutput ++ "` to the digest step's output; a consumer reading an output nothing produces gets the empty string, and an empty expectation must not pass for a matching one"]
  -- Uploaded from that same path, under that name, by the pinned action.
  let uploads := steps.filter fun step =>
    (step.uses.getD "").startsWith uploadAction && step.mentions s!"name: {toolArtifactName}"
  match uploads with
  | [upload] =>
      if !upload.mentions s!"path: {stagedToolPath}" then
        failures := failures ++
          [s!"the step uploading the `{toolArtifactName}` artifact does not upload {stagedToolPath}; it must upload exactly the bytes that were staged and hashed"]
      if upload.mentions s!"path: {gatedToolPath}" then
        failures := failures ++
          [s!"the `{toolArtifactName}` artifact is uploaded from {gatedToolPath}, which is below a dot-directory — `upload-artifact` excludes those by default, so it would find no file while every step before it succeeded"]
  | _ =>
      failures := failures ++
        [s!"the gates job has {uploads.length} step(s) uploading an artifact named `{toolArtifactName}`; exactly one must, or which bytes a consumer receives depends on upload order"]
  return failures

/-! ### The consumers, and the prefix each one instantiates

A consumer is any job that downloads the tool artifact — found by what it does,
so a fifth privileged job is covered the day it is written rather than the day
somebody remembers to add it here. Each must instantiate the same prefix:

    download the artifact → compare the received bytes → first use of the tool

with *nothing* between the comparison and the first use. That contiguity is the
point rather than a tidiness: a step admitted into the gap is a step that runs
before the bytes have been established, and an exception for one class of step
is a place for a later one to be added. -/

/-- Whether a step runs the downloaded tool. -/
private def Step.usesTool (step : Step) : Bool :=
  step.code.any fun line =>
    let text := line.trimAscii.toString
    (text.splitOn s!"./{consumerToolPath}").length > 1
      || (text.splitOn s!" {consumerToolPath} ").length > 1

/-- Whether a step is the download of the tool artifact. -/
private def Step.downloadsTool (step : Step) : Bool :=
  (step.uses.getD "").startsWith downloadAction && step.mentions s!"name: {toolArtifactName}"

/-- Whether a step is the comparison: it reads the published expectation, hashes
    what arrived, and refuses an empty expectation as well as a mismatched one.

    All three, because each alone is satisfiable without the others. A step that
    hashes and never compares establishes nothing; one that compares against
    `needs.gates.outputs.…` without refusing the empty string passes when the
    producer did not run, since an unset output is `''` and `'' == ''`. -/
private def Step.comparesTool (step : Step) : Bool :=
  step.runs s!"needs.gates.outputs.{toolDigestOutput}"
    && step.runs s!"sha256sum {consumerToolPath}"
    && step.runs "-z" && step.runs "exit 1"

private def consumerFailures (jobs : List (String × List String)) : List String := Id.run do
  let consumers := jobs.filter fun (_, lines) => (stepsOf lines).any (·.downloadsTool)
  if consumers.length < 2 then
    return [s!"only {consumers.length} job(s) download the `{toolArtifactName}` artifact. This scan finds consumers by what they do, so too few of them means it stopped recognising the download rather than that the workflow has one consumer — and a guard that checks nothing reports the same clean result as a workflow that is correct."]
  let mut failures : List String := []
  for (job, lines) in consumers do
    let steps := stepsOf lines
    let indexed := steps.zipIdx
    let downloadAt := (indexed.find? fun (step, _) => step.downloadsTool).map (·.2)
    let compareAt := (indexed.find? fun (step, _) => step.comparesTool).map (·.2)
    let firstUseAt := (indexed.find? fun (step, _) => step.usesTool).map (·.2)
    match downloadAt, compareAt, firstUseAt with
    | _, none, _ =>
        failures := failures ++
          [s!"the `{job}` job downloads the release tool and no step of it compares what arrived against `needs.gates.outputs.{toolDigestOutput}`, hashes {consumerToolPath}, and refuses an empty expectation. It is about to run that binary on the strength of the artifact store alone."]
    | none, _, _ =>
        failures := failures ++
          [s!"the `{job}` job compares the release tool without a step that downloads it, which this scan cannot read as a handoff at all."]
    | some download, some compare, use? =>
        if compare < download then
          failures := failures ++
            [s!"the `{job}` job compares the release tool before downloading it, so the comparison is over whatever was there beforehand."]
        match use? with
        | none =>
            failures := failures ++
              [s!"the `{job}` job downloads and validates the release tool and never runs it. Either the job does not need the handoff, or the step that used it was removed and its download left behind."]
        | some use =>
            if use < compare then
              failures := failures ++
                [s!"the `{job}` job runs the release tool at step {use + 1} and validates it at step {compare + 1}. The bytes are used before they are established, which is the whole failure the comparison exists to prevent."]
            else if use != compare + 1 then
              let between := ((steps.drop (compare + 1)).take (use - compare - 1)).map fun step =>
                if step.name.isEmpty then step.uses.getD "an unnamed step" else step.name
              failures := failures ++
                [s!"the `{job}` job has {use - compare - 1} step(s) between validating the release tool and first using it: {String.intercalate ", " between}. The prefix is contiguous by construction — a step admitted into that gap runs before the bytes have been established, and an exception for one is a place for the next to be added. Move it above the download."]
  return failures

/-- The jobs this scan reads as consumers, for a test that says which. -/
def releaseToolConsumers (workflow : String) : List String :=
  (jobsOf workflow).filterMap fun (job, lines) =>
    if (stepsOf lines).any (·.downloadsTool) then some job else none

/-- The whole handoff: one producer, and every consumer instantiating the same
    prefix. -/
def releaseToolHandoffShape (workflow : String) : Except String Unit :=
  let jobs := jobsOf workflow
  match producerFailures jobs ++ consumerFailures jobs with
  | [] => .ok ()
  | problems => .error (String.intercalate "\n" problems)

/-! ### The guard's own fixtures

A canonical workflow, and one mutation per way the handoff can be broken. Every
row is a workflow this parser reads as jobs and steps, because the defect the
old substring guard had was precisely that it never looked at either: its rows
were four lines of text that no workflow shape could contradict. -/

private def handoffConsumer (job : String) (steps : String) : String :=
  s!"  {job}:\n    needs: [gates]\n    steps:\n" ++ steps

private def canonicalPrefix : String :=
  "      - name: download the release tool\n" ++
  "        uses: actions/download-artifact@abc # v8\n" ++
  "        with:\n" ++
  "          name: release-tool\n" ++
  "          path: tool\n" ++
  "      - name: confirm the release tool landed unchanged\n" ++
  "        run: |\n" ++
  "          want='${{ needs.gates.outputs.releaseToolDigest }}'\n" ++
  "          if [ -z \"$want\" ]; then exit 1; fi\n" ++
  "          got_line=$(sha256sum tool/tlrelease)\n" ++
  "          if [ \"$got_line\" != \"$want\" ]; then exit 1; fi\n" ++
  "          chmod +x tool/tlrelease\n" ++
  "      - name: use it\n" ++
  "        run: ./tool/tlrelease manifest-verify --dist dist\n"

private def canonicalGates : String :=
  "  gates:\n" ++
  "    outputs:\n" ++
  "      releaseToolDigest: ${{ steps.tool.outputs.digest }}\n" ++
  "    steps:\n" ++
  "      - name: stage the release tool\n" ++
  "        run: install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease\n" ++
  "      - name: hash it\n" ++
  "        id: tool\n" ++
  "        run: |\n" ++
  "          line=$(sha256sum release-tool/tlrelease)\n" ++
  "          printf 'digest=%s\\n' \"${line%% *}\" >> \"$GITHUB_OUTPUT\"\n" ++
  "      - name: upload it\n" ++
  "        uses: actions/upload-artifact@def # v7\n" ++
  "        with:\n" ++
  "          name: release-tool\n" ++
  "          path: release-tool/tlrelease\n"

/-- The canonical workflow: one producer and two consumers. Two, because a
    single-consumer fixture cannot distinguish a scan that checks every consumer
    from one that checks the first. -/
private def canonicalHandoff : String :=
  "jobs:\n" ++ canonicalGates
    ++ handoffConsumer "sign" canonicalPrefix
    ++ handoffConsumer "publish-release" canonicalPrefix

private def handoffRefuses (workflow : String) (needle : String) : Bool :=
  match releaseToolHandoffShape workflow with
  | .ok () => false
  | .error message => (message.splitOn needle).length > 1

/-- Replace every occurrence, for building one mutation out of the canonical
    workflow. -/
private def swap (text : String) (before after : String) : String :=
  String.intercalate after (text.splitOn before)

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
    check "release natives: there is one custom native target"
      (occurrences lakefile "\ntarget " == 1)
      "a second custom target is a second native input; pin it here and amend ADR-0019",
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
  let scripts ← filesUnder "scripts" ["sh"]
  let releaseWorkflow ← IO.FS.readFile ".github/workflows/release.yml"
  let ciWorkflow ← IO.FS.readFile ".github/workflows/ci.yml"
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
  let lakefile ← IO.FS.readFile "lakefile.lean"
  let hermeticMutationRows := hermeticPodmanPrefix.map fun line =>
    check s!"hermetic release: removing `{line}` changes the pinned Podman argv"
      ((hermeticReleaseShape (swap canonicalHermeticWorkflow s!"          {line}\n" "")).toOption.isNone)
      s!"the mutated workflow still accepted a Podman argv without `{line}`"
  let hermeticEnvironmentRows := hermeticEnvironment.map fun line =>
    check s!"hermetic release: removing the input pin `{line}` is refused"
      ((hermeticReleaseShape (swap canonicalHermeticWorkflow s!"      {line}\n" "")).toOption.isNone)
      s!"the mutated workflow still accepted an environment without `{line}`"
  let hermeticBodyRows := hermeticBodyFragments.map fun line =>
    check s!"hermetic release: removing the evidence command `{line}` is refused"
      ((hermeticReleaseShape (swap canonicalHermeticWorkflow s!"          {line}\n" "")).toOption.isNone)
      s!"the mutated workflow still accepted a body without `{line}`"
  let hermeticInnerRows := hermeticInnerBody.flatMap fun line =>
    [check s!"hermetic release: deleting inner line `{line}` is refused"
       ((hermeticReleaseShape (String.intercalate "\n"
         ((ciWorkflow.splitOn "\n").filter fun actual => actual.trimAscii.toString != line))).toOption.isNone)
       "the live workflow accepted removal of required evidence",
     check s!"hermetic release: weakening inner line `{line}` is refused"
       ((hermeticReleaseShape (swap canonicalHermeticWorkflow
         s!"          {line}\n" s!"          {line} || true\n")).toOption.isNone)
       "the evidence program accepted a swallowed status"]
  let hermeticExecutionRows := ["if: false", "continue-on-error: true", "container: alpine", "environment: release"].flatMap fun field =>
    [check s!"hermetic release: job-level `{field}` is refused"
       ((hermeticReleaseShape (swap canonicalHermeticWorkflow "    timeout-minutes: 20\n"
         s!"    timeout-minutes: 20\n    {field}\n")).toOption.isNone),
     check s!"hermetic release: step-level `{field}` is refused"
       ((hermeticReleaseShape (swap canonicalHermeticWorkflow "        run: |\n"
         s!"        {field}\n        run: |\n")).toOption.isNone)]
  return documentRows ++ formattedErrnoRows ++ nativeRows ++ nativeBuildRows lakefile
    ++ hygieneRows ++ hermeticMutationRows ++ hermeticEnvironmentRows ++ hermeticBodyRows
    ++ hermeticInnerRows ++ hermeticExecutionRows ++ [
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
    -- Non-vacuity against the live file, which the fixtures cannot give: the
    -- scan finds consumers by what they do, so a parser that stopped reading
    -- the download step would report a clean workflow having checked one job.
    -- Five is what release.yml has — stamp, sign and the three publish jobs —
    -- and a sixth is a change to make deliberately. `stamp` joined when the
    -- build provenance moved into `tlrelease`: it runs the tool, so it
    -- validates the bytes it received like every other consumer.
    checkEq "release workflow: the scan reads all five real consumers"
      (releaseToolConsumers releaseWorkflow)
      ["stamp", "sign", "publish-release", "publish-homebrew", "publish-npm"],
    -- Non-vacuity, both halves. A walk that found no documents, or no script
    -- under the rule, reports the same clean result as a repository that
    -- satisfies it.
    check "release docs: the scan read documented invocations to check"
      (documented ≥ 4) s!"found {documented} documented invocation(s) with arguments",
    check "release policy: the library that owns the decision was found exactly once"
      (library == 1) s!"{library} file(s) define rc_tool_gate",
    check "release policy: the scripts that run gates were found"
      (policies.length ≥ 2) s!"{policies.length} policy script(s)",
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
      (hermeticRefuses "jobs:\n" "exactly one"),
    check "hermetic release: duplicate jobs are refused"
      (hermeticRefuses (canonicalHermeticWorkflow ++ "  hermetic-release:\n") "exactly one"),
    check "hermetic release: a different checkout action is refused"
      (hermeticRefuses (swap canonicalHermeticWorkflow
        "actions/checkout@9c091bb21b7c1c1d1991bb908d89e4e9dddfe3e0" "actions/checkout@main")
        "pinned checkout"),
    check "hermetic release: a noncanonical run header is refused"
      (hermeticRefuses (swap canonicalHermeticWorkflow
        "podman run --rm" "podman run --rm --quiet") "canonical Podman invocation"),
    check "hermetic release: an argument inserted before the image is refused"
      (hermeticRefuses
        (swap canonicalHermeticWorkflow
          "          \"$HERMETIC_IMAGE\" -eu -c '\n"
          "          --privileged \\\n          \"$HERMETIC_IMAGE\" -eu -c '\n")
        "Podman argv drifted"),
    check "hermetic release: a second Podman launch is refused"
      (hermeticRefuses
        (swap canonicalHermeticWorkflow
          "          podman run --rm \\\n"
          "          podman run --rm \\\n          podman run --rm \\\n")
        "more than once"),
    check "hermetic release: a second outer step is refused"
      ((hermeticReleaseShape (canonicalHermeticWorkflow ++
        "      - name: after the boundary\n        run: true\n")).toOption.isNone),
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
    -- The canonical shape is accepted. Without this every refusal row below
    -- would be satisfied by a guard that refuses everything.
    check "release handoff: the canonical workflow is accepted"
      (releaseToolHandoffShape canonicalHandoff).toOption.isSome
      (match releaseToolHandoffShape canonicalHandoff with
       | .ok () => ""
       | .error message => message),
    -- The producer.
    check "release handoff: an unstaged upload is refused"
      (handoffRefuses (swap canonicalHandoff
        "        run: install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease\n" "")
        "stages the release tool 0 time(s)"),
    check "release handoff: staging twice is refused"
      (handoffRefuses (swap canonicalHandoff
        "      - name: stage the release tool\n"
        "      - name: stage the release tool\n        run: install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease\n")
        "stages the release tool 2 time(s)"),
    -- The mutation the old guard could not see at all: the canonical text
    -- present, as a comment. Three of its four rows were satisfiable this way.
    check "release handoff: the staging command in a comment does not satisfy the rule"
      (handoffRefuses (swap canonicalHandoff
        "        run: install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease"
        "        # install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease\n        run: true")
        "stages the release tool 0 time(s)"),
    check "release handoff: hashing a path other than the staged one is refused"
      (handoffRefuses (swap canonicalHandoff
        "sha256sum release-tool/tlrelease" "sha256sum .lake/build/bin/tlrelease")
        "hashing release-tool/tlrelease"),
    check "release handoff: a digest produced under another step id is refused"
      (handoffRefuses (swap canonicalHandoff "        id: tool\n" "        id: hasher\n")
        "with `id: tool`"),
    check "release handoff: an output mapped from somewhere else is refused"
      (handoffRefuses (swap canonicalHandoff
        "releaseToolDigest: ${{ steps.tool.outputs.digest }}"
        "releaseToolDigest: ${{ steps.hasher.outputs.digest }}")
        "does not map `releaseToolDigest`"),
    check "release handoff: uploading a path other than the staged one is refused"
      (handoffRefuses (swap canonicalHandoff
        "          path: release-tool/tlrelease" "          path: .lake/build/bin/tlrelease")
        "below a dot-directory"),
    check "release handoff: a second artifact under the same name is refused"
      (handoffRefuses (swap canonicalHandoff
        "      - name: upload it\n"
        "      - name: upload a decoy\n        uses: actions/upload-artifact@def # v7\n        with:\n          name: release-tool\n          path: decoy\n      - name: upload it\n")
        "2 step(s) uploading"),
    -- The consumers.
    check "release handoff: a consumer that never validates what it downloaded is refused"
      (handoffRefuses (swap canonicalHandoff
        "      - name: confirm the release tool landed unchanged\n        run: |\n          want='${{ needs.gates.outputs.releaseToolDigest }}'\n          if [ -z \"$want\" ]; then exit 1; fi\n          got_line=$(sha256sum tool/tlrelease)\n          if [ \"$got_line\" != \"$want\" ]; then exit 1; fi\n          chmod +x tool/tlrelease\n" "")
        "no step of it compares"),
    -- Its own half of the comparison, each removed separately: a step that
    -- hashes and never compares establishes nothing, and one that compares
    -- without refusing an empty expectation passes when the producer did not
    -- run, since an unset output is '' and '' == ''.
    check "release handoff: a comparison that does not refuse an empty expectation is refused"
      (handoffRefuses (swap canonicalHandoff
        "          if [ -z \"$want\" ]; then exit 1; fi\n" "")
        "no step of it compares"),
    check "release handoff: a comparison that never hashes what arrived is refused"
      (handoffRefuses (swap canonicalHandoff
        "          got_line=$(sha256sum tool/tlrelease)\n" "")
        "no step of it compares"),
    -- Domination, in both directions.
    check "release handoff: a step inserted between validation and first use is refused"
      (handoffRefuses (swap canonicalHandoff
        "      - name: use it\n"
        "      - name: install cosign\n        uses: sigstore/cosign-installer@ghi\n      - name: use it\n")
        "step(s) between validating the release tool and first using it"),
    check "release handoff: the inserted step is named, so the fix is obvious"
      (handoffRefuses (swap canonicalHandoff
        "      - name: use it\n"
        "      - name: install cosign\n        uses: sigstore/cosign-installer@ghi\n      - name: use it\n")
        "install cosign"),
    check "release handoff: using the tool before validating it is refused"
      (handoffRefuses (swap canonicalHandoff
        "      - name: confirm the release tool landed unchanged\n"
        "      - name: use it early\n        run: ./tool/tlrelease prereqs\n      - name: confirm the release tool landed unchanged\n")
        "before they are established"),
    check "release handoff: a consumer that validates and never runs the tool is refused"
      (handoffRefuses (swap canonicalHandoff
        "      - name: use it\n        run: ./tool/tlrelease manifest-verify --dist dist\n" "")
        "never runs it"),
    -- The mutation that only a per-consumer scan can see: one consumer correct,
    -- the other not. A whole-file guard reports this as clean.
    check "release handoff: a second consumer that skips validation is refused"
      (handoffRefuses
        ("jobs:\n" ++ canonicalGates ++ handoffConsumer "sign" canonicalPrefix
          ++ handoffConsumer "publish-release"
            ("      - name: download the release tool\n" ++
             "        uses: actions/download-artifact@abc # v8\n" ++
             "        with:\n          name: release-tool\n          path: tool\n" ++
             "      - name: use it\n        run: ./tool/tlrelease manifest-verify --dist dist\n"))
        "the `publish-release` job downloads the release tool and no step of it compares"),
    -- Non-vacuity: the scan must be reading consumers at all.
    check "release handoff: a workflow whose consumers this scan cannot find is refused"
      (handoffRefuses ("jobs:\n" ++ canonicalGates) "download the `release-tool` artifact"),
    check "release handoff: a workflow with no gates job is refused"
      (handoffRefuses ("jobs:\n" ++ handoffConsumer "sign" canonicalPrefix) "no `gates` job"),
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
