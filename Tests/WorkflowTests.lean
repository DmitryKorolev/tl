/- Structural workflow-source reader mutations, shared by the release guards. -/
import Tests.Harness
import release.Workflow

namespace Tl.Tests
open Release.Workflow

private def parseSteps (body : String) : List Step :=
  stepsOf (body.splitOn "\n")

private def workflowSample : String :=
  "    steps:\n      - name: download\n        uses: actions/download-artifact@pin\n        with:\n          name: release-tool\n      - id: command\n        run: |\n          echo execute\n"

/-- Every row changes where a key appears, not just the text it carries. -/
def workflowParserTests : List Outcome := Id.run do
  let steps := parseSteps workflowSample
  let mut rows := [
    checkEq "workflow reader: direct steps and their order" (steps.map (·.name)) ["download", ""],
    checkEq "workflow reader: source line" (steps.map (·.sourceLine)) [2, 6],
    check "workflow reader: action and input share a step"
      ((steps[0]?).any fun step => step.uses == some "actions/download-artifact@pin"
        && step.hasInput "name" "release-tool"),
    check "workflow reader: later direct field positions include their offsets"
      ((steps[0]?).any fun step =>
        (step.field? "uses").any (·.sourceLine == 3) &&
        (step.field? "with").any (·.sourceLine == 4)),
    check "workflow reader: run scalar and id share a step"
      ((steps[1]?).any fun step => step.hasField "id" "command" && step.runs "echo execute")]
  let decoys : List (String × String) := [
    ("comment", "      # - run: echo execute\n"),
    ("name field", "      - name: 'run: echo execute'\n"),
    ("nested env", "      - env:\n          run: echo execute\n"),
    ("nested with", "      - with:\n          run: echo execute\n"),
    ("nested sequence", "      - with:\n          items:\n            - run: echo execute\n"),
    ("non-run scalar", "      - name: |\n          - run: echo execute\n"),
    ("quoted key", "      - 'run': echo execute\n"),
    ("empty run", "      - run:\n"),
    ("quoted run", "      - run: 'echo execute'\n"),
    ("double quoted run", "      - run: \"echo execute\"\n"),
    ("folded run", "      - run: >-\n          echo execute\n"),
    ("literal header comment", "      - run: | # echo execute\n          true\n"),
    ("literal indentation indicator", "      - run: |2 # echo execute\n          true\n"),
    ("inline comment", "      - run: true # echo execute\n"),
    ("tab-separated comment", "      - run: true\t# echo execute\n"),
    ("comment-only scalar", "      - run: # echo execute\n"),
    ("anchored scalar", "      - run: &execute true\n"),
    ("aliased scalar", "      - run: *execute\n"),
    ("tagged scalar", "      - run: !execute true\n"),
    ("flow sequence", "      - run: [echo execute]\n"),
    ("flow mapping", "      - run: {echo execute: true}\n"),
    ("plain continuation", "      - run: echo execute\n          suffix\n"),
    ("missing colon separator", "      - run:echo execute\n"),
    ("comment in run", "      - run: |\n          # echo execute\n"),
    ("quoted duplicate", "      - run: echo execute\n        'run': true\n"),
    ("under-indented body", "      - run: |\n          echo execute\n       env: spoof\n"),
    ("duplicate run", "      - run: echo execute\n        run: true\n")]
  for (label, body) in decoys do
    rows := rows ++ [check s!"workflow reader: {label} supplies no run"
      (!(parseSteps ("    steps:\n" ++ body)).any (·.runs "echo execute"))]
  let actionDecoys : List (String × String) := [
    ("with uses", "      - uses: actions/checkout@pin\n        with:\n          uses: actions/download-artifact@pin\n"),
    ("scalar uses", "      - run: |\n          uses: actions/download-artifact@pin\n"),
    ("continued uses", "      - uses: actions/download-artifact@pin\n          suffix\n"),
    ("duplicate uses", "      - uses: actions/download-artifact@pin\n        uses: actions/checkout@pin\n")]
  for (label, body) in actionDecoys do
    rows := rows ++ [check s!"workflow reader: {label} supplies no download"
      (!(parseSteps ("    steps:\n" ++ body)).any
        (fun step => step.uses == some "actions/download-artifact@pin"))]
  rows := rows ++ [
    check "workflow reader: scalar metadata and flow forms supply no run lines"
      (["&execute true", "*execute", "!execute true", "{execute: true}", "[execute]"].all fun value =>
        (parseSteps s!"    steps:\n      - run: {value}\n").all (·.runLines.isEmpty)),
    check "workflow reader: alternate input indentation and inline comments"
      ((parseSteps "    steps:\n      - with: # inputs\n            name: release-tool # comment\n").any
        (·.hasInput "name" "release-tool")),
    check "workflow reader: continued input does not match its first line"
      (!(parseSteps "    steps:\n      - with:\n          name: release-tool\n            suffix\n").any (·.hasInput "name" "release-tool")),
    check "workflow reader: continued id does not match its first line"
      (!(parseSteps "    steps:\n      - id: command\n          suffix\n").any (·.hasField "id" "command")),
    checkEq "workflow reader: duplicate steps mapping refuses"
      (parseSteps (workflowSample ++ "    steps:\n      - run: true\n")).length 0,
    checkEq "workflow reader: quoted duplicate steps mapping refuses"
      (parseSteps (workflowSample ++ "    'steps':\n      - run: true\n")).length 0,
    check "workflow reader: spaced and escaped duplicate keys refuse"
      (["steps :", "'steps' :", "\"steps\" :", "\"st\\u0065ps\":"].all fun key =>
        (parseSteps (workflowSample ++ s!"    {key}\n      - run: true\n")).isEmpty),
    check "workflow reader: missing and empty field keys refuse"
      (["run", ": true", ""].all fun text => (Release.Workflow.field? text 1).isNone),
    check "workflow reader: literal block chomping indicators"
      (["|", "|-", "|+"].all fun indicator =>
        (parseSteps s!"    steps:\n      - run: {indicator}\n          echo execute\n").any
          (·.runs "echo execute")),
    check "workflow reader: flow with mapping supplies no input"
      (!(parseSteps "    steps:\n      - with: {name: release-tool}\n").any
        (·.hasInput "name" "release-tool")),
    check "workflow reader: duplicate with mapping supplies no input"
      (!(parseSteps "    steps:\n      - with:\n          name: release-tool\n        with:\n          name: other\n").any
        (·.hasInput "name" "release-tool")),
    checkEq "workflow reader: malformed first item cannot discover a nested list"
      (parseSteps "    steps:\n      env:\n        - run: spoof\n").length 0,
    check "workflow reader: quoted duplicate input refuses the mapping"
      (!(parseSteps "    steps:\n      - with:\n          name: release-tool\n          'name': other\n").any
        (·.hasInput "name" "release-tool")),
    checkEq "workflow reader: nested steps are data"
      (parseSteps "    env:\n      steps:\n        - run: echo execute\n").length 0,
    checkEq "workflow reader: nested sequence cannot split the step"
      (parseSteps ("    steps:\n      - run: |\n          cat <<'EOF'\n          - run: echo execute\n          EOF\n      - run: true\n")).length 2,
    checkEq "workflow reader: a job field ends steps"
      (parseSteps (workflowSample ++ "    env:\n      - run: decoy\n")).length 2,
    checkEq "workflow reader: indentless sequence uses its first column"
      (parseSteps "    steps:\n    - run: first\n    - run: second\n").length 2,
    check "workflow reader: nested input name does not count"
      (!(parseSteps "    steps:\n      - with:\n          env:\n            name: release-tool\n").any
        (·.hasInput "name" "release-tool")),
    check "workflow reader: duplicate input does not count"
      (!(parseSteps "    steps:\n      - with:\n          name: release-tool\n          name: other\n").any
        (·.hasInput "name" "release-tool")),
    checkEq "workflow reader: job comments and uppercase names"
      ((jobScan "jobs:\n  Build: # comment\n    steps:\n      - run: true\n").jobs.map (·.name)) ["Build"],
    check "workflow reader: a job header requires a colon"
      (jobHeader? "  publish").isNone,
    check "workflow reader: a job comment requires a colon separator"
      (jobHeader? "  publish:# comment").isNone,
    checkEq "workflow reader: duplicate jobs stay visible"
      ((jobScan "jobs:\n  build:\n  build:\n").jobs.map (·.name)) ["build", "build"],
    check "workflow reader: unreadable job header is reported"
      (!(jobScan "jobs:\n  'publish':\n    steps:\n      - run: true\n").unreadable.isEmpty),
    checkEq "workflow reader: unreadable jobs refuse the raw compatibility view"
      (jobsOf "jobs:\n  build:\n  'publish':\n") [],
    checkEq "workflow reader: root key ends jobs"
      ((jobScan "jobs:\n  build:\nenv:\n  fake:\n").jobs.map (·.name)) ["build"]]
  let rawLines := ["    steps:", "      - run: |", "          echo start", "",
    "          # literal", "          echo end"]
  let source := "# header\njobs:\n  first:\n" ++ String.intercalate "\n" rawLines ++
    "\n  second:\n    steps:\n      - run: true"
  let jobs := (jobScan source).jobs
  rows := rows ++ [
    checkEq "workflow reader: absolute job positions" (jobs.map (·.sourceLine)) [3, 10],
    checkEq "workflow reader: raw job lines preserved" ((jobs[0]?).map (·.lines)) (some rawLines),
    check "workflow reader: job steps retain raw source and scalar contents"
      ((jobs[0]?).any fun job => (job.steps[0]?).any fun step =>
        step.lines == rawLines.drop 1 && step.sourceLine == 2 &&
        (step.field? "run").any (fun field => field.sourceLine == 2 &&
          field.children == rawLines.drop 2) && step.runLines == rawLines.drop 2 &&
        step.code == (rawLines.drop 1).filter (fun line => !line.trimAscii.toString.startsWith "#"))]
  return rows

end Tl.Tests
