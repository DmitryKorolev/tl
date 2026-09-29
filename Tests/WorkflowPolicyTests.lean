/- Adversarial changes to the actual workflow, checked through the same typed
   decision used by the public policy command. -/
import Tests.Harness
import release.Cli

namespace Tl.Tests
open Release WorkflowPolicy

private def changeJob (text name : String) (change : String → String) : String :=
  match (Workflow.jobScan text).jobs.find? (·.name == name) with
  | none => text
  | some job =>
    let body := String.intercalate "\n" job.lines
    text.replace ("  " ++ name ++ ":\n" ++ body) ("  " ++ name ++ ":\n" ++ change body)

private def refusal (label original mutated : String) (contract : Contract) : List Outcome :=
  [check s!"workflow mutation is real: {label}" (original != mutated),
   check s!"workflow policy refuses: {label}" (!accepts mutated contract)]

def workflowPolicyTests : IO (List Outcome) := do
  let release ← IO.FS.readFile ".github/workflows/release.yml"
  let ci ← IO.FS.readFile ".github/workflows/ci.yml"
  let mut rows := [
    check "workflow schema: release baseline passes" (accepts release releaseContract)
      (String.intercalate "\n" (Check.failures (checks release releaseContract))),
    check "workflow schema: CI baseline passes" (accepts ci ciContract)
      (String.intercalate "\n" (Check.failures (checks ci ciContract))),
    check "workflow schema: quoted control keys normalize once"
      (accepts (release.replace "    permissions:" "    \"permissions\":"
        |>.replace "        run:" "        'run':") releaseContract)]
  rows := rows ++ refusal "native hermetic runner is required" ci
    (ci.replace "./.lake/build/bin/tlrelease hermetic --root ." "true") ciContract
  rows := rows ++ refusal "candidate branch push checks are required" ci
    (ci.replace "branches: ['**']" "branches: [main]") ciContract
  rows := rows ++ refusal "CI must exclude tag pushes" ci
    (ci.replace "    branches: ['**']\n" "") ciContract
  for (label, before, after) in [
      ("inherited write permission", "permissions:\n  contents: read", "permissions:\n  contents: write"),
      ("plan producer shell", "./.lake/build/bin/tlrelease workflow-plan", "echo plan; ./.lake/build/bin/tlrelease workflow-plan"),
      ("plan mapping", "steps.plan.outputs.npm", "steps.decoy.outputs.npm"),
      ("stamp mapping", "steps.stamp.outputs.commit", "steps.stamp.outputs.other"),
      ("attestation subjects", "steps.subjects.outputs.paths", "steps.subjects.outputs.other"),
      ("plan predicate", "needs.gates.outputs.npm == 'true'", "needs.gates.outputs.npm != 'false'"),
      ("bracket authority", "needs.stamp.outputs.commit", "needs['stamp'].outputs.commit"),
      ("case-varied authority", "needs.stamp.outputs.commit", "Needs.stamp.outputs.commit"),
      ("transitive producer dependency", "--output \"$GITHUB_OUTPUT\"", "--output \"$GITHUB_OUTPUT\" ${{ needs.bridge.outputs.policy }}"),
      ("privileged interpolation", "--tag \"$RELEASE_TAG\"", "--tag ${{ github.ref_name }}"),
      ("privileged substitution", "--tag \"$RELEASE_TAG\"", "--tag \"$(echo v1.2.3)\""),
      ("privileged pipe", "./tool/tlrelease workflow-sign", "echo bypass | ./tool/tlrelease workflow-sign"),
      ("privileged assignment prefix", "./tool/tlrelease workflow-sign", "PATH=/tmp ./tool/tlrelease workflow-sign"),
      ("privileged backticks", "./tool/tlrelease workflow-sign", "`echo ./tool/tlrelease` workflow-sign"),
      ("privileged loop", "./tool/tlrelease workflow-sign", "for x in once; do ./tool/tlrelease workflow-sign"),
      ("action script input", "          subject-path:", "          script: publish()\n          subject-path:"),
      ("action ref", "sigstore/cosign-installer@6f9f17788090df1f26f669e9d70d6ae9567deba6", "sigstore/cosign-installer@main"),
      ("token binding", "GH_TOKEN: ${{ github.token }}", "GH_TOKEN: ${{ secrets.OTHER_TOKEN }}"),
      ("source binding", "RELEASE_COMMIT: ${{ needs.stamp.outputs.commit }}", "RELEASE_COMMIT: ${{ github.sha }}"),
      ("signed artifact destination", "          name: tl-signed-release\n          path: dist", "          name: tl-signed-release\n          path: elsewhere"),
      ("missing producer", "        id: subjects", "        id: decoy"),
      ("output alias", "    outputs:\n", "    outputs: *aliased\n") ] do
    rows := rows ++ refusal label release (release.replace before after) releaseContract
  for job in ["sign", "publish-release", "publish-homebrew", "publish-npm", "stamp"] do
    for (label, edit) in [
        ("runner", fun s : String => s.replace "runs-on: ubuntu-latest" "runs-on: self-hosted"),
        ("job failure override", fun s => "    continue-on-error: true\n" ++ s),
        ("job startup environment", fun s => "    env:\n      BASH_ENV: /tmp/startup\n" ++ s),
        ("step failure override", fun s => s.replace "        run: ./tool/tlrelease" "        continue-on-error: true\n        run: ./tool/tlrelease"),
        ("step shell override", fun s => s.replace "        run: ./tool/tlrelease" "        shell: bash -c {0}\n        run: ./tool/tlrelease"),
        ("step directory override", fun s => s.replace "        run: ./tool/tlrelease" "        working-directory: /tmp\n        run: ./tool/tlrelease"),
        ("step PATH override", fun s => s.replace "        run: ./tool/tlrelease --help" "        env:\n          PATH: /tmp\n        run: ./tool/tlrelease --help"),
        ("unregistered command", fun s => s ++ "\n      - run: echo publish\n") ] do
      rows := rows ++ refusal (job ++ ": " ++ label) release (changeJob release job edit) releaseContract
    for status in ["always()", "failure()", "cancelled()", "!cancelled()", "AlWaYs()", "success()"] do
      let mutated := changeJob release job fun s => s.replace "        run: ./tool/tlrelease --help"
        ("        if: " ++ status ++ "\n        run: ./tool/tlrelease --help")
      rows := rows ++ refusal (job ++ ": status " ++ status) release mutated releaseContract
  for token in ["secrets.TOKEN", "secrets['TOKEN']", "secrets ['TOKEN']", "SeCrEtS [ 'TOKEN' ]",
      "toJSON(secrets)", "toJSON( SeCrEtS )", "secrets"] do
    let mutated := changeJob release "gates" fun s => s ++
      "\n      - name: unregistered secret consumer\n        env:\n          GH_TOKEN: ${{ " ++ token ++ " }}\n        run: echo consume\n"
    rows := rows ++ refusal token release mutated releaseContract
  for token in ["toJSON(needs)", "toJSON( StEpS )", "needs.*.outputs", "steps.*.outputs"] do
    let mutated := changeJob release "gates" fun s => s ++
      "\n      - name: unregistered context consumer\n        env:\n          CONTEXT: ${{ " ++ token ++ " }}\n        run: echo consume\n"
    rows := rows ++ refusal token release mutated releaseContract
  for token in ["needs", "steps"] do
    for condition in ["contains('}}', '}') && contains(toJSON(" ++ token ++ "), 'true')",
        "${{ contains('}}', '}') && contains(toJSON(" ++ token ++ "), 'true') }}"] do
      let mutated := changeJob release "gates" fun s => s ++
        "\n      - name: quoted closing delimiter\n        if: " ++ condition ++ "\n        run: echo consume\n"
      rows := rows ++ refusal ("quoted delimiter " ++ condition) release mutated releaseContract
    let folded := changeJob release "gates" fun s => s ++
      "\n      - name: folded context\n        env:\n          CONTEXT: >-\n            ${{\n            toJSON(" ++ token ++ ")\n            }}\n        run: echo consume\n"
    rows := rows ++ refusal ("folded context " ++ token) release folded releaseContract
    let implicitCondition := changeJob release "gates" fun s => s ++
      "\n      - name: implicit condition\n        if: contains(toJSON(" ++ token ++ "), 'true')\n        run: echo consume\n"
    rows := rows ++ refusal ("implicit condition " ++ token) release implicitCondition releaseContract
  let scalarSecret := changeJob release "gates" fun s => s ++
    "\n      - name: hidden scalar secret\n        env:\n          GH_TOKEN: |\n            #${{ secrets.TOKEN }}\n        run: echo consume\n"
  rows := rows ++ refusal "secret inside comment-looking scalar data" release scalarSecret releaseContract
  let scalarReference := changeJob release "gates" fun s => s ++
    "\n      - name: hidden scalar reference\n        env:\n          CONTEXT: |\n            #${{ needs.bridge.outputs.value }}\n        run: echo consume\n"
  rows := rows ++ refusal "output edge inside comment-looking scalar data" release scalarReference releaseContract
  for expression in ["${{ \\u0073ecrets.TOKEN }}", "${{ \\x73ecrets.TOKEN }}",
      "${{ \\U00000073ecrets.TOKEN }}", "\\u0024{{ toJSON(needs) }}",
      "${{ sec\\\n            rets.TOKEN }}"] do
    let mutated := changeJob release "gates" fun s => s ++
      "\n      - name: escaped YAML expression\n        env:\n          TOKEN: \"" ++ expression ++ "\"\n        run: echo consume\n"
    rows := rows ++ refusal ("escaped YAML expression " ++ expression) release mutated releaseContract
    let escapedRun := changeJob release "gates" fun s => s ++
      "\n      - name: escaped run expression\n        run: \"echo " ++ expression ++ "\"\n"
    rows := rows ++ refusal ("escaped run expression " ++ expression) release escapedRun releaseContract
  for destination in ["GITHUB_OUTPUT", "GITHUB_ENV", "GITHUB_PATH", "GITHUB_STATE"] do
    let mutated := changeJob release "gates" fun s => s ++
      "\n      - name: unregistered producer\n        run: echo value >> \"$" ++ destination ++ "\"\n"
    rows := rows ++ refusal destination release mutated releaseContract
  for (text, contract, label) in [(release, releaseContract, "release"), (ci, ciContract, "ci")] do
    rows := rows ++ refusal (label ++ ": trailing root environment") text
      (text ++ "\nenv:\n  BASH_ENV: /tmp/startup\n") contract
    rows := rows ++ refusal (label ++ ": duplicate jobs mapping") text
      (text ++ "\njobs:\n  escape:\n    runs-on: ubuntu-latest\n    steps:\n      - run: echo publish\n") contract
    rows := rows ++ refusal (label ++ ": new output intermediary") text
      (text ++ "\n  bridge:\n    runs-on: ubuntu-latest\n    outputs:\n      policy: ${{ needs.gates.outputs.npm }}\n    steps:\n      - run: echo bridge\n") contract
  for steps in [" [{run: echo consume, env: {GH_TOKEN: \"${{ secrets.TOKEN }}\"}}]",
      " *hidden", " []", "\n      - *hidden", "\n      - run: echo consume\n        ? complex\n        : field"] do
    let mutated := changeJob ci "homebrew-formula" fun body =>
      (body.splitOn "    steps:").headD "" ++ "    steps:" ++ steps ++ "\n"
    rows := rows ++ refusal ("unreadable open steps: " ++ steps) ci mutated ciContract
  for invalid in [[], [""], ["./tool/tlrelease", "publish"], ["./tool/tlrelease  publish"],
      ["./tool/tlrelease > file"], ["./tool/tlrelease '$VALUE'"], ["./tool/tlrelease \"${VALUE}\""],
      ["./tool/tlrelease \"$\""], ["./tool/tlrelease \"$VALUE/extra\""], ["./tool/tlrelease;true"]] do
    rows := rows ++ [check s!"argv grammar refuses {repr invalid}" (invocation? invalid).isNone]
  rows := rows ++ [check "argv grammar accepts literal and whole environment arguments"
    ((invocation? ["./tool/tlrelease workflow-source --tag \"$RELEASE_TAG\""]).isSome)]
  let fixture ← IO.FS.createTempDir
  IO.FS.createDirAll (fixture / ".github/workflows")
  IO.FS.writeFile (fixture / ".github/workflows/release.yml") release
  IO.FS.writeFile (fixture / ".github/workflows/ci.yml") ci
  let binary ← IO.FS.realPath ".lake/build/bin/tlrelease"
  let run := IO.Process.output { cmd := binary.toString, args := #["workflow-policy", "--root", fixture.toString] }
  let good ← run
  IO.FS.writeFile (fixture / ".github/workflows/ci.yml") (ci ++ "\nenv:\n  BASH_ENV: /tmp/startup\n")
  let bad ← run
  IO.FS.removeFile (fixture / ".github/workflows/ci.yml")
  let missing ← run
  rows := rows ++ [checkEq "public workflow policy: valid checkout passes" good.exitCode 0,
    checkEq "public workflow policy: trailing authority refuses" bad.exitCode 1,
    checkEq "public workflow policy: missing workflow refuses" missing.exitCode 1]
  IO.FS.createDirAll (fixture / "release")
  let planPath := fixture / "release/plan.json"
  for (npm, brew) in [(false, false), (true, false), (false, true), (true, true)] do
    let channelRow (name : String) (enabled : Bool) :=
      "{\"channel\":\"" ++ name ++ "\",\"enabled\":" ++ (if enabled then "true" else "false,\"plannedFor\":\"0.2.0\"") ++ ",\"note\":\"fixture\"}"
    let planText := "{\"channels\":[" ++ String.intercalate ","
      [channelRow "github-release" true, channelRow "installer" true, channelRow "npm" npm, channelRow "homebrew" brew] ++ "]}"
    IO.FS.writeFile planPath planText
    let plan ← match ReleasePlan.parse "fixture" planText with
      | .ok plan => pure plan
      | .error message => throw (IO.userError message)
    let selected := Policy.selectedGates .release false plan
    let observed ← IO.Process.output {
      cmd := binary.toString, cwd := some fixture,
      args := #["policy-list", "--profile", "release"] }
    let names := ((observed.stdout.splitOn "\n").filter (!·.isEmpty)).dropLast
    rows := rows ++ [checkEq s!"policy list: enabled channels {npm}/{brew} match execution selection" names (selected.map (·.name)),
      checkEq s!"policy effects: npm suite follows plan {npm}/{brew}" (names.contains "npm packaging selftest") npm,
      checkEq s!"policy effects: Homebrew suite follows plan {npm}/{brew}" (names.contains "the rendered formulae parse") brew,
      check s!"policy effects: ci keeps both channels {npm}/{brew}"
        ((Policy.selectedGates .ci false plan).length == Policy.gates.length)]
  for malformed in [true, false] do
    if malformed then IO.FS.writeFile planPath "{}" else IO.FS.removeFile planPath
    for command in ["policy-list", "policy"] do
      let result ← IO.Process.output {
        cmd := binary.toString, cwd := some fixture,
        args := #[command, "--profile", "release", if command == "policy" then "--strict" else "--tag"] }
      rows := rows ++ [checkEq s!"{command}: missing/malformed plan {malformed} refuses before gates" result.exitCode 1]
  let fakeTool := fixture / "fake-release-tool"
  IO.FS.writeFile fakeTool
    "#!/bin/sh\nset -eu\n[ \"$*\" = 'npm-selftest --root .' ] || exit 22\n[ -f \"${npm_config_cache%/*}\" ] || exit 23\n[ -f \"${npm_config_userconfig%/*}\" ] || exit 24\n[ -f \"${npm_config_globalconfig%/*}\" ] || exit 25\nprintf '%s\\n' \"${npm_config_cache%/*}\"\n"
  let mode ← IO.Process.output { cmd := "chmod", args := #["755", fakeTool.toString] }
  if mode.exitCode != 0 then throw (IO.userError "could not make the native policy fixture executable")
  let output ← IO.mkRef { : IO.FS.Stream.Buffer }
  let poisoned ← IO.withStdout (IO.FS.Stream.ofBuffer output) <|
    Policy.spawnInvocationUsing fakeTool.toString (.releaseCommand ["npm-selftest", "--root", "."])
  let blocker := (String.fromUTF8! (← output.get).data).trimAscii.toString
  let ordinary ← Policy.spawnInvocationUsing "not-used" (.script fakeTool.toString ["npm-selftest", "--root", "."])
  IO.FS.writeFile fakeTool "#!/bin/sh\nexit 17\n"
  let failed ← Policy.spawnInvocationUsing fakeTool.toString (.releaseCommand ["npm-selftest", "--root", "."])
  rows := rows ++ [check "native policy: npm self-command receives all three poison paths" poisoned.toOption.isSome,
    check "native policy: poisoned scratch is removed after invocation" (!blocker.isEmpty && !(← System.FilePath.pathExists blocker)),
    check "native policy: ordinary scripts do not receive npm-specific overrides" ordinary.toOption.isNone,
    check "native policy: poisoned child failure propagates" failed.toOption.isNone]
  return rows

end Tl.Tests
