/- Workflow output producers: protocol bytes and planted clean/dirty checkouts. -/
import Tests.Harness
import release.Cli

namespace Tl.Tests
open Release

private def driveWorkflow (args : List String) : IO UInt32 := do
  let buffer ← IO.mkRef { : IO.FS.Stream.Buffer }
  IO.withStdout (IO.FS.Stream.ofBuffer buffer) <|
    IO.withStderr (IO.FS.Stream.ofBuffer buffer) <| dispatch args

private def fixtureGit (root : System.FilePath) (args : List String) : IO String := do
  let result ← succeededGit ((["-C", root.toString] ++ args).toArray)
  match result with
  | .ok output => return output.stdout.trimAscii.toString
  | .error message => throw (IO.userError message)

def workflowCommandTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let output := (base / "outputs").toString
  IO.FS.writeFile output "existing=value\n"
  let append ← WorkflowOutput.write output [("first", "value"), ("paths", "dist/a\ndist/b")]
  let bytes ← IO.FS.readFile output
  let unchanged := bytes
  let invalid ← WorkflowOutput.write output [("invalid=key", "bad")]
  let afterInvalid ← IO.FS.readFile output
  let directoryWrite ← WorkflowOutput.write base.toString [("key", "value")]
  let planPath := (base / "plan.json").toString
  IO.FS.writeFile planPath "{\"channels\":[{\"channel\":\"github-release\",\"enabled\":true,\"note\":\"fixture\"},{\"channel\":\"installer\",\"enabled\":true,\"note\":\"fixture\"},{\"channel\":\"npm\",\"enabled\":false,\"plannedFor\":\"0.2.0\",\"note\":\"fixture\"},{\"channel\":\"homebrew\",\"enabled\":false,\"plannedFor\":\"0.2.0\",\"note\":\"fixture\"}]}"
  let planStatus ← driveWorkflow ["workflow-plan", "--plan", planPath, "--output", output]
  let planned ← IO.FS.readFile output
  let badPlan := (base / "bad-plan").toString
  IO.FS.writeFile badPlan "{}"
  let badPlanStatus ← driveWorkflow ["workflow-plan", "--plan", badPlan, "--output", output]
  let absentPlanStatus ← driveWorkflow ["workflow-plan", "--plan", (base / "missing").toString, "--output", output]
  let planWriteStatus ← driveWorkflow ["workflow-plan", "--plan", "release/plan.json", "--output", base.toString]
  let planUsage ← driveWorkflow ["workflow-plan", "--plan", "release/plan.json"]
  let mut rows := [
    check "workflow output: append succeeds" append.toOption.isSome,
    checkEq "workflow output: multiline framing preserves existing bytes" bytes
      ("existing=value\nfirst<<TL_RELEASE_OUTPUT_END\nvalue\nTL_RELEASE_OUTPUT_END\n" ++
       "paths<<TL_RELEASE_OUTPUT_END\ndist/a\ndist/b\nTL_RELEASE_OUTPUT_END\n"),
    check "workflow output: invalid key refuses before opening" invalid.toOption.isNone,
    checkEq "workflow output: invalid batch leaves file unchanged" afterInvalid unchanged,
    check "workflow output: directory destination refuses" directoryWrite.toOption.isNone,
    check "workflow output: empty batch refuses" (WorkflowOutput.render []).toOption.isNone,
    check "workflow output: duplicate keys refuse" (WorkflowOutput.render [("x", "a"), ("x", "b")]).toOption.isNone,
    check "workflow output: framing injection refuses"
      (WorkflowOutput.render [("x", "ok\nTL_RELEASE_OUTPUT_END\nother=bad")]).toOption.isNone,
    check "workflow output: carriage return refuses" (WorkflowOutput.render [("x", "bad\r")]).toOption.isNone,
    check "workflow output: empty key refuses" (WorkflowOutput.render [("", "value")]).toOption.isNone,
    checkEq "workflow plan: public command succeeds" planStatus 0,
    check "workflow plan: every channel is present"
      (Channel.all.all fun channel => (planned.splitOn (channel.wire ++ "<<TL_RELEASE_OUTPUT_END\n")).length == 2),
    checkEq "workflow plan: true and false decisions keep their values" planned
      (bytes ++ "github-release<<TL_RELEASE_OUTPUT_END\ntrue\nTL_RELEASE_OUTPUT_END\n" ++
       "installer<<TL_RELEASE_OUTPUT_END\ntrue\nTL_RELEASE_OUTPUT_END\n" ++
       "npm<<TL_RELEASE_OUTPUT_END\nfalse\nTL_RELEASE_OUTPUT_END\n" ++
       "homebrew<<TL_RELEASE_OUTPUT_END\nfalse\nTL_RELEASE_OUTPUT_END\n"),
    checkEq "workflow plan: malformed plan refuses" badPlanStatus 1,
    checkEq "workflow plan: absent plan refuses" absentPlanStatus 1,
    checkEq "workflow plan: output error propagates" planWriteStatus 1,
    checkEq "workflow plan: missing destination is usage" planUsage 2]
  let root := base / "checkout"
  IO.FS.createDirAll (root / "Tl/Cli")
  IO.FS.createDirAll (root / "Tl/Build")
  IO.FS.createDirAll (root / "tool")
  IO.FS.writeFile (root / "Tl/Cli/Commands.lean") "def productVersion : String := \"0.1.0\"\n"
  IO.FS.writeFile (root / "lean-toolchain") "leanprover/lean4:v4.33.1\n"
  IO.FS.writeFile (root / "lake-manifest.json") "{}\n"
  let _ ← fixtureGit root ["init", "-q"]
  let _ ← fixtureGit root ["add", "Tl/Cli/Commands.lean", "lean-toolchain", "lake-manifest.json"]
  let commitFixture := fixtureGit root ["-c", "commit.gpgsign=false", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
    "commit", "-qm", "fixture"]
  let _ ← commitFixture
  let link ← succeeded "ln" #["-s", (← IO.appPath).toString, (root / "tool/tlrelease").toString]
  if link.toOption.isNone then throw (IO.userError "could not plant the workflow tool fixture")
  let runStamp (refType refName : String) (destination : String := output) :=
    driveWorkflow ["workflow-stamp", "--root", root.toString, "--ref-type", refType,
      "--ref-name", refName, "--output", destination]
  let clean ← runStamp "tag" "v0.1.0"
  let stamp ← IO.FS.readFile (root / "Tl/Build/Stamp.lean")
  let head ← fixtureGit root ["rev-parse", "HEAD"]
  let stampedOutputs ← IO.FS.readFile output
  let digester ← Digester.resolve
  let expectedDigest ← match digester with
    | .error message => throw (IO.userError message)
    | .ok engine => do
      match ← engine.digest (root / "Tl/Build/Stamp.lean").toString with
      | .error message => throw (IO.userError message)
      | .ok digest => pure digest.hex
  let repeatStamp ← runStamp "branch" "main"
  let mismatch ← runStamp "tag" "v0.2.0"
  let badType ← runStamp "other" "main"
  let badDestination ← runStamp "tag" "v0.1.0" base.toString
  IO.FS.writeFile (root / "unexpected") "dirty"
  let dirty ← runStamp "branch" "main"
  IO.FS.removeFile (root / "unexpected")
  IO.FS.writeFile (root / "tool/sibling") "dirty"
  let dirtySibling ← runStamp "branch" "main"
  IO.FS.removeFile (root / "tool/sibling")
  IO.FS.writeFile (root / "lake-manifest.json") "{\"changed\":true}\n"
  let dirtyTracked ← runStamp "branch" "main"
  IO.FS.writeFile (root / "lake-manifest.json") "{}\n"
  rows := rows ++ [
    checkEq "workflow stamp: clean tagged checkout succeeds" clean 0,
    check "workflow stamp: source carries the checkout identity"
      ((stamp.splitOn s!"stampCommit : String := \"{head}\"").length == 2 &&
       (stamp.splitOn "stampDirty : Bool := false").length == 2),
    check "workflow stamp: all three authority outputs are written"
      (["version", "commit", "stampDigest"].all fun key =>
        (stampedOutputs.splitOn (key ++ "<<TL_RELEASE_OUTPUT_END\n")).length == 2),
    checkEq "workflow stamp: output values describe the actual bytes" stampedOutputs
      (planned ++ s!"version<<TL_RELEASE_OUTPUT_END\n0.1.0\nTL_RELEASE_OUTPUT_END\ncommit<<TL_RELEASE_OUTPUT_END\n{head}\nTL_RELEASE_OUTPUT_END\nstampDigest<<TL_RELEASE_OUTPUT_END\n{expectedDigest}\nTL_RELEASE_OUTPUT_END\n"),
    checkEq "workflow stamp: repeat excludes only its stamp and validated tool" repeatStamp 0,
    checkEq "workflow stamp: wrong tag refuses" mismatch 1,
    checkEq "workflow stamp: unknown ref type is usage" badType 2,
    checkEq "workflow stamp: output write failure refuses" badDestination 1,
    checkEq "workflow stamp: untracked source makes checkout dirty" dirty 1,
    checkEq "workflow stamp: tool sibling is not excluded" dirtySibling 1,
    checkEq "workflow stamp: tracked edits refuse" dirtyTracked 1]
  for (label, text) in [("missing version", "-- no version\n"),
      ("duplicate version", "def productVersion : String := \"0.1.0\"\ndef productVersion : String := \"0.1.0\"\n"),
      ("malformed version", "def productVersion : String := \"bad\"\n")] do
    IO.FS.writeFile (root / "Tl/Cli/Commands.lean") text
    let _ ← fixtureGit root ["add", "Tl/Cli/Commands.lean"]
    let _ ← commitFixture
    let status ← runStamp "branch" "main"
    rows := rows ++ [checkEq s!"workflow stamp: {label} refuses" status 1]
  IO.FS.writeFile (root / "Tl/Cli/Commands.lean") "def productVersion : String := \"0.1.0\"\n"
  let _ ← fixtureGit root ["add", "Tl/Cli/Commands.lean"]
  let _ ← commitFixture
  IO.FS.writeFile (root / "lean-toolchain") "not safe to embed\n"
  let _ ← fixtureGit root ["add", "lean-toolchain"]
  let _ ← commitFixture
  let invalidToolchain ← runStamp "branch" "main"
  IO.FS.removeFile (root / "tool/tlrelease")
  let missingTool ← runStamp "branch" "main"
  IO.FS.writeFile (root / "tool/tlrelease") "another file"
  let wrongTool ← runStamp "branch" "main"
  rows := rows ++ [
    checkEq "workflow stamp: unembeddable toolchain refuses" invalidToolchain 1,
    checkEq "workflow stamp: absent handoff tool refuses" missingTool 1,
    checkEq "workflow stamp: another file is not the running handoff tool" wrongTool 1]
  return rows

private def fixtureValue {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

/-- The process seam records the actual argv and fails each position in turn.
    No signing key, network, or publication service is involved. -/
def workflowReleaseTests : IO (List Outcome) := do
  let disclosureBuffer ← IO.mkRef { : IO.FS.Stream.Buffer }
  let disclosureResult ← IO.withStderr (IO.FS.Stream.ofBuffer disclosureBuffer) <|
    (WorkflowRelease.reportWrite (pure (.ok (some "committed, directory flush failed")))).run
  let disclosureText := String.fromUTF8! (← disclosureBuffer.get).data
  let cleanWrite ← (WorkflowRelease.reportWrite (pure (.ok none))).run
  let failedWrite ← (WorkflowRelease.reportWrite (pure (.error "write refused"))).run
  let text ← IO.FS.readFile "Tests/fixtures/release-manifest-golden.json"
  let manifest ← fixtureValue (ManifestDescription.parse "fixture" text)
  let names ← fixtureValue (WorkflowRelease.assetNames manifest)
  let tag := manifest.version
  let hash := manifest.commit.hex
  let other := String.ofList (List.replicate 40 'a')
  let ref := "refs/tags/" ++ tag.tag
  let mut rows := [
    check "write reporting: disclosure retains success" disclosureResult.toOption.isSome,
    checkEq "write reporting: disclosure is visible" disclosureText "committed, directory flush failed\n",
    check "write reporting: clean write succeeds" cleanWrite.toOption.isSome,
    check "write reporting: refusal propagates" failedWrite.toOption.isNone,
    checkEq "workflow release: flat sorted set includes manifest" names
      ["LICENSE", "release-manifest.json", "tl-linux-arm64", "tl-linux-x64"],
    checkOk "remote tag: lightweight" (WorkflowRelease.remoteCommit tag (hash ++ "\t" ++ ref ++ "\n")) manifest.commit,
    checkOk "remote tag: annotated chooses peeled" (WorkflowRelease.remoteCommit tag
      (other ++ "\t" ++ ref ++ "\n" ++ hash ++ "\t" ++ ref ++ "^{}\n")) manifest.commit]
  for (label, remote) in [("missing", ""), ("malformed row", hash),
      ("foreign ref", hash ++ "\trefs/heads/main\n"), ("bad commit", "short\t" ++ ref),
      ("peeled without object", hash ++ "\t" ++ ref ++ "^{}"),
      ("duplicate", hash ++ "\t" ++ ref ++ "\n" ++ hash ++ "\t" ++ ref)] do
    rows := rows ++ [check s!"remote tag: {label} refuses" (WorkflowRelease.remoteCommit tag remote).toOption.isNone]
  for name in ["", "..", ".", "-option", "../escape", "name\nother", "name space"] do
    rows := rows ++ [check s!"release set: unsafe name {repr name} refuses" (!WorkflowRelease.assetNameAllowed name)]
  let duplicate := { manifest with assets := manifest.assets ++ manifest.assets }
  rows := rows ++ [check "release set: duplicate assets refuse" (WorkflowRelease.assetNames duplicate).toOption.isNone]
  let identity : Identity := {
    repository := manifest.repository
    npmPackage := "@scope/tl"
    releaseWorkflow := "w"
    certificateOidcIssuer := "i"
    certificateIdentityRegexp := "e" }
  let expectedSource : List WorkflowRelease.Action := [
    ⟨.git, ["rev-parse", "HEAD"]⟩,
    ⟨.git, ["fetch", "--no-tags", "https://github.com/Owner/tl.git", "+refs/heads/main:refs/remotes/origin/main"]⟩,
    ⟨.git, ["merge-base", "--is-ancestor", hash, "origin/main"]⟩,
    ⟨.git, ["ls-remote", "https://github.com/Owner/tl.git", ref, ref ++ "^{}"]⟩]
  for failure in [0, 1, 2, 3, 4] do
    let calls ← IO.mkRef ([] : List WorkflowRelease.Action)
    let runner : WorkflowRelease.Runner := ⟨fun action => do
      let seen ← calls.get
      calls.set (seen ++ [action])
      if seen.length == failure then return .error "injected failure"
      return .ok { exitCode := 0, stderr := "", stdout :=
        if seen.isEmpty then hash ++ "\n" else if seen.length == 3 then hash ++ "\t" ++ ref ++ "\n" else "" }⟩
    let result ← (WorkflowRelease.checkSource runner identity tag manifest.commit).run
    rows := rows ++ [checkEq s!"source chain: failure {failure} stops" result.toOption.isSome (failure == 4),
      checkEq s!"source chain: exact argv through position {failure}" (← calls.get) (expectedSource.take (failure + 1))]
  for (label, head, remote) in [("changed checkout", other, hash), ("changed tag", hash, other),
      ("invalid checkout", "bad", hash), ("missing tag", hash, "")] do
    let calls ← IO.mkRef (0 : Nat)
    let runner : WorkflowRelease.Runner := ⟨fun _ => do
      let index ← calls.get
      calls.set (index + 1)
      return .ok { exitCode := 0, stderr := "", stdout :=
        if index == 0 then head else if index == 3 && !remote.isEmpty then remote ++ "\t" ++ ref else "" }⟩
    let result ← (WorkflowRelease.checkSource runner identity tag manifest.commit).run
    rows := rows ++ [check s!"source chain: {label} refuses" result.toOption.isNone]
  let base ← IO.FS.createTempDir
  let dist := base.toString
  IO.FS.writeFile (base / "release-manifest.json") text
  for name in names.filter (· != "release-manifest.json") do IO.FS.writeFile (base / name) ("bytes of " ++ name)
  let expectedVerify : List WorkflowRelease.Action := [
    ⟨.verifier, ["--selftest"]⟩,
    ⟨.verifier, ["--require-signature", dist, "release-manifest.json"]⟩,
    ⟨.verifier, ["--require-signature", dist, "LICENSE", "release-manifest.json", "tl-linux-arm64", "tl-linux-x64"]⟩,
    ⟨.releaseTool, ["manifest-verify", "--dist", dist, "--manifest", dist ++ "/release-manifest.json"]⟩]
  for failure in [0, 1, 2, 3, 4] do
    let calls ← IO.mkRef ([] : List WorkflowRelease.Action)
    let runner : WorkflowRelease.Runner := ⟨fun action => do
      let seen ← calls.get
      calls.set (seen ++ [action])
      return if seen.length == failure then .error "injected refusal"
        else .ok { exitCode := 0, stdout := "", stderr := "" }⟩
    let result ← (WorkflowRelease.verify runner dist).run
    rows := rows ++ [checkEq s!"verification: failure {failure} stops" result.toOption.isSome (failure == 4),
      checkEq s!"verification: authentication precedes manifest use {failure}" (← calls.get) (expectedVerify.take (failure + 1))]
  let expectedSigning : List WorkflowRelease.Action := ("SHA256SUMS" :: names).map fun name =>
    ⟨.cosign, ["sign-blob", "--yes", dist ++ "/" ++ name, "--bundle", dist ++ "/" ++ name ++ ".sigstore.json"]⟩
  let output := (base / "output").toString
  for failure in [0, 1, 2, 3, 4, 5, 6] do
    IO.FS.writeFile output ""
    let calls ← IO.mkRef ([] : List WorkflowRelease.Action)
    let runner : WorkflowRelease.Runner := ⟨fun action => do
      let seen ← calls.get
      calls.set (seen ++ [action])
      return if seen.length == failure then .error "injected refusal"
        else .ok { exitCode := 0, stdout := "", stderr := "" }⟩
    let result ← (WorkflowRelease.sign runner dist output).run
    let expected := expectedVerify.drop 3 ++ expectedSigning
    let written ← IO.FS.readFile output
    rows := rows ++ [checkEq s!"signing: failure {failure} stops" result.toOption.isSome (failure == 6),
      checkEq s!"signing: exact argv through position {failure}" (← calls.get) (expected.take (failure + 1)),
      checkEq s!"signing: subjects emitted only after every signature {failure}" written.isEmpty (failure != 6)]
  let expectedSubjects ← fixtureValue (WorkflowOutput.render [("paths", String.intercalate "\n" (names.map (dist ++ "/" ++ ·)))])
  rows := rows ++ [checkEq "signing: exact multiline subjects" (← IO.FS.readFile output) expectedSubjects]
  let digester ← fixtureValue (← Digester.resolve)
  let mut expectedSums : Array String := #[]
  for name in names do
    let digest ← fixtureValue (← digester.digest (dist ++ "/" ++ name))
    expectedSums := expectedSums.push (digest.hex ++ "  " ++ name ++ "\n")
  rows := rows ++ [checkEq "signing: checksums describe actual asset bytes" (← IO.FS.readFile (base / "SHA256SUMS")) (String.join expectedSums.toList)]
  for reserved in ["SHA256SUMS", "tl-linux-x64.sigstore.json"] do
    rows := rows ++ [check s!"signing: reserved asset {reserved} refuses"
      (!WorkflowRelease.assetSetAllowed [reserved])]
    let planted := text.replace "\"assets\": ["
      ("\"assets\": [{\"kind\":\"notice\",\"name\":\"" ++ reserved ++ "\",\"sha256\":\"" ++
        String.ofList (List.replicate 64 'c') ++ "\"},")
    let _ ← fixtureValue (ManifestDescription.parse "reserved asset fixture" planted)
    IO.FS.writeFile (base / "release-manifest.json") planted
    IO.FS.writeFile output ""
    let calls ← IO.mkRef ([] : List WorkflowRelease.Action)
    let runner : WorkflowRelease.Runner := ⟨fun action => do
      calls.modify (· ++ [action])
      return .ok { exitCode := 0, stdout := "", stderr := "" }⟩
    let result ← (WorkflowRelease.sign runner dist output).run
    rows := rows ++ [check s!"signing: reserved manifest asset {reserved} refuses" result.toOption.isNone,
      checkEq s!"signing: reserved asset {reserved} never reaches cosign" (← calls.get) (expectedVerify.drop 3),
      checkEq s!"signing: reserved asset {reserved} emits no subjects" (← IO.FS.readFile output) ""]
    IO.FS.writeFile (base / "release-manifest.json") text
  let identityPath := (base / "identity.json").toString
  IO.FS.writeFile identityPath "{\"repository\":\"Owner/tl\",\"npmPackage\":\"@scope/tl\",\"releaseWorkflow\":\"w\",\"certificateOidcIssuer\":\"i\",\"certificateIdentityRegexp\":\"e\"}"
  let notes := s!"Built from `{hash}` with `{manifest.toolchain}`.\n\nVerify before running: https://github.com/Owner/tl/blob/{tag.tag}/VERIFYING.md\nEvery asset and SHA256SUMS carries a Sigstore bundle."
  let files := ["SHA256SUMS", "LICENSE", "release-manifest.json", "tl-linux-arm64", "tl-linux-x64"].flatMap
    fun name => [dist ++ "/" ++ name, dist ++ "/" ++ name ++ ".sigstore.json"]
  let expectedPublish := expectedVerify ++ expectedSource ++ [⟨WorkflowRelease.Program.gh,
    ["release", "create", tag.tag, "--repo", "Owner/tl", "--verify-tag", "--title", tag.tag, "--notes", notes] ++ files⟩]
  for failure in List.range 10 do
    let calls ← IO.mkRef ([] : List WorkflowRelease.Action)
    let runner : WorkflowRelease.Runner := ⟨fun action => do
      let seen ← calls.get
      calls.set (seen ++ [action])
      if seen.length == failure then return .error "injected refusal"
      return .ok { exitCode := 0, stderr := "", stdout :=
        if seen.length == 4 then hash else if seen.length == 7 then hash ++ "\t" ++ ref else "" }⟩
    let result ← (WorkflowRelease.publish runner dist identityPath tag manifest.commit).run
    rows := rows ++ [checkEq s!"publication: failure {failure} stops" result.toOption.isSome (failure == 9),
      checkEq s!"publication: exact argv through position {failure}" (← calls.get) (expectedPublish.take (failure + 1))]
  let wrongTag ← fixtureValue (Version.parseTag "fixture" "v9.9.9")
  let wrongCommit ← fixtureValue (Commit.parse "fixture" other)
  for (label, expectedTag, expectedCommit) in [("tag", wrongTag, manifest.commit), ("commit", tag, wrongCommit)] do
    let calls ← IO.mkRef ([] : List WorkflowRelease.Action)
    let runner : WorkflowRelease.Runner := ⟨fun action => do
      calls.modify (· ++ [action])
      return .ok { exitCode := 0, stdout := "", stderr := "" }⟩
    let result ← (WorkflowRelease.publish runner dist identityPath expectedTag expectedCommit).run
    rows := rows ++ [check s!"publication: another {label} refuses" result.toOption.isNone,
      checkEq s!"publication: another {label} cannot reach remote effects" (← calls.get) expectedVerify]
  let prerelease ← fixtureValue (Version.parse "fixture" "1.2.3-rc.1")
  rows := rows ++ [checkEq "publication: prerelease flag" (WorkflowRelease.prereleaseArgs prerelease) ["--prerelease"],
    checkEq "publication: stable has no prerelease flag" (WorkflowRelease.prereleaseArgs tag) []]
  let staging ← IO.FS.createTempDir
  let stagingPath := staging.toString
  let expectedPrepare : List WorkflowRelease.Action := [
    ⟨.releaseTool, ["sbom", "--version", tag.render, "--toolchain", "lean-toolchain", "--lake-manifest", "lake-manifest.json",
      "--output-dir", stagingPath, "--output", "tl-1.2.3.spdx.json"]⟩,
    ⟨.releaseTool, ["manifest", "--dist", stagingPath, "--tag", tag.tag, "--commit", hash,
      "--toolchain", "lean-toolchain", "--lake-manifest", "lake-manifest.json", "--targets", "release/targets.json",
      "--identity", "release/identity.json", "--workflow-ref", "fixture-workflow", "--run-id", "42",
      "--output-dir", stagingPath, "--output", "release-manifest.json"]⟩]
  for failure in [0, 1, 2] do
    let calls ← IO.mkRef ([] : List WorkflowRelease.Action)
    let runner : WorkflowRelease.Runner := ⟨fun action => do
      let seen ← calls.get
      calls.set (seen ++ [action])
      return if seen.length == failure then .error "injected refusal"
        else .ok { exitCode := 0, stdout := "", stderr := "" }⟩
    let result ← (WorkflowRelease.prepare runner stagingPath tag manifest.commit "fixture-workflow" "42").run
    rows := rows ++ [checkEq s!"prepare: failure {failure} stops" result.toOption.isSome (failure == 2),
      checkEq s!"prepare: explicit inputs through position {failure}" (← calls.get) (expectedPrepare.take (failure + 1))]
  for name in ["LICENSE", "THIRD-PARTY-LICENSES", "REBUILDING.md"] do
    rows := rows ++ [checkEq s!"prepare: {name} copied exactly" (← IO.FS.readFile (staging / name)) (← IO.FS.readFile name)]
  let publicRoot ← IO.FS.createTempDir
  IO.FS.createDirAll (publicRoot / "scripts")
  let verifier := publicRoot / "scripts/verify-release-artifacts.sh"
  IO.FS.writeFile verifier "#!/bin/sh\nprintf '%s\\n' \"$*\" >> verifier-calls\nexit 0\n"
  let mode ← IO.Process.output { cmd := "chmod", args := #["755", verifier.toString] }
  if mode.exitCode != 0 then throw (IO.userError "could not make the verifier fixture executable")
  let binary ← IO.FS.realPath ".lake/build/bin/tlrelease"
  let publicVerify ← IO.Process.output {
    cmd := binary.toString, cwd := some publicRoot,
    args := #["workflow-verify", "--dist", dist] }
  let observed ← IO.FS.readFile (publicRoot / "verifier-calls")
  rows := rows ++ [
    checkEq "public verification: real manifest checker rejects invented fixture digests" publicVerify.exitCode 1,
    checkEq "public verification: default runner executes verifier before self command" observed
      ("--selftest\n--require-signature " ++ dist ++ " release-manifest.json\n--require-signature " ++ dist ++
       " LICENSE release-manifest.json tl-linux-arm64 tl-linux-x64\n")]
  IO.FS.writeFile verifier "#!/bin/sh\nexit 17\n"
  let publicFailure ← IO.Process.output {
    cmd := binary.toString, cwd := some publicRoot,
    args := #["workflow-verify", "--dist", dist] }
  IO.FS.removeFile verifier
  let publicMissing ← IO.Process.output {
    cmd := binary.toString, cwd := some publicRoot,
    args := #["workflow-verify", "--dist", dist] }
  rows := rows ++ [checkEq "public verification: child refusal propagates" publicFailure.exitCode 1,
    checkEq "public verification: missing verifier refuses" publicMissing.exitCode 1]
  let recorded ← IO.mkRef ([] : List WorkflowRelease.Action)
  let passing : WorkflowRelease.Runner := ⟨fun action => do
    recorded.modify (· ++ [action])
    return .ok { exitCode := 0, stdout := "", stderr := "" }⟩
  for malformed in [false, true] do
    if malformed then IO.FS.writeFile (base / "release-manifest.json") "{}"
    else IO.FS.removeFile (base / "release-manifest.json")
    recorded.set []
    let verification ← (WorkflowRelease.verify passing dist).run
    rows := rows ++ [check s!"verification: unreadable manifest {malformed} refuses" verification.toOption.isNone,
      checkEq s!"verification: authenticate before parsing even malformed input {malformed}"
        (← recorded.get) (expectedVerify.take 2)]
    recorded.set []
    let signing ← (WorkflowRelease.sign passing dist output).run
    rows := rows ++ [check s!"signing: unreadable manifest {malformed} refuses" signing.toOption.isNone,
      checkEq s!"signing: unreadable manifest {malformed} never signs" (← recorded.get) (expectedVerify.drop 3)]
    IO.FS.writeFile (base / "release-manifest.json") text
  IO.FS.removeFile (base / "LICENSE")
  recorded.set []
  let missingAsset ← (WorkflowRelease.sign passing dist output).run
  rows := rows ++ [check "signing: missing asset refuses" missingAsset.toOption.isNone,
    checkEq "signing: missing asset never signs" (← recorded.get) (expectedVerify.drop 3)]
  IO.FS.writeFile (base / "LICENSE") "bytes of LICENSE"
  IO.FS.removeFile (base / "SHA256SUMS")
  IO.FS.createDir (base / "SHA256SUMS")
  recorded.set []
  let sumsFailure ← (WorkflowRelease.sign passing dist output).run
  rows := rows ++ [check "signing: sums destination refusal propagates" sumsFailure.toOption.isNone,
    checkEq "signing: sums write failure never signs" (← recorded.get) (expectedVerify.drop 3)]
  IO.FS.removeDir (base / "SHA256SUMS")
  recorded.set []
  let outputFailure ← (WorkflowRelease.sign passing dist dist).run
  rows := rows ++ [check "signing: output destination refusal propagates" outputFailure.toOption.isNone,
    checkEq "signing: output failure occurs after signatures" (← recorded.get) (expectedVerify.drop 3 ++ expectedSigning)]
  let badStaging := staging / "bad-staging"
  IO.FS.writeFile badStaging "file, not directory"
  recorded.set []
  let stagingFailure ← (WorkflowRelease.prepare passing badStaging.toString tag manifest.commit "workflow" "42").run
  rows := rows ++ [check "prepare: destination refusal propagates" stagingFailure.toOption.isNone,
    checkEq "prepare: destination refusal never invokes generators" (← recorded.get) []]
  for (label, contents) in [("malformed", "{}"), ("missing", ""),
      ("another repository", "{\"repository\":\"Other/tl\",\"npmPackage\":\"@scope/tl\",\"releaseWorkflow\":\"w\",\"certificateOidcIssuer\":\"i\",\"certificateIdentityRegexp\":\"e\"}")] do
    if contents.isEmpty then IO.FS.removeFile identityPath else IO.FS.writeFile identityPath contents
    recorded.set []
    let result ← (WorkflowRelease.publish passing dist identityPath tag manifest.commit).run
    rows := rows ++ [check s!"publication: {label} identity refuses" result.toOption.isNone,
      checkEq s!"publication: {label} identity never reaches remote effects" (← recorded.get) expectedVerify]
  return rows

end Tl.Tests
