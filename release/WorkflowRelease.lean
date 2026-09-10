/- Typed orchestration for the release jobs. Every child is an explicit argv;
   failures stop the sequence before a later signing or publication effect. -/
import release.Manifest
import release.WorkflowOutput

namespace Release.WorkflowRelease

inductive Program where
  | git | cosign | gh | releaseTool | verifier
  deriving DecidableEq, Repr

structure Action where
  program : Program
  args : List String
  deriving DecidableEq, Repr

structure Runner where
  invoke : Action → IO (Except String ProcessOutput)

def defaultRunner : Runner := ⟨fun action => do
  match action.program with
  | .git => succeededGit action.args.toArray
  | .cosign => succeeded "cosign" action.args.toArray 600000
  | .gh => succeeded "gh" action.args.toArray 600000
  | .releaseTool => succeeded (← IO.appPath).toString action.args.toArray 600000
  | .verifier => succeeded "./scripts/verify-release-artifacts.sh" action.args.toArray 600000⟩

def perform (runner : Runner) (action : Action) : Decision ProcessOutput :=
  ofIO (runner.invoke action)

def execute (runner : Runner) (actions : List Action) : Decision Unit := do
  for action in actions do
    let result ← perform runner action
    if !result.stdout.isEmpty then IO.print result.stdout
    if !result.stderr.isEmpty then IO.eprint result.stderr

/-- A committed write may still disclose a failed directory flush. -/
def reportWrite (result : IO (Except String (Option String))) : Decision Unit := do
  if let some disclosure ← ofIO result then IO.eprintln disclosure

def manifestName : String := "release-manifest.json"

def assetNameAllowed (name : String) : Bool :=
  !name.isEmpty && !name.startsWith "-" && name != "." && name != ".." &&
    name.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.')

def assetSetAllowed (names : List String) : Bool :=
  names.eraseDups.length == names.length && names.all (fun name =>
    assetNameAllowed name && name != "SHA256SUMS" && !name.endsWith ".sigstore.json")

theorem assetSetAllowed_iff (names : List String) :
    assetSetAllowed names = true ↔ names.eraseDups.length = names.length ∧
      ∀ name ∈ names, assetNameAllowed name = true ∧ name ≠ "SHA256SUMS" ∧
        name.endsWith ".sigstore.json" = false := by
  simp only [assetSetAllowed, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, WorkflowOutput.negation_iff]
  constructor
  · rintro ⟨distinct, accepted⟩
    exact ⟨distinct, fun name member => ⟨(accepted name member).1.1,
      (accepted name member).1.2, (accepted name member).2⟩⟩
  · rintro ⟨distinct, accepted⟩
    exact ⟨distinct, fun name member => ⟨⟨(accepted name member).1,
      (accepted name member).2.1⟩, (accepted name member).2.2⟩⟩

/-- The manifest is authenticated as a member of the set it describes. -/
def assetNames (description : ManifestDescription) : Except String (List String) := do
  let names := (description.assets.map (·.name)) ++ [manifestName]
  if !assetSetAllowed names then
    throw "the manifest has repeated or unsafe asset names; regenerate it from the flat candidate directory"
  return names.mergeSort (· ≤ ·)

def sourceAgrees (expected head remote : Commit) : Bool :=
  expected == head && expected == remote

theorem sourceAgrees_iff (expected head remote : Commit) :
    sourceAgrees expected head remote = true ↔ expected = head ∧ expected = remote := by
  simp only [sourceAgrees, Bool.and_eq_true, beq_iff_eq]

/-- Read only the two exact refs requested from ls-remote; annotated tags
    select the peeled commit. Missing, duplicate and foreign refs refuse. -/
def remoteCommit (tag : Version) (text : String) : Except String Commit := do
  let base := "refs/tags/" ++ tag.tag
  let mut found : List (String × Commit) := []
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [hash, name] := line.splitOn "\t"
      | throw "git returned a malformed tag row; retry the remote lookup and inspect the transport"
    if (name != base && name != base ++ "^{}") || (found.map Prod.fst).contains name then
      throw "git returned duplicate or unexpected tag refs; restore one unambiguous release tag"
    let commit ← Commit.parse "remote tag" hash
    found := (name, commit) :: found
  match found.lookup (base ++ "^{}"), found.lookup base with
  | some commit, some _ => return commit
  | none, some commit => return commit
  | _, _ => throw "the remote tag is missing or has no tag object; restore the intended tag before releasing"

def checkSource (runner : Runner) (identity : Identity) (tag : Version) (expected : Commit) : Decision Unit := do
  let headOutput ← perform runner ⟨.git, ["rev-parse", "HEAD"]⟩
  let head ← ofExcept (Commit.parse "checkout HEAD" headOutput.stdout.trimAscii.toString)
  let _ ← perform runner ⟨.git, ["fetch", "--no-tags", "https://github.com/" ++ identity.repository ++ ".git", "+refs/heads/main:refs/remotes/origin/main"]⟩
  let _ ← perform runner ⟨.git, ["merge-base", "--is-ancestor", expected.hex, "origin/main"]⟩
  let remote ← perform runner ⟨.git, ["ls-remote", "https://github.com/" ++ identity.repository ++ ".git",
    "refs/tags/" ++ tag.tag, "refs/tags/" ++ tag.tag ++ "^{}"]⟩
  let actual ← ofExcept (remoteCommit tag remote.stdout)
  if !sourceAgrees expected head actual then
    decline "the checkout or remote tag no longer matches the built commit; restore the intended tag and rebuild before publishing"

def verificationActions (dist : String) (names : List String) : List Action :=
  [⟨.verifier, ["--require-signature", dist] ++ names⟩,
   ⟨.releaseTool, ["manifest-verify", "--dist", dist, "--manifest", dist ++ "/" ++ manifestName]⟩]

def verify (runner : Runner) (dist : String) : Decision ManifestDescription := do
  execute runner [⟨.verifier, ["--selftest"]⟩,
    ⟨.verifier, ["--require-signature", dist, manifestName]⟩]
  let description ← readParsed (dist ++ "/" ++ manifestName) ManifestDescription.parse
  let names ← ofExcept (assetNames description)
  execute runner (verificationActions dist names)
  return description

def signingActions (dist : String) (names : List String) : List Action :=
  ("SHA256SUMS" :: names).map fun name =>
    ⟨.cosign, ["sign-blob", "--yes", dist ++ "/" ++ name,
      "--bundle", dist ++ "/" ++ name ++ ".sigstore.json"]⟩

/-- Exactly the authenticated assets and their bundles are offered to GitHub. -/
def publicationFiles (dist : String) (names : List String) : List String :=
  ("SHA256SUMS" :: names).flatMap fun name =>
    [dist ++ "/" ++ name, dist ++ "/" ++ name ++ ".sigstore.json"]

def prereleaseArgs (version : Version) : List String :=
  if version.isPrerelease then ["--prerelease"] else []

theorem prereleaseArgs_nonempty_iff (version : Version) :
    prereleaseArgs version ≠ [] ↔ version.isPrerelease = true := by
  unfold prereleaseArgs
  cases h : version.isPrerelease with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  | true => simp only [↓reduceIte, ne_eq, List.cons_ne_nil, not_false_eq_true]

def prepare (runner : Runner) (dist : String) (tag : Version) (commit : Commit)
    (workflowRef runId : String) : Decision Unit := do
  let directory ← ofExcept (Write.OutputDirectory.parse "--dist" dist)
  for name in ["LICENSE", "THIRD-PARTY-LICENSES", "REBUILDING.md"] do
    let text ← ofIO (readTextFile name)
    let path ← ofExcept (Write.OutputPath.parse "the compliance asset" name)
    reportWrite (writeEvidence directory path text)
  execute runner [
    ⟨.releaseTool, ["sbom", "--version", tag.render, "--toolchain", "lean-toolchain",
      "--lake-manifest", "lake-manifest.json", "--output-dir", dist,
      "--output", "tl-" ++ tag.render ++ ".spdx.json"]⟩,
    ⟨.releaseTool, ["manifest", "--dist", dist, "--tag", tag.tag, "--commit", commit.hex,
      "--toolchain", "lean-toolchain", "--lake-manifest", "lake-manifest.json",
      "--targets", "release/targets.json", "--identity", "release/identity.json",
      "--workflow-ref", workflowRef, "--run-id", runId, "--output-dir", dist, "--output", manifestName]⟩]

def sign (runner : Runner) (dist output : String) : Decision Unit := do
  execute runner [⟨.releaseTool, ["manifest-verify", "--dist", dist, "--manifest", dist ++ "/" ++ manifestName]⟩]
  let description ← readParsed (dist ++ "/" ++ manifestName) ManifestDescription.parse
  let names ← ofExcept (assetNames description)
  let digester ← ofIO Digester.resolve
  let mut sums : Array String := #[]
  for name in names do
    let digest ← ofIO (digester.digest (dist ++ "/" ++ name))
    sums := sums.push (digest.hex ++ "  " ++ name ++ "\n")
  let directory ← ofExcept (Write.OutputDirectory.parse "--dist" dist)
  let path ← ofExcept (Write.OutputPath.parse "the sums file" "SHA256SUMS")
  reportWrite (writeEvidence directory path (String.join sums.toList))
  execute runner (signingActions dist names)
  ofIO (WorkflowOutput.write output [("paths", String.intercalate "\n" (names.map (dist ++ "/" ++ ·)))])

def releaseMatches (description : ManifestDescription) (tag : Version) (commit : Commit) : Bool :=
  description.version == tag && description.commit == commit

theorem releaseMatches_iff (description : ManifestDescription) (tag : Version) (commit : Commit) :
    releaseMatches description tag commit = true ↔ description.version = tag ∧ description.commit = commit := by
  simp only [releaseMatches, Bool.and_eq_true, beq_iff_eq]

def publish (runner : Runner) (dist identityPath : String) (tag : Version) (commit : Commit) : Decision Unit := do
  let description ← verify runner dist
  if !releaseMatches description tag commit then
    decline "the signed manifest belongs to another tag or commit; download the signed set from this release run"
  let identity ← readParsed identityPath Identity.parse
  if description.repository != identity.repository then
    decline "the signed manifest names another repository; select the release matching the checked-out identity"
  checkSource runner identity description.version description.commit
  let names ← ofExcept (assetNames description)
  let notes := s!"Built from `{description.commit.hex}` with `{description.toolchain}`.\n\nVerify before running: https://github.com/{identity.repository}/blob/{description.tag}/VERIFYING.md\nEvery asset and SHA256SUMS carries a Sigstore bundle."
  execute runner [⟨.gh, ["release", "create", description.tag, "--repo", identity.repository,
    "--verify-tag", "--title", description.tag, "--notes", notes] ++
    prereleaseArgs description.version ++ publicationFiles dist names⟩]

def verifyContext (runner : Runner) (dist : String) (tag : Version) (commit : Commit) : Decision ManifestDescription := do
  let description ← verify runner dist
  if !releaseMatches description tag commit then
    decline "the signed manifest belongs to another tag or commit; download the signed set from this release run"
  return description

def homebrewPublication (push : Bool) (dist output tap : String) : List Action :=
  if push then [
    ⟨.gh, ["auth", "setup-git", "--hostname", "github.com"]⟩,
    ⟨.gh, ["repo", "clone", tap, output ++ "/tap", "--", "--depth", "1"]⟩,
    ⟨.releaseTool, ["homebrew-publish", "--dist", dist, "--manifest", dist ++ "/" ++ manifestName,
      "--tap", output ++ "/tap"]⟩]
  else []

theorem homebrewPublication_nonempty_iff (push : Bool) (dist output tap : String) :
    homebrewPublication push dist output tap ≠ [] ↔ push = true := by
  cases push <;> simp only [homebrewPublication, Bool.false_eq_true, ↓reduceIte,
    ne_eq, not_true_eq_false, List.cons_ne_nil, not_false_eq_true]

def homebrew (runner : Runner) (dist output : String) (tag : Version) (commit : Commit)
    (credential : Option String) : Decision Unit := do
  let description ← verifyContext runner dist tag commit
  if description.homebrew.push && (credential.getD "").isEmpty then
    decline "the stable Homebrew release needs GH_TOKEN; configure HOMEBREW_TAP_TOKEN for the protected release environment or defer the channel in release/plan.json"
  let _ ← ofExcept (Write.OutputDirectory.parse "--output-dir" output)
  attempt "creating the formula output directory; choose a writable --output-dir" (IO.FS.createDirAll output)
  execute runner [⟨.releaseTool, ["homebrew-render", "--dist", dist,
    "--manifest", dist ++ "/" ++ manifestName, "--output", "tl.rb", "--output-dir", output]⟩]
  execute runner (homebrewPublication description.homebrew.push dist output description.homebrew.tap)

private def valueOption (name : String) : OptionSpec := { name, takesValue := true }

def commands : List Command := [
  optionCommand "workflow-source" "--identity <identity.json> --tag <tag> --commit <sha>"
    "Refuse unless checkout, protected main and the remote tag identify the built commit."
    ["--identity", "release/identity.json", "--tag", "v0.1.0", "--commit", String.ofList (List.replicate 40 'a')]
    (["identity", "tag", "commit"].map valueOption)
    (fun options => do return (← options.required "identity",
      ← Version.parseTag "--tag" (← options.required "tag"), ← Commit.parse "--commit" (← options.required "commit")))
    (fun (path, tag, commit) => do
      checkSource defaultRunner (← readParsed path Identity.parse) tag commit
      return "checkout, protected main and remote tag agree"),
  optionCommand "workflow-prepare" "--dist <dir> --tag <tag> --commit <sha> --workflow-ref <ref> --run-id <id>"
    "Assemble compliance assets and the manifest from the current build evidence."
    ["--dist", "dist", "--tag", "v0.1.0", "--commit", String.ofList (List.replicate 40 'a'),
      "--workflow-ref", "owner/repo/.github/workflows/release.yml@refs/tags/v0.1.0", "--run-id", "1"]
    (["dist", "tag", "commit", "workflow-ref", "run-id"].map valueOption)
    (fun options => do return (← options.required "dist", ← Version.parseTag "--tag" (← options.required "tag"),
      ← Commit.parse "--commit" (← options.required "commit"), ← options.required "workflow-ref", ← options.required "run-id"))
    (fun (dist, tag, commit, workflowRef, runId) => do
      prepare defaultRunner dist tag commit workflowRef runId
      return "prepared the release manifest and compliance assets"),
  optionCommand "workflow-sign" "--dist <dir> --output <runner-output-file>"
    "Hash and sign the manifest's exact set, then emit the attestation subjects."
    ["--dist", "dist", "--output", "github-output"] (["dist", "output"].map valueOption)
    (fun options => do return (← options.required "dist", ← options.required "output"))
    (fun (dist, output) => do sign defaultRunner dist output; return "signed the exact release set"),
  optionCommand "workflow-verify" "--dist <dir> --tag <tag> --commit <sha>"
    "Authenticate the received set before checking its manifest."
    ["--dist", "dist", "--tag", "v0.1.0", "--commit", String.ofList (List.replicate 40 'a')]
    (["dist", "tag", "commit"].map valueOption)
    (fun options => do return (← options.required "dist", ← Version.parseTag "--tag" (← options.required "tag"),
      ← Commit.parse "--commit" (← options.required "commit")))
    (fun (dist, tag, commit) => do let _ ← verifyContext defaultRunner dist tag commit; return "authenticated the received release set"),
  optionCommand "workflow-homebrew" "--dist <dir> --output-dir <dir> --tag <tag> --commit <sha>"
    "Authenticate and render the formula; publish only when the signed manifest requests it."
    ["--dist", "dist", "--output-dir", "out", "--tag", "v0.1.0", "--commit", String.ofList (List.replicate 40 'a')]
    (["dist", "output-dir", "tag", "commit"].map valueOption)
    (fun options => do return (← options.required "dist", ← options.required "output-dir",
      ← Version.parseTag "--tag" (← options.required "tag"), ← Commit.parse "--commit" (← options.required "commit")))
    (fun (dist, output, tag, commit) => do
      homebrew defaultRunner dist output tag commit (← IO.getEnv "GH_TOKEN")
      return "rendered the authenticated formula and completed its declared publication effects"),
  optionCommand "workflow-publish" "--dist <dir> --identity <identity.json> --tag <tag> --commit <sha>"
    "Authenticate, recheck source identity, and publish exactly the signed set to GitHub."
    ["--dist", "dist", "--identity", "release/identity.json", "--tag", "v0.1.0", "--commit", String.ofList (List.replicate 40 'a')]
    (["dist", "identity", "tag", "commit"].map valueOption)
    (fun options => do return (← options.required "dist", ← options.required "identity",
      ← Version.parseTag "--tag" (← options.required "tag"), ← Commit.parse "--commit" (← options.required "commit")))
    (fun (dist, identity, tag, commit) => do publish defaultRunner dist identity tag commit; return "published the verified GitHub release")]

end Release.WorkflowRelease
