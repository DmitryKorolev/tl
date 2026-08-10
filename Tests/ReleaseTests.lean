/-
`Tests.ReleaseTests` -- the release-machinery guards.

Two of them:

1. A drift guard for the signed-release identity pinned by ADR-0006 /
   ADR-0014. `release/identity.json` is the machine-readable current pin;
   VERIFYING.md and the ADR must carry the same operative values. The installer
   and Homebrew formula join this guard when their files land.
2. Build provenance (`tl version`): every `Tl.Build.Kind` branch of both
   renderings, and a drift guard binding the generated `Tl.Build.Stamp` pins to
   `lean-toolchain` / `lake-manifest.json` on disk — the compiled constants
   cannot be varied at test time, so the renderings are exercised through
   explicit `Provenance` values and the *compiled* one is checked separately.

Tested release shell (ADR-0004); no Mathlib (ADR-0009).
-/
import Lean.Data.Json
import Tests.Harness
import Tests.JsonUtil
import Tl.Build.Provenance
import Tl.Cli.Commands
import Tl.Hash.Sha256

namespace Tl.Tests

open Lean (Json)
open System (FilePath)

private def has (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

private def readRequired (path : FilePath) : IO (Except String String) := do
  if !(← path.pathExists) then
    return .error s!"missing {path} under cwd {(← IO.currentDir)}"
  return .ok (← IO.FS.readFile path)

def releaseIdentityTests : IO (List Outcome) := do
  let configPath : FilePath := "release/identity.json"
  let verifyingPath : FilePath := "VERIFYING.md"
  let distributionPath : FilePath := "docs/adr/ADR-0006-distribution-and-platforms.md"
  let threatPath : FilePath := "docs/adr/ADR-0014-threat-model.md"
  let installerPath : FilePath := "install.sh"
  let configRaw ← readRequired configPath
  let verifyingRaw ← readRequired verifyingPath
  let distributionRaw ← readRequired distributionPath
  let threatRaw ← readRequired threatPath
  let mut outs := [
    check "release identity: canonical config exists" configRaw.isOk s!"{configRaw}",
    check "release identity: VERIFYING.md exists" verifyingRaw.isOk s!"{verifyingRaw}",
    check "release identity: ADR-0006 exists" distributionRaw.isOk s!"{distributionRaw}",
    check "release identity: ADR-0014 exists" threatRaw.isOk s!"{threatRaw}" ]
  let some configText := configRaw.toOption
    | return outs
  let some config := (Json.parse configText).toOption
    | return outs ++ [check "release identity: canonical config parses as JSON" false
        "release/identity.json is malformed"]
  outs := outs ++ [check "release identity: canonical config parses as JSON" true]
  let fields := ["repository", "npmPackage", "releaseWorkflow",
    "certificateOidcIssuer", "certificateIdentityRegexp"]
  for field in fields do
    outs := outs ++ [check s!"release identity: canonical field {field} is present"
      (jStr config field).isSome s!"release/identity.json lacks string field {field}"]
  let some repository := jStr config "repository" | return outs
  let some npmPackage := jStr config "npmPackage" | return outs
  let some workflow := jStr config "releaseWorkflow" | return outs
  let some issuer := jStr config "certificateOidcIssuer" | return outs
  let some identity := jStr config "certificateIdentityRegexp" | return outs
  outs := outs ++ [
    checkEq "release identity: final repository is pinned" repository "DmitryKorolev/tl",
    checkEq "release identity: npm package is pinned" npmPackage "@taskloop/tl",
    checkEq "release identity: direct workflow path is pinned" workflow ".github/workflows/release.yml",
    checkEq "release identity: GitHub OIDC issuer is pinned" issuer
      "https://token.actions.githubusercontent.com",
    check "release identity: certificate expression is start-anchored" (identity.startsWith "^") identity,
    check "release identity: certificate expression is end-anchored" (identity.endsWith "$") identity,
    check "release identity: certificate expression fixes repository and workflow"
      (has identity "DmitryKorolev/tl/\\.github/workflows/release\\.yml@refs/tags/v") identity ]
  -- The installer is a piped shell script: it cannot read release/identity.json
  -- out of a checkout, so it carries its own copy of the issuer and the
  -- certificate expression. That copy is the one users actually verify
  -- against, which makes drift here a silent downgrade of the check rather
  -- than a documentation lapse.
  let installerRaw ← readRequired (installerPath : FilePath)
  outs := outs ++ [check "release identity: the installer exists" installerRaw.isOk s!"{installerRaw}"]
  -- Per-file expectations rather than one list applied everywhere. The prose
  -- documents describe the whole arrangement, so they carry every pin; the
  -- installer is a verifier, so it carries the values a verifier acts on. It
  -- has no reason to name the npm package, and it holds the workflow path only
  -- inside the (escaped) certificate expression, so demanding the plain string
  -- there would be a coincidence to satisfy rather than an invariant to keep.
  let allPins := [("repository", repository), ("npm package", npmPackage),
    ("workflow", workflow), ("OIDC issuer", issuer), ("certificate identity", identity)]
  let verifierPins := [("repository", repository), ("OIDC issuer", issuer),
    ("certificate identity", identity)]
  -- The Homebrew formula is the fourth home of the same pin, and the one a
  -- `brew install` user relies on. Like the installer it is a verifier, so it
  -- carries the verifier pins.
  let formulaRaw ← readRequired ("Formula/tl.rb" : FilePath)
  outs := outs ++ [check "release identity: the Homebrew formula exists" formulaRaw.isOk s!"{formulaRaw}"]
  -- The fifth home of the pin, and the one the scripted verifier actually
  -- reads: two inert lines a POSIX shell can take without a JSON parser. It
  -- carries the verifier pins for the same reason install.sh does.
  let pinRaw ← readRequired ("release/identity.pin" : FilePath)
  outs := outs ++ [check "release identity: the two-line pin exists" pinRaw.isOk s!"{pinRaw}"]
  let docs := [("VERIFYING.md", verifyingRaw, allPins), ("ADR-0006", distributionRaw, allPins),
    ("ADR-0014", threatRaw, allPins), ("install.sh", installerRaw, verifierPins),
    ("Formula/tl.rb", formulaRaw, verifierPins),
    ("release/identity.pin", pinRaw, verifierPins)]
  for (name, raw, pins) in docs do
    match raw with
    | .error _ => pure ()
    | .ok content =>
        for (label, value) in pins do
          outs := outs ++ [check s!"release identity: {name} carries {label} pin"
            (has content value) s!"{name} does not contain canonical {label} value {value}"]
  -- The escape hatch has one name. Two spellings across the installer and the
  -- scripted procedure would leave a user who read the documented one silently
  -- running the check they meant to skip, or vice versa.
  let verifierScriptRaw ← readRequired ("scripts/verify-release-artifacts.sh" : FilePath)
  for (name, raw) in [("install.sh", installerRaw),
      ("scripts/verify-release-artifacts.sh", verifierScriptRaw)] do
    match raw with
    | .error e => outs := outs ++ [check s!"release identity: {name} is readable" false e]
    | .ok content =>
        outs := outs ++ [
          check s!"release identity: {name} uses the documented skip variable"
            (has content "TL_INSTALL_SKIP_SIGNATURE")
            s!"{name} does not mention TL_INSTALL_SKIP_SIGNATURE, the escape hatch ADR-0006 and VERIFYING.md name",
          check s!"release identity: {name} has no second name for the skip variable"
            (!has content "TL_VERIFY_SKIP_SIGNATURE")
            s!"{name} still mentions TL_VERIFY_SKIP_SIGNATURE — one escape hatch, one name"]
  -- The transparency-log bypass is checked behaviourally rather than here.
  -- Both shell verifiers now embed a stub cosign that *rejects* the flag, so
  -- the string legitimately appears in each file and a text scan would report
  -- the guard as the violation. Each script's `--selftest` asserts on the
  -- arguments actually passed, which is the property that matters.
  return outs

/-! ## The release plan, and the documents that describe it

`release/plan.json` is where "which channels does a release actually publish"
is written, and several documents now state the answer in prose. This guards
the two things that would silently diverge: the file's own shape, and whether
VERIFYING.md still tells a user the same thing the file says.

`enabled` and `plannedFor` are exclusive by construction — an enabled channel
has no future version to name, and a deferred one must name the release it is
planned for so deferral cannot decay into abandonment. -/

def releasePlanTests : IO (List Outcome) := do
  let raw ← readRequired ("release/plan.json" : FilePath)
  let some text := raw.toOption
    | return [check "release plan: release/plan.json exists" false s!"{raw}"]
  let some plan := (Json.parse text).toOption
    | return [check "release plan: release/plan.json parses as JSON" false text]
  let rows := jArr plan "channels"
  let named (name : String) : Option Json :=
    rows.find? fun row => jStr row "channel" == some name
  let mut outs := [
    check "release plan: release/plan.json parses as JSON" true,
    checkEq "release plan: every ADR-0006 channel has exactly one row" rows.length 4]
  -- v0.1.0 publishes through these two and defers the other two. The values are
  -- pinned rather than merely read: VERIFYING.md tells users npm and Homebrew
  -- are not published, and flipping a channel on without revisiting that
  -- sentence would make the document wrong in the direction users act on.
  for (channel, wantEnabled) in
      [("github-release", true), ("installer", true), ("npm", false), ("homebrew", false)] do
    match named channel with
    | none => outs := outs ++ [check s!"release plan: '{channel}' has a row" false
        s!"release/plan.json has no row for the channel {channel}"]
    | some row =>
        let enabled := (row.getObjVal? "enabled" |>.toOption).bind (·.getBool?.toOption)
        let plannedFor := jStr row "plannedFor"
        -- Read off the row's own two fields, not off `wantEnabled`. Comparing
        -- against the expectation would make this row restate the one above it
        -- and say nothing about the file: an `enabled` channel that still
        -- carried a `plannedFor` passed it.
        let exclusive := match enabled, plannedFor with
          | some true, none => true
          | some false, some _ => true
          | _, _ => false
        outs := outs ++ [
          checkEq s!"release plan: '{channel}' is {if wantEnabled then "enabled" else "deferred"}"
            enabled (some wantEnabled),
          check s!"release plan: '{channel}' names a target release iff it is deferred"
            exclusive
            s!"channel {channel} has enabled={enabled} and plannedFor={plannedFor}; a deferred channel must name the release it is planned for, an enabled one must not, and every row must state `enabled`"]
  -- The user-facing half. A reader deciding how to install tl reads this
  -- sentence, so it is the one that must not outlive the decision behind it.
  let verifying ← readRequired ("VERIFYING.md" : FilePath)
  match verifying with
  | .error e => outs := outs ++ [check "release plan: VERIFYING.md is readable" false e]
  | .ok content =>
      outs := outs ++ [
        check "release plan: VERIFYING.md says npm and Homebrew are not published yet"
          (has content "npm and Homebrew are **not published in v0.1.0**")
          "VERIFYING.md no longer states which channels v0.1.0 publishes through"]
  return outs

/-! ## Privileged release jobs are reachable only from a pushed tag

`github.ref_type == 'tag'` is satisfied by a `workflow_dispatch` against a tag
ref, and by any trigger added later that can name one. The `stamp` job refuses
that particular combination, but a rehearsal should be *incapable* of signing
rather than dependent on an upstream job having refused first — so every job
that mints an OIDC token, writes to the repository, or reads a secret carries
the full `push` + tag condition.

The guard is stated over what makes a job privileged rather than over a list of
job names, so a privileged job added later is covered without anyone
remembering to extend this test. -/

/-- The `permissions:` grants and secret reads that make a job privileged. -/
private def privilegeGrants : List String :=
  ["id-token: write", "contents: write", "attestations: write", "packages: write"]

private def dropIndent (line : String) : String :=
  String.ofList (line.toList.dropWhile (· == ' '))

/-- Whether a workflow line actually *grants* privilege, as opposed to
    discussing it. Both files reason about `id-token: write` in prose — the
    build job's comment explains why it does not take one — so a substring scan
    over the block would report every commented job as privileged and the guard
    would pass by accident. -/
private def grantsPrivilege (line : String) : Bool :=
  let body := dropIndent line
  if body.startsWith "#" then false
  else privilegeGrants.contains body || has body "secrets."

/-- A top-level job block: the job's name and the lines belonging to it. -/
private structure JobBlock where
  name : String
  lines : List String

/-- A top-level job header — indented exactly two spaces, ending in `:`. -/
private def jobHeader? (line : String) : Option String :=
  if line.startsWith "  " && !line.startsWith "   " && line.endsWith ":"
      && !(dropIndent line).startsWith "#" then
    some (String.ofList ((line.toList.drop 2).dropLast))
  else none

/-- Split a workflow file into its top-level job blocks: everything after the
    column-zero `jobs:` key, up to the next column-zero key. -/
private def jobBlocks (content : String) : List JobBlock := Id.run do
  let mut inJobs := false
  let mut blocks : List JobBlock := []
  let mut current : Option (String × List String) := none
  for line in content.splitOn "\n" do
    if !inJobs then
      if line == "jobs:" then inJobs := true
      continue
    -- A column-zero key ends the `jobs:` mapping.
    if line != "" && !line.startsWith " " && !line.startsWith "#" then
      break
    match jobHeader? line with
    | some name =>
        if let some (n, ls) := current then blocks := blocks ++ [{ name := n, lines := ls.reverse }]
        current := some (name, [])
    | none =>
        if let some (n, ls) := current then current := some (n, line :: ls)
  if let some (n, ls) := current then blocks := blocks ++ [{ name := n, lines := ls.reverse }]
  return blocks

/-- The job's own `if:` — indented four spaces, so a step's `if:` is not it. -/
private def jobLevelIf? (block : JobBlock) : Option String :=
  (block.lines.filter (·.startsWith "    if:")).head?

def releaseWorkflowPrivilegeTests : IO (List Outcome) := do
  let path : FilePath := ".github/workflows/release.yml"
  let raw ← readRequired path
  let some content := raw.toOption
    | return [check "release workflow: the workflow is readable" false s!"{raw}"]
  let blocks := jobBlocks content
  let names := blocks.map (·.name)
  let privileged := blocks.filter fun b => b.lines.any grantsPrivilege
  let privilegedNames := privileged.map (·.name)
  let guard := "    if: github.event_name == 'push' && github.ref_type == 'tag'"
  -- Non-vacuity first. Every assertion below is universally quantified over a
  -- list this parser produced, so a parser that silently found nothing would
  -- report a clean sweep over an empty set.
  let mut outs := [
    check "release workflow: the job scan finds the build matrix"
      (names.contains "build") s!"parsed job names: {names}",
    check "release workflow: the privilege scan finds the signing job"
      (privilegedNames.contains "sign") s!"jobs found privileged: {privilegedNames}",
    check "release workflow: the privilege scan finds the publishing job"
      (privilegedNames.contains "publish-release") s!"jobs found privileged: {privilegedNames}",
    -- The build job reasons about `id-token: write` in a comment and takes
    -- none. If it ever reads as privileged, `grantsPrivilege` has regressed to
    -- a substring scan and the checks below stop meaning anything.
    check "release workflow: discussing a permission does not grant it"
      (!privilegedNames.contains "build") s!"jobs found privileged: {privilegedNames}"]
  for block in privileged do
    outs := outs ++ [
      checkEq s!"release workflow: privileged job '{block.name}' runs only on a pushed tag"
        (jobLevelIf? block |>.getD "<no job-level if:>") guard]
  return outs

/-! ## Build provenance (`tl version`, ADR-0006 "Tool versioning") -/

open Tl.Build (Provenance Kind)

/-- A stand-in stamp. Only `commit`/`dirty` decide the kind, so the pins are
    fixed here and varied only in the drift guard below. -/
private def sampleStamp (commit : String) (dirty : Bool) : Provenance :=
  { commit, dirty, toolchain := "leanprover/lean4:v4.32.2",
    manifestDigest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" }

def buildProvenanceTests : IO (List Outcome) := do
  let devClean := sampleStamp "" false
  -- A development build with a dirty tree still reports `development`: with no
  -- commit there is nothing for `dirty` to be relative to.
  let devDirty := sampleStamp "" true
  let stamped := sampleStamp "9af04c0ba31b6ecf3ad3ebe2f24fb86171a144c0" false
  let stampedDirty := sampleStamp "9af04c0ba31b6ecf3ad3ebe2f24fb86171a144c0" true
  let mut outs := [
    checkEq "build provenance: no commit is a development build" devClean.kind Kind.development,
    checkEq "build provenance: no commit stays development even with a dirty tree"
      devDirty.kind Kind.development,
    checkEq "build provenance: a commit from a clean tree is a clean build"
      stamped.kind Kind.clean,
    checkEq "build provenance: a commit from a dirty tree is a dirty build"
      stampedDirty.kind Kind.dirty,
    checkEq "build provenance: kind wire spellings"
      (Kind.development.name, Kind.dirty.name, Kind.clean.name)
      ("development", "dirty", "clean"),
    checkEq "build provenance: a development build has no short commit"
      devClean.shortCommit "",
    checkEq "build provenance: the short commit is the leading 12 hex characters"
      stamped.shortCommit "9af04c0ba31b" ]
  -- --json, per kind. `commit` is null exactly for a development build.
  for (label, p, expectKind, expectCommit) in
      [("development", devClean, "development", none),
       ("dirty", stampedDirty, "dirty", some stamped.commit),
       ("clean", stamped, "clean", some stamped.commit)] do
    let j := Tl.Cli.buildProvenanceJson p
    outs := outs ++ [
      checkEq s!"build provenance json ({label}): kind" (jStr j "kind") (some expectKind),
      checkEq s!"build provenance json ({label}): commit" (jStr j "commit") expectCommit,
      checkEq s!"build provenance json ({label}): dirty"
        ((jGet j "dirty").bind (·.getBool?.toOption)) (some p.dirty),
      checkEq s!"build provenance json ({label}): toolchain"
        (jStr j "toolchain") (some p.toolchain),
      checkEq s!"build provenance json ({label}): manifest digest"
        (jStr j "manifestDigest") (some p.manifestDigest)]
  -- Human output, per kind: parity with the json (same facts), and each kind's
  -- distinguishing claim actually stated.
  let humanDev := Tl.Cli.buildProvenanceHuman devClean
  let humanDirty := Tl.Cli.buildProvenanceHuman stampedDirty
  let humanClean := Tl.Cli.buildProvenanceHuman stamped
  outs := outs ++ [
    check "build provenance human (development): says no commit was stamped"
      (has humanDev "development build" && has humanDev "no source commit") humanDev,
    check "build provenance human (development): names no commit"
      (!has humanDev stamped.commit && !has humanDev stamped.shortCommit) humanDev,
    check "build provenance human (dirty): names the commit and disclaims it"
      (has humanDirty "dirty build" && has humanDirty stamped.shortCommit
       && has humanDirty "does not describe this binary") humanDirty,
    check "build provenance human (clean): names the commit"
      (has humanClean "clean build" && has humanClean stamped.shortCommit) humanClean]
  for (label, human) in [("development", humanDev), ("dirty", humanDirty), ("clean", humanClean)] do
    outs := outs ++ [
      check s!"build provenance human ({label}): carries the toolchain pin"
        (has human "leanprover/lean4:v4.32.2") human,
      check s!"build provenance human ({label}): carries the manifest digest prefix"
        (has human "0123456789ab") human]
  -- The compiled `tl version` payload: the additive `build` object joins the
  -- ADR-0020 shape without displacing `version` / `logFormat`, and human output
  -- carries the same build line (human/json parity).
  let out := Tl.Cli.cmdVersion
  let compiled := Tl.Build.current
  outs := outs ++ [
    checkEq "tl version: product version" (jStr out.data "version") (some "0.1.0"),
    checkEq "tl version: log format" ((jGet out.data "logFormat").bind (·.getNat?.toOption)) (some 2),
    check "tl version: the build object is present" (jGet out.data "build").isSome
      "tl version --json lost its build provenance",
    checkEq "tl version: the build object is this binary's stamp"
      ((jGet out.data "build").map (·.compress))
      (some (Tl.Cli.buildProvenanceJson compiled).compress),
    check "tl version: human output carries the build line"
      (has out.human (Tl.Cli.buildProvenanceHuman compiled)) out.human]
  -- The `build` object's key set, pinned exactly rather than by presence.
  --
  -- `Tests/CliTests.lean` used to compare the whole `tl version --json`
  -- envelope against a hand-written literal; it now splices
  -- `buildProvenanceJson` into the expected string, so both sides of that
  -- comparison move together for anything inside `build`. The rows above check
  -- that each of the five known fields is present and correct, which a sixth
  -- field satisfies just as well — so an added key would ship in every
  -- release's wire output with nothing failing. ADR-0020 froze this shape at
  -- the first release, and an additive field is a schema decision, not an
  -- incidental one.
  let buildKeys : List String :=
    match jGet out.data "build" with
    | some (Json.obj fields) => (fields.toArray.map (·.1)).toList
    | _ => []
  outs := outs ++ [
    checkEq "tl version: the build object has exactly the ADR-0006 fields"
      (buildKeys.mergeSort (· ≤ ·))
      ["commit", "dirty", "kind", "manifestDigest", "toolchain"]]
  -- Drift guard: the generated stamp's pins must match the checkout. Both are
  -- regenerated by `scripts/gen-build-provenance.sh`.
  let toolchainOnDisk := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  let manifestBytes ← IO.FS.readBinFile "lake-manifest.json"
  let manifestOnDisk := Tl.Hash.Sha256.toHex (Tl.Hash.Sha256.digest manifestBytes)
  outs := outs ++ [
    checkEq "build provenance: the stamped toolchain matches lean-toolchain"
      compiled.toolchain toolchainOnDisk,
    checkEq "build provenance: the stamped manifest digest matches lake-manifest.json"
      compiled.manifestDigest manifestOnDisk,
    check "build provenance: a stamped commit is a full 40-character git object id"
      (compiled.commit.isEmpty || compiled.commit.length == 40)
      s!"stamped commit '{compiled.commit}' is neither empty nor a full object id",
    check "build provenance: a development stamp never claims dirtiness"
      (!compiled.commit.isEmpty || !compiled.dirty)
      "the generated stamp has no commit but reports dirty := true"]
  return outs

end Tl.Tests
