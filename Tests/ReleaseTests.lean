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
  let docs := [("VERIFYING.md", verifyingRaw, allPins), ("ADR-0006", distributionRaw, allPins),
    ("ADR-0014", threatRaw, allPins), ("install.sh", installerRaw, verifierPins),
    ("Formula/tl.rb", formulaRaw, verifierPins)]
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
