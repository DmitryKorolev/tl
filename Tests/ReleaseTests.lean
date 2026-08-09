/-
`Tests.ReleaseTests` -- drift guard for the signed-release identity pinned by
ADR-0006 / ADR-0014. `release/identity.json` is the machine-readable current
pin; VERIFYING.md and the ADR must carry the same operative values. The
installer and Homebrew formula join this guard when their files land.

Tested release shell (ADR-0004); no Mathlib (ADR-0009).
-/
import Lean.Data.Json
import Tests.Harness
import Tests.JsonUtil

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
  let docs := [("VERIFYING.md", verifyingRaw), ("ADR-0006", distributionRaw),
    ("ADR-0014", threatRaw)]
  for (name, raw) in docs do
    match raw with
    | .error _ => pure ()
    | .ok content =>
        for (label, value) in [("repository", repository), ("npm package", npmPackage),
            ("workflow", workflow), ("OIDC issuer", issuer),
            ("certificate identity", identity)] do
          outs := outs ++ [check s!"release identity: {name} carries {label} pin"
            (has content value) s!"{name} does not contain canonical {label} value {value}"]
  return outs

end Tl.Tests
