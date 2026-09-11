import Tests.Harness
import release.VerifierSuite

namespace Tl.Tests

def verifierProcessTests : IO (List Outcome) := do
  return (← Release.VerifierSuite.run "." "scripts/verify-release-artifacts.sh").map fun row =>
    { name := row.name, passed := row.passed, msg := row.msg }

/-- Observer mutations use the same public corpus and target the decisions
    whose deletion could otherwise leave a convincing successful process. -/
def verifierProcessMutationTests : IO (List Outcome) := do
  let source ← IO.FS.readFile "scripts/verify-release-artifacts.sh"
  let base ← IO.FS.createTempDir
  try
    let mut rows : List Outcome := []
    for (name, before, after, cases) in [
        ("artifact-write", r#"  sums="$dir/SHA256SUMS""#,
          "  printf 'modified by verifier\\n' > \"$dir/THIRD-PARTY-LICENSES\"\n  sums=\"$dir/SHA256SUMS\"", ["signed"]),
        ("early-success", "set -eu\n", "set -eu\nexit 0\n", ["signed"]),
        ("sums-signature", r#"    cosign_verify "$sums" "$bundle" SHA256SUMS"#, "    :", ["sums-signature"]),
        ("asset-signature", r#"      cosign_verify "$path" "$asset_bundle" "$asset""#, "      :", ["asset-signature"]),
        ("digest", r#"    if [ "$actual" != "$expected" ]; then"#, "    if false; then", ["mismatch", "second-digest"]),
        ("second-asset", r#"  for asset in "$@"; do"#, r#"  for asset in "$1"; do"#, ["two-assets", "second-signature"]),
        ("pin-bytes", r#"  if [ "$pin_stray_count" -ne 0 ]; then"#, "  if false; then", ["nul"]),
        ("signature-pin", r#"--certificate-oidc-issuer "$issuer""#, "--certificate-oidc-issuer wrong", ["signed"]),
        ("required-signature", r#"    if [ "$require_signature" -eq 1 ]; then"#, "    if false; then", ["required-skip", "required-no-cosign"])]
      do
      -- The required-signature guard occurs once for each refusal path.
      let sites := if name == "required-signature" then 3 else 2
      unless (source.splitOn before).length == sites do
        throw (IO.userError s!"verifier mutation {name} changed its target sites; update the probe")
      let script := base / name
      IO.FS.writeFile script (source.replace before after)
      let observations ← Release.VerifierSuite.run "." script cases
      rows := rows ++ [check s!"verifier observer rejects {name}"
        (!observations.isEmpty && observations.any (!·.passed)) "every observation accepted the mutated verifier"]
    return rows
  finally IO.FS.removeDirAll base

/-- The public native command must propagate failing observations, input errors,
    and usage errors as well as a successful run. -/
def verifierSuiteCommandTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  try
    let bad := base / "bad-adapter"
    IO.FS.createDirAll (bad / "release")
    IO.FS.createDirAll (bad / "scripts")
    IO.FS.writeFile (bad / "release/identity.pin") (← IO.FS.readFile "release/identity.pin")
    IO.FS.writeFile (bad / "scripts/verify-release-artifacts.sh") "#!/bin/sh\nexit 0\n"
    let mut rows : List Outcome := []
    for (name, args, status, diagnostic) in [
        ("success", #["--root", "."], 0, "standalone verifier public-process corpus passed"),
        ("missing-root", #[], 2, "--root"),
        ("unknown-option", #["--root", ".", "--unknown"], 2, "unknown"),
        ("unreadable-input", #["--root", base.toString], 1, "verify-release-artifacts.sh"),
        ("failed-observations", #["--root", bad.toString], 1, "Repair the standalone verifier")]
      do
      let result ← IO.Process.output {
        cmd := ".lake/build/bin/tlrelease"
        args := #["artifact-verifier-selftest"] ++ args }
      rows := rows ++ [checkEq s!"verifier suite command {name}: status" result.exitCode status,
        check s!"verifier suite command {name}: diagnostic"
          (((result.stdout ++ result.stderr).splitOn diagnostic).length > 1) (result.stdout ++ result.stderr)]
    return rows
  finally IO.FS.removeDirAll base

end Tl.Tests
