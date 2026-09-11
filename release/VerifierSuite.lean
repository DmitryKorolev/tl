/- Public-process corpus for the standalone artifact verifier. It invokes the
complete script over planted artifact directories and pins, never extracted
functions or test entry points inside the adapter. -/
import release.AdapterFixture
import release.Command

namespace Release.VerifierSuite
open AdapterFixture

private structure Case where
  name : String
  fault : String := ""
  pin : Option String := none
  skip : String := "0"
  cosignAvailable : Bool := true
  required : Bool := false
  digestMode : String := "sha256sum"
  status : UInt32 := 1
  diagnostic : String
  signatures : List String := []
  hashed : Bool := false

private def cases : List Case := [
  { name := "signed", status := 0, diagnostic := "verified 1 asset", signatures := ["SHA256SUMS", "asset"], hashed := true },
  { name := "required", required := true, status := 0, diagnostic := "verified 1 asset", signatures := ["SHA256SUMS", "asset"], hashed := true },
  { name := "uppercase", fault := "uppercase", status := 0, diagnostic := "digest ok", signatures := ["SHA256SUMS", "asset"], hashed := true },
  { name := "binary-marker", fault := "binary-marker", status := 0, diagnostic := "digest ok", signatures := ["SHA256SUMS", "asset"], hashed := true },
  { name := "missing-sums", fault := "missing-SHA256SUMS", diagnostic := "SHA256SUMS not found" },
  { name := "missing-sums-bundle", fault := "missing-SHA256SUMS.sigstore.json", diagnostic := "SHA256SUMS.sigstore.json not found" },
  { name := "missing-asset", fault := "missing-asset", diagnostic := "not found", signatures := ["SHA256SUMS"] },
  { name := "missing-asset-bundle", fault := "missing-asset.sigstore.json", diagnostic := "per-asset Sigstore bundle", signatures := ["SHA256SUMS"], hashed := true },
  { name := "missing-entry", fault := "missing-entry", diagnostic := "has no entry named", signatures := ["SHA256SUMS"] },
  { name := "nonhex", fault := "nonhex", diagnostic := "not a hex digest", signatures := ["SHA256SUMS"] },
  { name := "short", fault := "short", diagnostic := "not the 64", signatures := ["SHA256SUMS"] },
  { name := "mismatch", fault := "mismatch", diagnostic := "digest mismatch", signatures := ["SHA256SUMS"], hashed := true },
  { name := "sums-signature", fault := "signature-SHA256SUMS", diagnostic := "did not verify against the pinned identity", signatures := ["SHA256SUMS"] },
  { name := "asset-signature", fault := "signature-asset", diagnostic := "did not verify against the pinned identity", signatures := ["SHA256SUMS", "asset"], hashed := true },
  { name := "cosign-broken", fault := "cosign-broken", diagnostic := "not evidence of tampering", signatures := ["SHA256SUMS"] },
  { name := "skip", skip := "1", cosignAvailable := false, fault := "no-bundles", status := 0, diagnostic := "verified 1 asset", hashed := true },
  { name := "skip-mismatch", skip := "1", cosignAvailable := false, fault := "mismatch", diagnostic := "digest mismatch", hashed := true },
  { name := "required-skip", required := true, skip := "1", diagnostic := "invoked with --require-signature" },
  { name := "required-no-cosign", required := true, fault := "no-cosign", diagnostic := "cannot fall back to a digest-only check" },
  { name := "no-cosign", fault := "no-cosign", diagnostic := "cosign not found" },
  { name := "other-skip-value", skip := "true", status := 0, diagnostic := "verified 1 asset", signatures := ["SHA256SUMS", "asset"], hashed := true },
  { name := "no-digest", digestMode := "none", diagnostic := "digest check is mandatory", signatures := ["SHA256SUMS"] },
  { name := "broken-digest", fault := "digest-broken", diagnostic := "present but not working", signatures := ["SHA256SUMS"], hashed := true },
  { name := "empty-digest", fault := "digest-empty", diagnostic := "produced no output", signatures := ["SHA256SUMS"], hashed := true },
  { name := "shasum", digestMode := "shasum", status := 0, diagnostic := "digest ok", signatures := ["SHA256SUMS", "asset"], hashed := true },
  { name := "read-only", fault := "read-only", status := 0, diagnostic := "digest ok", signatures := ["SHA256SUMS", "asset"], hashed := true },
  { name := "read-only-refusal", fault := "read-only-nonhex", diagnostic := "not a hex digest", signatures := ["SHA256SUMS"] },
  { name := "empty-pin", pin := some "", diagnostic := "no issuer on its first line" },
  { name := "issuer-only", pin := some "https://example.invalid\n", diagnostic := "no certificate identity expression" },
  { name := "empty-issuer", pin := some "\n^identity$\n", diagnostic := "no issuer on its first line" },
  { name := "empty-identity", pin := some "issuer\n\n", diagnostic := "no certificate identity expression" },
  { name := "third-line", pin := some "issuer\n^identity$\nextra\n", diagnostic := "more than two lines" },
  { name := "empty-third-line", pin := some "issuer\n^identity$\n\n", diagnostic := "more than two lines" },
  { name := "trailing-data", pin := some "issuer\n^identity$\nextra", diagnostic := "more than two lines" },
  { name := "unterminated", pin := some "issuer\n^identity$", diagnostic := "does not end with a newline" },
  { name := "crlf", pin := some "issuer\r\n^identity$\r\n", diagnostic := "outside printable ASCII" },
  { name := "non-ascii", pin := some "issuér\n^identity$\n", diagnostic := "outside printable ASCII" },
  { name := "nul", pin := some ("issuer" ++ String.singleton (Char.ofNat 0) ++ "\n^identity$\n"), diagnostic := "vanishes on its way into a shell variable" },
  { name := "unanchored-head", pin := some "issuer\nidentity$\n", diagnostic := "not anchored at ^" },
  { name := "unanchored-tail", pin := some "issuer\n^identity\n", diagnostic := "not anchored at" },
  { name := "inert-pin", fault := "inert-pin", diagnostic := "not anchored at" },
  { name := "missing-pin", fault := "missing-pin", diagnostic := "identity.pin not found" },
  { name := "unreadable-pin", fault := "unreadable-pin", diagnostic := "is not readable" },
  { name := "scratch-failure", fault := "mktemp", diagnostic := "Set TMPDIR to a writable directory" },
  { name := "no-arguments", fault := "no-arguments", status := 2, diagnostic := "usage:" },
  { name := "unknown-option", fault := "unknown-option", status := 2, diagnostic := "usage:" },
  { name := "no-assets", fault := "no-assets", status := 2, diagnostic := "usage:" },
  { name := "required-no-arguments", required := true, fault := "no-arguments", status := 2, diagnostic := "usage:" },
  { name := "required-no-assets", required := true, fault := "no-assets", status := 2, diagnostic := "usage:" },
  { name := "required-unknown-option", required := true, fault := "unknown-option", status := 2, diagnostic := "usage:" },
  { name := "not-directory", fault := "not-directory", diagnostic := "is not a directory" },
  { name := "second-digest", fault := "second-digest", diagnostic := "digest mismatch", signatures := ["SHA256SUMS", "asset"], hashed := true },
  { name := "second-signature", fault := "signature-second", diagnostic := "did not verify against the pinned identity", signatures := ["SHA256SUMS", "asset", "second"], hashed := true },
  { name := "two-assets", fault := "two-assets", status := 0, diagnostic := "verified 2 asset", signatures := ["SHA256SUMS", "asset", "second"], hashed := true }
]

private def artifactBytes (dir : System.FilePath) : IO (List (String × List UInt8)) := do
  let names := ((← dir.readDir).toList.map (·.fileName)).mergeSort
  names.mapM fun (name : String) => do
    return (name, (← IO.FS.readBinFile (dir / name)).data.toList)

/-- Optional names let observer mutations use the same rows without rerunning
    unrelated fixture cases. Production runs the complete corpus. -/
def run (root script : System.FilePath) (names : List String := []) : IO (List Outcome) := do
  let source ← IO.FS.readFile script
  let pin ← IO.FS.readFile (root / "release/identity.pin")
  let pinLines := pin.splitOn "\n"
  let base ← IO.FS.createTempDir
  try
    let digester ← requireResult (← Release.Digester.resolve)
    let resolve (tool : String) : IO String := do
      return (← requireResult (← Release.succeeded "/bin/sh"
        #["-c", "command -v \"$1\"", "probe", tool])).stdout.trimAscii.toString
    let backend ← resolve digester.command
    let realMktemp ← resolve "mktemp"
    let selected := if names.isEmpty then cases else cases.filter (fun row => names.contains row.name)
    let modes := (selected.map fun row => if !row.cosignAvailable || row.fault == "no-cosign" then "no-cosign" else row.digestMode).eraseDups
    for mode in modes do
      let bin := base / ("bin-" ++ mode)
      IO.FS.createDirAll bin
      for tool in ["awk", "cat", "dirname", "rm", "tr", "wc", "touch"] do
        runTool "ln" #["-s", ← resolve tool, (bin / tool).toString]
      IO.FS.writeFile (bin / "mktemp") r#"#!/bin/sh
set -eu
printf 'mktemp\n' >> "$PROBE_EVENTS"
[ "$#" -eq 1 ] && [ "$1" = -d ] || exit 91
[ "$PROBE_FAULT" != mktemp ] || exit 1
exec "$PROBE_REAL_MKTEMP" "$@"
"#
      let mut executables : Array String := #[(bin / "mktemp").toString]
      unless mode == "no-cosign" do
        IO.FS.writeFile (bin / "cosign") cosignFixture
        executables := executables.push (bin / "cosign").toString
      unless mode == "none" do
        let name := if mode == "shasum" then "shasum" else "sha256sum"
        IO.FS.writeFile (bin / name) digestFixture
        executables := executables.push (bin / name).toString
      unless executables.isEmpty do runTool "chmod" (#["+x"] ++ executables)
    let mut outcomes : List Outcome := []
    for row in selected do
      let work := base / row.name
      let artifacts := work / "artifacts"
      let script := work / "scripts/verify-release-artifacts.sh"
      let pinPath := work / "release/identity.pin"
      let tmp := work / "tmp"
      for dir in [artifacts, work / "scripts", work / "release", tmp] do IO.FS.createDirAll dir
      IO.FS.writeFile script source
      let marker := work / "pin-evaluated"
      IO.FS.writeFile pinPath (if row.fault == "inert-pin" then
        "issuer\n$(touch '" ++ marker.toString ++ "')\n" else row.pin.getD pin)
      let asset := "tl-" ++ "linux-x64"
      let second := "THIRD-PARTY-LICENSES"
      IO.FS.writeFile (artifacts / asset) "binary fixture\n"
      IO.FS.writeFile (artifacts / second) "notice fixture\n"
      let digest := (← requireResult (← digester.digest (artifacts / asset).toString)).hex
      let secondDigest := (← requireResult (← digester.digest (artifacts / second).toString)).hex
      let expected := match row.fault with
        | "uppercase" => digest.toUpper
        | "nonhex" | "read-only-nonhex" => "not-a-digest"
        | "short" => "abcdef"
        | "mismatch" => String.ofList (List.replicate 64 '0')
        | _ => digest
      IO.FS.writeFile (artifacts / "SHA256SUMS")
        ((if row.fault == "missing-entry" then "" else
          s!"{expected}  {if row.fault == "binary-marker" then "*" else ""}{asset}\n") ++
          s!"{secondDigest}  {second}\n")
      for name in ["SHA256SUMS", asset, second] do IO.FS.writeFile (artifacts / (name ++ ".sigstore.json")) "{}\n"
      for name in ["SHA256SUMS", "SHA256SUMS.sigstore.json", asset, asset ++ ".sigstore.json"] do
        if row.fault == "missing-" ++ name.replace asset "asset" ||
            (row.fault == "no-bundles" && name.endsWith ".json") then IO.FS.removeFile (artifacts / name)
      if row.fault == "second-digest" then IO.FS.writeFile (artifacts / second) "tampered notice\n"
      if row.fault == "missing-pin" then IO.FS.removeFile pinPath
      let readonly := row.fault.startsWith "read-only"
      let beforeBytes ← artifactBytes artifacts
      let beforeEntries := ((← artifacts.readDir).toList.map (·.fileName)).mergeSort
      if readonly then
        runTool "chmod" #["0555", artifacts.toString]
        let writable ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "test -w \"$1\"", "probe", artifacts.toString] }
        if writable.exitCode == 0 then
          outcomes := outcomes ++ [{ name := s!"verifier {row.name}: permission premise skipped because this user bypasses write permissions", passed := true, skipped := true }]

      if row.fault == "unreadable-pin" then
        runTool "chmod" #["0000", pinPath.toString]
        let readable ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "test -r \"$1\"", "probe", pinPath.toString] }
        if readable.exitCode == 0 then
          runTool "chmod" #["0644", pinPath.toString]
          outcomes := outcomes ++ [{ name := "verifier unreadable pin: skipped because this user bypasses read permissions", passed := true, skipped := true }]
          continue
      let mode := if !row.cosignAvailable || row.fault == "no-cosign" then "no-cosign" else row.digestMode
      let args := #["-i", s!"PATH={base / ("bin-" ++ mode)}", s!"HOME={work}", s!"TMPDIR={tmp}",
        s!"TL_INSTALL_SKIP_SIGNATURE={row.skip}", s!"PROBE_EVENTS={work / "events"}",
        s!"PROBE_SIGNATURES={work / "signatures"}", s!"PROBE_DIGESTS={work / "digests"}",
        s!"PROBE_ASSET={asset}", s!"PROBE_SECOND_ASSET={second}", s!"PROBE_FAULT={row.fault}",
        s!"PROBE_ISSUER={pinLines[0]!}", s!"PROBE_IDENTITY={pinLines[1]!}",
        s!"PROBE_DIGEST_MODE={row.digestMode}", s!"PROBE_BACKEND={backend}",
        s!"PROBE_REAL_MKTEMP={realMktemp}",
        s!"PROBE_BACKEND_SHASUM={if digester.command == "shasum" then "1" else "0"}",
        "/bin/sh", script.toString] ++
        (if row.required then #["--require-signature"] else #[]) ++
        (match row.fault with
          | "no-arguments" => #[]
          | "unknown-option" => #["--bogus"]
          | "no-assets" => #[artifacts.toString]
          | "not-directory" => #[(work / "absent").toString, asset]
          | "two-assets" | "second-digest" | "signature-second" => #[artifacts.toString, asset, second]
          | _ => #[artifacts.toString, asset])
      let result ← try IO.Process.output { cmd := "/usr/bin/env", args }
        finally
          if readonly then runTool "chmod" #["0755", artifacts.toString]
          if row.fault == "unreadable-pin" then runTool "chmod" #["0644", pinPath.toString]
      let output := result.stdout ++ result.stderr
      let signed ← readLog (work / "signatures")
      let hashed ← readLog (work / "digests")
      let events ← readLog (work / "events")
      outcomes := outcomes ++ [
        checkEq s!"verifier {row.name}: artifact bytes unchanged"
          (← artifactBytes artifacts) beforeBytes,
        checkEq s!"verifier {row.name}: artifact entries unchanged"
          (((← artifacts.readDir).toList.map (·.fileName)).mergeSort) beforeEntries,
        checkEq s!"verifier {row.name}: status ({output})" result.exitCode row.status,
        check s!"verifier {row.name}: diagnostic" ((output.splitOn row.diagnostic).length > 1) output,
        checkEq s!"verifier {row.name}: ordered signature calls" signed
          (row.signatures.map fun name => if name == "asset" then asset else if name == "second" then second else name),
        checkEq s!"verifier {row.name}: binary digest reachability" (hashed.contains asset) row.hashed,
        check s!"verifier {row.name}: pin was never evaluated" (!(← marker.pathExists)) marker.toString,
        check s!"verifier {row.name}: temporary work cleaned" (← tmp.readDir).isEmpty "scratch remains"]
      if row.fault == "mktemp" then outcomes := outcomes ++ [
        check "verifier scratch-failure: mktemp reached" (events.contains "mktemp") (repr events).pretty]
      if row.fault == "not-directory" then outcomes := outcomes ++ [
        check "verifier not-directory: teaches invocation" ((output.splitOn "for example").length > 1) output]
      if ["two-assets", "second-digest", "signature-second"].contains row.fault then outcomes := outcomes ++ [
        checkEq "verifier two-assets: both digests checked" hashed [asset, second]]
      if events.contains "digest" && signed.contains "SHA256SUMS" then outcomes := outcomes ++ [
        check s!"verifier {row.name}: sums signature precedes digest"
          (events.idxOf "cosign" < events.idxOf "digest") (repr events).pretty]
      if row.fault == "short" || row.digestMode == "none" || row.fault.startsWith "digest-" then
        outcomes := outcomes ++ [check s!"verifier {row.name}: broken input/tool is not tampering"
          ((output.splitOn "digest mismatch").length == 1) output]
    return outcomes
  finally IO.FS.removeDirAll base

private def suite (root : String) : Decision String := do
  let outcomes ← attempt "run the standalone verifier corpus; restore its declared fixtures and retry"
    (run root (System.FilePath.mk root / "scripts/verify-release-artifacts.sh"))
  unless outcomes.any (!·.skipped) do decline "the verifier corpus ran no assertions; restore its cases before trusting this gate."
  let failures := outcomes.filter (!·.passed)
  unless failures.isEmpty do
    decline (String.intercalate "\n" (failures.map fun row => s!"{row.name}: {row.msg}") ++
      "\nRepair the standalone verifier or its declared fixture before publishing.")
  let skips := outcomes.filter (·.skipped)
  return s!"standalone verifier public-process corpus passed ({outcomes.length - skips.length} assertions)" ++
    String.join (skips.map fun row => "\n" ++ row.name)

def command : Command :=
  optionCommand "artifact-verifier-selftest" "--root <dir>"
    "Run the standalone artifact verifier through isolated public-process fixtures."
    ["--root", "."] [{ name := "root", takesValue := true }]
    (fun options => options.required "root") suite

end Release.VerifierSuite
