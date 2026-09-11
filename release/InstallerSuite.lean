/- Lean-driven public-process corpus for the retained installer. All process
fixtures live outside the adapter, which is invoked through its public dispatch.
This module imports no product or test code, so the release policy can run it
inside the runtime-stripped container. -/
import release.AdapterFixture
import release.Command

namespace Release.InstallerSuite

open AdapterFixture

/-- A public invocation and its expected effects. Each row gets a fresh release,
    tool manifest, and logs, so evidence cannot leak from an earlier row. -/
private structure InstallCase where
  name : String
  os : String := "Linux"
  arch : String := "x86_64"
  target : String := "linux-x64"
  skip : String := "0"
  fault : String := ""
  notice : String := "absent"
  digestMode : String := "sha256sum"
  translated : String := "0"
  status : UInt32 := 0
  diagnostic : String := "tl-install: installed"
  installed : Bool := true
  noticeInstalled : Bool := false
  signatures : List String := ["SHA256SUMS", "asset"]
  reached : List String := []
  absent : List String := []

private def installCases : List InstallCase := [
  { name := "signed" },
  { name := "replace", fault := "existing" },
  { name := "uppercase", fault := "uppercase" },
  { name := "binary-marker", fault := "binary-marker" },
  { name := "darwin-arm", os := "Darwin", arch := "arm64", target := "darwin-arm64" },
  { name := "darwin-intel", os := "Darwin", target := "darwin-x64", reached := ["sysctl"] },
  { name := "linux-arm", arch := "aarch64", target := "linux-arm64" },
  { name := "linux-arm-alias", arch := "arm64", target := "linux-arm64" },
  { name := "linux-intel-alias", arch := "amd64" },
  { name := "rosetta", os := "Darwin", target := "darwin-x64", translated := "1",
    diagnostic := "running under Rosetta", reached := ["sysctl"] },
  { name := "sysctl-failed", os := "Darwin", target := "darwin-x64", translated := "fail",
    reached := ["sysctl"] },
  { name := "windows", os := "MINGW64_NT-10.0", status := 1, installed := false,
    diagnostic := "WSL2", signatures := [], absent := ["curl"] },
  { name := "msys", os := "MSYS_NT", status := 1, installed := false,
    diagnostic := "WSL2", signatures := [], absent := ["curl"] },
  { name := "cygwin", os := "CYGWIN_NT", status := 1, installed := false,
    diagnostic := "WSL2", signatures := [], absent := ["curl"] },
  { name := "windows-nt", os := "Windows_NT", status := 1, installed := false,
    diagnostic := "WSL2", signatures := [], absent := ["curl"] },
  { name := "unsupported-os", os := "FreeBSD", status := 1, installed := false,
    diagnostic := "unsupported operating system", signatures := [], absent := ["curl"] },
  { name := "unsupported-arch", arch := "riscv64", status := 1, installed := false,
    diagnostic := "unsupported CPU architecture", signatures := [], absent := ["curl"] },
  { name := "missing-curl", fault := "missing-curl", status := 1, installed := false,
    diagnostic := "curl not found", signatures := [], absent := ["curl", "uname"] },
  { name := "missing-cosign", fault := "missing-cosign", status := 1, installed := false,
    diagnostic := "cosign not found", signatures := [], absent := ["curl"] },
  { name := "custom-no-version", fault := "no-version", status := 1, installed := false,
    diagnostic := "TL_VERSION is not", signatures := [], absent := ["curl"] },
  { name := "http-refused", fault := "http", status := 1, installed := false,
    diagnostic := "could not download", signatures := [], reached := ["curl"] },
  { name := "missing-binary", fault := "missing-asset", status := 1, installed := false,
    diagnostic := "could not download", signatures := [], reached := ["curl"] },
  { name := "missing-sums", fault := "missing-SHA256SUMS", status := 1, installed := false,
    diagnostic := "could not download", signatures := [], reached := ["curl"] },
  { name := "missing-sums-bundle", fault := "missing-SHA256SUMS.sigstore.json", status := 1,
    installed := false, diagnostic := "could not download", signatures := [], reached := ["curl"] },
  { name := "missing-asset-bundle", fault := "missing-asset.sigstore.json", status := 1,
    installed := false, diagnostic := "could not download", signatures := ["SHA256SUMS"] },
  { name := "sums-signature", fault := "signature-SHA256SUMS", status := 1, installed := false,
    diagnostic := "signature on SHA256SUMS", signatures := ["SHA256SUMS"] },
  { name := "asset-signature", fault := "signature-asset", status := 1, installed := false,
    diagnostic := "did not verify against" },
  { name := "cosign-broken", fault := "cosign-broken", status := 1, installed := false,
    diagnostic := "not evidence of tampering", signatures := ["SHA256SUMS"] },
  { name := "missing-entry", fault := "missing-entry", status := 1, installed := false,
    diagnostic := "has no entry", signatures := ["SHA256SUMS"] },
  { name := "nonhex", fault := "nonhex", status := 1, installed := false,
    diagnostic := "not a hex digest", signatures := ["SHA256SUMS"] },
  { name := "short", fault := "short", status := 1, installed := false,
    diagnostic := "not the 64", signatures := ["SHA256SUMS"] },
  { name := "mismatch", fault := "mismatch", status := 1, installed := false,
    diagnostic := "digest mismatch", signatures := ["SHA256SUMS"] },
  { name := "skip-signatures", skip := "1", fault := "no-bundles", signatures := [] },
  { name := "skip-still-checks", skip := "1", fault := "mismatch", status := 1,
    installed := false, diagnostic := "digest mismatch", signatures := [] },
  { name := "other-skip-value", skip := "true" },
  { name := "no-digester", digestMode := "none", status := 1, installed := false,
    diagnostic := "mandatory", signatures := ["SHA256SUMS"] },
  { name := "broken-digester", fault := "digest-broken", status := 1, installed := false,
    diagnostic := "present but not working", signatures := ["SHA256SUMS"], reached := ["digest"] },
  { name := "empty-digester", fault := "digest-empty", status := 1, installed := false,
    diagnostic := "produced no output", signatures := ["SHA256SUMS"], reached := ["digest"] },
  { name := "shasum", digestMode := "shasum", notice := "good", noticeInstalled := true,
    reached := ["digest"] },
  { name := "shasum-mismatch", digestMode := "shasum", fault := "mismatch", status := 1,
    installed := false, diagnostic := "digest mismatch", signatures := ["SHA256SUMS"], reached := ["digest"] },
  { name := "mkdir-failure", fault := "mkdir", status := 1, installed := false,
    diagnostic := "TL_INSTALL_DIR", reached := ["mkdir"] },
  { name := "readonly", fault := "readonly", status := 1, installed := false,
    diagnostic := "is not writable" },
  { name := "occupied", fault := "occupied", status := 1, installed := false,
    diagnostic := "not a regular file" },
  { name := "copy-failure", fault := "cp", status := 1, installed := false,
    diagnostic := "could not write", reached := ["cp"] },
  { name := "rename-failure", fault := "mv", status := 1, installed := false,
    diagnostic := "could not replace", reached := ["mv"] },
  { name := "notice", notice := "good", noticeInstalled := true },
  { name := "notice-absent", diagnostic := "publishes no THIRD-PARTY-LICENSES" },
  { name := "notice-mismatch", notice := "mismatch", diagnostic := "digest mismatch for THIRD-PARTY-LICENSES" },
  { name := "notice-nonhex", notice := "nonhex", diagnostic := "not a hex digest" },
  { name := "notice-short", notice := "short", diagnostic := "not the 64" },
  { name := "notice-download", notice := "missing", diagnostic := "could not download THIRD-PARTY-LICENSES" },
  { name := "notice-digest", notice := "good", fault := "notice-digest",
    diagnostic := "could not be checked", reached := ["digest"] },
  { name := "notice-mkdir", notice := "good", fault := "notice-mkdir",
    diagnostic := "could not write", reached := ["mkdir"] },
  { name := "notice-copy", notice := "good", fault := "notice-cp",
    diagnostic := "could not write", reached := ["cp"] },
  { name := "notice-default", notice := "good", fault := "default-share", noticeInstalled := true },
  { name := "default-install", fault := "default-install" },
  { name := "on-path", fault := "on-path" },
  { name := "version-fails", fault := "version-fails" },
  { name := "unknown-argument", fault := "argument", status := 2, installed := false,
    diagnostic := "unknown argument", signatures := [], absent := ["curl", "uname"] }
]

private def installCurl : String := r#"#!/bin/sh
set -eu
printf 'curl\n' >> "$PROBE_EVENTS"
[ "$#" -eq 10 ] && [ "$1" = -fsSL ] && [ "$2" = --retry ] &&
[ "$3" = 3 ] && [ "$4" = --proto ] && [ "$5" = '=https,file' ] &&
[ "$6" = --proto-redir ] && [ "$7" = '=https,file' ] && [ "$8" = -o ] || exit 91
url=${10}
name=${url##*/}
[ "$url" = "$PROBE_BASE/$name" ] || exit 92
printf '%s\n' "$name" >> "$PROBE_FETCHES"
case $url in https://*|file://*) ;; *) exit 93 ;; esac
case $name in
  "$PROBE_ASSET"|SHA256SUMS|SHA256SUMS.sigstore.json|"$PROBE_ASSET.sigstore.json"|THIRD-PARTY-LICENSES) ;;
  *) exit 94 ;;
esac
"$PROBE_REAL_CP" "$PROBE_RELEASE/$name" "$9"
"#

private def installObserverTool (tool : String) : String :=
  "#!/bin/sh\nset -eu\nprintf '" ++ tool ++ "\\n' >> \"$PROBE_EVENTS\"\n" ++
  (match tool with
  | "uname" => "case $1 in -s) echo \"$PROBE_OS\" ;; -m) echo \"$PROBE_ARCH\" ;; *) exit 91 ;; esac\n"
  | "sysctl" => "[ \"$#\" -eq 2 ] && [ \"$1\" = -n ] && [ \"$2\" = sysctl.proc_translated ] || exit 91\n[ \"$PROBE_TRANSLATED\" != fail ] || exit 1\necho \"$PROBE_TRANSLATED\"\n"
  | "cp" => "case $2 in */.tl.install.*) if [ \"$PROBE_FAULT\" = cp ]; then : > \"$2\"; exit 1; fi ;; */THIRD-PARTY-LICENSES) [ \"$PROBE_FAULT\" != notice-cp ] || exit 1 ;; esac\nexec \"$PROBE_REAL_CP\" \"$@\"\n"
  | "mv" => "if [ \"$PROBE_FAULT\" = mv ]; then [ -f \"$2\" ] || exit 92; printf 'staged-rename\\n' >> \"$PROBE_EVENTS\"; exit 1; fi\nexec \"$PROBE_REAL_MV\" \"$@\"\n"
  | "mkdir" => "if [ \"$2\" = \"$PROBE_DEST\" ] && [ \"$PROBE_FAULT\" = mkdir ]; then exit 1; fi\nif [ \"$2\" = \"$PROBE_SHARE\" ] && [ \"$PROBE_FAULT\" = notice-mkdir ]; then exit 1; fi\nexec \"$PROBE_REAL_MKDIR\" \"$@\"\n"
  | _ => "exit 95\n")

/-- Public branch corpus for the retained bootstrap adapter. PATH contains only
    declared collaborators; the original script's dispatch is the only entry. -/
private def runInstallerBranches (root script : System.FilePath) (cases : List InstallCase) : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  try
    let digester ← requireResult (← Release.Digester.resolve)
    let resolve (tool : String) : IO String := do
      return (← requireResult (← Release.succeeded "/bin/sh"
        #["-c", "command -v \"$1\"", "probe", tool])).stdout.trimAscii.toString
    let backend ← resolve digester.command
    let realCp ← resolve "cp"
    let realMv ← resolve "mv"
    let realMkdir ← resolve "mkdir"
    let pin ← IO.FS.readFile (root / "release/identity.pin")
    let pinLines := pin.splitOn "\n"
    -- Resolve and prepare immutable tool manifests once per suite, rather
    -- than spawning tool-discovery processes for every corpus row.
    let modes := (cases.map fun row =>
      if ["missing-curl", "missing-cosign"].contains row.fault then row.fault else row.digestMode).eraseDups
    for mode in modes do
      let bin := base / ("bin-" ++ mode)
      IO.FS.createDirAll bin
      for tool in ["awk", "chmod", "dirname", "mktemp", "rm", "tr"] do
        runTool "ln" #["-s", ← resolve tool, (bin / tool).toString]
      let mut executables : Array String := #[]
      for tool in ["uname", "sysctl", "cp", "mv", "mkdir"] do
        IO.FS.writeFile (bin / tool) (installObserverTool tool)
        executables := executables.push (bin / tool).toString
      for (tool, content) in [("curl", installCurl), ("cosign", cosignFixture)] do
        unless mode == "missing-" ++ tool do
          IO.FS.writeFile (bin / tool) content
          executables := executables.push (bin / tool).toString
      unless mode == "none" do
        let digestName := if mode == "shasum" then "shasum" else "sha256sum"
        IO.FS.writeFile (bin / digestName) digestFixture
        executables := executables.push (bin / digestName).toString
      runTool "chmod" (#["+x"] ++ executables)
    let mut rows : List Outcome := []
    for row in cases do
      let root := base / row.name
      let mode := if ["missing-curl", "missing-cosign"].contains row.fault then row.fault else row.digestMode
      let bin := base / ("bin-" ++ mode)
      let release := root / "release"
      let dest := if row.fault == "default-install" then root / ".local/bin" else root / "dest"
      let share := if row.fault == "default-share" then root / "share/tl" else root / "share"
      IO.FS.createDirAll release
      IO.FS.createDirAll (root / "tmp")
      let asset := "tl-" ++ row.target
      let binary := "#!/bin/sh\nprintf 'installed fixture " ++ row.target ++ "\\n'\n" ++
        (if row.fault == "version-fails" then "exit 19\n" else "")
      IO.FS.writeFile (release / asset) binary
      let digest := (← requireResult (← digester.digest (release / asset).toString)).hex
      let expected := match row.fault with
        | "uppercase" => digest.toUpper
        | "nonhex" => "not-a-digest"
        | "short" => "abcdef"
        | "mismatch" => String.ofList (List.replicate 64 '0')
        | _ => digest
      let sums := if row.fault == "missing-entry" then "" else
        s!"{expected}  {if row.fault == "binary-marker" then "*" else ""}{asset}\n"
      let mut sums := sums
      if row.notice != "absent" then
        IO.FS.writeFile (release / "THIRD-PARTY-LICENSES") "fixture notice\n"
        let noticeDigest := (← requireResult (← digester.digest (release / "THIRD-PARTY-LICENSES").toString)).hex
        let expected := match row.notice with
          | "short" => "abcdef"
          | "nonhex" => "not-hex"
          | "mismatch" => String.ofList (List.replicate 64 '0')
          | _ => noticeDigest
        sums := sums ++ s!"{expected}  THIRD-PARTY-LICENSES\n"
        if row.notice == "missing" then IO.FS.removeFile (release / "THIRD-PARTY-LICENSES")
      IO.FS.writeFile (release / "SHA256SUMS") sums
      IO.FS.writeFile (release / "SHA256SUMS.sigstore.json") "{}\n"
      IO.FS.writeFile (release / (asset ++ ".sigstore.json")) "{}\n"
      for name in [asset, "SHA256SUMS", "SHA256SUMS.sigstore.json", asset ++ ".sigstore.json"] do
        let faultName := name.replace asset "asset"
        if row.fault == "missing-" ++ faultName ||
            (row.fault == "no-bundles" && name.endsWith ".json") then
          IO.FS.removeFile (release / name)
      let oldBinary := "previous installation\n"
      if ["existing", "cp", "mv"].contains row.fault then
        IO.FS.createDirAll dest
        IO.FS.writeFile (dest / "tl") oldBinary
      if row.fault == "readonly" then
        IO.FS.createDirAll dest
        runTool "chmod" #["0555", dest.toString]
        let writable ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "test -w \"$1\"", "probe", dest.toString] }
        if writable.exitCode == 0 then
          runTool "chmod" #["0755", dest.toString]
          rows := rows ++ [{ name := "installer readonly: skipped because this user bypasses write permissions", passed := true, skipped := true }]
          continue
      if row.fault == "occupied" then IO.FS.createDirAll (dest / "tl/occupied")
      let url := if row.fault == "http" then "http://invalid.example/release" else "file://" ++ release.toString
      let events := root / "events"
      let signatures := root / "signatures"
      let digests := root / "digests"
      let fetches := root / "fetches"
      let args := #["-i", s!"PATH={bin}{if row.fault == "on-path" then ":" ++ dest.toString else ""}",
        s!"HOME={root}", s!"TMPDIR={root / "tmp"}", s!"TL_INSTALL_SKIP_SIGNATURE={row.skip}", s!"TL_INSTALL_BASE_URL={url}",
        s!"PROBE_BASE={url}", s!"PROBE_RELEASE={release}", s!"PROBE_ASSET={asset}",
        s!"PROBE_EVENTS={events}", s!"PROBE_SIGNATURES={signatures}", s!"PROBE_FETCHES={fetches}",
        s!"PROBE_DIGESTS={digests}", s!"PROBE_OS={row.os}", s!"PROBE_ARCH={row.arch}",
        s!"PROBE_TRANSLATED={row.translated}", s!"PROBE_FAULT={row.fault}",
        s!"PROBE_REAL_CP={realCp}", s!"PROBE_REAL_MV={realMv}", s!"PROBE_REAL_MKDIR={realMkdir}",
        s!"PROBE_DEST={dest}", s!"PROBE_SHARE={share}", s!"PROBE_BACKEND={backend}",
        s!"PROBE_DIGEST_MODE={row.digestMode}", s!"PROBE_BACKEND_SHASUM={if digester.command == "shasum" then "1" else "0"}",
        s!"PROBE_ISSUER={pinLines[0]!}", s!"PROBE_IDENTITY={pinLines[1]!}"] ++
        (if row.fault == "no-version" then #[] else #["TL_VERSION=v1.2.3"]) ++
        (if row.fault == "default-install" then #[] else #[s!"TL_INSTALL_DIR={dest}"]) ++
        (if row.fault == "default-share" then #[] else #[s!"TL_INSTALL_SHARE_DIR={share}"]) ++
        #["/bin/sh", script.toString] ++ (if row.fault == "argument" then #["--bogus"] else #[])
      let result ← try
          IO.Process.output { cmd := "/usr/bin/env", args }
        finally
          if row.fault == "readonly" then runTool "chmod" #["0755", dest.toString]
      let output := result.stdout ++ result.stderr
      let observed ← readLog events
      let signed ← readLog signatures
      let hashed ← readLog digests
      let fetched ← readLog fetches
      let installed ← if ← (dest / "tl").isDir then pure "<directory>"
        else if ← (dest / "tl").pathExists then IO.FS.readFile (dest / "tl") else pure ""
      let notice ← if ← (share / "THIRD-PARTY-LICENSES").pathExists then
        IO.FS.readFile (share / "THIRD-PARTY-LICENSES") else pure ""
      let leftovers ← if ← dest.isDir then do
        pure ((← dest.readDir).toList.filter (·.fileName.startsWith ".tl.install."))
        else pure []
      rows := rows ++ [
        check s!"installer branch {row.name}: temporary work cleaned"
          (← (root / "tmp").readDir).isEmpty "installer left temporary work behind",
        checkEq s!"installer branch {row.name}: status ({output})" result.exitCode row.status,
        check s!"installer branch {row.name}: diagnostic" ((output.splitOn row.diagnostic).length > 1) output,
        checkEq s!"installer branch {row.name}: verified bytes installed" (installed == binary) row.installed,
        checkEq s!"installer branch {row.name}: notice effect" notice
          (if row.noticeInstalled then "fixture notice\n" else ""),
        checkEq s!"installer branch {row.name}: ordered signature calls" signed
          (row.signatures.map fun name => if name == "asset" then asset else name),
        check s!"installer branch {row.name}: no staging debris" leftovers.isEmpty (repr leftovers).pretty]
      for tool in row.reached do
        rows := rows ++ [check s!"installer branch {row.name}: reaches {tool}" (observed.contains tool) (repr observed).pretty]
      for tool in row.absent do
        rows := rows ++ [check s!"installer branch {row.name}: does not reach {tool}" (!observed.contains tool) (repr observed).pretty]
      -- Validation and download refusals must leave no sidecar. A failing
      -- filesystem copy has no rollback contract; its warning and the verified
      -- binary's continued success are checked separately.
      if !row.noticeInstalled && row.fault != "notice-cp" then
        rows := rows ++ [check s!"installer branch {row.name}: refused notice absent"
          (!(← (share / "THIRD-PARTY-LICENSES").pathExists)) notice]
      if !row.installed && !["cp", "mv", "occupied"].contains row.fault then
        rows := rows ++ [check s!"installer branch {row.name}: no destination created"
          (!(← (dest / "tl").pathExists)) installed]
      if row.installed then
        rows := rows ++ [
          check s!"installer branch {row.name}: runs installed binary"
            ((output.splitOn s!"installed fixture {row.target}").length > 1) output,
          check s!"installer branch {row.name}: digest collaborator reached selected binary" (hashed.contains asset) (repr hashed).pretty,
          check s!"installer branch {row.name}: selected binary fetched" (fetched.contains asset) (repr fetched).pretty]
      if row.noticeInstalled then
        rows := rows ++ [check s!"installer branch {row.name}: notice digester reached"
          (hashed.contains "THIRD-PARTY-LICENSES") (repr hashed).pretty]
      if ["cp", "mv"].contains row.fault then
        rows := rows ++ [checkEq s!"installer branch {row.name}: previous install preserved" installed oldBinary]
      if row.fault == "mv" then
        rows := rows ++ [check s!"installer branch {row.name}: rename failed after staging"
          (observed.contains "staged-rename") (repr observed).pretty]
      if row.fault == "occupied" then
        rows := rows ++ [checkEq s!"installer branch {row.name}: occupied tree preserved"
          ((← (dest / "tl").readDir).toList.map (·.fileName)) ["occupied"]]
      if row.installed && row.fault != "on-path" then
        rows := rows ++ [check s!"installer branch {row.name}: PATH advice"
          ((output.splitOn "is not on your PATH").length > 1) output]
      if signed.contains "SHA256SUMS" && observed.contains "digest" then
        rows := rows ++ [check s!"installer branch {row.name}: sums signature precedes digest"
          (observed.idxOf "cosign" < observed.idxOf "digest") (repr observed).pretty]
      if row.fault == "on-path" then
        rows := rows ++ [check s!"installer branch {row.name}: no PATH advice"
          ((output.splitOn "is not on your PATH").length == 1) output]
      if row.fault == "short" || row.notice == "short" then
        rows := rows ++ [check s!"installer branch {row.name}: corrupt digest is not tampering"
          ((output.splitOn "digest mismatch").length == 1) output]
    return rows
  finally IO.FS.removeDirAll base

/-- The complete public installer branch corpus. -/
def run (root script : System.FilePath) (names : List String := []) : IO (List Outcome) :=
  runInstallerBranches root script (if names.isEmpty then installCases else
    installCases.filter (fun row => names.contains row.name))


private def suite (root : String) : Decision String := do
  let outcomes ← attempt "run the installer public-process corpus; restore its declared fixtures and retry"
    (run root (System.FilePath.mk root / "install.sh"))
  unless outcomes.any (!·.skipped) do decline "the installer corpus ran no assertions; restore its cases before trusting this gate."
  let failures := outcomes.filter (!·.passed)
  unless failures.isEmpty do
    decline (String.intercalate "\n" (failures.map fun row => s!"{row.name}: {row.msg}") ++
      "\nRepair the installer or its declared fixture before publishing.")
  let skips := outcomes.filter (·.skipped)
  return s!"installer public-process corpus passed ({outcomes.length - skips.length} assertions)" ++
    String.join (skips.map fun row => "\n" ++ row.name)

def command : Command :=
  optionCommand "installer-selftest" "--root <dir>"
    "Run the retained installer through isolated public-process fixtures."
    ["--root", "."] [{ name := "root", takesValue := true }]
    (fun options => options.required "root") suite

end Release.InstallerSuite
