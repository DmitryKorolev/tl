/- Public installer probes. The adapter is run unchanged, with declared tool
fixtures; no function is extracted, sourced, or invoked through a test hatch. -/
import Tests.Harness
import release.Digest

namespace Tl.Tests

private def installerRequire (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def installerTool (cmd : String) (args : Array String) : IO Unit := do
  let _ ← installerRequire (← Release.succeeded cmd args)

/-- Accept only the adapter's declared request forms. A reached fixture logs
    before returning, including on a simulated transport failure. No network
    client is reachable through this fixture. -/
private def redirectCurl : String := r#"#!/bin/sh
set -eu
printf '%s\n' "$@" >> "$PROBE_CURL_LOG"
[ "$#" -eq 10 ] || exit 91
case $1 in
  -fsSLI)
    [ "$2" = -o ] && [ "$3" = /dev/null ] && [ "$4" = -w ] &&
    [ "$5" = '%{url_effective}' ] && [ "$6" = --proto ] &&
    [ "$7" = '=https' ] && [ "$8" = --proto-redir ] &&
    [ "$9" = '=https' ] &&
    [ "${10}" = 'https://github.com/DmitryKorolev/tl/releases/latest' ] || exit 92
    printf '%s\n' "$PROBE_EFFECTIVE_URL"
    exit "$PROBE_CURL_STATUS"
    ;;
  -fsSL)
    [ "$2" = --retry ] && [ "$3" = 3 ] && [ "$4" = --proto ] &&
    [ "$5" = '=https,file' ] && [ "$6" = --proto-redir ] &&
    [ "$7" = '=https,file' ] && [ "$8" = -o ] || exit 93
    url=${10}
    case $url in
      https://github.com/DmitryKorolev/tl/releases/download/*) ;;
      *) exit 94 ;;
    esac
    cp "$PROBE_RELEASE/${url##*/}" "$9"
    ;;
  *) exit 95 ;;
esac
"#

/-- The optional path lets mutation probes drive precisely the same suite. -/
def installerProcessTests (script : System.FilePath := "install.sh") : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  try
    let bin := base / "bin"
    let release := base / "release"
    IO.FS.createDirAll bin
    IO.FS.createDirAll release
    -- Resolve the host's real utilities once, then expose only this manifest.
    -- curl and uname are the two declared collaborators replaced below.
    let digester ← installerRequire (← Release.Digester.resolve)
    for tool in (["awk", "chmod", "cp", "mkdir", "mktemp", "mv", "rm", "tr"] ++
        [digester.command]) do
      let resolved ← installerRequire (← Release.succeeded "/bin/sh" #["-c", "command -v \"$1\"", "probe", tool])
      installerTool "ln" #["-s", resolved.stdout.trimAscii.toString, (bin / tool).toString]
    IO.FS.writeFile (bin / "curl") redirectCurl
    IO.FS.writeFile (bin / "uname") "#!/bin/sh\ncase $1 in -s) echo Linux ;; -m) echo x86_64 ;; *) exit 96 ;; esac\n"
    installerTool "chmod" #["+x", (bin / "curl").toString, (bin / "uname").toString]
    let asset := "tl-" ++ "linux-x64"
    let binary := "#!/bin/sh\nprintf 'installed fixture version\\n'\n"
    IO.FS.writeFile (release / asset) binary
    let digest ← installerRequire (← digester.digest (release / asset).toString)
    IO.FS.writeFile (release / "SHA256SUMS") s!"{digest.hex}  {asset}\n"
    let mut rows : List Outcome := []
    for (label, effective, transport, want, diagnostic) in [
        ("stable", "https://github.com/DmitryKorolev/tl/releases/tag/v1.2.3", "0", 0, "v1.2.3"),
        ("prerelease", "https://github.com/DmitryKorolev/tl/releases/tag/v0.1.0-rc.1", "0", 0, "v0.1.0-rc.1"),
        ("no-stable", "https://github.com/DmitryKorolev/tl/releases", "0", 1, "no stable release yet"),
        ("changed-redirect", "https://github.com/DmitryKorolev/tl/something/else", "0", 1, "redirect changed shape"),
        ("transport", "https://github.com/DmitryKorolev/tl/releases/tag/v1.2.3", "37", 1, "could not reach GitHub")]
      do
      let dest := base / label
      let log := base / (label ++ ".log")
      let result ← IO.Process.output {
        cmd := "/usr/bin/env"
        args := #["-i", s!"PATH={bin}", s!"HOME={base}",
          s!"TL_INSTALL_DIR={dest}", "TL_INSTALL_SKIP_SIGNATURE=1",
          -- These formerly disabled the script before its dispatch. A success
          -- row must still install and execute the binary with them present.
          "TL_INSTALL_SOURCE_ONLY=1", "TL_INSTALL_SELFTEST=1", "TL_SOURCE_ONLY=1",
          s!"PROBE_CURL_LOG={log}", s!"PROBE_EFFECTIVE_URL={effective}",
          s!"PROBE_CURL_STATUS={transport}", s!"PROBE_RELEASE={release}",
          "/bin/sh", script.toString] }
      let output := result.stdout ++ result.stderr
      let reached ← if ← log.pathExists then IO.FS.readFile log else pure ""
      let calls := (reached.splitOn "\n").filter (· == "-fsSLI")
      let installed ← (dest / "tl").pathExists
      rows := rows ++ [
        checkEq s!"installer process: {label} status" result.exitCode want,
        check s!"installer process: {label} reports the actual outcome"
          ((output.splitOn diagnostic).length > 1) output,
        checkEq s!"installer process: {label} reaches latest resolution exactly once" calls.length 1,
        checkEq s!"installer process: {label} installation effect" installed (want == 0)]
      if want == 0 then
        rows := rows ++ [
          checkEq s!"installer process: {label} installs the checked bytes"
            (← if installed then IO.FS.readFile (dest / "tl") else pure "<not installed>") binary,
          check s!"installer process: {label} executes the installed binary"
            ((output.splitOn "installed fixture version").length > 1) output,
          check s!"installer process: {label} uses the resolved tag for asset downloads"
            ((reached.splitOn s!"/releases/download/{diagnostic}/{asset}").length > 1) reached]
      else
        rows := rows ++ [check s!"installer process: {label} refuses before downloading assets"
          (!(reached.splitOn "\n").contains "-fsSL") reached]
    return rows
  finally IO.FS.removeDirAll base

/-- Adversarial checks of the observer itself: status alone, a guessed version,
    discarded transport failure, and weakened downloader arguments must all be
    distinguishable from the real adapter by the same public-process rows. -/
def installerProcessMutationTests : IO (List Outcome) := do
  let source ← IO.FS.readFile "install.sh"
  let base ← IO.FS.createTempDir
  try
    let mut rows : List Outcome := []
    for (name, before, after) in [
        ("early-success", "set -eu\n", "set -eu\nexit 0\n"),
        ("guessed-version", "version=$(version_from_effective_url \"$latest_url\")", "version=v1.2.3"),
        ("swallowed-transport", "|| die \"could not reach GitHub to find the latest release. Check the network, or set TL_VERSION to install a specific tag.\"", "|| :"),
        ("weakened-protocol", "--proto '=https' --proto-redir '=https'", "--proto '=all' --proto-redir '=all'")]
      do
      unless (source.splitOn before).length == 2 do
        throw (IO.userError s!"installer mutation {name} no longer targets exactly one site; update the probe")
      let script := base / name
      IO.FS.writeFile script (source.replace before after)
      let observations ← installerProcessTests script
      rows := rows ++ [check s!"installer process observer rejects {name}"
        (observations.any (!·.passed)) "every observation accepted the mutated adapter"]
    return rows
  finally IO.FS.removeDirAll base

end Tl.Tests
