/- Shared local/CI hermetic runner. Every effect returns a checked result;
preparation has network access, evidence runs in the restricted inner container. -/
import release.Command
import release.Digest
import release.Policy
import release.HermeticFixture
import release.HermeticPlan

namespace Release.Hermetic

abbrev Executor := Call → IO (Except String ProcessOutput)

def execute (call : Call) : IO (Except String ProcessOutput) :=
  succeeded call.tool call.args call.timeoutMs

def checked (exec : Executor) (call : Call) : Decision ProcessOutput := do
  let result ← ofIO (exec call)
  if result.exitCode != 0 then
    decline s!"{call.tool} failed ({result.exitCode}). Fix the reported tool failure and retry."
  return result

def steps (exec : Executor) (calls : List Call) : Decision Unit := do
  for call in calls do
    let _ ← checked exec call

def checkedCompletion (exec : Executor) (call : Call) (verdict : String) : Decision Unit := do
  let output ← checked exec call
  if !completed output verdict then
    decline s!"{call.tool} did not reach '{verdict}'. Inspect the retained log and repair the incomplete run."

/-- Once a container has been created, removal runs on success and failure.
Removal failure cannot turn a successful body into a successful overall run. -/
def withContainer (exec : Executor) (name : String) (create : Call)
    (body : Decision Unit) : Decision Unit := do
  let _ ← checked exec create
  let outcome ← attempt "run container stages" body.run.toBaseIO
  let result := match outcome with
    | .ok result => result
    | .error error => .error s!"{error}. Repair the failed container stage and retry."
  let cleanup ← attempt "remove temporary container" (exec { tool := "podman", args := #["rm", "--force", name] })
  match result, cleanup with
  | .error error, .error removal => decline s!"{error}\nContainer {name} cleanup also failed: {removal}. Remove it with Podman."
  | .error error, .ok output =>
      if output.exitCode != 0 then decline s!"{error}\nRemove temporary container {name} with Podman; cleanup failed."
      decline error
  | .ok (), .error error => decline s!"Remove temporary container {name} with Podman: {error}"
  | .ok (), .ok output =>
      if output.exitCode != 0 then decline s!"Remove temporary container {name} with Podman; cleanup failed."

abbrev Hasher := String → IO (Except String Sha256)

def ensureDigest (hash : Hasher) (path expected : String) : Decision Unit := do
  let actual ← ofIO (hash path)
  if actual.hex != expected then
    decline s!"Digest mismatch for {path}. Remove the damaged download and retry; do not change the pin to match it."

def prepare (exec : Executor) (root scratch : String) (hash : Hasher) : Decision Unit := do
  for dir in ["static", "tools", "lib", "lib64", "tmp", "home", "packed", "npm-cache"] do
    attempt "create hermetic scratch; check disk permissions" (IO.FS.createDirAll (System.FilePath.mk scratch / dir))
  for input in inputs do
    let path := s!"{scratch}/{input.file}"
    let _ ← checked exec { tool := "curl", args := #["-sSfL", "--retry", "3", "-o", path, input.url], timeoutMs := 600000 }
    ensureDigest hash path input.sha256
  steps exec [
    { tool := "tar", args := #["-xzf", s!"{scratch}/busybox.apk", "-C", s!"{scratch}/static", "bin/busybox.static"] },
    { tool := "tar", args := #["-xzf", s!"{scratch}/actionlint.tar.gz", "-C", s!"{scratch}/tools", "actionlint"] },
    { tool := "tar", args := #["-xJf", s!"{scratch}/shellcheck.tar.xz", "-C", scratch] },
    { tool := "cp", args := #[s!"{scratch}/shellcheck-v0.11.0/shellcheck", s!"{scratch}/tools/shellcheck"] }]
  for path in ["npm-userconfig", "npm-globalconfig"] do
    attempt "write isolated npm configuration; check scratch permissions" (IO.FS.writeFile s!"{scratch}/{path}" "")
  steps exec [
    { tool := "npm", args := #["--cache", s!"{scratch}/npm-cache", "--userconfig", s!"{scratch}/npm-userconfig",
      "--globalconfig", s!"{scratch}/npm-globalconfig", "pack", s!"{root}/npm/tl", "--ignore-scripts", "--pack-destination", s!"{scratch}/packed"], timeoutMs := 600000 },
    { tool := "tar", args := #["-xzf", s!"{scratch}/packed/taskloop-tl-0.0.0.tgz", "-C", s!"{scratch}/packed", "package/bin/tl"] }]
  let original ← attempt "read tracked launcher; restore npm/tl/bin/tl" (IO.FS.readBinFile s!"{root}/npm/tl/bin/tl")
  let packed ← attempt "read packed launcher; repair npm packaging" (IO.FS.readBinFile s!"{scratch}/packed/package/bin/tl")
  if original != packed then decline "npm changed the launcher bytes. Repair the package configuration before retrying."
  let name := "hermetic-" ++ (System.FilePath.mk scratch).fileName.getD "build"
  withContainer exec name (builderCreate name root scratch) (steps exec (builderCalls name))
  withContainer exec name
    { tool := "podman", args := #["create", "--name", name, "--platform", "linux/amd64", image] }
    (steps exec [{ tool := "podman", args := #["cp", s!"{name}:/lib/.", s!"{scratch}/lib"] }])
  attempt "write launcher fixture; check scratch permissions" (IO.FS.writeFile s!"{scratch}/launcher-suite" launcherFixture)
  let _ ← checked exec { tool := "chmod", args := #["0755", s!"{scratch}/static/bin/busybox.static", s!"{scratch}/tools/tlrelease",
    s!"{scratch}/tools/actionlint", s!"{scratch}/tools/shellcheck", s!"{scratch}/launcher-suite"] }
  let mut hashes : List String := []
  for file in positiveFiles do
    let digest ← ofIO (hash s!"{scratch}/{file}")
    hashes := hashes ++ [s!"{digest.hex}  /scratch/{file}\n"]
  attempt "write digest inventory; check scratch permissions" (IO.FS.writeFile s!"{scratch}/positive-inputs.sha256" (String.join hashes))

def loggedExecutor (scratch : String) : IO Executor := do
  let sequence ← IO.mkRef (0 : Nat)
  return fun call => do
    let number ← sequence.modifyGet fun n => (n + 1, n + 1)
    let logBase := s!"{scratch}/{number}"
    IO.println s!"hermetic: {call.tool} {String.intercalate " " call.args.toList}"
    (← IO.getStdout).flush
    IO.FS.writeFile (logBase ++ ".argv") (reprStr (call.tool, call.args))
    let result ← execute call
    match result with
    | .ok output =>
        IO.FS.writeFile (logBase ++ ".stdout") output.stdout
        IO.FS.writeFile (logBase ++ ".stderr") output.stderr
    | .error message => IO.FS.writeFile (logBase ++ ".error") message
    return result

def preflight (exec : Executor) : Decision Unit := do
  let os ← checked exec { tool := "uname", args := #["-s"] }
  let arch ← checked exec { tool := "uname", args := #["-m"] }
  if !hostSupported os.stdout.trimAscii.toString arch.stdout.trimAscii.toString then
    decline "Hermetic validation supports Linux and macOS on x64 or arm64. Use a supported host with rootless Podman."
  let info ← checked exec { tool := "podman", args := #["info", "--format", "{{.Host.Security.Rootless}}"] }
  if info.stdout.trimAscii.toString != "true" then
    decline "Start a rootless Podman machine or connection before running hermetic validation."

def run (root : String) : Decision String := do
  let root ← attempt "resolve checkout; retry with an existing --root" (IO.FS.realPath root)
  if root.toString.contains ',' || root.toString.contains '\n' then
    decline "Podman mount paths cannot contain commas or newlines. Move the checkout to a path without them and retry."
  let top ← ofIO (succeededGit #["-C", root.toString, "rev-parse", "--show-toplevel"])
  let top ← attempt "resolve Git root; repair checkout" (IO.FS.realPath top.stdout.trimAscii.toString)
  if top != root then decline "Pass the checkout root to --root, rather than a subdirectory."
  preflight execute
  let token ← attempt "allocate unique scratch name; check temporary directory" IO.FS.createTempDir
  let scratch := root / ".lake" / "hermetic" / token.fileName.getD "run"
  attempt "release scratch name reservation" (IO.FS.removeDir token)
  attempt "create logs directory; check checkout permissions" (IO.FS.createDirAll scratch)
  attempt "report scratch location" (IO.println s!"hermetic: logs and inputs retained at {scratch}")
  attempt "flush scratch location" ((← IO.getStdout).flush)
  let exec ← attempt "open hermetic log" (loggedExecutor scratch.toString)
  let digester ← ofIO Digester.resolve
  prepare exec root.toString scratch.toString digester.digest
  checkedCompletion exec { tool := "podman", args := containerArgs root.toString scratch.toString, timeoutMs := 1200000 } ("tlrelease hermetic-worker: " ++ completion)
  return s!"{completion}\nLogs: {scratch}"

/-- The same worker logic is driven against planted observations in tests.
No alternate executable or environment override is exposed by the public CLI. -/
structure World where
  exec : Executor
  read : String → IO (Except String String)
  write : String → String → IO (Except String Unit)
  pathExists : String → IO Bool
  present : String → IO Bool

def nativeWorld : World := {
  exec := execute, read := readTextFile,
  write := fun path text => do
    match ← (IO.FS.writeFile path text).toBaseIO with
    | .ok () => return .ok ()
    | .error error => return .error s!"{error}",
  pathExists := fun path => System.FilePath.pathExists path,
  present := Policy.onPath }

def workerWith (world : World) (root scratch : String) : Decision String := do
  if root != "/workspace" || scratch != "/scratch" then
    decline "The worker must run inside the isolated container. Use hermetic --root at the checkout root."
  let mounts ← ofIO (world.read "/proc/mounts")
  for path in ["/workspace", "/scratch", "/lib", "/lib64", "/bin/busybox"] do
    if !(mounts.splitOn "\n").any (fun line => (line.splitOn " ")[1]? == some path) then
      decline s!"Missing isolated {path} mount. Run the public hermetic command to construct the container."
  let writable ← attempt "test checkout mount" (world.write "/workspace/.hermetic-write-probe" "")
  if writable.isOk then decline "The checkout mount is writable. Restore the read-only Podman mount."
  let scratchWrite ← attempt "test scratch mount" (world.write "/scratch/write-probe" "")
  ofExcept (scratchWrite.mapError (fun e => s!"Scratch is not writable: {e}. Repair the scratch mount permissions."))
  for (flag, format) in [("-u", "%u"), ("-g", "%g")] do
    let actual ← checked world.exec { tool := "id", args := #[flag] }
    let owner ← checked world.exec { tool := "stat", args := #["-c", format, scratch] }
    if actual.stdout != owner.stdout then decline "Container identity does not match scratch ownership. Restore the rootless UID mapping."
  for path in ["/var/run/docker.sock", "/run/podman/podman.sock", "/run/user/0/podman/podman.sock"] do
    if ← attempt "check engine socket absence" (world.pathExists path) then
      decline "A container-engine socket entered validation. Remove the socket mount and retry."
  for runtime in forbiddenRuntimes do
    if ← attempt "check forbidden PATH entry" (world.present runtime) then
      decline s!"Forbidden runtime {runtime} is on PATH. Restore the runtime-stripped image."
    let found ← checked world.exec { tool := "find", args := #["/", "-xdev", "(", "-type", "f", "-o", "-type", "l", ")", "(", "-name", runtime,
      "-o", "-name", runtime ++ "[0-9]*", "-o", "-name", "nodejs", ")", "-print"] }
    if !found.stdout.trimAscii.isEmpty then decline s!"Forbidden runtime files: {found.stdout}. Restore the pinned stripped image."
  for tool in requiredTools do
    if !(← attempt "check required tool" (world.present tool)) then
      decline s!"Missing hermetic input {tool}. Rerun preparation to restore the complete tool set."
  steps world.exec evidenceCalls
  checkedCompletion world.exec { tool := "/scratch/launcher-suite", args := #[], timeoutMs := 600000 } launcherCompletion
  return completion

def command : Command := optionCommand "hermetic" "--root <dir>"
  "Build and run the shared local/CI runtime-stripped release validation."
  ["--root", "."] [{ name := "root", takesValue := true }]
  (fun options => options.required "root") run

def workerCommand : Command := optionCommand "hermetic-worker" "--root <dir> --scratch <dir>"
  "Run evidence inside the isolated container prepared by hermetic."
  ["--root", "/workspace", "--scratch", "/scratch"]
  [{ name := "root", takesValue := true }, { name := "scratch", takesValue := true }]
  (fun options => do return (← options.required "root", ← options.required "scratch"))
  (fun (root, scratch) => workerWith nativeWorld root scratch)

end Release.Hermetic
