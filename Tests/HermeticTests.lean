import Tests.Harness
import release.Hermetic

namespace Tl.Tests
open Release Release.Hermetic

private def answer (text : String := "") : Except String ProcessOutput :=
  .ok { exitCode := 0, stdout := text, stderr := "" }

private def refused {α : Type} (result : Except String α) (needle : String := "") : Bool :=
  match result with
  | .error text => (text.splitOn needle).length > 1 || needle.isEmpty
  | .ok _ => false

private def workerFixture (trace : IO.Ref (List Call)) (fault : String := "") : World := {
  exec := fun call => do
    trace.modify (· ++ [call])
    if fault == "call:" ++ call.tool ++ String.intercalate " " call.args.toList then return .error "process sentinel; repair the tool"
    if call.tool == "id" then return answer "0\n"
    if call.tool == "stat" then
      return answer (if fault == "owner:" ++ call.args[1]! then "1\n" else "0\n")
    if call.tool == "find" then
      return answer (if fault == "file:" ++ call.args[11]! then "/usr/bin/forbidden\n" else "")
    if call.tool == "/scratch/launcher-suite" then
      return answer (if fault == "completion" then "" else launcherCompletion ++ "\n")
    return answer,
  read := fun _ => pure <| if fault == "mount-read" then .error "unreadable mounts" else .ok <|
    String.join (["/workspace", "/scratch", "/lib", "/lib64", "/bin/busybox"].filterMap fun path =>
      if fault == "mount:" ++ path then none else some s!"source {path} filesystem rw 0 0\n"),
  write := fun path _ => pure <|
    if path.startsWith "/workspace" then
      if fault == "writable" then .ok () else .error "read-only"
    else if fault == "scratch" then .error "denied" else .ok (),
  pathExists := fun path => pure (fault == "socket:" ++ path),
  present := fun tool => pure <|
    if forbiddenRuntimes.contains tool then fault == "path:" ++ tool
    else fault != "missing:" ++ tool }

private def workerRows : IO (List Outcome) := do
  let trace ← IO.mkRef []
  let good ← (workerWith (workerFixture trace) "/workspace" "/scratch").run
  let calls ← trace.get
  let mut rows := [checkOk "hermetic worker: complete evidence reaches the verdict" good completion]
  let faults := ["mount-read", "writable", "scratch", "owner:%u", "owner:%g", "completion"] ++
    (["/workspace", "/scratch", "/lib", "/lib64", "/bin/busybox"].map ("mount:" ++ ·)) ++
    (["/var/run/docker.sock", "/run/podman/podman.sock", "/run/user/0/podman/podman.sock"].map ("socket:" ++ ·)) ++
    (forbiddenRuntimes.map ("path:" ++ ·)) ++ (forbiddenRuntimes.map ("file:" ++ ·)) ++
    (requiredTools.map ("missing:" ++ ·)) ++
    (calls.map fun c => "call:" ++ c.tool ++ String.intercalate " " c.args.toList)
  for fault in faults do
    let record ← IO.mkRef []
    let result ← (workerWith (workerFixture record fault) "/workspace" "/scratch").run
    rows := rows ++ [check s!"hermetic worker: {fault} refuses" (refused result) (reprStr result)]
  for (root, scratch) in [("/", "/scratch"), ("/workspace", "/tmp")] do
    let record ← IO.mkRef []
    let result ← (workerWith (workerFixture record) root scratch).run
    rows := rows ++ [check "hermetic worker: refuses host paths before effects" (refused result && (← record.get).isEmpty)]
  return rows

private def preflightRows : IO (List Outcome) := do
  let mut rows := []
  for os in ["Linux", "Darwin", "FreeBSD", "Windows"] do
    for arch in ["x86_64", "amd64", "arm64", "aarch64", "riscv64"] do
      let exec : Executor := fun call => pure <| answer <|
        if call.tool == "podman" then "true\n" else if call.args == #["-s"] then os else arch
      let result ← (preflight exec).run
      rows := rows ++ [check s!"hermetic preflight: {os}/{arch}"
        (result.isOk == (["Linux", "Darwin"].contains os && arch != "riscv64"))]
  for fault in ["uname-s", "uname-m", "podman", "rootful", "malformed"] do
    let exec : Executor := fun call => pure <|
      if fault == "uname-s" && call.args == #["-s"] || fault == "uname-m" && call.args == #["-m"] || fault == "podman" && call.tool == "podman" then
        .error "unavailable process sentinel"
      else answer (if call.tool == "podman" then (if fault == "rootful" then "false" else "invalid")
        else if call.args == #["-s"] then "Linux" else "x86_64")
    rows := rows ++ [check s!"hermetic preflight: {fault} refuses" (refused (← (preflight exec).run))]
  return rows

private def cleanupRows : IO (List Outcome) := do
  let mut rows := []
  for bodyFailure in [false, true] do
    for removalFailure in [false, true] do
      let trace ← IO.mkRef ([] : List Call)
      let exec : Executor := fun call => do
        trace.modify (· ++ [call])
        if removalFailure && call.args[0]? == some "rm" then return .error "removal sentinel"
        return answer
      let body : Decision Unit := if bodyFailure then decline "body sentinel" else pure ()
      let result ← (withContainer exec "fixture" { tool := "podman", args := #["create"] } body).run
      rows := rows ++ [check s!"hermetic cleanup: body={bodyFailure}, removal={removalFailure}"
        (result.isOk == (!bodyFailure && !removalFailure) && (← trace.get).length == 2)]
  let count ← IO.mkRef (0 : Nat)
  let createFailure : Executor := fun _ => do count.modify (· + 1); return .error "create sentinel"
  let result ← (withContainer createFailure "fixture" { tool := "podman", args := #[] } (pure ())).run
  rows := rows ++ [check "hermetic cleanup: failed creation has no later effects" (refused result && (← count.get) == 1)]
  for throwing in [false, true] do
    let removed ← IO.mkRef false
    let exec : Executor := fun call => do
      if call.args[0]? == some "rm" then removed.set true
      return answer
    let body : Decision Unit := if throwing then ofIO (throw (IO.userError "throw sentinel")) else decline "body sentinel"
    let result ← (withContainer exec "fixture" { tool := "podman", args := #["create"] } body).run
    rows := rows ++ [check s!"hermetic cleanup: thrown={throwing} still removes container" (refused result && (← removed.get))]
  for bodyFailure in [false, true] do
    let exec : Executor := fun call => pure <| if call.args[0]? == some "rm" then
      .ok { exitCode := 42, stdout := "", stderr := "" } else answer
    let result ← (withContainer exec "fixture" { tool := "podman", args := #["create"] }
      (if bodyFailure then decline "body sentinel" else pure ())).run
    rows := rows ++ [check "hermetic cleanup: nonzero removal never passes" (refused result "cleanup failed")]
  return rows

private def preparationRows : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  try
    let root := base / "root with spaces"
    IO.FS.createDirAll (root / "npm/tl/bin")
    IO.FS.writeFile (root / "npm/tl/bin/tl") "launcher"
    let exercise (label : String) (failAt : Option Nat := none) (fault : String := "") := do
      let scratch := base / label
      IO.FS.writeFile (root / "npm/tl/bin/tl") "launcher"
      if fault == "source-missing" then IO.FS.removeFile (root / "npm/tl/bin/tl")
      if fault == "scratch-file" then IO.FS.writeFile scratch "not a directory"
      let seen ← IO.mkRef ([] : List Call)
      let put (path text : String) : IO Unit := do
        let path := System.FilePath.mk path
        IO.FS.createDirAll path.parent.get!
        IO.FS.writeFile path text
      let exec : Executor := fun call => do
        let index ← seen.modifyGet fun ls => (ls.length, ls ++ [call])
        if failAt == some index then return .error s!"stage {index} sentinel; repair the tool"
        if call.tool == "tar" && call.args.contains "package/bin/tl" && fault != "packed-missing" then
          put (scratch / "packed/package/bin/tl").toString (if fault == "packed-corrupt" then "changed" else "launcher")
        if call.tool == "cp" && fault.startsWith "config:" then
          IO.FS.createDirAll (scratch / (fault.drop 7).toString)
        if call.tool == "podman" && call.args[0]? == some "rm" && fault == "fixture-dir" then
          IO.FS.createDirAll (scratch / "launcher-suite")
        if call.tool == "chmod" && fault == "manifest-dir" then
          IO.FS.createDirAll (scratch / "positive-inputs.sha256")
        return answer
      let hash : Hasher := fun path => do
        if fault == "hash:" ++ (System.FilePath.mk path).fileName.getD "" then return .error "hash sentinel"
        let expected := match inputs.find? (fun input => path.endsWith ("/" ++ input.file)) with
          | some input => input.sha256
          | none => String.ofList (List.replicate 64 'a')
        return Sha256.parse "fixture" (if fault == "corrupt:" ++ (System.FilePath.mk path).fileName.getD "" then String.ofList (List.replicate 64 '0') else expected)
      let result ← (prepare exec root.toString scratch.toString hash).run
      return (result, ← seen.get, scratch)
    let (good, calls, scratch) ← exercise "good"
    let fixture ← IO.FS.readFile (scratch / "launcher-suite")
    let manifest ← IO.FS.readFile (scratch / "positive-inputs.sha256")
    let mut rows := [check "hermetic preparation: full sequence passes" good.isOk (reprStr good),
      checkEq "hermetic preparation: fixture bytes preserved" fixture launcherFixture,
      check "hermetic preparation: complete positive inventory" ((manifest.splitOn "\n").length == positiveFiles.length + 1),
      check "hermetic preparation: uses actual Lake configuration"
        (calls.any fun c => c.args.contains "/source/lakefile.lean"),
      check "hermetic preparation: builds static target"
        (calls.any fun c => c.args.toList.drop (c.args.size - 5) == ["lake", "-KreleaseOnly=true", "build", "tlreleaseStatic", "--wfail"]),
      check "hermetic preparation: Lake refreshes the disposable release-only manifest"
        (calls.any fun c => c.args.toList.drop (c.args.size - 3) == ["lake", "-KreleaseOnly=true", "update"])]
    for i in [:calls.length] do
      let (result, _, _) ← exercise s!"failure-{i}" (some i)
      rows := rows ++ [check s!"hermetic preparation: subprocess {i} failure propagates" (refused result)]
    for fault in ["packed-missing", "packed-corrupt", "source-missing", "scratch-file",
        "config:npm-userconfig", "config:npm-globalconfig", "fixture-dir", "manifest-dir"] ++
        (inputs.map (fun input => "corrupt:" ++ input.file)) ++
        (inputs.map (fun input => "hash:" ++ input.file)) ++
        (positiveFiles.map (fun path => "hash:" ++ (System.FilePath.mk path).fileName.getD "")) do
      let (result, _, _) ← exercise s!"fault-{rows.length}" none fault
      rows := rows ++ [check s!"hermetic preparation: {fault} refuses" (refused result)]
    return rows
  finally IO.FS.removeDirAll base

private def processRows : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  try
    let mut rows := []
    for (label, body, passes) in [
        ("complete", "printf 'fixture verdict\\n'", true),
        ("early exit", "exit 0", false),
        ("nonzero", "printf 'fixture verdict\\n'; exit 42", false),
        ("not final", "printf 'fixture verdict\\nlater\\n'", false)] do
      let result ← (checkedCompletion execute { tool := "sh", args := #["-c", body] } "fixture verdict").run
      rows := rows ++ [check s!"hermetic supervision: {label}" (result.isOk == passes)]
    let timeout ← execute { tool := "sleep", args := #["1"], timeoutMs := 10 }
    let absent ← execute { tool := (base / "absent").toString, args := #[] }
    rows := rows ++ [check "hermetic processes: timeout refuses" (refused timeout "did not finish"),
      check "hermetic processes: missing tool refuses" (refused absent "could not be run")]
    let brokenLog ← loggedExecutor (base / "missing-logs").toString
    let logFailure ← (brokenLog { tool := "true", args := #[] }).toBaseIO
    rows := rows ++ [check "hermetic logs: unwritable log refuses before process execution" (!logFailure.isOk)]
    let tool := ((← IO.currentDir) / ".lake/build/bin/tlrelease").toString
    IO.FS.createDirAll (base / "comma,path")
    for (args, expected) in [
        (#["hermetic"], (2 : UInt32)),
        (#["hermetic", "--root", (base / "absent-root").toString], 1),
        (#["hermetic", "--root", (base / "comma,path").toString], 1),
        (#["hermetic", "--root", base.toString], 1),
        (#["hermetic-worker", "--root", "/", "--scratch", "/scratch"], 1),
        (#["hermetic-worker", "--root", "/workspace"], 2)] do
      let result ← IO.Process.output { cmd := tool, args }
      rows := rows ++ [checkEq s!"hermetic public command: {args} exits {expected}" result.exitCode expected,
        check "hermetic public refusal includes a diagnosis" (!result.stderr.trimAscii.isEmpty)]
    let exec ← loggedExecutor base.toString
    let _ ← exec { tool := "sh", args := #["-c", "printf out; printf err >&2"] }
    let _ ← exec { tool := (base / "absent").toString, args := #[] }
    rows := rows ++ [checkEq "hermetic logs: stdout retained" (← IO.FS.readFile (base / "1.stdout")) "out",
      checkEq "hermetic logs: stderr retained" (← IO.FS.readFile (base / "1.stderr")) "err",
      check "hermetic logs: failure retained" (!(← IO.FS.readFile (base / "2.error")).isEmpty)]
    let digester ← Digester.resolve
    if let .ok hash := digester then
      IO.FS.writeFile (base / "launcher-suite") launcherFixture
      let preserved ← (ensureDigest hash.digest (base / "launcher-suite").toString
        "364977500f97395aaa7903f62de90f2077fdef28eaf103e128acb55abb75d778").run
      rows := rows ++ [check "hermetic fixture: migrated launcher corpus is byte-identical" preserved.isOk (reprStr preserved)]
      IO.FS.writeFile (base / "abc") "abc"
      let known := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
      rows := rows ++ [check "hermetic input: real digest accepts pinned bytes"
        (← (ensureDigest hash.digest (base / "abc").toString known).run).isOk,
        check "hermetic input: corrupt bytes refuse"
          (refused (← (ensureDigest hash.digest (base / "abc").toString (String.ofList (List.replicate 64 '0'))).run) "Digest mismatch"),
        check "hermetic input: absent input refuses"
          (refused (← (ensureDigest hash.digest (base / "missing").toString known).run))]
    else rows := rows ++ [check "hermetic input: digest tool is available" false]
    return rows
  finally IO.FS.removeDirAll base

def hermeticTests : IO (List Outcome) := do
  let _ := @Release.Hermetic.completed_iff
  let expected := #["run", "--rm", "--platform", "linux/amd64", "--network", "none", "--read-only",
    "--read-only-tmpfs=false", "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
    "--userns", "host", "--user", "0:0",
    "--mount", "type=bind,source=/repo with spaces,target=/workspace,readonly",
    "--mount", "type=bind,source=/scratch with spaces,target=/scratch",
    "--mount", "type=bind,source=/scratch with spaces/static/bin/busybox.static,target=/bin/busybox,readonly",
    "--mount", "type=bind,source=/scratch with spaces/lib,target=/lib",
    "--mount", "type=bind,source=/scratch with spaces/lib64,target=/lib64",
    "--workdir", "/workspace", "--env", "HOME=/scratch/home", "--env", "TMPDIR=/scratch/tmp",
    "--env", "PATH=/scratch/tools:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
    "--entrypoint", "/scratch/tools/tlrelease",
    "docker.io/alpine/git@sha256:53a6239398162098fed2f49a46512f9cbba9e3f31b9f2cea4fa90129ee069a99",
    "hermetic-worker", "--root", "/workspace", "--scratch", "/scratch"]
  return [checkEq "hermetic container: exact restricted argv with unsplit paths"
    (containerArgs "/repo with spaces" "/scratch with spaces") expected] ++
    (← preflightRows) ++ (← workerRows) ++ (← cleanupRows) ++ (← preparationRows) ++ (← processRows)

end Tl.Tests
