import Tests.Harness
import release.Cli

namespace Tl.Tests

private def inventoryGit (root : System.FilePath) (args : Array String) : IO Unit := do
  match ← Release.succeededGit (#["-C", root.toString] ++ args) with
  | .ok _ => pure ()
  | .error message => throw (IO.userError message)

private def inventoryWrite (root : System.FilePath) (path text : String) : IO Unit := do
  let full := root / path
  if let some parent := full.parent then IO.FS.createDirAll parent
  IO.FS.writeFile full text

private def inventoryRun (root : System.FilePath)
    (env : Array (String × Option String) := #[]) : IO Release.ProcessOutput := do
  let output ← IO.Process.output {
    cmd := ((← IO.currentDir) / ".lake/build/bin/tlrelease").toString
    args := #["shell-inventory", "--root", root.toString], env := env }
  return { exitCode := output.exitCode, stdout := output.stdout, stderr := output.stderr }

private def includes (text needle : String) : Bool := (text.splitOn needle).length > 1

def shellInventoryTests : IO (List Outcome) := do
  let _ := @Release.ShellInventory.accepts_iff
  let base ← IO.FS.createTempDir
  try
    let plant := fun (name : String) => do
      let root := base / name
      IO.FS.createDirAll root
      inventoryGit root #["init", "--quiet"]
      for path in ["install.sh", "scripts/verify-release-artifacts.sh", "npm/tl/bin/tl"] do
        inventoryWrite root path "#!/bin/sh\nexit 0\n"
      inventoryGit root #["add", "--all"]
      pure root
    let mut rows : List Outcome := []
    let clean ← plant "clean"
    inventoryWrite clean "untracked.sh" "#!/bin/sh\n"
    inventoryWrite clean "data" "ordinary data\n#!/bin/bash\n"
    inventoryWrite clean "workflow.yml" "run: sh hidden\n"
    inventoryWrite clean "binary" "\x00\xff\n"
    inventoryGit clean #["add", "--", "data", "workflow.yml", "binary"]
    let result ← inventoryRun clean
    rows := rows ++ [checkEq "shell inventory: clean exact checkout and untracked/data exclusions"
      result.exitCode 0,
      check "shell inventory: success discloses its complete scope"
        (includes result.stdout "npm/tl/bin/tl" && result.stderr.isEmpty) result.stderr]
    for path in ["install.sh", "scripts/verify-release-artifacts.sh", "npm/tl/bin/tl"] do
      inventoryWrite clean path "#!/bin/sh"
    let unterminated ← inventoryRun clean
    rows := rows ++ [checkEq "shell inventory: EOF terminates the exact first line"
      unterminated.exitCode 0]
    let shapes := [
      ("extension", "extra.sh", "ordinary text\n", "Extra"),
      ("bash", "extra", "#!/bin/bash\n", "Extra"),
      ("env", "extra", "#!/usr/bin/env sh\n", "Extra"),
      ("env-s", "extra", "#! /usr/bin/env -S bash -eu\n", "Extra"),
      ("tabs", "extra", "#!\t/bin/dash\t-e\n", "Extra"),
      ("crlf", "extra", "#!/bin/sh\r\n", "Extra"),
      ("spaces", "has spaces.sh", "\n", "has spaces.sh"),
      ("newline", "line\nbreak.sh", "\n", "line\nbreak.sh"),
      ("tab-name", "tab\tname.sh", "\n", "tracked entry"),
      ("long-header", "extra", "#!/bin/sh " ++ String.ofList (List.replicate 4090 ' ') ++ "\n", "4096")]
    for (label, path, text, diagnostic) in shapes do
      let root ← plant label
      inventoryWrite root path text
      inventoryGit root #["add", "--all"]
      let result ← inventoryRun root
      rows := rows ++ [check s!"shell inventory: {label} refuses through the public command"
        (result.exitCode == 1 && result.stdout.isEmpty && includes result.stderr diagnostic)
        result.stderr]
    for (label, header) in [("wrong-shell", "#!/bin/bash"), ("trailing-space", "#!/bin/sh "),
        ("survivor-crlf", "#!/bin/sh\r"), ("empty", ""), ("not-a-shell", "#!/usr/bin/perl")] do
      let root ← plant label
      inventoryWrite root "install.sh" (header ++ "\n")
      let result ← inventoryRun root
      rows := rows ++ [check s!"shell inventory: exact survivor header refuses {label}"
        (result.exitCode == 1 && includes result.stderr "wrong shebang") result.stderr]
    for path in ["install.sh", "scripts/verify-release-artifacts.sh", "npm/tl/bin/tl"] do
      let root ← plant ("missing-" ++ (path.replace "/" "-"))
      inventoryGit root #["rm", "--force", "--quiet", "--", path]
      let result ← inventoryRun root
      rows := rows ++ [check s!"shell inventory: missing {path} refuses"
        (result.exitCode == 1 && includes result.stderr "missing" && includes result.stderr path)
        result.stderr]
    for path in ["install.sh", "extensionless"] do
      let root ← plant ("unreadable-" ++ path)
      inventoryWrite root path "#!/bin/sh\n"
      inventoryGit root #["add", "--all"]
      IO.FS.removeFile (root / path)
      let result ← inventoryRun root
      rows := rows ++ [check s!"shell inventory: unreadable tracked candidate {path} refuses"
        (result.exitCode == 1 && includes result.stderr "restore" && includes result.stderr path)
        result.stderr]
    let directory ← plant "directory"
    IO.FS.removeFile (directory / "install.sh")
    IO.FS.createDirAll (directory / "install.sh")
    let directoryResult ← inventoryRun directory
    rows := rows ++ [check "shell inventory: a directory cannot stand in for a tracked regular file"
      (directoryResult.exitCode == 1 && includes directoryResult.stderr "not a regular file")
      directoryResult.stderr]
    let denied ← plant "permission-denied"
    inventoryWrite denied "candidate" "#!/bin/sh\n"
    inventoryGit denied #["add", "--all"]
    let mode ← Release.succeeded "chmod" #["000", (denied / "candidate").toString]
    if let .error message := mode then throw (IO.userError message)
    try
      let deniedResult ← inventoryRun denied
      rows := rows ++ [check "shell inventory: unreadable extensionless candidate cannot disappear"
        (deniedResult.exitCode == 1 && includes deniedResult.stderr "could not read tracked candidate")
        deniedResult.stderr]
    finally
      let mode ← Release.succeeded "chmod" #["644", (denied / "candidate").toString]
      if let .error message := mode then throw (IO.userError message)
    for (name, path, tracked, expected) in [
        ("substituted-link", "install.sh", false, 1),
        ("tracked-shell-link", "install.sh", true, 1),
        ("tracked-data-link", "link", true, 0)] do
      let root ← plant name
      if ← (root / path).pathExists then IO.FS.removeFile (root / path)
      let link ← Release.succeeded "ln" #["-s", (clean / "install.sh").toString, (root / path).toString]
      if let .error message := link then throw (IO.userError message)
      if tracked then inventoryGit root #["add", "--all"]
      let result ← inventoryRun root
      rows := rows ++ [checkEq s!"shell inventory: {name}" result.exitCode expected]
    let alien := base / "not-a-checkout"
    IO.FS.createDirAll alien
    let alienResult ← inventoryRun alien
    rows := rows ++ [check "shell inventory: cannot establish the tracked inventory outside git"
      (alienResult.exitCode == 1 && alienResult.stdout.isEmpty) alienResult.stderr]
    let nested ← inventoryRun (clean / "scripts")
    rows := rows ++ [check "shell inventory: checkout subdirectories cannot narrow the inventory"
      (nested.exitCode == 1 && includes nested.stderr "checkout root") nested.stderr]
    let broken ← plant "broken-index"
    IO.FS.writeFile (broken / ".git/index") "corrupt index\n"
    let brokenResult ← inventoryRun broken
    rows := rows ++ [check "shell inventory: an unreadable index refuses with a repair instruction"
      (brokenResult.exitCode == 1 && includes brokenResult.stderr "Repair") brokenResult.stderr]
    let empty := base / "empty-checkout"
    IO.FS.createDirAll empty
    inventoryGit empty #["init", "--quiet"]
    let emptyResult ← inventoryRun empty
    rows := rows ++ [check "shell inventory: an empty inventory is not success"
      (emptyResult.exitCode == 1 && includes emptyResult.stderr "missing") emptyResult.stderr]
    let hostile ← inventoryRun clean #[("GIT_DIR", some (directory / ".git").toString),
      ("GIT_WORK_TREE", some directory.toString), ("GIT_INDEX_FILE", some (base / "absent-index").toString)]
    rows := rows ++ [checkEq "shell inventory: ambient git routing cannot substitute a checkout"
      hostile.exitCode 0]
    for header in ["", "#", "#!", "#! /usr/bin/env", "#! /usr/bin/env -S",
        "#!/usr/bin/env python3", "#!/usr/bin/perl", "#!/bin/shadow", " #!/bin/sh"] do
      rows := rows ++ [check s!"shell inventory: non-shell first line {repr header}"
        (!Release.ShellInventory.shellShebang header)]
    return rows
  finally IO.FS.removeDirAll base

end Tl.Tests
