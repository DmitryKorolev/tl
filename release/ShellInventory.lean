/-
ADR-0028's declared shell surfaces. This reads only tracked names and first
lines; it does not interpret shell bodies, workflow arguments, or operands.
Both policy profiles enforce this inventory before linting the survivors.
-/
import release.TaskId

namespace Release.ShellInventory

def survivors : List String :=
  ["install.sh", "scripts/verify-release-artifacts.sh", "npm/tl/bin/tl"]

/-- A bounded lexical vocabulary, not a shell command parser. `env` accepts
    a direct name or the conventional `-S` separator. No quoting, assignments,
    wrappers, or command operands are interpreted. -/
def shellShebang (line : String) : Bool :=
  if !line.startsWith "#!" then false
  else
    let words := ((line.drop 2).toString.trimAscii.toString.splitOn "\t" |>.flatMap (·.splitOn " "))
      |>.filter (!·.isEmpty)
    let shells := ["sh", "bash", "dash", "ash", "ksh", "ksh93", "mksh", "pdksh",
      "zsh", "csh", "tcsh", "fish"]
    match words with
    | interpreter :: args =>
        let name := (interpreter.splitOn "/").getLast!
        if name == "env" then
          let rest := if args.head? == some "-S" then args.drop 1 else args
          rest.head?.any fun name => shells.contains ((name.splitOn "/").getLast!)
        else shells.contains name
    | [] => false

/-- Set equality plus an independently pinned header for every survivor.
    The collector has already refused unreadable and nonregular candidates. -/
def accepts (candidates : List (String × String)) : Bool :=
  candidates.all (fun (path, line) => survivors.contains path && line == "#!/bin/sh") &&
    survivors.all (fun path => candidates.contains (path, "#!/bin/sh"))

theorem accepts_iff (candidates : List (String × String)) :
    accepts candidates = true ↔
      (∀ candidate ∈ candidates,
        (survivors.contains candidate.1 && candidate.2 == "#!/bin/sh") = true) ∧
      (∀ path ∈ survivors, candidates.contains (path, "#!/bin/sh") = true) := by
  simp only [accepts, Bool.and_eq_true, List.all_eq_true]

/-- Read at most 4097 bytes, without decoding binary files as UTF-8. A longer
    shebang is refused rather than silently truncated. Ordinary data needs
    only its first two bytes to establish that it has no shebang. -/
private def firstLine (path : System.FilePath) : IO String := do
  let handle ← IO.FS.Handle.mk path .read
  let mut bytes := ByteArray.empty
  for _ in [0:4097] do
    let byte ← handle.read 1
    if byte.isEmpty then break
    if byte[0]! == 10 then break
    bytes := bytes.push byte[0]!
    if bytes.size == 2 && bytes != "#!".toUTF8 then break
  let text := String.ofList (bytes.data.toList.map (fun byte => Char.ofNat byte.toNat))
  if bytes.size == 4097 then
    throw (IO.userError "the first line exceeds 4096 bytes; shorten the shebang before checking it")
  return text

private def inspect (root : String) : Decision String := do
  let relativePrefix ← ofIO (do
    match ← Release.succeededGit #["-C", root, "rev-parse", "--show-prefix"] with
    | .ok output => return .ok output.stdout
    | .error message => return .error s!"cannot inspect checkout {root}: {message}. Pass --root at a readable git checkout root and retry.")
  if !relativePrefix.trimAscii.isEmpty then
    decline "--root names a checkout subdirectory; pass the git checkout root so the inventory includes every tracked path."
  let listing ← ofIO (do
    match ← Release.succeededGit #["-C", root, "ls-files", "-s", "-z", "--"] with
    | .ok output => return .ok output
    | .error message => return .error s!"cannot list tracked files: {message}. Repair the checkout index and retry.")
  let entries ← ofExcept (TaskId.parseEntries listing.stdout >>= TaskId.collapseStages)
  let mut candidates : List (String × String) := []
  for entry in entries do
    if entry.isRegularFile || entry.path.endsWith ".sh" then
      let path := System.FilePath.mk root / entry.path
      let metadata ← attempt s!"could not inspect tracked candidate {entry.path}; restore the file and retry"
        path.symlinkMetadata
      if !entry.isRegularFile || metadata.type != .file then
        decline s!"tracked candidate {entry.path} is not a regular file; restore a regular file and retry."
      let line ← attempt s!"could not read tracked candidate {entry.path}; restore its readable bytes and retry"
        (firstLine path)
      if entry.path.endsWith ".sh" || shellShebang line then
        candidates := (entry.path, line) :: candidates
  if accepts candidates then
    return "exact shell inventory: install.sh, scripts/verify-release-artifacts.sh, npm/tl/bin/tl; each begins with #!/bin/sh"
  let extras := candidates.filterMap fun (path, _) => if survivors.contains path then none else some path
  let missing := survivors.filter fun path => !(candidates.any fun (name, _) => name == path)
  let wrong := candidates.filterMap fun (path, line) =>
    if survivors.contains path && line != "#!/bin/sh" then some path else none
  decline s!"shell inventory differs from ADR-0028; remove extra programs, restore missing survivors, and pin each survivor to exact #!/bin/sh. Extra: {extras}; missing: {missing}; wrong shebang: {wrong}."

def command : Command :=
  optionCommand "shell-inventory" "--root <dir>"
    "Require exactly the three ADR-0028 shell programs, each with the pinned shebang."
    ["--root", "."] [{ name := "root", takesValue := true }]
    (fun options => options.required "root") inspect

end Release.ShellInventory
