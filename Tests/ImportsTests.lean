/-
`Tests.ImportsTests` — guards the AGENTS.md rule that every `Tl/**/*.lean` is
imported by the root module `Tl.lean`. A file not reachable from the root is
invisible to `lake build` (its proofs/code never compile), so an omission is a
silent defect. This walks the source tree and asserts each module appears as an
`import` line in `Tl.lean` — the class-fix for the `Tl.Cli.Sanitize` omission,
so the whole class (not just that instance) cannot recur.
-/
import Tests.Harness

namespace Tl.Tests

open System (FilePath)

/-- Every `.lean` file under `dir`, recursively. -/
private partial def leanFilesUnder (dir : FilePath) : IO (Array FilePath) := do
  let mut acc : Array FilePath := #[]
  for e in (← dir.readDir) do
    let p := e.path
    if (← p.isDir) then
      acc := acc ++ (← leanFilesUnder p)
    else if p.extension == some "lean" then
      acc := acc.push p
  return acc

/-- `Tl/Cli/Sanitize.lean` → the module name `Tl.Cli.Sanitize`. -/
private def moduleOf (p : FilePath) : String :=
  let s := p.toString
  let s := if s.endsWith ".lean" then s.dropEnd 5 else s
  (s.replace "/" ".").replace "\\" "."

/-- Assert the root module imports every source file under `Tl/`. -/
def importsTests : IO (List Outcome) := do
  let root : FilePath := "Tl"
  if !(← root.isDir) then
    return [check "imports: Tl/ source tree present at cwd" false
      s!"could not find {root} under cwd {(← IO.currentDir)} — run tltest from the repo root"]
  let tl ← IO.FS.readFile "Tl.lean"
  let importLines := (tl.splitOn "\n").map (·.trimAscii)
  let files ← leanFilesUnder root
  let mut outs : Array Outcome := #[]
  outs := outs.push (check "imports: walked the Tl/ tree"
    (files.size ≥ 30) s!"found only {files.size} .lean files under Tl/ — the walk looks wrong")
  for p in files do
    let mod := moduleOf p
    outs := outs.push (check s!"root imports {mod}"
      (importLines.contains ("import " ++ mod))
      s!"{p} is not imported by Tl.lean — add `import {mod}` (AGENTS.md every-file-in-root rule)")
  return outs.toList

end Tl.Tests
