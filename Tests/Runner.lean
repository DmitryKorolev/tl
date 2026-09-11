import Tests.Harness
import Std.Data.HashSet

namespace Tl.Tests

/-- A named, deferred group. Constructing the registry never runs fixtures. -/
structure TestGroup where
  id : String
  label : String
  run : Unit → IO (List Outcome)

inductive TestRequest where
  | help
  | list
  | run (groups : List String)
  deriving BEq, DecidableEq, Repr

def testRunnerUsage : String :=
  "Usage: lake exe tltest [--group NAME ... | --list | --help]\n\
   With no arguments, run every group sequentially.\n\
   --group NAME selects an exact group name; repeat to select several.\n\
   Selected groups run once, in registry order. Use --list to find names.\n\
   Focused runs do not replace the complete CI suite."

def parseTestRequest : List String → Except String TestRequest
  | [] => .ok (.run [])
  | ["--help"] => .ok .help
  | ["--list"] => .ok .list
  | args => go args []
where
  go : List String → List String → Except String TestRequest
    | [], names => .ok (.run names.reverse)
    | "--group" :: name :: rest, names =>
      if name.trimAscii.isEmpty || name.startsWith "--" then
        .error "--group needs a nonempty group name; use --list to find names"
      else go rest (name :: names)
    | ["--group"], _ => .error "--group needs a group name; use --list to find names"
    | arg :: _, _ => .error s!"unexpected argument '{arg}'; use --help for supported options"

/-- Validate before running any fixture, including requests with a valid prefix. -/
def selectTestGroups (registry : List TestGroup) (names : List String) :
    Except String (List TestGroup) := do
  if registry.isEmpty then
    throw "the group registry is empty; restore the complete test registry"
  let mut ids : Std.HashSet String := {}
  for group in registry do
    if group.id.trimAscii.isEmpty then
      throw "a group has an empty name; give every registered group a stable name"
    if ids.contains group.id then
      throw "the group registry has duplicate names; give each group a distinct name"
    ids := ids.insert group.id
  let mut requested : Std.HashSet String := {}
  for name in names do
    unless ids.contains name do
      throw s!"unknown group '{name}'; use --list to find names"
    requested := requested.insert name
  let selected := if names.isEmpty then registry else registry.filter (fun g => requested.contains g.id)
  return selected

/-- Flush progress even when the public supervisor's stdout is a pipe. -/
def testProgress (text : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn text
  out.flush

/-- Subgroup timing for a large suite's fixture/process boundaries. Exceptions
    still propagate to the enclosing group, with elapsed time reported first. -/
def measureTestFixture (name : String) (action : IO α) : IO α := do
  testProgress s!"FIXTURE START {name}"
  let started ← IO.monoMsNow
  try action finally
    testProgress s!"FIXTURE END {name}: {(← IO.monoMsNow) - started} ms"

/-- Execute sequentially so timing assertions never compete with other groups.
    Group exceptions and empty results are failures, and later groups still run. -/
def runTestGroups (groups : List TestGroup) : IO UInt32 := do
  if groups.isEmpty then
    IO.eprintln "No test groups selected; restore the registry or use --list to select a group."
    return 1
  let started ← IO.monoMsNow
  let mut total := 0
  let mut failed := 0
  for group in groups do
    testProgress s!"START {group.id}: {group.label}"
    let groupStarted ← IO.monoMsNow
    let outcomes ← try group.run () catch error => pure [{
      name := "group execution"
      passed := false
      msg := s!"{error}; repair this group's fixture or setup and rerun --group {group.id}"
    }]
    let outcomes := nonemptyOutcomes outcomes
    total := total + outcomes.length
    let groupFailed ← runGroup group.label outcomes
    failed := failed + groupFailed
    let elapsed := (← IO.monoMsNow) - groupStarted
    testProgress s!"END {group.id}: {outcomes.length} assertions, {groupFailed} failed, {elapsed} ms"
  let elapsed := (← IO.monoMsNow) - started
  testProgress s!"Finished {groups.length} groups in {elapsed} ms."
  return ← reportOutcomes total failed

def runTestRequest (registry : List TestGroup) (args : List String) : IO UInt32 := do
  match parseTestRequest args with
  | .error message =>
    IO.eprintln s!"tltest: {message}"
    return 2
  | .ok .help =>
    testProgress testRunnerUsage
    return 0
  | .ok request =>
    let names := match request with | .run names => names | _ => []
    match selectTestGroups registry names with
    | .error message =>
      IO.eprintln s!"tltest: {message}"
      return 2
    | .ok groups =>
      match request with
      | .list =>
        for group in groups do testProgress s!"{group.id}\t{group.label}"
        return 0
      | .run _ =>
        testProgress (if args.isEmpty then "Running the complete test suite."
          else "Running selected test groups only; this is not the complete CI suite.")
        runTestGroups groups
      | .help => return 0

end Tl.Tests
