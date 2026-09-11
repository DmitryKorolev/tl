/-
Which `uname` a target is, said once in typed form.

`install.sh` and `npm/tl/bin/tl` both classify `uname -s` and `uname -m` into
the `os`/`cpu` pair that names a published asset. Neither can read this
repository at the moment it runs — the installer is piped from `curl`, and the
launcher ships inside a published npm package — so each carries the mapping
inline. That duplication is forced and is not the problem.

What was a problem is where the mapping was *authoritative*. It used to live in
the former shared shell library as a shell function nothing called, and the two
shipped copies were compared against it as text. That made a shell file the
source of truth for a decision the release already models in typed form, and it
meant the guard died with the file: deleting that library would delete
the comparison rather than migrate it.

The authority is here instead, as data. `release/targets.json` says which
`os`/`cpu` pairs this project publishes; the arms below say which `uname`
spellings reach them. The two are cross-checked in both directions, so a target
added to `targets.json` with no arm that selects it is a refusal, and an arm
selecting something no target names is a refusal too. The shipped copies are
then compared against *this*, not against each other and not against a shell
function.

The comparison is still textual in one narrow sense: the adapters' `case`
blocks are read with `Consistency.caseClassification` and matched against the
rendering below. That is deliberate. What has to agree is which pattern selects
which target, and both files write that as a shell `case` — so the rendering is
compared with what the shell will actually run, rather than with a paraphrase
of it.
-/
import release.Command
import release.Consistency
import release.Model

namespace Release
namespace Platform

/-! ## The authority -/

/-- One arm of a platform mapping: the `case` pattern exactly as it is written,
    and the target component it selects.

    `selects := none` is an arm that only refuses. It is carried rather than
    omitted because an adapter that dropped its refusing arm would otherwise
    read as agreeing: the remaining arms would still match, and an unsupported
    system would fall through to whatever came next instead of being told it is
    unsupported. -/
structure Arm where
  pattern : String
  selects : Option String
  deriving Repr, DecidableEq

/-- What `uname -s` classifies to.

    The Windows arm refuses rather than selecting: tl's filesystem primitives
    are unimplemented there, so a binary would start and then be unable to
    mutate task state safely. It is a named arm rather than falling to `*`
    because the message a Windows user needs — use WSL2, where the Linux build
    is fully supported — is not the message an unknown system needs. -/
def osArms : List Arm :=
  [{ pattern := "Darwin", selects := some "darwin" },
   { pattern := "Linux", selects := some "linux" },
   { pattern := "MINGW* | MSYS* | CYGWIN* | Windows_NT", selects := none },
   { pattern := "*", selects := none }]

/-- What `uname -m` classifies to.

    Two spellings reach each architecture because the kernels disagree: Linux
    says `aarch64` and `x86_64`, macOS says `arm64`, and some BSD-derived
    userlands say `amd64`. All four are the same two machines. -/
def archArms : List Arm :=
  [{ pattern := "arm64 | aarch64", selects := some "arm64" },
   { pattern := "x86_64 | amd64", selects := some "x64" },
   { pattern := "*", selects := none }]

/-- The arms rendered into the shape `Consistency.caseClassification` produces:
    a pattern, and the values its arm assigns in order.

    A selecting arm assigns exactly one value and a refusing arm assigns none,
    which is what makes the comparison total — every arm of a shipped copy has
    a counterpart here, including the ones that only produce a message. -/
def expected (arms : List Arm) : List (String × List String) :=
  arms.map fun arm =>
    (arm.pattern, match arm.selects with
                  | some value => [value]
                  | none => [])

/-- Every component these arms select, without the refusing ones. -/
def selections (arms : List Arm) : List String :=
  arms.filterMap (·.selects)

/-! ## Cross-checking the authority against the target list

The arms above are only an authority if they describe the targets this project
actually publishes. Both directions are checked, because they fail differently:
an arm selecting an unknown component would name an asset no release builds,
and a target no arm selects would be a published binary nobody's `uname` can
ever reach. -/

/-- Whether every selection names a component some target has, and every target's
    component is reachable from some arm. -/
def covers (arms : List Arm) (components : List String) : Bool :=
  (selections arms).all components.contains
    && components.all (selections arms).contains

/-- **The cross-check holds exactly when the two component sets contain each
    other.**

    Stated in both directions because the two failures are different releases:
    left to right, an arm that selects something no target names sends a user to
    an asset that was never built; right to left, a target with no arm is a
    binary the release publishes and no installer can ever ask for. A check that
    silently dropped either direction would still pass on today's data, which is
    exactly the kind of gate that reads as green until the day a target is
    added. -/
theorem covers_iff (arms : List Arm) (components : List String) :
    covers arms components = true ↔
      ((∀ value ∈ selections arms, value ∈ components)
        ∧ (∀ component ∈ components, component ∈ selections arms)) := by
  rw [covers, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · intro ⟨forward, backward⟩
    refine ⟨fun value member => ?_, fun component member => ?_⟩
    · exact List.mem_of_elem_eq_true (forward value member)
    · exact List.mem_of_elem_eq_true (backward component member)
  · intro ⟨forward, backward⟩
    refine ⟨fun value member => ?_, fun component member => ?_⟩
    · exact List.elem_eq_true_of_mem (forward value member)
    · exact List.elem_eq_true_of_mem (backward component member)

/-- The `os` values the target list names, each once. -/
def targetOperatingSystems (targets : Targets) : List String :=
  (targets.targets.map (·.os)).eraseDups

/-- The `cpu` values the target list names, each once. -/
def targetArchitectures (targets : Targets) : List String :=
  (targets.targets.map (·.cpu)).eraseDups

/-! ## Comparing a shipped copy against the authority -/

/-- Where one classification block lives, and which arms it must instantiate. -/
structure Mapping where
  /-- The adapter carrying the block. -/
  consumer : String
  /-- The `EMBEDDED-COPY` marker name bounding it. -/
  blockName : String
  /-- What the block classifies, for the message. -/
  what : String
  /-- The typed arms it is held to. -/
  arms : List Arm

/-- Every classification this gate owns.

    The list is the gate: a block not named here is not compared. Both consumers
    carry both mappings, and both are checked, because a copy that drifts in
    either file selects the wrong asset in a different distribution channel. -/
def mappings : List Mapping :=
  [{ consumer := "install.sh", blockName := "detect_os",
     what := "uname -s", arms := osArms },
   { consumer := "install.sh", blockName := "detect_arch",
     what := "uname -m", arms := archArms },
   { consumer := "npm/tl/bin/tl", blockName := "detect_os",
     what := "uname -s", arms := osArms },
   { consumer := "npm/tl/bin/tl", blockName := "detect_arch",
     what := "uname -m", arms := archArms }]

/-- Whether a parsed block agrees with the arms it is held to. -/
def agrees (observed : List (String × List String)) (arms : List Arm) : Bool :=
  observed == expected arms

/-- **A block is accepted exactly when it is the rendering of its arms.**

    The direction that matters is left to right: `agrees` returning `true` is
    what lets a release ship, so a comparison that drifted into accepting a
    block whose arms differ would pass a copy that maps a `uname` to the wrong
    target — an installer that fetches the wrong binary, reporting success. The
    reverse direction is what keeps the gate from being unsatisfiable, which is
    a different bug with a much shorter life. -/
theorem agrees_iff (observed : List (String × List String)) (arms : List Arm) :
    agrees observed arms = true ↔ observed = expected arms := by
  rw [agrees]
  exact beq_iff_eq

private def renderArms (rows : List (String × List String)) : String :=
  String.intercalate "; " (rows.map fun (pattern, values) =>
    if values.isEmpty then s!"{pattern} -> <refuses>"
    else s!"{pattern} -> {String.intercalate ", " values}")

/-- One mapping against the typed authority. -/
def mappingCheck (mapping : Mapping) (consumerText : String) :
    Except String Check := do
  let block ← embeddedBlock mapping.consumer consumerText mapping.blockName
  let observed := caseClassification block
  if observed.isEmpty then
    .error s!"{mapping.consumer}: the {mapping.blockName} block has no case arms to compare. The markers probably no longer wrap the mapping, which would leave this guard reporting success over nothing."
  return { held := agrees observed mapping.arms,
           failure := s!"{mapping.consumer}: the {mapping.blockName} block classifies {mapping.what} differently from the typed authority in release/Platform.lean.\n    shipped: {renderArms observed}\n    typed:   {renderArms (expected mapping.arms)}\n    A copy that maps a {mapping.what} to a different target ships the wrong binary to somebody. Change release/Platform.lean and both copies together, or explain why this consumer differs by giving it its own arms." }

/-- The authority against the target list. -/
def coverageChecks (targets : Targets) : List Check :=
  [{ held := covers osArms (targetOperatingSystems targets),
     failure := s!"the operating systems release/Platform.lean classifies to ({String.intercalate ", " (selections osArms)}) are not the operating systems release/targets.json publishes ({String.intercalate ", " (targetOperatingSystems targets)}). An arm selecting an os no target names sends an installer after an asset no release builds; a target no arm selects is a binary no uname can ever ask for. Add the arm, or remove the target." },
   { held := covers archArms (targetArchitectures targets),
     failure := s!"the architectures release/Platform.lean classifies to ({String.intercalate ", " (selections archArms)}) are not the architectures release/targets.json publishes ({String.intercalate ", " (targetArchitectures targets)}). An arm selecting a cpu no target names sends an installer after an asset no release builds; a target no arm selects is a binary no uname can ever ask for. Add the arm, or remove the target." }]

/-! ## The command -/

private def platformOptions : List OptionSpec :=
  [{ name := "root", takesValue := true },
   { name := "targets", takesValue := true }]

private structure PlatformArgs where
  root : String
  targetsPath : String

private def platformArgs (options : Options) : Except String PlatformArgs := do
  return { root := ← options.required "root"
           targetsPath := ← options.required "targets" }

/-- The target list and the checkout are arguments rather than paths this
    command knows, for the same reason the other consistency commands take
    theirs: which files the authority is cross-checked against is not a detail
    to discover by reading the source, and a command that can be invoked with
    nothing and still do something is not the contract the rest of this tool
    keeps. `--root` is also what makes every refusal below reachable from a
    planted checkout, rather than only from a repository someone has broken. -/
private def platformDecision (args : PlatformArgs) : Decision String := do
  let targets ← readParsed args.targetsPath Targets.parse
  let mut checks : Array Check := (coverageChecks targets).toArray
  -- Each consumer read once, not once per mapping: both carry two blocks each,
  -- and reading a file twice is how two rows come to disagree about what it
  -- says.
  let consumers := mappings.map (·.consumer) |>.eraseDups
  let mut texts : List (String × String) := []
  for consumer in consumers do
    let text ← ofIO (readTextFile ((System.FilePath.mk args.root) / consumer).toString)
    texts := texts ++ [(consumer, text)]
  for mapping in mappings do
    match texts.lookup mapping.consumer with
    | none => decline s!"{mapping.consumer} was not read, which is this gate failing to look."
    | some consumerText =>
        let check ← ofExcept (mappingCheck mapping consumerText)
        checks := checks.push check
  match Check.failures checks.toList with
  | [] =>
      return s!"{mappings.length} shipped platform mappings agree with the typed authority, which covers {args.targetsPath}"
  | problems =>
      decline (s!"a shipped platform mapping disagrees with the typed authority.\n"
        ++ String.join (problems.map fun problem => s!"  {problem}\n")
        ++ "install.sh is piped from curl and the npm launcher ships inside a package, so neither can read this repository when it runs; the copies are the interface, and a copy that drifts selects the wrong asset without failing.")

def platformCommand : Command :=
  optionCommand "platform-classification" "--root <checkout> --targets <targets.json>"
    "Refuse unless every shipped uname mapping agrees with the typed platform authority."
    ["--root", ".", "--targets", "release/targets.json"]
    platformOptions platformArgs platformDecision

def platformCommands : List Command := [platformCommand]

end Platform

export Platform (platformCommands)

end Release
