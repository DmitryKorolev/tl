/-
The release policy, as typed data instead of a shell script's call order.

`scripts/check-release-policy.sh` is two things at once: a list of what the
policy *is*, and a program that runs it. The list lives in a heredoc, the
program lives in a sequence of `rc_gate` calls, and nothing compares them —
`--list` has been wrong about the profile split, about which tool a gate needs,
and about which gates a tag run omits, each time without any gate failing.
Profile membership is the same shape: `ci` and `release` differ by one `if`, and
what that `if` means is written in three comments.

Here the gates are a list of values. Which profile a gate belongs to, which
tools it needs, what it runs and what a missing tool costs are fields, so the
listing is a projection of the registry rather than a parallel document, and
the runner reads the same list. A gate that exists but is unlisted, or listed
but never run, is not representable.

## What is decided rather than described

Three decisions here can be wrong silently, and each carries a theorem:

- **Whether a gate may be skipped.** A skipped gate is not a passing one, and
  under `--strict` it is a failure. Collapsing the two is how a policy run comes
  to mean "everything installed here passed" while reading as "everything
  passed".
- **Whether the run passed.** A failed gate must not be recoverable by a later
  one, and a run with no gates at all must not read as a clean run.
- **What a distribution surface contributes.** GitHub Release, npm and Homebrew
  are publication channels; the installer is a repository-served adapter with no
  publish job. A surface that silently acquired a publication effect would put a
  job behind a plan row that never promised one.

## The oracle, and its lifetime

While the shell policy is still authoritative, `policy-parity` requires the
typed gate and profile lists to equal the names the shell scripts report. It is
deleted with the shell policy, in the same change that makes this registry
authoritative — ADR-0028 says so, and a checker that outlives what it compares
against becomes a second definition of the thing.
-/
import release.Command
import release.Model
import release.Process

namespace Release

namespace Policy

/-! ## Which run this is -/

/-- The two policy profiles.

    They are not a narrowing of convenience. `release` is what the release
    workflow runs against the tagged commit, and ADR-0026's dependency boundary
    forbids `python`, `python3`, `ruby`, `brew`, `node` and `npm` on any path it
    reaches; `ci` additionally runs the gates for channels that are built but
    switched off, each of which invokes one of those. A deferred channel's gates
    are therefore *absent* from the release profile rather than skipped: a skip
    is a report about this run, and absence is a statement about the release. -/
inductive Profile where
  | ci
  | release
  deriving DecidableEq, Repr

def Profile.wire : Profile → String
  | .ci => "ci"
  | .release => "release"

def Profile.all : List Profile := [.ci, .release]

def Profile.parse (what : String) (text : String) : Except String Profile :=
  match Profile.all.find? (·.wire == text) with
  | some profile => .ok profile
  | none =>
      .error s!"{what}: '{text}' is not a policy profile. Pass 'ci' — every gate, including the ones for channels this release defers — or 'release', the v0.1 release path, which does not have them."

/-- Whether this run is checking a tagged commit.

    One gate is about the working tree rather than about the release: the
    checked-in build stamp must be the *development* stamp, and a tag run stamps
    on purpose. It is omitted rather than skipped, because "not applicable" and
    "could not run" have different remedies and only one of them is worth
    reporting. -/
inductive TagBehaviour where
  /-- Runs on every commit. -/
  | always
  /-- Not applicable to a tagged commit. -/
  | workingTreeOnly
  deriving DecidableEq, Repr

/-! ## What a gate is -/

/-- A tool a gate needs on `PATH`, and what its absence costs.

    The second field is not decoration. Two of these gates need two tools, and
    the absences differ: one stops the gate running at all, and the other leaves
    it running over less than it claims — `actionlint` without `shellcheck`
    checks the YAML and silently skips every `run:` block. A report that named
    only the tool would describe those as the same thing. -/
structure ToolRequirement where
  tool : String
  lost : String
  deriving DecidableEq, Repr

/-- What a gate runs.

    Closed, and separated from the argument list, so that "which program does
    this gate invoke" is a value a test can read rather than a prefix of a
    string. It is also what the dependency boundary is about: a gate in the
    release profile may not invoke a budgeted runtime, and that is a property of
    this field. -/
inductive Invocation where
  /-- A tracked program in this repository, run as itself. -/
  | script (path : String) (args : List String)
  /-- An external tool. -/
  | tool (command : String) (args : List String)
  /-- This executable, with a subcommand. -/
  | releaseCommand (args : List String)
  deriving DecidableEq, Repr

def Invocation.command : Invocation → String
  | .script path _ => path
  | .tool command _ => command
  | .releaseCommand _ => "tlrelease"

def Invocation.arguments : Invocation → List String
  | .script _ args => args
  | .tool _ args => args
  | .releaseCommand args => args

/-- The invocation as an operator would type it, for a report. -/
def Invocation.render (invocation : Invocation) : String :=
  String.intercalate " " (invocation.command :: invocation.arguments)

/-- One gate: what it is called, when it runs, what it needs, and what it
    does. -/
structure Gate where
  /-- The name every report uses. It is also what the parity oracle compares,
      so it is the shell's name exactly while both exist. -/
  name : String
  profiles : List Profile
  onTag : TagBehaviour
  requires : List ToolRequirement
  invocation : Invocation
  summary : String
  deriving Repr

/-! ## The registry

Every gate the release policy runs, in the order it runs them. The order is part
of the contract: a policy run is read top to bottom, and two runs of the same
profile that reported their gates in different orders would be two documents to
compare by hand.

Three gates still invoke a shell script's single-gate flag — the ShellCheck
sweep, the build-stamp comparison and the formula parse — because their bodies
have not been ported yet. Naming a real invocation rather than a placeholder is
what lets this run before it is authoritative; each becomes a `tlrelease`
command as its own port lands, and the shell allowlist is what will say when
none is left. -/

private def shellcheckTool : ToolRequirement :=
  { tool := "shellcheck", lost := "shellcheck is not on PATH" }

private def npmTool : ToolRequirement :=
  { tool := "npm", lost := "npm is not on PATH" }

def gates : List Gate :=
  [{ name := "task-id lint selftest"
     profiles := Profile.all, onTag := .always, requires := []
     invocation := .script "./scripts/check-task-ids.sh" ["--selftest"]
     summary := "The task-ID checker proves it still refuses before its silence is believed." },
   { name := "task-id leakage"
     profiles := Profile.all, onTag := .always, requires := []
     invocation := .script "./scripts/check-task-ids.sh" []
     summary := "No tracker id in a tracked artifact outside docs/ and README.md." },
   { name := "shell static analysis"
     profiles := Profile.all, onTag := .always, requires := [shellcheckTool]
     invocation := .script "./scripts/check-release-policy.sh" ["--shellcheck-only"]
     summary := "ShellCheck over every tracked shell file, found by shebang and extension." },
   { name := "build-provenance generator selftest"
     profiles := Profile.all, onTag := .always, requires := []
     invocation := .script "./scripts/gen-build-provenance.sh" ["--selftest"]
     summary := "The build-stamp generator proves it fails closed on what it cannot establish." },
   { name := "artifact verifier selftest"
     profiles := Profile.all, onTag := .always, requires := []
     invocation := .script "./scripts/verify-release-artifacts.sh" ["--selftest"]
     summary := "The code path behind VERIFYING.md, driven through every refusal it has." },
   { name := "release runtime boundary selftest"
     profiles := Profile.all, onTag := .always, requires := []
     invocation := .script "./scripts/check-release-runtimes.sh" ["--selftest"]
     summary := "The PATH shims that observe the dependency budget prove they still fire." },
   { name := "installer selftest"
     profiles := Profile.all, onTag := .always, requires := []
     invocation := .tool "sh" ["install.sh", "--selftest"]
     summary := "The script users pipe into a shell, driven through every branch it has." },
   { name := "workflow lint"
     profiles := Profile.all, onTag := .always
     requires := [{ tool := "actionlint", lost := "actionlint is not on PATH" },
                  { tool := "shellcheck",
                    lost := "actionlint is present but shellcheck is not, and without it actionlint checks the YAML only" }]
     invocation := .tool "actionlint"
       ["-color", ".github/workflows/ci.yml", ".github/workflows/release.yml"]
     summary := "A workflow cannot validate itself; actionlint parses both and shells out to ShellCheck." },
   { name := "the checked-in build stamp is the development stamp"
     profiles := Profile.all, onTag := .workingTreeOnly, requires := []
     invocation := .script "./scripts/check-release-policy.sh" ["--stamp-only"]
     summary := "The tracked stamp is the development one; a tag run stamps on purpose." },
   -- The deferred channels. Each invokes a runtime ADR-0026's dependency budget
   -- forbids on the release path, which is the whole reason they are the
   -- profiles' one difference.
   { name := "npm package selftest"
     profiles := [.ci], onTag := .always, requires := [npmTool]
     invocation := .script "./scripts/npm-pack.sh" ["--selftest"]
     summary := "Staging, then a real npm pack, install and launcher run over the result." },
   { name := "npm publisher selftest"
     profiles := [.ci], onTag := .always, requires := [npmTool]
     invocation := .script "./scripts/npm-publish.sh" ["--selftest"]
     summary := "The publisher's refusals, which are the ones an immutable registry makes final." },
   { name := "npm bootstrap selftest"
     profiles := [.ci], onTag := .always, requires := [npmTool]
     invocation := .script "./scripts/npm-bootstrap.sh" ["--selftest"]
     summary := "The one manual step before the first release, and the only one that publishes by hand." },
   { name := "the rendered formulae parse"
     profiles := [.ci], onTag := .always
     requires := [{ tool := "ruby", lost := "ruby is not on PATH" }]
     invocation := .script "./scripts/check-channel-policy.sh" ["--ruby-only"]
     summary := "An early signal on the rendered formulae; real Homebrew is the acceptance authority." }]

/-- The gates of one profile, in registry order. -/
def gatesIn (profile : Profile) (tagRun : Bool) : List Gate :=
  gates.filter fun gate =>
    gate.profiles.contains profile
      && (!tagRun || gate.onTag == .always)

/-- Their names, which is what a listing and the parity oracle compare. -/
def gateNames (profile : Profile) (tagRun : Bool) : List String :=
  (gatesIn profile tagRun).map (·.name)

/-! ## What a distribution surface contributes

ADR-0028's four surfaces do not have one uniform shape, and forcing them into
one is what put a Homebrew publish job behind a plan row that promised only that
the installer exists. Each surface has a closed, typed effect set; an enabled
surface contributes exactly its own, and a deferred one contributes none of its
release-path effects. -/

/-- What being enabled makes a surface do. -/
inductive SurfaceEffect where
  /-- Contributes rows to the external-prerequisite audit. -/
  | prerequisiteRows
  /-- Contributes a job to the release workflow. -/
  | workflowJob
  /-- Contributes a command that publishes to somewhere outside this
      repository. -/
  | publicationCommand
  /-- Is offered by this repository and said to be. -/
  | presence
  /-- Is documented for a user to follow. -/
  | documentation
  /-- Carries a bootstrap suite that has to pass before it can be enabled. -/
  | bootstrapSuite
  deriving DecidableEq, Repr

def SurfaceEffect.wire : SurfaceEffect → String
  | .prerequisiteRows => "prerequisite-rows"
  | .workflowJob => "workflow-job"
  | .publicationCommand => "publication-command"
  | .presence => "presence"
  | .documentation => "documentation"
  | .bootstrapSuite => "bootstrap-suite"

/-- What each surface is.

    The installer's row is the one worth reading twice: `install.sh` is served
    from this repository over the GitHub Release, so enabling it adds no job and
    no publication — it says the path is offered, documented, and covered by a
    suite. Giving it the publication effects "for uniformity" would create a
    job with nowhere to publish to. -/
def effectsOf : Channel → List SurfaceEffect
  | .githubRelease => [.prerequisiteRows, .workflowJob, .publicationCommand]
  | .npm => [.prerequisiteRows, .workflowJob, .publicationCommand, .bootstrapSuite]
  | .homebrew => [.prerequisiteRows, .workflowJob, .publicationCommand, .bootstrapSuite]
  | .installer => [.presence, .documentation, .bootstrapSuite]

/-- The three surfaces that publish somewhere outside this repository. -/
def publicationChannels : List Channel := [.githubRelease, .npm, .homebrew]

/-- What a surface contributes to *this* release. -/
def contributedEffects (plan : ReleasePlan) (channel : Channel) : List SurfaceEffect :=
  if plan.enabled channel then effectsOf channel else []

/-- **A surface publishes exactly when it is one of the three publication
    channels.**

    Stated over the effect table rather than checked per call site, because the
    failure it rules out is additive: giving the installer a publication effect
    would put a job behind a plan row that promised only that the path exists,
    and nothing else in the system would notice. -/
theorem publicationCommand_iff (channel : Channel) :
    (effectsOf channel).contains .publicationCommand = true ↔
      publicationChannels.contains channel = true := by
  cases channel <;> rfl

/-- **A deferred surface contributes nothing, and an enabled one contributes its
    own effects.**

    Both halves, because the two failures are opposite and each is silent. A
    deferred surface that still contributed would demand prerequisites for a
    channel nobody is publishing — "missing" is a defect report, and a channel
    nobody publishes has no defect. An enabled one that contributed nothing
    would run no job for a channel the plan says is on. -/
theorem contributedEffects_eq (plan : ReleasePlan) (channel : Channel) :
    contributedEffects plan channel = if plan.enabled channel then effectsOf channel else [] :=
  rfl

/-- **No surface has an empty effect set.**

    This is what makes the theorem above say something: if some surface
    contributed nothing when enabled, "contributes nothing" would not
    distinguish deferred from enabled for it. -/
theorem effectsOf_ne_nil (channel : Channel) : effectsOf channel ≠ [] := by
  cases channel <;> exact List.cons_ne_nil _ _

/-! ## Whether a gate may run

The three-way decision the shell wrote out by hand in four places: is the tool
on PATH, is this run strict, and did the command succeed. Every combination
decides whether a release proceeds past a gate that did not run, and the two
that differ most in consequence differ least in text — a missing tool without
`--strict` is "the policy was smaller today", and the same tool under `--strict`
is "this job is broken". -/

/-- What a gate did, or did not do. -/
inductive GateOutcome where
  | passed
  /-- It ran and refused; `why` is what it said. -/
  | failed (why : String)
  /-- It did not run, because a tool it needs is not there. -/
  | skipped (requirement : ToolRequirement)
  deriving Repr

/-- The first requirement that is not met, in declaration order.

    In order, and the first one decides, which is what lets a two-tool gate
    report each absence in its own terms. `actionlint` absent means the gate did
    not run; `shellcheck` absent means it would run over less than it claims,
    and only the first of those reads as anything but a pass. -/
def firstMissing (present : String → Bool) (gate : Gate) : Option ToolRequirement :=
  gate.requires.find? fun requirement => !present requirement.tool

/-- Whether a gate runs at all. -/
def gateRuns (present : String → Bool) (gate : Gate) : Bool :=
  (firstMissing present gate).isNone

/-- **A gate runs exactly when every tool it declares is present.**

    The direction that matters is left to right: a gate that ran is one whose
    tools were all there, so a requirement dropped from the list makes the
    verdict strictly more permissive and this implication stops compiling. Right
    to left is what a check that refused to run anything would fail — and that
    is not idle, since the ordinary case is a machine with every tool installed
    and a verdict nobody would notice was always `false` until CI went quiet. -/
theorem gateRuns_iff (present : String → Bool) (gate : Gate) :
    gateRuns present gate = true ↔
      ∀ requirement ∈ gate.requires, present requirement.tool = true := by
  rw [gateRuns, firstMissing, Option.isNone_iff_eq_none, List.find?_eq_none]
  constructor
  · intro noneMissing requirement member
    match found : present requirement.tool with
    | true => rfl
    | false =>
        exact absurd (by rw [found]; rfl) (noneMissing requirement member)
  · intro every requirement member
    rw [every requirement member]
    exact fun absurdity => Bool.noConfusion absurdity

/-! ## Whether the run passed -/

/-- One gate's outcome, as a condition with what to say when it does not hold. -/
def outcomeCheck (strict : Bool) (gate : Gate) : GateOutcome → Check
  | .passed => { held := true, failure := "" }
  | .failed why =>
      { held := false, failure := s!"{gate.name}: {why}" }
  | .skipped requirement =>
      { held := !strict,
        failure := s!"{gate.name} could not run and this is a --strict run: {requirement.lost}. Locally a missing tool is a smaller policy and the run says so; here it is a broken job, not a smaller release." }

def runChecks (strict : Bool) (rows : List (Gate × GateOutcome)) : List Check :=
  rows.map fun (gate, outcome) => outcomeCheck strict gate outcome

/-- Whether the run may be reported as a pass. -/
def runAccepts (strict : Bool) (rows : List (Gate × GateOutcome)) : Bool :=
  Check.allHeld (runChecks strict rows)

/-- What a gate's outcome has to be for the run to pass. -/
def GateOutcome.acceptable (strict : Bool) : GateOutcome → Prop
  | .passed => True
  | .failed _ => False
  | .skipped _ => strict = false

private theorem outcomeCheck_held_iff (strict : Bool) (gate : Gate) (outcome : GateOutcome) :
    (outcomeCheck strict gate outcome).held = true ↔ outcome.acceptable strict := by
  match outcome with
  | .passed => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | .failed _ =>
      constructor
      · intro impossible; exact Bool.noConfusion impossible
      · intro impossible; exact absurd impossible not_false
  | .skipped _ =>
      match strict with
      | true =>
          constructor
          · intro impossible; exact Bool.noConfusion impossible
          · intro impossible; exact Bool.noConfusion impossible
      | false => exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- **A run passes exactly when no gate failed and, under `--strict`, none was
    skipped.**

    Left to right is what stops a skipped gate from being counted as a passing
    one — the failure this whole decision exists to prevent, because a policy
    run that reports "all gates passed" having run eight of thirteen is a green
    check nobody can act on. Right to left is what a verdict that refused every
    run would fail, and it is the direction that keeps a legitimately smaller
    local run reportable. -/
theorem runAccepts_iff (strict : Bool) (rows : List (Gate × GateOutcome)) :
    runAccepts strict rows = true ↔
      ∀ row ∈ rows, row.2.acceptable strict := by
  rw [runAccepts, Check.allHeld, runChecks, List.all_eq_true]
  constructor
  · intro held row member
    exact (outcomeCheck_held_iff strict row.1 row.2).mp
      (held _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  · intro every check member
    have ⟨row, isMember, isCheck⟩ := List.mem_map.mp member
    rw [← isCheck]
    exact (outcomeCheck_held_iff strict row.1 row.2).mpr (every row isMember)

/-- Why it did not, or nothing at all. -/
def runFailures (strict : Bool) (rows : List (Gate × GateOutcome)) : List String :=
  Check.failures (runChecks strict rows)

/-- **The report is empty exactly when the run passed.** -/
theorem runFailures_isEmpty_iff (strict : Bool) (rows : List (Gate × GateOutcome)) :
    runFailures strict rows = [] ↔ ∀ row ∈ rows, row.2.acceptable strict :=
  Iff.trans (Check.allHeld_iff_noFailures (runChecks strict rows)).symm
    (runAccepts_iff strict rows)

/-! ## Running them

The world this needs is two questions — is a tool on `PATH`, and did a command
succeed — so it is a value with two fields rather than a set of calls buried in
a loop. Every crossing the shell wrote out by hand four times is then reachable
from a test without installing or uninstalling anything, which is what makes
"tool absent, not strict, would have failed" a row rather than a thought
experiment. -/

/-- What running the policy needs from the world. -/
structure Runner where
  /-- Whether a command could be executed by that name. -/
  present : String → IO Bool
  /-- Run one gate's invocation; a refusal carries what to report. -/
  invoke : Invocation → IO (Except String Unit)

/-- Whether `PATH` offers a command by that name.

    A name containing `/` is a path and is checked as one — `sh install.sh` is
    invoked as `sh`, but a gate could name `./scripts/x` and searching `PATH`
    for that would always answer no. Existence rather than executability,
    because Lean's metadata does not carry a mode: a file that is there and not
    executable makes the gate *run* and fail with the process layer's own
    "could not be run", which is a refusal rather than a skip — the safe
    direction. -/
def onPath (command : String) : IO Bool := do
  if command.contains '/' then
    return ← System.FilePath.pathExists command
  let some pathValue ← IO.getEnv "PATH" | return false
  for directory in pathValue.splitOn ":" do
    if directory.isEmpty then continue
    if ← System.FilePath.pathExists (directory ++ "/" ++ command) then
      return true
  return false

/-- Run a gate's invocation, reporting what it said when it refused.

    The output arrives after the gate finishes rather than as it is produced,
    because the process layer captures both streams so that a tool's diagnosis
    can become a refusal message rather than being lost. That is the right trade
    for a refusal and the wrong one for a five-minute gate's progress, and it is
    the one thing about this runner a reader of a CI log would notice at
    cutover. -/
def spawnInvocation (invocation : Invocation) : IO (Except String Unit) := do
  match ← succeeded invocation.command invocation.arguments.toArray with
  | .error message => return .error message
  | .ok output =>
      if !output.stdout.isEmpty then IO.print output.stdout
      if !output.stderr.isEmpty then IO.eprint output.stderr
      return .ok ()

def defaultRunner : Runner := { present := onPath, invoke := spawnInvocation }

/-- Ask about each distinct tool once.

    Once, and that is the point rather than an optimisation: two gates declaring
    `shellcheck` must not be able to disagree about whether it is there, and a
    run that answered the question twice could — a `PATH` that changed under it,
    or a lookup that is not a function. One answer per tool per run. -/
def resolveTools (runner : Runner) (selected : List Gate) : IO (String → Bool) := do
  let tools := ((selected.flatMap (·.requires)).map (·.tool)).eraseDups
  let mut answers : Array (String × Bool) := #[]
  for tool in tools do
    answers := answers.push (tool, ← runner.present tool)
  return fun tool => (answers.toList.lookup tool).getD false

/-- Run one profile's gates, in order, reporting each as it goes.

    Deliberately not stopping at the first failure. The gates are independent,
    and a run that stopped would make an operator fix and re-run once per
    problem; the exit status at the end is what decides. -/
def runGates (runner : Runner) (profile : Profile) (tagRun : Bool) :
    IO (List (Gate × GateOutcome)) := do
  let selected := gatesIn profile tagRun
  let present ← resolveTools runner selected
  let mut rows : Array (Gate × GateOutcome) := #[]
  for gate in selected do
    IO.println s!"── {gate.name}"
    match firstMissing present gate with
    | some requirement =>
        IO.println s!"   skipped: {requirement.lost}"
        rows := rows.push (gate, .skipped requirement)
    | none =>
        match ← runner.invoke gate.invocation with
        | .ok _ => rows := rows.push (gate, .passed)
        | .error message => rows := rows.push (gate, .failed message)
  return rows.toList

/-- How many gates did what, for the line an operator reads first. -/
def tally (rows : List (Gate × GateOutcome)) : Nat × Nat × Nat :=
  rows.foldl (init := (0, 0, 0)) fun (passed, failed, skipped) (_, outcome) =>
    match outcome with
    | .passed => (passed + 1, failed, skipped)
    | .failed _ => (passed, failed + 1, skipped)
    | .skipped _ => (passed, failed, skipped + 1)

/-! ## The parity oracle

Temporary, and deleted with the shell policy. Until then the shell is
authoritative and this says the typed registry agrees with it: same gates, same
order, same profile. The comparison is over the names the shell scripts report,
because that is the thing both a reader and a report use to say which gate is
which.

Two listings compose into one profile because the shell nests: the `ci` profile
runs the deferred channels as a *single* outer gate whose command is the other
script. That wrapper is the shell's own grouping and has no typed counterpart —
naming it here, once, is what lets the comparison be exact rather than
approximate. -/

/-- The outer script's name for the gate that runs the channel script. -/
def shellChannelGroupGate : String := "deferred-channel gates"

/-- What the shell reports for a profile, flattened the way the registry is: the
    grouping gate replaced by the gates it groups.

    A listing that does not contain the wrapper is left alone, which is what the
    release profile's listing looks like — it does not have the group at all. -/
def flattenShellNames (outer : List String) (channel : List String) : List String :=
  outer.flatMap fun name => if name == shellChannelGroupGate then channel else [name]

/-- The two ways the caller can pair the listings wrongly.

    Checked before the comparison, and separately from it, because both make the
    comparison *pass* rather than fail. A `ci` listing given with no channel
    listing has its wrapper flattened to nothing, which leaves exactly the nine
    gates of the release profile — so comparing the ci listing against the
    release registry succeeded, having silently dropped four gates. A channel
    listing given for a profile with no wrapper is the same mistake in the other
    direction: four gate names that never reach the comparison. -/
def groupingProblems (outer : List String) (channelGiven : Bool) : List String :=
  let grouped := outer.contains shellChannelGroupGate
  (if grouped && !channelGiven then
     [s!"the listing names '{shellChannelGroupGate}', which is the shell's grouping for the gates in another script, and no --channel listing was given. Flattening it to nothing would drop those gates from the comparison and the comparison would pass."]
   else [])
  ++ (if !grouped && channelGiven then
        [s!"a --channel listing was given and the profile's listing does not name '{shellChannelGroupGate}', so nothing would expand into it. Either the wrong profile was listed, or the channel gates are no longer grouped and this oracle is comparing a listing it does not understand."]
      else [])

/-- Every way the two lists disagree, in the order a reader would find them.

    Reported as the whole comparison rather than the first difference: the two
    lists are short, and an oracle that reported one disagreement per run would
    be run once per gate during a migration that moves several at a time. -/
def parityProblems (profile : Profile) (typed observed : List String) : List String :=
  let missing := observed.filter fun name => !typed.contains name
  let extra := typed.filter fun name => !observed.contains name
  (missing.map fun name =>
    s!"the {profile.wire} profile runs '{name}' and the typed registry does not have it. A gate the shell runs and the registry does not know about is one the cutover would drop.")
  ++ (extra.map fun name =>
    s!"the typed registry puts '{name}' in the {profile.wire} profile and the shell does not run it there. Either the registry invented a gate or it moved one between profiles, and a gate that moved into 'release' is one the dependency boundary has not been checked against.")
  ++ (if missing.isEmpty && extra.isEmpty && typed != observed then
        [s!"the {profile.wire} profile runs the same gates in a different order: the shell runs {String.intercalate ", " observed} and the registry lists {String.intercalate ", " typed}. A policy run is read top to bottom, so the order is part of what it says."]
      else [])
  ++ (if observed.isEmpty then
        [s!"the shell reported no gates at all for the {profile.wire} profile, so this comparison would hold by having nothing to compare. That is the one result an oracle must never accept."]
      else [])

end Policy

/-! ## The commands -/

open Policy in
private def listOptions : List OptionSpec :=
  [{ name := "profile", takesValue := true }, { name := "tag", takesValue := false }]

open Policy in
private def listDecision (arguments : Profile × Bool) : Decision String := do
  let (profile, tagRun) := arguments
  for name in gateNames profile tagRun do
    IO.println name
  return s!"{(gateNames profile tagRun).length} gate(s) in the {profile.wire} profile{if tagRun then " on a tag run" else ""}"

open Policy in
private def listArguments (options : Options) : Except String (Profile × Bool) := do
  return (← Profile.parse "--profile" (← options.required "profile"), options.given "tag")

open Policy in
private def listCommand : Command :=
  optionCommand "policy-list" "--profile <ci|release> [--tag]"
    "Name the gates a profile runs, one per line, in the order it runs them."
    ["--profile", "ci"] listOptions listArguments listDecision

open Policy in
private def parityOptions : List OptionSpec :=
  [{ name := "profile", takesValue := true },
   { name := "observed", takesValue := true },
   { name := "channel", takesValue := true },
   { name := "tag", takesValue := false }]

open Policy in
private structure ParityArgs where
  profile : Profile
  observedPath : String
  channelPath : Option String
  tagRun : Bool

open Policy in
private def parityArgs (options : Options) : Except String ParityArgs := do
  return {
    profile := ← Profile.parse "--profile" (← options.required "profile")
    observedPath := ← options.required "observed"
    channelPath := options.value? "channel"
    tagRun := options.given "tag" }

/-- One name per line, blank lines dropped and surrounding space trimmed.

    Trimmed because the shell prints these through `echo` and a trailing space
    is invisible in a diff; blank lines dropped because a file written by a
    redirect ends with one. -/
private def listedNames (text : String) : List String :=
  ((text.splitOn "\n").map (·.trimAscii.toString)).filter (!·.isEmpty)

open Policy in
private def parityDecision (args : ParityArgs) : Decision String := do
  let observedText ← ofIO (readTextFile args.observedPath)
  let channelNames ← match args.channelPath with
    | none => pure []
    | some path => do
        let text ← ofIO (readTextFile path)
        pure (listedNames text)
  let outer := listedNames observedText
  let observed := flattenShellNames outer channelNames
  let typed := gateNames args.profile args.tagRun
  match groupingProblems outer args.channelPath.isSome ++ parityProblems args.profile typed observed with
  | [] =>
      return s!"the typed registry and the shell policy run the same {typed.length} gate(s) in the same order for the {args.profile.wire} profile"
  | problems =>
      decline ("the typed release policy registry and the shell policy disagree.\n"
        ++ String.join (problems.map fun problem => s!"  {problem}\n")
        ++ "While both exist the shell is authoritative, so this is the registry to correct — and the correction lands before either workflow reads the registry instead.")

open Policy in
private def parityCommand : Command :=
  optionCommand "policy-parity"
    "--profile <ci|release> --observed <names-file> [--channel <names-file>] [--tag]"
    "Refuse unless the typed gate registry names exactly what the shell policy runs, in order."
    ["--profile", "ci", "--observed", "ci-gates.txt", "--channel", "channel-gates.txt"]
    parityOptions parityArgs parityDecision

open Policy in
private def runOptions : List OptionSpec :=
  [{ name := "profile", takesValue := true },
   { name := "strict", takesValue := false },
   { name := "tag", takesValue := false }]

open Policy in
private structure RunArgs where
  profile : Profile
  strict : Bool
  tagRun : Bool

open Policy in
private def runArgs (options : Options) : Except String RunArgs := do
  return {
    profile := ← Profile.parse "--profile" (← options.required "profile")
    strict := options.given "strict"
    tagRun := options.given "tag" }

open Policy in
private def runDecision (args : RunArgs) : Decision String := do
  let rows ← attempt "running the release policy" (runGates defaultRunner args.profile args.tagRun)
  let (passed, failed, skipped) := tally rows
  match runFailures args.strict rows with
  | [] =>
      return s!"{passed} gate(s) passed in the {args.profile.wire} profile"
        ++ (if skipped == 0 then "" else s!", {skipped} skipped for a tool this machine does not have")
  | problems =>
      decline (s!"the {args.profile.wire} profile did not pass: {failed} failed, {skipped} skipped, {passed} passed.\n"
        ++ String.join (problems.map fun problem => s!"  {problem}\n")
        ++ "Every gate ran; the ones above are the ones to fix.")

open Policy in
private def runCommand : Command :=
  optionCommand "policy" "--profile <ci|release> [--strict] [--tag]"
    "Run one profile's gates, in order, and refuse unless every one of them passed."
    ["--profile", "release", "--strict"] runOptions runArgs runDecision

def policyCommands : List Command := [listCommand, parityCommand, runCommand]

end Release
