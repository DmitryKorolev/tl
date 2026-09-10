/- Closed workflow authority and invocation schemas. Raw payload builders are
   outside the privileged argv grammar; every output and authority consumer is
   registered, so adding an intermediate output cannot hide a policy decision. -/
import release.Command
import release.Workflow
import release.Check
import release.WorkflowOutput

namespace Release.WorkflowPolicy
open Workflow

inductive Argument where
  | literal (value : String)
  | environment (name : String)
  deriving DecidableEq, Repr

structure Invocation where
  executable : String
  arguments : List Argument
  deriving DecidableEq, Repr

def wordChar (c : Char) : Bool :=
  c.isAlphanum || "_./:@=+-".contains c

def argument? (word : String) : Option Argument := do
  if word.startsWith "\"$" && word.endsWith "\"" then
    let name := (word.drop 2).toString.dropEnd 1 |>.toString
    if name.isEmpty || !name.all (fun c => c.isAlphanum || c == '_') then none
    else some (.environment name)
  else if word.isEmpty || !word.all wordChar then none
  else some (.literal word)

/-- One line, one executable, literal arguments or whole quoted env variables.
    No shell evaluation syntax is part of this language. -/
def invocation? (lines : List String) : Option Invocation := do
  let [line] := lines.map (·.trimAscii.toString) | none
  let executable :: words := line.splitOn " " | none
  if executable.isEmpty || !executable.all wordChar then none
  let arguments ← words.mapM argument?
  return { executable, arguments }

theorem invocation_eq_iff (lines : List String) (expected : Invocation) :
    (invocation? lines == some expected) = true ↔ invocation? lines = some expected := by
  simp only [beq_iff_eq]

/-- Simple YAML quotes on keys have one interpretation. Escapes, tags, anchors,
    aliases and complex keys remain unsupported and therefore refuse. -/
def unquote (text : String) : String :=
  if (text.startsWith "\"" && text.endsWith "\"") || (text.startsWith "'" && text.endsWith "'") then
    (text.drop 1).toString.dropEnd 1 |>.toString
  else text

def normalizeKeys (text : String) : String :=
  String.intercalate "\n" ((text.splitOn "\n").map fun line =>
    let indent := String.ofList (List.replicate (indentation line) ' ')
    let body := line.trimAsciiStart.toString
    let (marker, body) := if body.startsWith "- " then ("- ", (body.drop 2).toString) else ("", body)
    let key := (body.splitOn ":").headD ""
    let plain := unquote key
    if plain != key && !plain.isEmpty && plain.all (fun c => c.isAlphanum || c == '-' || c == '_') then
      indent ++ marker ++ plain ++ (body.drop key.length).toString
    else line)

def significant (lines : List String) : List String :=
  lines.filter fun line => !line.trimAscii.isEmpty && !line.trimAscii.toString.startsWith "#"

def scalar (text : String) : String :=
  unquote ((text.splitOn " #").headD "" |>.trimAscii.toString)

def fieldValue (field : Field) : String :=
  if field.singleLine then scalar field.value
  else if [">", ">-", ">+"].contains field.value then
    String.intercalate " " ((significant field.children).map (·.trimAscii.toString))
  else scalar field.value ++ "\n" ++ String.intercalate "\n"
    ((significant field.children).map (·.trimAsciiEnd.toString))

def fields? (scan : FieldScan) (excluded : List String := []) : Option (List (String × String)) := do
  if !scan.readable then none
  if (scan.fields.map (·.key)).eraseDups.length != scan.fields.length then none
  return ((scan.fields.filter (fun field => !excluded.contains field.key)).map
    (fun field => (field.key, fieldValue field))).mergeSort (fun a b => a.1 ≤ b.1)

inductive Run where
  | none
  | command (invocation : Invocation)
  /-- The one pre-execution hash producer cannot invoke the tool it binds. -/
  | fileSetHash
  deriving DecidableEq, Repr

structure StepContract where
  name : String
  fields : List (String × String)
  run : Run
  deriving DecidableEq, Repr

def stepRun? (step : Step) : Option Run :=
  if (step.field? "run").isNone then some .none
  else if step.hasField "id" "tool_file_set_hash" &&
      step.runLines.map (·.trimAscii.toString) == ["printf '%s\\n' \"fileSetHash=$RELEASE_TOOL_FILE_SET_HASH\" >> \"$GITHUB_OUTPUT\""] then
    some .fileSetHash
  else (invocation? step.runLines).map Run.command

def stepContract? (step : Step) : Option StepContract := do
  let fields ← fields? ⟨step.fields, step.readable⟩ ["name", "run"]
  return { name := step.name, fields, run := ← stepRun? step }

def stepAccepts (step : Step) (contract : StepContract) : Bool :=
  stepContract? step == some contract

theorem stepAccepts_iff (step : Step) (contract : StepContract) :
    stepAccepts step contract = true ↔ stepContract? step = some contract := by
  simp only [stepAccepts, beq_iff_eq]

structure JobContract where
  name : String
  fields : List (String × String)
  /-- Privileged jobs and handoff consumers have no unregistered steps. -/
  closedSteps : Bool
  steps : List StepContract
  /-- Every local or cross-job output edge, including producer dependencies. -/
  references : List String
  deriving Repr

structure Contract where
  header : List (String × String)
  jobs : List JobContract

def references (text : String) : List String :=
  let words := text.splitOn "\n" |>.flatMap fun line =>
    (String.ofList (line.toList.map fun c => if c.isAlphanum || c == '_' || c == '-' || c == '.' then c else ' ')).splitOn " "
  (words.filter fun word => word.startsWith "needs." || word.startsWith "steps.").eraseDups.mergeSort (· ≤ ·)

def suspiciousReference (text : String) : Bool :=
  let compact := String.ofList (text.toList.filter (!·.isWhitespace))
  let lowered := compact.toLower
  let expressions := (text.splitOn "${{").drop 1 |>.map fun tail => (tail.splitOn "}}").headD ""
  let contextWords := expressions.flatMap fun expression =>
    (String.ofList (expression.toLower.toList.map fun c =>
      if c.isAlphanum || c == '_' || c == '-' || c == '.' then c else ' ')).splitOn " "
  -- A closing delimiter inside a quoted expression literal is outside this
  -- bounded grammar. Refuse it rather than truncating away a later read.
  expressions.any (fun expression => expression.toList.count '\'' % 2 == 1) ||
  contextWords.any (fun word => word == "needs" || word == "steps" ||
    word.endsWith "." && (word.startsWith "needs." || word.startsWith "steps.")) ||
    (lowered.splitOn "needs[").length > 1 || (lowered.splitOn "steps[").length > 1 ||
    (lowered.splitOn ".outputs[").length > 1 ||
    ["needs.", "steps.", ".outputs."].any (fun token =>
      (compact.splitOn token).length != (lowered.splitOn token).length)

def rawStepAllowed (step : Step) : Bool :=
  -- A line beginning with # inside a literal env value is data, not a YAML
  -- comment. Scan all raw bytes here rather than dropping such secret inputs.
  let text := String.intercalate "\n" step.lines
  let compact := String.ofList (text.toLower.toList.filter (!·.isWhitespace))
  let words := (String.ofList (text.toLower.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else ' ')).splitOn " "
  let conditionSuspicious := (step.fields.filter (·.key == "if")).any fun field =>
    suspiciousReference ("${{" ++ fieldValue field ++ "}}")
  -- YAML decodes escapes before GitHub sees an expression. Raw run blocks
  -- have literal bytes; other scalar forms and nested metadata must not hide
  -- context names or expression delimiters behind escapes or line joining.
  let escapedMetadata := step.fields.any fun field =>
    if field.key == "run" && (field.value.startsWith "|" || field.value.startsWith ">") then false
    else (field.value ++ String.intercalate "\n" field.children).contains '\\'
  !escapedMetadata && !conditionSuspicious && !words.contains "secrets" &&
  !["github_output", "github_env", "github_path", "github_state", "continue-on-error"].any
    (fun token => (compact.splitOn token).length > 1)

/-- Pin every output, rather than exempting outputs that currently look
    unprivileged. This covers arbitrarily long transitive producer chains:
    every intermediate mapping and every dependency of its named step must be
    registered too. Unknown jobs cannot introduce an unexamined chain. -/
def jobChecks (job : JobBlock) (expected : JobContract) : List Check :=
  let actualFields := fields? (fieldsOf job.lines 1 4) ["steps"]
  let steps := job.steps
  let stepValues := ((fieldsOf job.lines 1 4).fields.filter (·.key == "steps")).map (·.value)
  let required := expected.steps.all fun contract =>
    (steps.filter fun step => stepAccepts step contract).length == 1
  let raw := String.intercalate "\n" job.lines
  let outside := steps.filter fun step => !(expected.steps.any (stepAccepts step))
  [{ held := actualFields == some expected.fields,
     failure := s!"{job.name}: restore the registered permissions, runner, environment, outputs, needs and predicate" },
   { held := stepValues == [""] && !steps.isEmpty && steps.all (·.readable),
     failure := s!"{job.name}: use one nonempty block steps sequence with readable direct fields; flow steps and aliases can conceal authority" },
   { held := required && (!expected.closedSteps || steps.length == expected.steps.length),
     failure := s!"{job.name}: restore the named producers and exact command/action schemas; privileged steps cannot carry shell programs or undeclared inputs" },
   { held := !expected.closedSteps || (steps.map stepContract?) == expected.steps.map some,
     failure := s!"{job.name}: restore the registered step order; authentication and handoff must precede effects" },
   { held := references raw == expected.references &&
       !suspiciousReference raw,
     failure := s!"{job.name}: restore the registered output edges in lowercase dot form, including every intermediate producer dependency" },
   { held := outside.all rawStepAllowed,
     failure := s!"{job.name}: register every output producer and secret consumer; raw builders may not acquire authority or mask policy failures" }]

def checks (text : String) (contract : Contract) : List Check :=
  let normalized := normalizeKeys text
  let lines := normalized.splitOn "\n"
  let scan := jobScan normalized
  let header := fields? (fieldsOf lines 1 0) ["jobs"]
  [{ held := header == some contract.header,
     failure := "restore the workflow's registered triggers, permission defaults and execution environment" },
   { held := scan.unreadable.isEmpty && (scan.jobs.map (·.name)) == contract.jobs.map (·.name),
     failure := "restore the registered jobs in readable block form; an unknown job may inherit publication authority" }]
  ++ contract.jobs.flatMap fun expected =>
    match scan.jobs.find? (·.name == expected.name) with
    | none => [{ held := false, failure := s!"restore the missing {expected.name} job" }]
    | some job => jobChecks job expected

def accepts (text : String) (contract : Contract) : Bool := Check.allHeld (checks text contract)

/-- The policy statement is independent of the check-list constructor: losing
    a check from that constructor must invalidate its characterization. -/
def JobValid (job : JobBlock) (expected : JobContract) : Prop :=
  fields? (fieldsOf job.lines 1 4) ["steps"] = some expected.fields ∧
  ((fieldsOf job.lines 1 4).fields.filter (·.key == "steps")).map (·.value) = [""] ∧
  job.steps.isEmpty = false ∧ (∀ step ∈ job.steps, step.readable = true) ∧
  (∀ contract ∈ expected.steps, (job.steps.filter fun step => stepAccepts step contract).length = 1) ∧
  (expected.closedSteps = false ∨ job.steps.length = expected.steps.length) ∧
  (expected.closedSteps = false ∨ job.steps.map stepContract? = expected.steps.map some) ∧
  references (String.intercalate "\n" job.lines) = expected.references ∧
  suspiciousReference (String.intercalate "\n" job.lines) = false ∧
  (∀ step ∈ job.steps.filter (fun step => !(expected.steps.any (stepAccepts step))), rawStepAllowed step = true)

theorem jobChecks_valid (job : JobBlock) (expected : JobContract) :
    Check.allHeld (jobChecks job expected) = true ↔ JobValid job expected := by
  simp only [Check.allHeld, jobChecks, JobValid, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, Bool.or_eq_true, WorkflowOutput.negation_iff,
    beq_iff_eq, List.all_eq_true, and_assoc]

def Valid (text : String) (contract : Contract) : Prop :=
  let normalized := normalizeKeys text
  let scan := jobScan normalized
  fields? (fieldsOf (normalized.splitOn "\n") 1 0) ["jobs"] = some contract.header ∧
  scan.unreadable.isEmpty = true ∧ scan.jobs.map (·.name) = contract.jobs.map (·.name) ∧
  ∀ expected ∈ contract.jobs,
    match scan.jobs.find? (·.name == expected.name) with
    | none => False
    | some job => JobValid job expected

theorem accepts_iff (text : String) (contract : Contract) :
    accepts text contract = true ↔ Valid text contract := by
  simp only [accepts, checks, Valid, Check.allHeld, List.all_append, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq, List.all_flatMap,
    List.all_eq_true, and_assoc]
  constructor
  · rintro ⟨header, readable, inventory, checked⟩
    refine ⟨header, readable, inventory, ?_⟩
    intro expected member
    have evidence := checked expected member
    cases found : (jobScan (normalizeKeys text)).jobs.find? (·.name == expected.name) with
    | none =>
        simp only [found, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at evidence
        exact Bool.noConfusion evidence
    | some job =>
        simp only [found] at evidence
        exact (jobChecks_valid job expected).mp (List.all_eq_true.mpr evidence)
  · rintro ⟨header, readable, inventory, checked⟩
    refine ⟨header, readable, inventory, ?_⟩
    intro expected member
    have evidence := checked expected member
    cases found : (jobScan (normalizeKeys text)).jobs.find? (·.name == expected.name) with
    | none =>
        simp only [found] at evidence
    | some job =>
        simp only [found] at evidence
        exact List.all_eq_true.mp ((jobChecks_valid job expected).mpr evidence)

end Release.WorkflowPolicy
