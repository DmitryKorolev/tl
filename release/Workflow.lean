/-
Structural reader for the repository's block-style workflows. This is a source
reader, not a general YAML implementation or a publication-policy verdict.
It preserves raw lines for exact contracts and separates direct step fields
from nested mappings and scalar bodies. Unsupported YAML spellings do not
supply executable fields; policy callers must require the fields they need.
-/
namespace Release.Workflow

/-- Leading ASCII spaces, the indentation used by the checked-in workflows. -/
def indentation (line : String) : Nat :=
  (line.toList.takeWhile (· == ' ')).length

/-- A direct mapping field, with its nested data kept separately. -/
structure Field where
  key : String
  value : String
  children : List String := []
  sourceLine : Nat
  deriving Repr

/-- One step; sourceLine is one-based within the supplied job lines. -/
structure Step where
  name : String := ""
  uses : Option String := none
  lines : List String
  fields : List Field := []
  sourceLine : Nat
  readable : Bool := true
  deriving Repr

/-- Preserve duplicates: a consumer must not silently choose one definition. -/
def Step.field? (step : Step) (key : String) : Option Field :=
  match if step.readable then step.fields.filter (·.key == key) else [] with
  | [field] => some field
  | _ => none

/-- Parse a plain key only. Quoted keys are unsupported, not substring matches. -/
def field? (text : String) (sourceLine : Nat) : Option Field := do
  let key := (text.splitOn ":").headD ""
  let rest := (text.drop (key.length + 1)).toString
  if key.isEmpty || !key.all (fun c => c.isAlphanum || c == '-' || c == '_') then none
  else if !text.startsWith (key ++ ":") then none
  else if !rest.isEmpty && !rest.startsWith " " then none
  else some { key, value := rest.trimAscii.toString,
              sourceLine }

/-- Direct fields and whether every direct key could be read. -/
structure FieldScan where
  fields : List Field
  readable : Bool

/-- Read a block mapping at one column, retaining each field's scalar or
    nested mapping verbatim. Only the first line may carry a sequence marker. -/
def fieldsOf (lines : List String) (sourceLine column : Nat)
    (sequenceHead : Bool := false) : FieldScan := Id.run do
  let mut fields : List Field := []
  let mut current : Option Field := none
  let mut readable := true
  for (line, offset) in lines.zipIdx do
    let body := line.trimAscii.toString
    if body.isEmpty || body.startsWith "#" then
      if let some field := current then
        current := some { field with children := line :: field.children }
      continue
    let head := sequenceHead && offset == 0
    let direct := head || indentation line == column
    let text := if head then (body.drop 2).toString else body
    if direct then
      if let some field := current then
        fields := { field with children := field.children.reverse } :: fields
      current := field? text (sourceLine + offset)
      if current.isNone then readable := false
    else if let some field := current then
      if indentation line > column then
        current := some { field with children := line :: field.children }
      else readable := false
    else readable := false
  if let some field := current then
    fields := { field with children := field.children.reverse } :: fields
  return { fields := fields.reverse, readable }

/-- Plain one-line scalars cannot acquire a continuation from deeper lines.
    Blank lines and comments alone do not change a plain scalar's value. -/
def Field.singleLine (field : Field) : Bool :=
  field.children.all fun line => line.trimAscii.isEmpty || line.trimAscii.toString.startsWith "#"

/-- YAML plain scalars end at a separated comment. Other scalar styles are
    unsupported here, so their metadata cannot be mistaken for their value. -/
def plainScalar? (value : String) : Option String :=
  if ["'", "\"", "&", "*", "!", "{", "[", "|", ">"].any (fun marker => value.startsWith marker) then none
  else if value.startsWith "#" then some ""
  else some ((value.splitOn " #").headD "" |>.splitOn "\t#" |>.headD "" |>.trimAscii.toString)

def Step.scalar? (step : Step) (key : String) : Option String := do
  let field ← step.field? key
  if field.singleLine then some field.value else none

/-- Direct step fields begin two columns after the sequence marker. -/
def stepOf (lines : List String) (sourceLine column : Nat) : Step :=
  let scan := fieldsOf lines sourceLine (column + 2) true
  let step : Step := { lines, fields := scan.fields, sourceLine, readable := scan.readable }
  { step with name := (step.scalar? "name").getD "", uses := step.scalar? "uses" }

/-- Raw source without whole-line comments, for exact source contracts. -/
def Step.code (step : Step) : List String :=
  step.lines.filter fun line => !(line.trimAscii.toString.startsWith "#")

/-- The run scalar only; nested env/with values never become commands.
    Folded scalars and quoted run values are deliberately not interpreted. -/
def Step.runLines (step : Step) : List String :=
  match step.field? "run" with
  | none => []
  | some field =>
    if ["|", "|-", "|+"].contains field.value then field.children
    else if field.singleLine then
      match plainScalar? field.value with
      | some value => if value.isEmpty then [] else [value]
      | none => []
    else []

def Step.runs (step : Step) (needle : String) : Bool :=
  step.runLines.any fun line => !(line.trimAscii.toString.startsWith "#")
    && (line.splitOn needle).length > 1

/-- A unique direct field with the expected plain value. -/
def Step.hasField (step : Step) (key value : String) : Bool :=
  step.scalar? key == some value

/-- A unique plain input under the step's with mapping. Unsupported mappings
    return none, so prohibitions can refuse uncertainty rather than omit it. -/
def Step.input? (step : Step) (key : String) : Option String :=
  match step.field? "with" with
  | none => none
  | some field =>
    if plainScalar? field.value != some "" then none
    else
      let first := field.children.find? fun line =>
        !line.trimAscii.isEmpty && !line.trimAscii.toString.startsWith "#"
      let column := first.map indentation |>.getD 0
      let scan := fieldsOf field.children (field.sourceLine + 1) column
      match if scan.readable then scan.fields.filter (·.key == key) else [] with
      | [input] => if input.singleLine then plainScalar? input.value else none
      | _ => none

def Step.hasInput (step : Step) (key value : String) : Bool :=
  step.input? key == some value

/-- Read only the job's direct steps mapping. The first sequence item fixes
    the column; nested sequences and block-scalar content cannot open steps. -/
def stepsOf (jobLines : List String) : List Step := Id.run do
  -- Escaped quoted keys are outside this reader's vocabulary; they must not
  -- conceal a second steps mapping while the first supplies evidence.
  if jobLines.any (fun line => indentation line == 4 &&
      ((line.splitOn ":").headD "").contains '\\') then return []
  let mappings := jobLines.filter fun line =>
    indentation line == 4 &&
      ["steps", "'steps'", "\"steps\""].contains ((line.splitOn ":").headD "" |>.trimAscii.toString)
  if mappings.length != 1 then return []
  let mut steps : List Step := []
  let mut current : List String := []
  let mut start := 0
  let mut inSteps := false
  let mut column : Option Nat := none
  for (line, offset) in jobLines.zipIdx do
    let body := line.trimAscii.toString
    if body.isEmpty || body.startsWith "#" then
      if !current.isEmpty then current := line :: current
      continue
    let indent := indentation line
    if !inSteps then
      if line == "    steps:" then inSteps := true
      continue
    if indent < 4 || (indent == 4 && !body.startsWith "- ") then break
    if column.isNone then
      if !body.startsWith "- " then return []
      column := some indent
    if column == some indent && body.startsWith "- " then
      if !current.isEmpty then steps := stepOf current.reverse start indent :: steps
      current := [line]
      start := offset + 1
    else if !current.isEmpty then current := line :: current
  if !current.isEmpty then steps := stepOf current.reverse start (column.getD 6) :: steps
  return steps.reverse

/-- A top-level job block: the job's name and the lines belonging to it. -/
structure JobBlock where
  name : String
  lines : List String
  sourceLine : Nat := 0
  steps : List Step := []

/-- A top-level job header — indented exactly two spaces, a bare name, then
    `:` and nothing but an optional comment. Tolerating the trailing comment
    matters: without it such a header is not recognised, the job folds into the
    preceding block, and it silently inherits that job's `if:` for the purposes
    of every check below. -/
def jobHeader? (line : String) : Option String :=
  if !(line.startsWith "  ") || line.startsWith "   " then none
  else
    let body := line.trimAsciiStart.toString
    if body.startsWith "#" then none
    else
      match body.splitOn ":" with
      | name :: first :: rest =>
          let rawTail := String.intercalate ":" (first :: rest)
          let tail := rawTail.trimAsciiStart.toString
          if (!rawTail.isEmpty && !rawTail.startsWith " ") then none
          else if (!name.isEmpty && name.all (fun c => c.isAlphanum || c == '-' || c == '_')) && (tail.isEmpty || tail.startsWith "#") then some name
          else none
      | _ => none

/-- A workflow's `jobs:` mapping, as this scan could read it. -/
structure JobScan where
  jobs : List JobBlock
  /-- Lines sitting exactly where a top-level job header does that this scan
      cannot read as one. Reported rather than folded into the preceding job:
      a header this parser skips silently attributes its job's permissions to
      the job above and gives it that job's `if:`, so a privileged job could
      join the file already covered by somebody else's guard. -/
  unreadable : List String

/-- Split a workflow file into its top-level job blocks: everything after the
    column-zero `jobs:` key, up to the next column-zero key. -/
def jobScan (content : String) : JobScan := Id.run do
  let mut start := 0
  let mut inJobs := false
  let mut blocks : List JobBlock := []
  let mut unreadable : List String := []
  let mut current : Option (String × List String) := none
  for (line, offset) in (content.splitOn "\n").zipIdx do
    if !inJobs then
      if line == "jobs:" then inJobs := true
      continue
    -- A column-zero key ends the `jobs:` mapping.
    if line != "" && !line.startsWith " " && !line.startsWith "#" then
      break
    match jobHeader? line with
    | some name =>
        if let some (n, ls) := current then
          blocks := { name := n, lines := ls.reverse, sourceLine := start, steps := stepsOf ls.reverse } :: blocks
        current := some (name, [])
        start := offset + 1
    | none =>
        -- Inside `jobs:`, a line indented exactly two spaces is a job header or
        -- it is nothing; a job's own keys sit at four. One this parser cannot
        -- read is therefore a header it must not pass over.
        if line.startsWith "  " && !line.startsWith "   "
            && !line.trimAscii.isEmpty && !line.trimAscii.toString.startsWith "#" then
          unreadable := line :: unreadable
        if let some (n, ls) := current then current := some (n, line :: ls)
  if let some (n, ls) := current then
    blocks := { name := n, lines := ls.reverse, sourceLine := start, steps := stepsOf ls.reverse } :: blocks
  return { jobs := blocks.reverse, unreadable := unreadable.reverse }

/-- Compatibility view for guards that pin raw job source. An unreadable job
    header makes this view empty, so required-job checks refuse the document. -/
def jobsOf (content : String) : List (String × List String) :=
  let scan := jobScan content
  if scan.unreadable.isEmpty then scan.jobs.map (fun job => (job.name, job.lines)) else []

end Release.Workflow
