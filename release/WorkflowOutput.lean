/- GitHub's output-file protocol, with explicit destinations and framed values. -/
import release.Command

namespace Release.WorkflowOutput

def delimiter : String := "TL_RELEASE_OUTPUT_END"

def keyChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-'

/-- Values may contain newlines, but cannot terminate their own frame. -/
def rowAllowed (key value : String) : Bool :=
  !key.isEmpty && key.toList.all keyChar &&
    !value.contains '\r' && !(value.splitOn "\n").contains delimiter

theorem negation_iff (b : Bool) : (!b) = true ↔ b = false :=
  match b with
  | false => ⟨fun _ => rfl, fun _ => rfl⟩
  | true => ⟨fun impossible => Bool.noConfusion impossible, fun impossible => Bool.noConfusion impossible⟩

theorem rowAllowed_iff (key value : String) :
    rowAllowed key value = true ↔
      key.isEmpty = false ∧ (∀ c ∈ key.toList, keyChar c = true) ∧
      value.contains '\r' = false ∧ (value.splitOn "\n").contains delimiter = false := by
  simp only [rowAllowed, Bool.and_eq_true, negation_iff, List.all_eq_true, and_assoc]

def render (rows : List (String × String)) : Except String String := do
  let keys := rows.map Prod.fst
  if keys.isEmpty || keys.eraseDups.length != keys.length then
    throw "workflow outputs must have at least one row and unique keys; fix the named producer"
  for (key, value) in rows do
    if !rowAllowed key value then
      throw s!"workflow output '{key}' cannot be framed safely; remove control characters or the reserved delimiter"
  return String.join (rows.map fun (key, value) =>
    s!"{key}<<{delimiter}\n{value}\n{delimiter}\n")

/-- The runner owns this file; append one complete, validated batch. -/
def write (destination : String) (rows : List (String × String)) : IO (Except String Unit) := do
  match render rows with
  | .error message => return .error message
  | .ok text =>
    try
      IO.FS.withFile destination .append fun handle => handle.putStr text
      return .ok ()
    catch error =>
      return .error s!"could not append workflow outputs to '{destination}': {error}; pass the runner's GITHUB_OUTPUT path and check its permissions"

end Release.WorkflowOutput
