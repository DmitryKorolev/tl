/-
`Tl.Tests.Harness` — a dependency-free assertion runner for the tested I/O shell
(ADR-0009: no Mathlib, no external test framework; a thin runner + seeded
`List`-based generators). The shell is *tested*, not proved (ADR-0004); this is
where its branches and error paths are exercised.
-/

namespace Tl.Tests

/-- One assertion's outcome. -/
structure Outcome where
  name : String
  passed : Bool
  msg : String := ""

/-- A boolean assertion. -/
def check (name : String) (cond : Bool) (msg : String := "expected true") : Outcome :=
  { name, passed := cond, msg := if cond then "" else msg }

/-- An equality assertion with a diff message. -/
def checkEq {α : Type _} [DecidableEq α] [Repr α] (name : String) (actual expected : α) : Outcome :=
  if actual = expected then { name, passed := true }
  else { name, passed := false, msg := s!"expected {repr expected}, got {repr actual}" }

/-- Assert an `Except` is `.ok` carrying the expected value. -/
def checkOk {ε α : Type _} [DecidableEq α] [Repr α] [Repr ε]
    (name : String) (actual : Except ε α) (expected : α) : Outcome :=
  match actual with
  | .ok a => checkEq name a expected
  | .error e => { name, passed := false, msg := s!"expected ok {repr expected}, got error {repr e}" }

/-- Assert an `Except` is `.error`. -/
def checkError {ε α : Type _} [Repr α] (name : String) (actual : Except ε α) : Outcome :=
  match actual with
  | .error _ => { name, passed := true }
  | .ok a => { name, passed := false, msg := s!"expected error, got ok {repr a}" }

/-- Run a labelled group of assertions; print results, return failure count. -/
def runGroup (label : String) (outcomes : List Outcome) : IO Nat := do
  IO.println s!"── {label} ──"
  let mut failed := 0
  for o in outcomes do
    if o.passed then
      IO.println s!"  ✓ {o.name}"
    else
      IO.println s!"  ✗ {o.name}: {o.msg}"
      failed := failed + 1
  return failed

/-- Run all groups; exit non-zero on any failure. -/
def runAll (groups : List (String × List Outcome)) : IO UInt32 := do
  let mut total := 0
  let mut failed := 0
  for (label, outcomes) in groups do
    -- A conditional suite returning `[]` used to erase its own coverage while
    -- the harness printed all-green. Skips must now be explicit passing rows;
    -- every accidental empty group is one visible failure.
    let outcomes := if outcomes.isEmpty then [{
      name := "test group is nonempty"
      passed := false
      msg := "the group produced no assertions; emit an explicit skip row or restore its setup"
    }] else outcomes
    total := total + outcomes.length
    failed := failed + (← runGroup label outcomes)
  if failed = 0 then
    IO.println s!"\nAll {total} assertions passed."
    return 0
  else
    IO.eprintln s!"\n{failed}/{total} assertions FAILED."
    return 1

/-! ### Deterministic seeded generation (for property-style tests)

A tiny splitmix-style PRNG over `Nat`, seeded by a fixed constant so runs are
reproducible (ADR-0009). Not cryptographic — just spread for property coverage. -/

/-- Next state + a pseudo-random `Nat` below `bound` (bound ≥ 1). -/
def nextNat (seed : Nat) (bound : Nat) : Nat × Nat :=
  let s := (seed * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)
  (s, s % (max 1 bound))

/-- Generate `n` deterministic samples via `gen`, threading the seed. -/
def sample {α : Type _} (seed : Nat) (n : Nat) (gen : Nat → α × Nat) : List α :=
  go seed n
where
  go (s : Nat) : Nat → List α
    | 0 => []
    | k + 1 => let (a, s') := gen s; a :: go s' k

end Tl.Tests
