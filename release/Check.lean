/-
A gate's verdict and its report, as one list.

A gate has two outputs that have to stay in step: whether it passed, and what
it says went wrong. Written as two functions over the same inputs they drift,
and both directions of the drift are silent — a condition added to the verdict
and not to the report refuses with no reason given, and one added to the report
and not to the verdict prints a complaint and exits zero. The shell being
replaced had both, in one file.

So they are one list. A `Check` carries the condition *and* what to say when it
does not hold; the verdict is "every check held" and the report is "the failure
text of the ones that did not". A new condition is one row in one list, and
`allHeld_iff_noFailures` is the statement that the two readings can never
disagree.

Its own module, with no imports, because both the CLI plumbing and the model
layer build check lists and neither should have to import the other to do it.
-/

namespace Release

/-- One thing that had to be true, and what to tell whoever has to fix it if it
    was not. -/
structure Check where
  held : Bool
  failure : String
  deriving Repr

/-- The verdict: every check held. -/
def Check.allHeld (checks : List Check) : Bool := checks.all (·.held)

/-- The report: what to say about each check that did not hold, in order. -/
def Check.failures (checks : List Check) : List String :=
  (checks.filter (!·.held)).map (·.failure)

/-- **The verdict and the report are the same fact.**

    Proved rather than maintained by inspection, and both directions rule out a
    defect that is invisible in the output. Left to right, a pass cannot coexist
    with an unreported complaint. Right to left, a refusal cannot coexist with
    an empty report — a gate that refuses and says nothing is one nobody can
    act on.

    Stated over an arbitrary list rather than over the lists this project
    happens to build, so it holds for every check list added later without
    anything being restated. -/
theorem Check.allHeld_iff_noFailures (checks : List Check) :
    Check.allHeld checks = true ↔ Check.failures checks = [] := by
  constructor
  · intro held
    have every : ∀ check ∈ checks, check.held = true := List.all_eq_true.mp held
    have empty : checks.filter (!·.held) = [] := by
      refine List.filter_eq_nil_iff.mpr ?_
      intro check member
      rw [every check member]
      exact Bool.noConfusion
    rw [Check.failures, empty]
    rfl
  · intro reported
    refine List.all_eq_true.mpr ?_
    intro check member
    have empty : checks.filter (!·.held) = [] := List.map_eq_nil_iff.mp reported
    have absent := List.filter_eq_nil_iff.mp empty check member
    match held : check.held with
    | true => rfl
    | false => exact absurd (by rw [held]; rfl) absent

end Release
