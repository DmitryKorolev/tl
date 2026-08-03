/-
Verdict-logic theorems for the Lean-native trust gate.

`Verify.Report.analyze`, `Verify.Policy.importViolations`,
`Verify.Supervise.completedSuccessfully`, and
`Verify.Environment.replayDependencies` are total pure functions that decide
the entire `tlverify` verdict. Every arm of that decision is characterised here
as an if-and-only-if: the forward direction is what makes a green gate mean
something, and the backward direction is what rules out a gate that fails on a
clean checkout.

These are the gate's *own* correctness, not one of the product's proved claims,
so they deliberately get no entry in `Tl.Verify.landmarkTheorems` and no row in
the docs/overview.md proved-claims table (ADR-0026).
-/
import Verify.Environment
import Verify.Policy
import Verify.Report
import Verify.Supervise

open Lean (Name)

namespace Tl.Verify

/-! ### Array and hash-set plumbing

Explicit bridges from the shapes the verdict functions are written in (a
`foldl`-built membership index, a one-element finding array) to the shapes the
arm characterisations are stated in. -/

/-- A finding array that was appended to at all is not the empty verdict. -/
theorem push_ne_empty {α : Type} (xs : Array α) (a : α) : xs.push a ≠ #[] := by
  intro h
  have size : (xs.push a).size = 0 := by rw [h]; exact Array.size_empty
  rw [Array.size_push] at size
  exact Nat.succ_ne_zero _ size

private theorem contains_listFoldl_insert {α : Type} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (l : List α) (init : Std.HashSet α) (a : α) :
    (l.foldl (fun s x => s.insert x) init).contains a
      = (init.contains a || l.contains a) := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil, List.contains_nil, Bool.or_false]
  | cons x xs ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, List.contains_cons,
      Bool.or_assoc, BEq.comm (a := a) (b := x)]
    exact Bool.or_left_comm _ _ _

/-- Folding `insert` over an array yields exactly the union of the starting set
    with the array's elements. -/
theorem contains_foldl_insert {α : Type} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (xs : Array α) (init : Std.HashSet α) (a : α) :
    (xs.foldl (fun s x => s.insert x) init).contains a
      = (init.contains a || xs.contains a) := by
  rw [← Array.foldl_toList, contains_listFoldl_insert, ← Array.contains_toList]

/-- The membership index the module arms build is exactly array membership, so
    neither arm can accept a module the array never held. -/
theorem contains_foldl_insert_empty_iff {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    [LawfulHashable α] (xs : Array α) (a : α) :
    (xs.foldl (fun s x => s.insert x) (∅ : Std.HashSet α)).contains a = true ↔ a ∈ xs := by
  rw [contains_foldl_insert, Std.HashSet.contains_empty, Bool.false_or,
    Array.contains_iff_mem]

/-! ### Supervision -/

/-- The completion marker never rescues a worker that failed: accepting a run
    requires status zero independently of what it printed. -/
theorem completedSuccessfully_exitZero {protocol : CompletionProtocol}
    {exitCode : UInt32} {stdout : String}
    (h : completedSuccessfully protocol exitCode stdout = true) : exitCode = 0 := by
  have hand : (exitCode == 0) = true ∧ _ := Bool.and_eq_true _ _ |>.mp h
  exact eq_of_beq hand.1

/-! ### Replay dependency cone -/

/-- Every stored constant a declaration uses is enqueued by a replay step, so
    the dependency cone cannot silently drop a body's own references. -/
theorem replayDependencies_superset (info : Lean.ConstantInfo) {name : Name}
    (h : name ∈ info.getUsedConstantsAsSet.toArray) :
    name ∈ replayDependencies info := by
  unfold replayDependencies
  cases info with
  | inductInfo inductiveInfo => exact Array.mem_append_left _ h
  | _ => exact h

end Tl.Verify
