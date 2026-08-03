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

/-- A one-element finding array is not the empty verdict. -/
theorem singleton_ne_empty {α : Type} (a : α) : (#[a] : Array α) ≠ #[] := fun h =>
  Nat.succ_ne_zero 0 ((congrArg Array.size h).trans Array.size_empty)

private theorem not_not_eq_true {b : Bool} : ¬ (!b) = true ↔ b = true := by
  cases b with
  | false => exact iff_of_false (fun h => h rfl) nofun
  | true => exact iff_of_true nofun rfl

private theorem ite_singleton_eq_nil_iff {α : Type} {c : Prop} [Decidable c] (a : α) :
    (if c then [a] else []) = [] ↔ ¬ c := by
  by_cases h : c
  · rw [if_pos h]; exact iff_of_false nofun (fun hn => hn h)
  · rw [if_neg h]; exact iff_of_true rfl h

/-! ### The arms of `analyze`

One characterisation per arm of `Verify.Report.analyze`. Each says exactly when
that arm is silent, so the aggregate theorem below can neither lose a condition
nor invent one. -/

theorem replayFindings_eq_empty_iff (o : Observation) :
    replayFindings o = #[] ↔ o.evidence.replayError? = none := by
  unfold replayFindings
  split
  · next h => exact iff_of_true rfl h
  · next replayError h => exact iff_of_false (singleton_ne_empty _) (by rw [h]; exact nofun)

theorem missingModules_eq_empty_iff (o : Observation) :
    missingModules o = #[] ↔ ∀ name ∈ o.expectedModules, name ∈ o.localModules := by
  unfold missingModules
  rw [Array.filter_eq_empty_iff]
  refine forall_congr' fun name => imp_congr_right fun _ => ?_
  rw [not_not_eq_true, contains_foldl_insert_empty_iff]

theorem unexpectedModules_eq_empty_iff (o : Observation) :
    unexpectedModules o = #[] ↔ ∀ name ∈ o.localModules, name ∈ o.expectedModules := by
  unfold unexpectedModules
  rw [Array.filter_eq_empty_iff]
  refine forall_congr' fun name => imp_congr_right fun _ => ?_
  rw [not_not_eq_true, contains_foldl_insert_empty_iff]

theorem missingModuleFindings_eq_empty_iff (o : Observation) :
    missingModuleFindings o = #[] ↔ ∀ name ∈ o.expectedModules, name ∈ o.localModules := by
  unfold missingModuleFindings
  rw [← missingModules_eq_empty_iff]
  by_cases h : missingModules o = #[]
  · rw [if_pos (Array.isEmpty_iff.mpr h)]; exact iff_of_true rfl h
  · rw [if_neg (fun hc => h (Array.isEmpty_iff.mp hc))]
    exact iff_of_false (singleton_ne_empty _) h

theorem unexpectedModuleFindings_eq_empty_iff (o : Observation) :
    unexpectedModuleFindings o = #[] ↔ ∀ name ∈ o.localModules, name ∈ o.expectedModules := by
  unfold unexpectedModuleFindings
  rw [← unexpectedModules_eq_empty_iff]
  by_cases h : unexpectedModules o = #[]
  · rw [if_pos (Array.isEmpty_iff.mpr h)]; exact iff_of_true rfl h
  · rw [if_neg (fun hc => h (Array.isEmpty_iff.mp hc))]
    exact iff_of_false (singleton_ne_empty _) h

theorem vacuityReasons_eq_nil_iff (o : Observation) :
    vacuityReasons o = [] ↔
      o.decls ≠ #[] ∧ o.evidence.replayedConstants ≠ 0 ∧ o.evidence.importEdges ≠ 0 := by
  unfold vacuityReasons
  rw [List.append_eq_nil_iff, List.append_eq_nil_iff, ite_singleton_eq_nil_iff,
    ite_singleton_eq_nil_iff, ite_singleton_eq_nil_iff, Array.isEmpty_iff,
    beq_iff_eq, beq_iff_eq, and_assoc]

/-- The vacuity arm is silent exactly when the scope inspected some module and
    every kind of evidence the later arms depend on was actually observed. -/
theorem vacuityFindings_eq_empty_iff (o : Observation) :
    vacuityFindings o = #[] ↔
      o.localModules ≠ #[] ∧ o.decls ≠ #[] ∧ o.evidence.replayedConstants ≠ 0
        ∧ o.evidence.importEdges ≠ 0 := by
  unfold vacuityFindings
  by_cases hlocal : o.localModules = #[]
  · rw [if_pos (Array.isEmpty_iff.mpr hlocal)]
    refine iff_of_false (singleton_ne_empty _) ?_
    rintro ⟨hne, -, -, -⟩
    exact hne hlocal
  · rw [if_neg (fun hc => hlocal (Array.isEmpty_iff.mp hc))]
    by_cases hvacuous : vacuityReasons o = []
    · rw [if_pos (List.isEmpty_iff.mpr hvacuous)]
      obtain ⟨hdecls, hreplay, hedges⟩ := (vacuityReasons_eq_nil_iff o).mp hvacuous
      exact iff_of_true rfl ⟨hlocal, hdecls, hreplay, hedges⟩
    · rw [if_neg (fun hc => hvacuous (List.isEmpty_iff.mp hc))]
      refine iff_of_false (singleton_ne_empty _) ?_
      rintro ⟨-, hdecls, hreplay, hedges⟩
      exact hvacuous ((vacuityReasons_eq_nil_iff o).mpr ⟨hdecls, hreplay, hedges⟩)

theorem landmarkPolicyFindings_eq_empty_iff (o : Observation) :
    landmarkPolicyFindings o = #[] ↔ o.landmarks.map (·.name) = o.expectedLandmarks := by
  unfold landmarkPolicyFindings
  by_cases h : o.landmarks.map (·.name) = o.expectedLandmarks
  · rw [if_neg (fun hne => bne_iff_ne.mp hne h)]
    exact iff_of_true rfl h
  · rw [if_pos (bne_iff_ne.mpr h)]
    exact iff_of_false (singleton_ne_empty _) h

theorem landmarkKindFindings_eq_empty_iff (o : Observation) :
    landmarkKindFindings o = #[] ↔
      ∀ landmark ∈ o.landmarks, landmark.kind? = some .theoremDecl := by
  unfold landmarkKindFindings
  rw [Array.filterMap_eq_empty_iff]
  refine forall_congr' fun landmark => imp_congr_right fun _ => ?_
  cases hkind : landmark.kind? with
  | none => exact iff_of_false nofun nofun
  | some kind =>
    cases kind with
    | axiomDecl => exact iff_of_false nofun nofun
    | theoremDecl => exact iff_of_true rfl rfl
    | other => exact iff_of_false nofun nofun

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
