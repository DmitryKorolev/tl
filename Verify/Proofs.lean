/-
Verdict-logic theorems for the Lean-native trust gate.

`Verify.Report.analyze`, `Verify.Policy.importViolations`,
`Verify.Supervise.completedSuccessfully`, and
`Verify.Environment.replayDependencies` are total pure functions that decide
the entire `tlverify` verdict.

What is characterised here, and how far:

* `analyze`, `Verify.Report.gateEvidenceOf`, and the two aggregates between
  them are characterised as **if-and-only-ifs**. The forward direction is what
  makes a green gate mean something; the backward direction is what rules out a
  gate that fails on a clean checkout.
* `importViolations` is characterised **exactly**: an if-and-only-if for its
  silence, plus a cardinality equation pinning one finding per rejected edge.
* `completedSuccessfully`, `directImportAllowed`, and `replayDependencies`
  carry **one-directional** implications only — accepted implies status zero
  and marker-final, allowed implies one of the two recorded reasons, and a
  used constant — or, for an inductive, a mutual sibling — implies an enqueued
  replay dependency. Their converses, and
  everything about how the evidence those functions run on is *collected*
  (declaration selection, `replayClosure`'s transitive walk, the supervisor's
  process handling), stay in the tested tier.

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
nor invent one. The stored-body axiom propagation those arms report on is
characterised separately, at the end of this file. -/

theorem replayFindings_eq_empty_iff (o : Observation) :
    replayFindings o = #[] ↔ o.evidence.replayError? = none := by
  unfold replayFindings
  split
  · next h => exact iff_of_true rfl h
  · next replayError h => exact iff_of_false (singleton_ne_empty _) (by rw [h]; exact nofun)

theorem propagationFindings_eq_empty_iff (o : Observation) :
    propagationFindings o = #[] ↔ o.evidence.propagationError? = none := by
  unfold propagationFindings
  split
  · next h => exact iff_of_true rfl h
  · next propagationError h =>
      exact iff_of_false (singleton_ne_empty _) (by rw [h]; exact nofun)

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

private theorem eq_false_of_not_eq_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

private theorem repeatedLandmarkStep_eq (seen : Std.HashSet Name) (repeated : Array Name)
    (landmark : Landmark) :
    repeatedLandmarkStep (seen, repeated) landmark =
      if seen.contains landmark.name then (seen, repeated.push landmark.name)
      else (seen.insert landmark.name, repeated) := rfl

/-- The duplicate scan only ever appends, so a name reported once stays
    reported. This is what makes the single-pass scan's silence meaningful. -/
private theorem repeated_size_le (ls : List Landmark) (seen : Std.HashSet Name)
    (repeated : Array Name) :
    repeated.size ≤ (ls.foldl repeatedLandmarkStep (seen, repeated)).2.size := by
  induction ls generalizing seen repeated with
  | nil => exact Nat.le_refl _
  | cons landmark rest ih =>
    rw [List.foldl_cons, repeatedLandmarkStep_eq]
    by_cases h : seen.contains landmark.name = true
    · rw [if_pos h]
      refine Nat.le_trans ?_ (ih seen (repeated.push landmark.name))
      rw [Array.size_push]
      exact Nat.le_succ _
    · rw [if_neg h]
      exact ih (seen.insert landmark.name) repeated

private theorem repeated_ne_empty (ls : List Landmark) (seen : Std.HashSet Name)
    (repeated : Array Name) (h : repeated ≠ #[]) :
    (ls.foldl repeatedLandmarkStep (seen, repeated)).2 ≠ #[] := by
  intro hempty
  have size := repeated_size_le ls seen repeated
  rw [hempty, Array.size_empty] at size
  exact h (Array.eq_empty_iff_size_eq_zero.mpr (Nat.le_zero.mp size))

private theorem foldl_repeatedLandmarkStep_eq_empty_iff (ls : List Landmark)
    (seen : Std.HashSet Name) :
    (ls.foldl repeatedLandmarkStep (seen, #[])).2 = #[] ↔
      (ls.map (·.name)).Nodup ∧ ∀ landmark ∈ ls, seen.contains landmark.name = false := by
  induction ls generalizing seen with
  | nil => exact iff_of_true rfl ⟨List.nodup_nil, nofun⟩
  | cons landmark rest ih =>
    rw [List.foldl_cons, repeatedLandmarkStep_eq]
    by_cases hseen : seen.contains landmark.name = true
    · rw [if_pos hseen]
      refine iff_of_false (repeated_ne_empty _ _ _ (push_ne_empty _ _)) ?_
      rintro ⟨-, hfresh⟩
      have hcontains := hfresh landmark (List.Mem.head _)
      rw [hseen] at hcontains
      exact Bool.noConfusion hcontains
    · rw [if_neg hseen, ih (seen.insert landmark.name)]
      constructor
      · rintro ⟨hnodup, hfresh⟩
        refine ⟨?_, ?_⟩
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, hnodup⟩
          intro hmem
          obtain ⟨other, hother, hname⟩ := List.mem_map.mp hmem
          have hcontains := hfresh other hother
          rw [Std.HashSet.contains_insert, hname, beq_self_eq_true, Bool.true_or] at hcontains
          exact Bool.noConfusion hcontains
        · intro other hother
          cases hother with
          | head => exact eq_false_of_not_eq_true hseen
          | tail _ hmem =>
            have hcontains := hfresh other hmem
            rw [Std.HashSet.contains_insert] at hcontains
            exact (Bool.or_eq_false_iff.mp hcontains).2
      · rintro ⟨hnodup, hfresh⟩
        rw [List.map_cons, List.nodup_cons] at hnodup
        obtain ⟨hnotmem, hnodup⟩ := hnodup
        refine ⟨hnodup, fun other hother => ?_⟩
        rw [Std.HashSet.contains_insert]
        refine Bool.or_eq_false_iff.mpr ⟨?_, hfresh other (List.Mem.tail _ hother)⟩
        cases hbeq : landmark.name == other.name with
        | false => rfl
        | true => exact absurd (List.mem_map.mpr ⟨other, hother, (eq_of_beq hbeq).symm⟩) hnotmem

/-- The single-pass duplicate scan reports nothing exactly when the observed
    landmark names are pairwise distinct. -/
theorem repeatedLandmarks_eq_empty_iff (landmarks : Array Landmark) :
    repeatedLandmarks landmarks = #[] ↔ (landmarks.map (·.name)).toList.Nodup := by
  unfold repeatedLandmarks
  rw [← Array.foldl_toList, foldl_repeatedLandmarkStep_eq_empty_iff, Array.toList_map]
  constructor
  · rintro ⟨hnodup, -⟩; exact hnodup
  · exact fun hnodup => ⟨hnodup, fun _ _ => Std.HashSet.contains_empty⟩

theorem duplicateLandmarkFindings_eq_empty_iff (o : Observation) :
    duplicateLandmarkFindings o = #[] ↔ (o.landmarks.map (·.name)).toList.Nodup := by
  unfold duplicateLandmarkFindings
  rw [← repeatedLandmarks_eq_empty_iff]
  by_cases h : repeatedLandmarks o.landmarks = #[]
  · rw [if_pos (Array.isEmpty_iff.mpr h)]; exact iff_of_true rfl h
  · rw [if_neg (fun hc => h (Array.isEmpty_iff.mp hc))]
    exact iff_of_false (singleton_ne_empty _) h

theorem axiomDeclarations_eq_empty_iff (o : Observation) :
    axiomDeclarations o = #[] ↔ ∀ decl ∈ o.decls, decl.kind ≠ .axiomDecl := by
  unfold axiomDeclarations
  rw [Array.filter_eq_empty_iff]
  refine forall_congr' fun decl => imp_congr_right fun _ => ?_
  constructor
  · exact fun h hkind => h (by rw [hkind]; exact beq_self_eq_true _)
  · exact fun h hbeq => h (of_decide_eq_true hbeq)

theorem axiomDeclarationFindings_eq_empty_iff (o : Observation) :
    axiomDeclarationFindings o = #[] ↔ ∀ decl ∈ o.decls, decl.kind ≠ .axiomDecl := by
  unfold axiomDeclarationFindings
  rw [← axiomDeclarations_eq_empty_iff]
  by_cases h : axiomDeclarations o = #[]
  · rw [if_pos (Array.isEmpty_iff.mpr h)]; exact iff_of_true rfl h
  · rw [if_neg (fun hc => h (Array.isEmpty_iff.mp hc))]
    exact iff_of_false (singleton_ne_empty _) h

/-- A first-party axiom is reported by its own arm, so this arm's silence is
    conditional on the declaration not being one. -/
theorem axiomDependencyOffenders_eq_empty_iff (cfg : Config) (o : Observation) :
    axiomDependencyOffenders cfg o = #[] ↔
      ∀ decl ∈ o.decls, decl.kind ≠ .axiomDecl →
        ∀ name ∈ decl.axioms, name ∈ cfg.allowedAxioms := by
  unfold axiomDependencyOffenders
  rw [Array.filterMap_eq_empty_iff]
  refine forall_congr' fun decl => imp_congr_right fun _ => ?_
  by_cases hkind : decl.kind = DeclKind.axiomDecl
  · rw [if_pos (by rw [hkind]; exact beq_self_eq_true _)]
    exact iff_of_true rfl (fun hne => absurd hkind hne)
  · rw [if_neg (show ¬((decl.kind == DeclKind.axiomDecl) = true) from
      fun hbeq => hkind (of_decide_eq_true hbeq))]
    have allowed : (decl.axioms.filter fun name => !cfg.allowedAxioms.contains name) = #[]
        ↔ ∀ name ∈ decl.axioms, name ∈ cfg.allowedAxioms := by
      rw [Array.filter_eq_empty_iff]
      refine forall_congr' fun name => imp_congr_right fun _ => ?_
      rw [not_not_eq_true, Array.contains_iff_mem]
    by_cases hbad : (decl.axioms.filter fun name => !cfg.allowedAxioms.contains name) = #[]
    · rw [if_pos (Array.isEmpty_iff.mpr hbad)]
      exact iff_of_true rfl (fun _ => allowed.mp hbad)
    · rw [if_neg (fun hc => hbad (Array.isEmpty_iff.mp hc))]
      exact iff_of_false nofun (fun h => hbad (allowed.mpr (h hkind)))

theorem axiomDependencyFindings_eq_empty_iff (cfg : Config) (o : Observation) :
    axiomDependencyFindings cfg o = #[] ↔
      ∀ decl ∈ o.decls, decl.kind ≠ .axiomDecl →
        ∀ name ∈ decl.axioms, name ∈ cfg.allowedAxioms := by
  unfold axiomDependencyFindings
  rw [← axiomDependencyOffenders_eq_empty_iff]
  by_cases h : axiomDependencyOffenders cfg o = #[]
  · rw [if_pos (Array.isEmpty_iff.mpr h)]; exact iff_of_true rfl h
  · rw [if_neg (fun hc => h (Array.isEmpty_iff.mp hc))]
    exact iff_of_false (singleton_ne_empty _) h

/-! ### The whole verdict for one scope -/

/-- Every condition `analyze` can report about one audited scope, stated
    positively. A field per arm: adding an arm without adding a field here
    breaks `analyze_clean_iff`, so the verdict cannot grow a condition this
    characterisation does not mention. -/
structure GateClean (cfg : Config) (o : Observation) : Prop where
  /-- The ADR-0009 direct-import audit found nothing. -/
  importAuditClean : o.evidence.importErrors = #[]
  /-- Independent kernel replay accepted the stored dependency cone. -/
  replayClean : o.evidence.replayError? = none
  /-- Stored-body axiom propagation answered, so the axiom rows are complete.
      Without this the axiom conjuncts below would be satisfiable by a scope
      whose axiom rows were discarded rather than empty. -/
  propagationClean : o.evidence.propagationError? = none
  /-- Every source module the scope claims was actually imported. -/
  everyExpectedModuleImported : ∀ name ∈ o.expectedModules, name ∈ o.localModules
  /-- Every imported first-party module is inside the declared scope. -/
  everyImportedModuleExpected : ∀ name ∈ o.localModules, name ∈ o.expectedModules
  /-- The scope is one of the mandatory six, so it must inspect something. -/
  modulesInspected : o.localModules ≠ #[]
  /-- Declaration ownership selected something to audit. -/
  declsSelected : o.decls ≠ #[]
  /-- Something reached independent replay validation. -/
  replayValidated : o.evidence.replayedConstants ≠ 0
  /-- The stored import traversal read something. -/
  importEdgesRead : o.evidence.importEdges ≠ 0
  /-- Landmark observation preserved the policy list one for one. On the
      shipped path `observeEnvironment` builds `landmarks` by mapping over
      `expectedLandmarks`, so no current run can violate this: it is a tripwire
      against a future refactor that looks landmarks up separately, not a live
      per-run check. What the landmark list actually *contains* is pinned by
      `Tests/VerifyTests.lean`, not by this conjunct. -/
  landmarkPolicyPreserved : o.landmarks.map (·.name) = o.expectedLandmarks
  /-- Every observed landmark is present and is a theorem. -/
  landmarksAreTheorems : ∀ landmark ∈ o.landmarks, landmark.kind? = some .theoremDecl
  /-- No documented claim is covered twice by the same landmark name. -/
  landmarksDistinct : (o.landmarks.map (·.name)).toList.Nodup
  /-- No inspected declaration is itself a first-party axiom. -/
  noFirstPartyAxiom : ∀ decl ∈ o.decls, decl.kind ≠ .axiomDecl
  /-- Every stored axiom dependency is inside the configured allowance. -/
  axiomsWithinAllowance : ∀ decl ∈ o.decls, ∀ name ∈ decl.axioms, name ∈ cfg.allowedAxioms

/-- The verdict for one scope is the conjunction of its arms staying silent. -/
theorem analyze_errors_eq_empty_iff_arms (cfg : Config) (o : Observation) :
    (analyze cfg o).errors = #[] ↔
      o.evidence.importErrors = #[] ∧ replayFindings o = #[]
        ∧ propagationFindings o = #[]
        ∧ missingModuleFindings o = #[] ∧ unexpectedModuleFindings o = #[]
        ∧ vacuityFindings o = #[] ∧ landmarkPolicyFindings o = #[]
        ∧ landmarkKindFindings o = #[] ∧ duplicateLandmarkFindings o = #[]
        ∧ axiomDeclarationFindings o = #[] ∧ axiomDependencyFindings cfg o = #[] := by
  unfold analyze
  simp only [Array.append_eq_empty_iff, and_assoc]

/-- A scope passes exactly when `GateClean` holds of it.

    The forward direction is what a green gate buys: no first-party axiom, no
    out-of-allowance axiom dependency, an exact module match, a preserved
    landmark policy, and evidence that the audit was not vacuous. The backward
    direction rules out a gate that fails on a clean checkout.

    Read the axiom and evidence conjuncts as quantified over what the
    observation *carries*: `noFirstPartyAxiom` and `axiomsWithinAllowance` range
    over `o.decls`, and the three non-vacuity conjuncts only say the selection
    was not empty. That `o.decls` is the scope's full declaration set, that
    `o.evidence.importErrors` is a real ADR-0009 audit, and that
    `o.evidence.replayError?` is a real kernel replay are properties of
    `Verify.Environment`'s collection layer, which stays in the tested tier
    (ADR-0026). -/
theorem analyze_clean_iff (cfg : Config) (o : Observation) :
    (analyze cfg o).errors = #[] ↔ GateClean cfg o := by
  rw [analyze_errors_eq_empty_iff_arms, replayFindings_eq_empty_iff,
    propagationFindings_eq_empty_iff,
    missingModuleFindings_eq_empty_iff, unexpectedModuleFindings_eq_empty_iff,
    vacuityFindings_eq_empty_iff, landmarkPolicyFindings_eq_empty_iff,
    landmarkKindFindings_eq_empty_iff, duplicateLandmarkFindings_eq_empty_iff,
    axiomDeclarationFindings_eq_empty_iff, axiomDependencyFindings_eq_empty_iff]
  constructor
  · rintro ⟨himports, hreplay, hpropagation, hexpected, hlocal,
      ⟨hmodules, hdecls, hreplayed, hedges⟩,
      hpolicy, hkinds, hdistinct, hnoaxiom, hdependencies⟩
    exact {
      importAuditClean := himports
      replayClean := hreplay
      propagationClean := hpropagation
      everyExpectedModuleImported := hexpected
      everyImportedModuleExpected := hlocal
      modulesInspected := hmodules
      declsSelected := hdecls
      replayValidated := hreplayed
      importEdgesRead := hedges
      landmarkPolicyPreserved := hpolicy
      landmarksAreTheorems := hkinds
      landmarksDistinct := hdistinct
      noFirstPartyAxiom := hnoaxiom
      axiomsWithinAllowance := fun decl hdecl =>
        hdependencies decl hdecl (hnoaxiom decl hdecl) }
  · intro clean
    exact ⟨clean.importAuditClean, clean.replayClean, clean.propagationClean,
      clean.everyExpectedModuleImported,
      clean.everyImportedModuleExpected,
      ⟨clean.modulesInspected, clean.declsSelected, clean.replayValidated,
        clean.importEdgesRead⟩,
      clean.landmarkPolicyPreserved, clean.landmarksAreTheorems, clean.landmarksDistinct,
      clean.noFirstPartyAxiom, fun decl hdecl _ => clean.axiomsWithinAllowance decl hdecl⟩

/-! ### The whole gate verdict -/

/-- All six audited scopes reach the final verdict: no scope's findings can be
    lost in the flattening. -/
theorem auditedReports_errors_eq_empty_iff (reports : AuditedReports) :
    reports.errors = #[] ↔
      reports.production.errors = #[] ∧ reports.tests.errors = #[]
        ∧ reports.verifier.errors = #[] ∧ reports.supervisor.errors = #[]
        ∧ reports.testSupervisor.errors = #[] ∧ reports.tooling.errors = #[] := by
  unfold AuditedReports.errors
  rw [Array.flatMap_eq_empty_iff]
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]

theorem unclaimedSourceError?_eq_none_iff (unclaimed : Array String) :
    unclaimedSourceError? unclaimed = none ↔ unclaimed = #[] := by
  unfold unclaimedSourceError?
  by_cases h : unclaimed = #[]
  · rw [if_pos (Array.isEmpty_iff.mpr h)]; exact iff_of_true rfl h
  · rw [if_neg (fun hc => h (Array.isEmpty_iff.mp hc))]
    exact iff_of_false nofun h

/-- The gate accepts exactly when every scope report, the source inventory, and
    the unclaimed-source scan are all silent. -/
theorem gateEvidence_errors_eq_empty_iff (evidence : GateEvidence) :
    evidence.errors = #[] ↔
      evidence.reports.errors = #[] ∧ evidence.inventoryErrors = #[]
        ∧ evidence.unclaimedSources = #[] := by
  unfold GateEvidence.errors
  cases hunclaimed : unclaimedSourceError? evidence.unclaimedSources with
  | none =>
    rw [Array.append_eq_empty_iff]
    constructor
    · rintro ⟨hreports, hinventory⟩
      exact ⟨hreports, hinventory, (unclaimedSourceError?_eq_none_iff _).mp hunclaimed⟩
    · rintro ⟨hreports, hinventory, -⟩
      exact ⟨hreports, hinventory⟩
  | some error =>
    refine iff_of_false (push_ne_empty _ _) ?_
    rintro ⟨-, -, hempty⟩
    rw [(unclaimedSourceError?_eq_none_iff _).mpr hempty] at hunclaimed
    exact absurd hunclaimed nofun

/-- The same verdict with the six scope reports expanded: nothing between an
    individual scope's findings and the gate's exit status can absorb them. -/
theorem gateEvidence_errors_eq_empty_iff_scopes (evidence : GateEvidence) :
    evidence.errors = #[] ↔
      evidence.reports.production.errors = #[] ∧ evidence.reports.tests.errors = #[]
        ∧ evidence.reports.verifier.errors = #[] ∧ evidence.reports.supervisor.errors = #[]
        ∧ evidence.reports.testSupervisor.errors = #[] ∧ evidence.reports.tooling.errors = #[]
        ∧ evidence.inventoryErrors = #[] ∧ evidence.unclaimedSources = #[] := by
  rw [gateEvidence_errors_eq_empty_iff, auditedReports_errors_eq_empty_iff, and_assoc,
    and_assoc, and_assoc, and_assoc, and_assoc]

/-- The finding array the worker builds is empty exactly when all six audited
    scopes satisfy `GateClean` and neither the source inventory nor the
    unclaimed-source scan found anything.

    This is stated about `gateEvidenceOf`, the function `runChecked` calls, so a
    scope audited twice or left out of the assembly breaks this theorem instead
    of slipping past it. The remaining step is IO and stays tested: `runChecked`
    turning an empty array into status zero plus the completion marker, and the
    supervisor's handling of that marker. -/
theorem analyzedGateEvidence_clean_iff (cfg : Config)
    (production tests verifier supervisor testSupervisor tooling : Observation)
    (inventoryErrors unclaimedSources : Array String) :
    (gateEvidenceOf cfg production tests verifier supervisor testSupervisor tooling
      inventoryErrors unclaimedSources).errors = #[] ↔
      GateClean cfg production ∧ GateClean cfg tests ∧ GateClean cfg verifier
        ∧ GateClean cfg supervisor ∧ GateClean cfg testSupervisor
        ∧ GateClean cfg tooling
        ∧ inventoryErrors = #[] ∧ unclaimedSources = #[] := by
  rw [gateEvidenceOf, gateEvidence_errors_eq_empty_iff_scopes]
  rw [analyze_clean_iff, analyze_clean_iff, analyze_clean_iff, analyze_clean_iff,
    analyze_clean_iff, analyze_clean_iff]

/-! ### The ADR-0009 direct-import audit

`importViolations` is a nested imperative loop, so its silence is only
meaningful if the traversal reaches every edge. These lemmas turn the loop into
a fold and characterise when the fold produces nothing. -/

private theorem forIn_yield_eq_foldl_id {α β : Type} (xs : Array α) (init : β) (f : α → β → β) :
    (forIn (m := Id) xs init fun x acc => ForInStep.yield (f x acc))
      = xs.foldl (fun acc x => f x acc) init :=
  Array.forIn_pure_yield_eq_foldl (m := Id) (fun x acc => f x acc) init

private theorem ite_yield {β : Type} {c : Prop} [Decidable c] (a b : β) :
    (if c then ForInStep.yield a else ForInStep.yield b)
      = ForInStep.yield (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- A fold whose every step is empty-preserving is empty exactly when it started
    empty and every element was clean. This is the general form of "the
    traversal cannot silently stop". -/
private theorem listFoldl_eq_empty_iff {α β : Type} (xs : List α)
    (step : Array β → α → Array β) (clean : α → Prop) (init : Array β)
    (hstep : ∀ acc x, step acc x = #[] ↔ acc = #[] ∧ clean x) :
    xs.foldl step init = #[] ↔ init = #[] ∧ ∀ x ∈ xs, clean x := by
  induction xs generalizing init with
  | nil => exact ⟨fun h => ⟨h, nofun⟩, fun h => h.1⟩
  | cons x rest ih =>
    rw [List.foldl_cons, ih (step init x)]
    constructor
    · rintro ⟨hstepEmpty, hrest⟩
      obtain ⟨hinit, hclean⟩ := (hstep init x).mp hstepEmpty
      refine ⟨hinit, fun y hy => ?_⟩
      cases hy with
      | head => exact hclean
      | tail _ hmem => exact hrest y hmem
    · rintro ⟨hinit, hclean⟩
      exact ⟨(hstep init x).mpr ⟨hinit, hclean x (List.Mem.head _)⟩,
        fun y hy => hclean y (List.Mem.tail _ hy)⟩

private theorem arrayFoldl_eq_empty_iff {α β : Type} (xs : Array α)
    (step : Array β → α → Array β) (clean : α → Prop) (init : Array β)
    (hstep : ∀ acc x, step acc x = #[] ↔ acc = #[] ∧ clean x) :
    xs.foldl step init = #[] ↔ init = #[] ∧ ∀ x ∈ xs, clean x := by
  rw [← Array.foldl_toList, listFoldl_eq_empty_iff xs.toList step clean init hstep]
  refine and_congr_right fun _ => forall_congr' fun x => ?_
  exact imp_congr_left (Array.mem_toList_iff (a := x) (xs := xs))

private theorem push_unless_eq_empty_iff {α β : Type} (p : α → Bool) (g : α → β)
    (acc : Array β) (x : α) :
    (if p x = true then acc else acc.push (g x)) = #[] ↔ acc = #[] ∧ p x = true := by
  by_cases h : p x = true
  · rw [if_pos h]
    exact ⟨fun hacc => ⟨hacc, h⟩, fun hc => hc.1⟩
  · rw [if_neg h]
    exact iff_of_false (push_ne_empty _ _) (fun hc => h hc.2)

private theorem nestedFoldl_push_eq_empty_iff {α β γ : Type} (rows : Array α)
    (inner : α → Array β) (p : α → β → Bool) (g : α → β → γ) :
    rows.foldl (fun acc row =>
        (inner row).foldl (fun acc y => if p row y then acc else acc.push (g row y)) acc)
      #[] = #[] ↔ ∀ row ∈ rows, ∀ y ∈ inner row, p row y = true := by
  rw [arrayFoldl_eq_empty_iff (clean := fun row => ∀ y ∈ inner row, p row y = true)
    (hstep := fun acc row => arrayFoldl_eq_empty_iff (inner row) _ _ acc
      (fun acc' y => push_unless_eq_empty_iff (p row) (g row) acc' y))]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- No ADR-0009 finding means every edge of every row was checked and allowed:
    the nested traversal reaches all of them. -/
theorem importViolations_isEmpty_iff (policy : ImportPolicy) (scope : String)
    (projectModules : Std.HashSet Name) (rows : Array (Name × Array Name)) :
    importViolations policy scope projectModules rows = #[] ↔
      ∀ row ∈ rows, ∀ importedModule ∈ row.2,
        directImportAllowed policy row.1 importedModule
          (projectModules.contains importedModule) = true := by
  simp only [importViolations, Id.run, Id, bind, pure, ite_yield, forIn_yield_eq_foldl_id]
  exact nestedFoldl_push_eq_empty_iff rows (·.2)
    (fun row importedModule => directImportAllowed policy row.1 importedModule
      (projectModules.contains importedModule)) _

/-! Emptiness says nothing about how many findings survive, so a traversal that
reports only its first violation, or overwrites the accumulator instead of
appending to it, would satisfy the theorem above. The count below closes that:
the audit emits exactly one finding per rejected edge. -/

/-- The edges the ADR-0009 policy rejects, counted per row with `filter` rather
    than by rerunning the traversal being characterised. Proof scaffolding: the
    gate never calls it. -/
def disallowedEdgeCount (policy : ImportPolicy) (projectModules : Std.HashSet Name)
    (rows : Array (Name × Array Name)) : Nat :=
  rows.foldl (fun total row =>
    total + (row.2.filter fun importedModule =>
      !directImportAllowed policy row.1 importedModule
        (projectModules.contains importedModule)).size) 0

private theorem listFoldl_size_eq {α β : Type} (xs : List α) (step : Array β → α → Array β)
    (w : α → Nat) (init : Array β)
    (hstep : ∀ acc x, (step acc x).size = acc.size + w x) :
    (xs.foldl step init).size = xs.foldl (fun total x => total + w x) init.size := by
  induction xs generalizing init with
  | nil => rfl
  | cons x rest ih => rw [List.foldl_cons, List.foldl_cons, ih (step init x), hstep init x]

private theorem arrayFoldl_size_eq {α β : Type} (xs : Array α) (step : Array β → α → Array β)
    (w : α → Nat) (init : Array β)
    (hstep : ∀ acc x, (step acc x).size = acc.size + w x) :
    (xs.foldl step init).size = xs.foldl (fun total x => total + w x) init.size := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact listFoldl_size_eq xs.toList step w init hstep

private theorem push_unless_size {β : Type} (c : Prop) [Decidable c] (acc : Array β) (b : β) :
    (if c then acc else acc.push b).size = acc.size + (if c then 0 else 1) := by
  by_cases h : c
  · rw [if_pos h, if_pos h, Nat.add_zero]
  · rw [if_neg h, if_neg h, Array.size_push]

private theorem listFoldl_count_eq_filter_length {β : Type} (ys : List β) (p : β → Bool)
    (n : Nat) :
    ys.foldl (fun total y => total + (if p y = true then 0 else 1)) n
      = n + (ys.filter fun y => !p y).length := by
  induction ys generalizing n with
  | nil => exact (Nat.add_zero n).symm
  | cons y rest ih =>
    rw [List.foldl_cons]
    by_cases h : p y = true
    · rw [if_pos h, Nat.add_zero, ih n,
        List.filter_cons_of_neg (by rw [h, Bool.not_true]; exact nofun)]
    · rw [if_neg h, ih (n + 1),
        List.filter_cons_of_pos (by rw [eq_false_of_not_eq_true h, Bool.not_false]),
        List.length_cons]
      exact Nat.add_right_comm n 1 _

private theorem arrayFoldl_count_eq_filter_size {β : Type} (ys : Array β) (p : β → Bool)
    (n : Nat) :
    ys.foldl (fun total y => total + (if p y = true then 0 else 1)) n
      = n + (ys.filter fun y => !p y).size := by
  rw [← Array.foldl_toList, listFoldl_count_eq_filter_length, ← Array.length_toList,
    Array.toList_filter]

private theorem innerFoldl_push_size {β γ : Type} (ys : Array β) (p : β → Bool) (g : β → γ)
    (acc : Array γ) :
    (ys.foldl (fun acc y => if p y = true then acc else acc.push (g y)) acc).size
      = acc.size + (ys.filter fun y => !p y).size :=
  calc (ys.foldl (fun acc y => if p y = true then acc else acc.push (g y)) acc).size
      = ys.foldl (fun total y => total + (if p y = true then 0 else 1)) acc.size :=
        arrayFoldl_size_eq ys _ _ acc (fun acc' _ => push_unless_size _ acc' _)
    _ = acc.size + (ys.filter fun y => !p y).size :=
        arrayFoldl_count_eq_filter_size ys p acc.size

private theorem nestedFoldl_push_size {α β γ : Type} (rows : Array α)
    (inner : α → Array β) (p : α → β → Bool) (g : α → β → γ) :
    (rows.foldl (fun acc row =>
        (inner row).foldl (fun acc y => if p row y then acc else acc.push (g row y)) acc)
      #[]).size
      = rows.foldl (fun total row => total + ((inner row).filter fun y => !p row y).size) 0 := by
  rw [arrayFoldl_size_eq rows _
    (fun row => ((inner row).filter fun y => !p row y).size) #[]
    (fun acc row => innerFoldl_push_size (inner row) (p row) (g row) acc), Array.size_empty]

/-- The ADR-0009 audit reports one finding per rejected edge: findings
    accumulate across rows and across the edges of a row, so neither a
    truncating nor an overwriting accumulator can pass. -/
theorem importViolations_size_eq (policy : ImportPolicy) (scope : String)
    (projectModules : Std.HashSet Name) (rows : Array (Name × Array Name)) :
    (importViolations policy scope projectModules rows).size
      = disallowedEdgeCount policy projectModules rows := by
  simp only [importViolations, Id.run, Id, bind, pure, ite_yield, forIn_yield_eq_foldl_id,
    disallowedEdgeCount]
  exact nestedFoldl_push_size rows (·.2)
    (fun row importedModule => directImportAllowed policy row.1 importedModule
      (projectModules.contains importedModule)) _

/-- Without the first-party escape, an allowed import is justified by exactly
    one of the two recorded reasons: an ordinary dependency prefix, or an
    allowlisted reachability module reaching Mathlib. -/
theorem directImportAllowed_cases {policy : ImportPolicy} {definingModule importedModule : Name}
    (h : directImportAllowed policy definingModule importedModule false = true) :
    (∃ candidate ∈ policy.ordinaryPrefixes, Name.isPrefixOf candidate importedModule) ∨
      (definingModule ∈ policy.mathlibModules ∧ Name.isPrefixOf `Mathlib importedModule) := by
  unfold directImportAllowed at h
  rw [Bool.false_or] at h
  rcases (Bool.or_eq_true _ _).mp h with hordinary | hmathlib
  · exact Or.inl (Array.any_eq_true'.mp hordinary)
  · obtain ⟨hcontains, hprefix⟩ := (Bool.and_eq_true _ _).mp hmathlib
    exact Or.inr ⟨Array.contains_iff_mem.mp hcontains, hprefix⟩

/-! ### Supervision -/

/-- The completion marker never rescues a worker that failed: accepting a run
    requires status zero independently of what it printed. -/
theorem completedSuccessfully_exitZero {protocol : CompletionProtocol}
    {exitCode : UInt32} {stdout : String}
    (h : completedSuccessfully protocol exitCode stdout = true) : exitCode = 0 := by
  have hand : (exitCode == 0) = true ∧ _ := Bool.and_eq_true _ _ |>.mp h
  exact eq_of_beq hand.1

/-- The scan that keeps the latest nonempty line reports a line only by having
    read it, with nothing but blank lines after it. -/
private theorem lastNonemptyLine_eq_some (lines : List String) (init : Option String)
    (marker : String)
    (h : lines.foldl (fun latest line => if line.trimAscii.isEmpty then latest else some line)
      init = some marker) :
    (init = some marker ∧ ∀ line ∈ lines, line.trimAscii.isEmpty = true) ∨
      ∃ before after, lines = before ++ marker :: after ∧
        ∀ line ∈ after, line.trimAscii.isEmpty = true := by
  induction lines generalizing init with
  | nil => exact Or.inl ⟨h, nofun⟩
  | cons line rest ih =>
    rw [List.foldl_cons] at h
    by_cases hblank : line.trimAscii.isEmpty = true
    · rw [if_pos hblank] at h
      rcases ih init h with ⟨hinit, hrest⟩ | ⟨before, after, hsplit, hafter⟩
      · refine Or.inl ⟨hinit, fun other hother => ?_⟩
        cases hother with
        | head => exact hblank
        | tail _ hmem => exact hrest other hmem
      · exact Or.inr ⟨line :: before, after, by rw [hsplit]; rfl, hafter⟩
    · rw [if_neg hblank] at h
      rcases ih (some line) h with ⟨hinit, hrest⟩ | ⟨before, after, hsplit, hafter⟩
      · exact Or.inr ⟨[], rest, by rw [Option.some.inj hinit]; rfl, hrest⟩
      · exact Or.inr ⟨line :: before, after, by rw [hsplit]; rfl, hafter⟩

/-- Accepting a run also requires the marker to be the *last* nonempty line the
    worker printed: it occurs in the output with only blank lines after it. A
    scan that reported the marker without reading it, or that ignored work
    printed after it, cannot satisfy this — that unmarked-early-exit and
    work-after-the-marker detection is the reason the protocol exists. -/
theorem completedSuccessfully_markerFinal {protocol : CompletionProtocol}
    {exitCode : UInt32} {stdout : String}
    (h : completedSuccessfully protocol exitCode stdout = true) :
    ∃ before after, stdout.splitOn "\n" = before ++ protocol.marker :: after ∧
      ∀ line ∈ after, line.trimAscii.isEmpty = true := by
  rw [completedSuccessfully, Bool.and_eq_true] at h
  have hmarker := eq_of_beq h.2
  rcases lastNonemptyLine_eq_some (stdout.splitOn "\n") none protocol.marker hmarker with
    ⟨hnone, -⟩ | hsplit
  · exact absurd hnone nofun
  · exact hsplit

/-! ### Replay dependency cone -/

/-- One replay step enqueues every stored constant the declaration's body uses:
    the inductive case's extra mutual-inductive siblings (below) are added to
    that set, never in place of it.

    This is a statement about the single step only. That `replayClosure` then
    walks those dependencies to a fixed point is not proved — it is a
    `partial def` worklist — and stays covered by the cross-package replay
    closure test in `Tests/VerifyLoadedTests.lean`. -/
theorem replayDependencies_superset (info : Lean.ConstantInfo) {name : Name}
    (h : name ∈ info.getUsedConstantsAsSet.toArray) :
    name ∈ replayDependencies info := by
  unfold replayDependencies
  cases info with
  | inductInfo inductiveInfo => exact Array.mem_append_left _ h
  | _ => exact h

/-- The other half of a replay step for an inductive: every member of the
    mutual block is enqueued as well, since replay reconstructs the block
    together. -/
theorem replayDependencies_inductiveSiblings {inductiveInfo : Lean.InductiveVal} {name : Name}
    (h : name ∈ inductiveInfo.all) :
    name ∈ replayDependencies (.inductInfo inductiveInfo) := by
  unfold replayDependencies
  exact Array.mem_append_right _ (List.mem_toArray.mpr h)

/-! ### Stored-body axiom propagation

`propagatedAxioms` decides which axioms each inspected declaration transitively
depends on, and the axiom-dependency arm reports exactly what it says. A miss
there is the one failure this gate cannot survive: not a wrong verdict a reader
would question, but an ordinary green run with an axiom sitting unreported in a
theorem's cone — the opposite of the claim `docs/overview.md` publishes.

The spec is stated over `axiomEdges`, the seam the code actually walks.
`Reaches` is an *inductive* relation rather than a bounded iteration, which is
what keeps this whole section batteries-only: completeness inducts on a
derivation the caller supplies, so it never asks how long a chain is and no
cardinality or pigeonhole argument enters. `Tl/Kernel/Reach.lean` needed
Mathlib for exactly the argument avoided here — that a fixed iteration count
suffices — and `Verify/` is outside ADR-0009's escape hatch, which is scoped to
`Reach.lean` and its dependents. -/

/-- `used` is named by the stored type or value of `user`, and `user` is one of
    the inspected constants. The membership side condition is built in, so a
    chain never leaves the map and no separate hypothesis is needed. -/
def UsesStored (cs : Std.HashMap Name Lean.ConstantInfo) (user used : Name) : Prop :=
  ∃ info, cs[user]? = some info ∧ used ∈ axiomEdges info

/-- Transitive reachability along stored-body edges, reflexive at the root. -/
inductive Reaches (cs : Std.HashMap Name Lean.ConstantInfo) : Name → Name → Prop where
  | refl (n : Name) : Reaches cs n n
  | step {n d a : Name} (edge : UsesStored cs n d) (rest : Reaches cs d a) : Reaches cs n a

/-- `a` is one of the inspected constants and is an axiom. -/
def IsAxiom (cs : Std.HashMap Name Lean.ConstantInfo) (a : Name) : Prop :=
  ∃ val, cs[a]? = some (.axiomInfo val)

/-! #### The rows only ever grow

Every statement below is about membership, never about the order of `pending`
or of a `reverse` bucket — those follow `Std.HashMap` iteration order, which
nothing pins and nothing needs to. -/

/-- `left`'s rows are contained in `right`'s, entry by entry. -/
def RowsGrew (left right : Std.HashMap Name (Std.HashSet Name)) : Prop :=
  ∀ n a : Name, a ∈ left[n]?.getD ({} : Std.HashSet Name) →
    a ∈ right[n]?.getD ({} : Std.HashSet Name)

theorem RowsGrew.refl (m : Std.HashMap Name (Std.HashSet Name)) : RowsGrew m m :=
  fun _ _ h => h

theorem RowsGrew.trans {x y z : Std.HashMap Name (Std.HashSet Name)}
    (h₁ : RowsGrew x y) (h₂ : RowsGrew y z) : RowsGrew x z :=
  fun n a h => h₂ n a (h₁ n a h)

/-- The `rfl`-level equation that makes the step splittable: without it `split`
    cannot see past the `let`-bound `existing`. Same device as
    `repeatedLandmarkStep_eq` above. -/
theorem propagateStep_eq (axiomName : Name) (acc : Std.HashMap Name (Std.HashSet Name))
    (pending : Array (Name × Name)) (dependent : Name) :
    propagateStep axiomName (acc, pending) dependent =
      (if (acc[dependent]?.getD ({} : Std.HashSet Name)).contains axiomName then (acc, pending)
        else (acc.insert dependent ((acc[dependent]?.getD ({} : Std.HashSet Name)).insert axiomName),
          pending.push (dependent, axiomName))) := rfl

theorem propagateStep_grew (axiomName : Name)
    (state : Std.HashMap Name (Std.HashSet Name) × Array (Name × Name)) (dependent : Name) :
    RowsGrew state.1 (propagateStep axiomName state dependent).1 := by
  obtain ⟨acc, pending⟩ := state
  intro n a hmem
  rw [propagateStep_eq]
  by_cases hcontains :
      (acc[dependent]?.getD ({} : Std.HashSet Name)).contains axiomName = true
  · rw [if_pos hcontains]; exact hmem
  · rw [if_neg hcontains]
    show a ∈ (acc.insert dependent _)[n]?.getD ({} : Std.HashSet Name)
    rw [Std.HashMap.getElem?_insert]
    cases hbeq : dependent == n with
    | false => rw [if_neg nofun]; exact hmem
    | true =>
      rw [if_pos rfl, Option.getD_some]
      refine Std.HashSet.mem_insert.mpr (Or.inr ?_)
      rw [eq_of_beq hbeq]
      exact hmem

theorem foldl_propagateStep_grew (axiomName : Name) (deps : Array Name)
    (state : Std.HashMap Name (Std.HashSet Name) × Array (Name × Name)) :
    RowsGrew state.1 (deps.foldl (propagateStep axiomName) state).1 := by
  rw [← Array.foldl_toList]
  induction deps.toList generalizing state with
  | nil => exact RowsGrew.refl _
  | cons dep rest ih =>
    rw [List.foldl_cons]
    exact RowsGrew.trans (propagateStep_grew axiomName state dep) (ih _)

/-- A drained run never loses a row it had. This is the shape every
    drain-level induction takes: structural on fuel, `split` on the cursor
    test. -/
theorem drainWorklist_grew (reverse : Std.HashMap Name (Array Name)) :
    ∀ (fuel cursor : Nat) (acc : Std.HashMap Name (Std.HashSet Name))
      (pending : Array (Name × Name)) (result : Std.HashMap Name (Std.HashSet Name)),
      drainWorklist reverse fuel cursor acc pending = some result → RowsGrew acc result
  | 0, _, _, _, _, h => by rw [drainWorklist] at h; exact absurd h nofun
  | fuel + 1, cursor, acc, pending, result, h => by
    rw [drainWorklist] at h
    split at h
    · next hlt =>
      refine RowsGrew.trans ?_ (drainWorklist_grew reverse fuel (cursor + 1) _ _ result h)
      exact foldl_propagateStep_grew _ _ (acc, pending)
    · next => rw [Option.some.inj h]; exact RowsGrew.refl _

/-! #### The seed

Each projection of `seedStep` is pinned by its own `rfl`-level equation, so the
fold inductions below never have to see through the shared `let`. -/

theorem seedStep_axiomsByName (seed : PropagationSeed) (name : Name)
    (info : Lean.ConstantInfo) :
    (seedStep seed name info).axiomsByName =
      (match info with
        | .axiomInfo _ => seed.axiomsByName.alter name fun row =>
            some ((row.getD {}).insert name)
        | _ => seed.axiomsByName) := by
  unfold seedStep
  cases info <;> rfl

theorem seedStep_pending (seed : PropagationSeed) (name : Name) (info : Lean.ConstantInfo) :
    (seedStep seed name info).pending =
      (match info with
        | .axiomInfo _ => seed.pending.push (name, name)
        | _ => seed.pending) := by
  unfold seedStep
  cases info <;> rfl

theorem seedStep_reverse (seed : PropagationSeed) (name : Name) (info : Lean.ConstantInfo) :
    (seedStep seed name info).reverse =
      (axiomEdges info).foldl (init := seed.reverse) (fun reverse dependency =>
        reverse.alter dependency fun dependents => some ((dependents.getD #[]).push name)) := by
  unfold seedStep
  cases info <;> rfl

/-- Every row the seed carries is an axiom's own row. -/
theorem seed_rows_sound {cs : Std.HashMap Name Lean.ConstantInfo} {n a : Name}
    (h : a ∈ (propagationSeed cs).axiomsByName[n]?.getD ({} : Std.HashSet Name)) :
    n = a ∧ IsAxiom cs a := by
  have general : ∀ (l : List (Name × Lean.ConstantInfo)) (seed : PropagationSeed),
      (∀ p ∈ l, cs[p.1]? = some p.2) →
      (∀ m b : Name, b ∈ seed.axiomsByName[m]?.getD ({} : Std.HashSet Name) →
        m = b ∧ IsAxiom cs b) →
      ∀ m b : Name,
        b ∈ (l.foldl (fun s p => seedStep s p.1 p.2) seed).axiomsByName[m]?.getD
          ({} : Std.HashSet Name) → m = b ∧ IsAxiom cs b := by
    intro l
    induction l with
    | nil => intro seed _ hseed m b hb; exact hseed m b hb
    | cons p rest ih =>
      intro seed hlist hseed m b hb
      refine ih _ (fun q hq => hlist q (List.mem_cons_of_mem _ hq)) ?_ m b hb
      intro m' b' hb'
      rw [seedStep_axiomsByName] at hb'
      cases hinfo : p.2 with
      | axiomInfo val =>
        rw [hinfo] at hb'
        simp only at hb'
        rw [Std.HashMap.getElem?_alter] at hb'
        cases hbeq : p.1 == m' with
        | false => rw [if_neg (by rw [hbeq]; exact nofun)] at hb'; exact hseed m' b' hb'
        | true =>
          rw [if_pos (by rw [hbeq])] at hb'
          rw [Option.getD_some] at hb'
          rcases Std.HashSet.mem_insert.mp hb' with heq | hold
          · refine ⟨?_, ?_⟩
            · rw [← eq_of_beq hbeq, eq_of_beq heq]
            · refine ⟨val, ?_⟩
              rw [← eq_of_beq heq, hlist p (List.mem_cons_self ..), hinfo]
          · exact hseed m' b' (by rw [← eq_of_beq hbeq]; exact hold)
      | _ => rw [hinfo] at hb'; exact hseed m' b' hb'
  refine general cs.toList {} (fun p hp => ?_) (fun m b hb => ?_) n a ?_
  · exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
  · exact absurd hb (by
      simp only [Std.HashMap.getElem?_empty, Option.getD_none,
        Std.HashSet.not_mem_empty, not_false_eq_true])
  · rw [propagationSeed, Std.HashMap.fold_eq_foldl_toList] at h
    exact h

/-- Every seeded worklist pair is an axiom paired with itself. -/
theorem seed_pending_sound {cs : Std.HashMap Name Lean.ConstantInfo} {d x : Name}
    (h : (d, x) ∈ (propagationSeed cs).pending) : d = x ∧ IsAxiom cs x := by
  have general : ∀ (l : List (Name × Lean.ConstantInfo)) (seed : PropagationSeed),
      (∀ p ∈ l, cs[p.1]? = some p.2) →
      (∀ e f : Name, (e, f) ∈ seed.pending → e = f ∧ IsAxiom cs f) →
      ∀ e f : Name,
        (e, f) ∈ (l.foldl (fun s p => seedStep s p.1 p.2) seed).pending →
          e = f ∧ IsAxiom cs f := by
    intro l
    induction l with
    | nil => intro seed _ hseed e f hf; exact hseed e f hf
    | cons p rest ih =>
      intro seed hlist hseed e f hf
      refine ih _ (fun q hq => hlist q (List.mem_cons_of_mem _ hq)) ?_ e f hf
      intro e' f' hf'
      rw [seedStep_pending] at hf'
      cases hinfo : p.2 with
      | axiomInfo val =>
        rw [hinfo] at hf'
        simp only at hf'
        rcases Array.mem_push.mp hf' with hold | hnew
        · exact hseed e' f' hold
        · rw [Prod.mk.injEq] at hnew
          obtain ⟨hfst, hsnd⟩ := hnew
          refine ⟨hfst.trans hsnd.symm, val, ?_⟩
          rw [hsnd, hlist p (List.mem_cons_self ..), hinfo]
      | _ => rw [hinfo] at hf'; exact hseed e' f' hf'
  refine general cs.toList {} (fun p hp => ?_) (fun e f hf => ?_) d x ?_
  · exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
  · exact absurd hf (by
      simp only [Array.not_mem_empty, not_false_eq_true])
  · rw [propagationSeed, Std.HashMap.fold_eq_foldl_toList] at h
    exact h

/-- One constant's contribution to the reverse map, over the edge list: an entry
    appears only for a dependency that constant's stored body actually names. -/
private theorem alterFold_reverse_sound_list (name : Name) :
    ∀ (edges : List Name) (rev : Std.HashMap Name (Array Name)) (d m : Name),
      m ∈ (edges.foldl (init := rev) (fun r dependency =>
          r.alter dependency fun dependents => some ((dependents.getD #[]).push name)))[d]?.getD #[] →
        m ∈ rev[d]?.getD #[] ∨ (m = name ∧ d ∈ edges)
  | [], _, _, _, h => Or.inl h
  | edge :: rest, rev, d, m, h => by
    rw [List.foldl_cons] at h
    rcases alterFold_reverse_sound_list name rest _ d m h with hprev | hnew
    · rw [Std.HashMap.getElem?_alter] at hprev
      cases hbeq : edge == d with
      | false => rw [if_neg (by rw [hbeq]; exact nofun)] at hprev; exact Or.inl hprev
      | true =>
        have hed : edge = d := eq_of_beq hbeq
        subst hed
        rw [if_pos (by rw [hbeq]), Option.getD_some] at hprev
        rcases Array.mem_push.mp hprev with hold | hlast
        · exact Or.inl hold
        · exact Or.inr ⟨hlast, List.mem_cons_self ..⟩
    · exact Or.inr ⟨hnew.1, List.mem_cons_of_mem _ hnew.2⟩

/-- The same, at the `Array` the code actually folds over. -/
private theorem alterFold_reverse_sound (name : Name) (edges : Array Name)
    (rev : Std.HashMap Name (Array Name)) (d m : Name)
    (h : m ∈ (edges.foldl (init := rev) (fun r dependency =>
        r.alter dependency fun dependents => some ((dependents.getD #[]).push name)))[d]?.getD #[]) :
    m ∈ rev[d]?.getD #[] ∨ (m = name ∧ d ∈ edges) := by
  rw [← Array.foldl_toList] at h
  rcases alterFold_reverse_sound_list name edges.toList rev d m h with hold | hnew
  · exact Or.inl hold
  · exact Or.inr ⟨hnew.1, Array.mem_def.mpr hnew.2⟩

/-- A reverse-edge entry is justified: if `n` is listed under `d`, then `n` is
    one of the inspected constants and its stored body names `d`. -/
theorem reverse_sound {cs : Std.HashMap Name Lean.ConstantInfo} {d n : Name}
    (h : n ∈ (propagationSeed cs).reverse[d]?.getD #[]) : UsesStored cs n d := by
  have general : ∀ (l : List (Name × Lean.ConstantInfo)) (seed : PropagationSeed),
      (∀ p ∈ l, cs[p.1]? = some p.2) →
      (∀ e m : Name, m ∈ seed.reverse[e]?.getD #[] → UsesStored cs m e) →
      ∀ e m : Name,
        m ∈ (l.foldl (fun s p => seedStep s p.1 p.2) seed).reverse[e]?.getD #[] →
          UsesStored cs m e := by
    intro l
    induction l with
    | nil => intro seed _ hseed e m hm; exact hseed e m hm
    | cons p rest ih =>
      intro seed hlist hseed e m hm
      refine ih _ (fun q hq => hlist q (List.mem_cons_of_mem _ hq)) ?_ e m hm
      intro e' m' hm'
      rw [seedStep_reverse] at hm'
      rcases alterFold_reverse_sound p.1 (axiomEdges p.2) seed.reverse e' m' hm' with hold | hnew
      · exact hseed e' m' hold
      · exact ⟨p.2, by rw [hnew.1]; exact hlist p (List.mem_cons_self ..), hnew.2⟩
  refine general cs.toList {} (fun p hp => ?_) (fun e m hm => ?_) d n ?_
  · exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
  · exact absurd hm (by
      simp only [Std.HashMap.getElem?_empty, Option.getD_none,
        Array.not_mem_empty, not_false_eq_true])
  · rw [propagationSeed, Std.HashMap.fold_eq_foldl_toList] at h
    exact h

/-! #### Soundness — nothing is filed that is not there

The invariant is carried by the drain: every recorded row and every queued pair
names a real axiom that really is reachable from the declaration it is filed
under. It holds at fuel exhaustion too, which is why this half needs neither
the drained exit nor the reverse map's completeness. -/

/-- Both halves of the drain invariant. -/
structure PropagationSound (cs : Std.HashMap Name Lean.ConstantInfo)
    (acc : Std.HashMap Name (Std.HashSet Name)) (pending : Array (Name × Name)) : Prop where
  rows : ∀ n a : Name, a ∈ acc[n]?.getD ({} : Std.HashSet Name) → IsAxiom cs a ∧ Reaches cs n a
  queued : ∀ d x : Name, (d, x) ∈ pending → IsAxiom cs x ∧ Reaches cs d x

/-- One propagation step preserves it: the queued pair supplies the tail of the
    chain, the reverse edge supplies its first hop. -/
private theorem propagateStep_sound {cs : Std.HashMap Name Lean.ConstantInfo}
    {acc : Std.HashMap Name (Std.HashSet Name)} {pending : Array (Name × Name)}
    {dependency axiomName dependent : Name}
    (hinv : PropagationSound cs acc pending)
    (hchain : IsAxiom cs axiomName ∧ Reaches cs dependency axiomName)
    (hedge : UsesStored cs dependent dependency) :
    PropagationSound cs (propagateStep axiomName (acc, pending) dependent).1
      (propagateStep axiomName (acc, pending) dependent).2 := by
  have hreach : Reaches cs dependent axiomName := Reaches.step hedge hchain.2
  rw [propagateStep_eq]
  by_cases hcontains :
      (acc[dependent]?.getD ({} : Std.HashSet Name)).contains axiomName = true
  · rw [if_pos hcontains]; exact hinv
  · rw [if_neg hcontains]
    refine ⟨fun n a hmem => ?_, fun d x hq => ?_⟩
    · rw [Std.HashMap.getElem?_insert] at hmem
      cases hbeq : dependent == n with
      | false => rw [if_neg (by rw [hbeq]; exact nofun)] at hmem; exact hinv.rows n a hmem
      | true =>
        rw [if_pos (by rw [hbeq]), Option.getD_some] at hmem
        have hdn : dependent = n := eq_of_beq hbeq
        rcases Std.HashSet.mem_insert.mp hmem with heq | hold
        · rw [← eq_of_beq heq]
          exact ⟨hchain.1, hdn ▸ hreach⟩
        · exact hinv.rows n a (hdn ▸ hold)
    · rcases Array.mem_push.mp hq with hold | hnew
      · exact hinv.queued d x hold
      · rw [Prod.mk.injEq] at hnew
        obtain ⟨hfst, hsnd⟩ := hnew
        rw [hfst, hsnd]
        exact ⟨hchain.1, hreach⟩

private theorem foldl_propagateStep_sound {cs : Std.HashMap Name Lean.ConstantInfo}
    {dependency axiomName : Name}
    (hchain : IsAxiom cs axiomName ∧ Reaches cs dependency axiomName) :
    ∀ (deps : List Name) (acc : Std.HashMap Name (Std.HashSet Name))
      (pending : Array (Name × Name)),
      (∀ m ∈ deps, UsesStored cs m dependency) →
      PropagationSound cs acc pending →
      PropagationSound cs (deps.foldl (propagateStep axiomName) (acc, pending)).1
        (deps.foldl (propagateStep axiomName) (acc, pending)).2
  | [], _, _, _, hinv => hinv
  | dep :: rest, acc, pending, hedges, hinv => by
    rw [List.foldl_cons]
    have hstep := propagateStep_sound hinv hchain (hedges dep (List.mem_cons_self ..))
    exact foldl_propagateStep_sound hchain rest _ _
      (fun m hm => hedges m (List.mem_cons_of_mem _ hm)) hstep

/-- The drain preserves the invariant, whether it runs out of fuel or drains. -/
private theorem drainWorklist_sound {cs : Std.HashMap Name Lean.ConstantInfo}
    (hrev : ∀ d m : Name, m ∈ (propagationSeed cs).reverse[d]?.getD #[] → UsesStored cs m d) :
    ∀ (fuel cursor : Nat) (acc : Std.HashMap Name (Std.HashSet Name))
      (pending : Array (Name × Name)) (result : Std.HashMap Name (Std.HashSet Name)),
      PropagationSound cs acc pending →
      drainWorklist (propagationSeed cs).reverse fuel cursor acc pending = some result →
      ∀ n a : Name, a ∈ result[n]?.getD ({} : Std.HashSet Name) → IsAxiom cs a ∧ Reaches cs n a
  | 0, _, _, _, _, _, h => by rw [drainWorklist] at h; exact absurd h nofun
  | fuel + 1, cursor, acc, pending, result, hinv, h => by
    rw [drainWorklist] at h
    split at h
    · next hlt =>
      refine drainWorklist_sound hrev fuel (cursor + 1) _ _ result ?_ h
      have hqueued := hinv.queued (pending[cursor]'hlt).1 (pending[cursor]'hlt).2
        (Array.getElem_mem hlt)
      rw [← Array.foldl_toList]
      exact foldl_propagateStep_sound hqueued _ acc pending
        (fun m hm => hrev _ m (Array.mem_def.mpr hm)) hinv
    · next => rw [← Option.some.inj h]; exact hinv.rows

/-- **No false positives.** Every axiom the gate files under a declaration is a
    real axiom, and really is reachable from that declaration along stored-body
    edges — so an axiom row a reviewer acts on is never an artefact of the
    propagation. -/
theorem propagatedAxioms_sound {cs : Std.HashMap Name Lean.ConstantInfo}
    {result : Std.HashMap Name (Std.HashSet Name)} {n a : Name}
    (hrun : propagatedAxioms cs = some result)
    (hmem : a ∈ result[n]?.getD ({} : Std.HashSet Name)) :
    IsAxiom cs a ∧ Reaches cs n a := by
  rw [propagatedAxioms] at hrun
  refine drainWorklist_sound (fun _ _ hm => reverse_sound hm) _ 0
    (propagationSeed cs).axiomsByName (propagationSeed cs).pending result ?_ hrun n a hmem
  refine ⟨fun m b hb => ?_, fun d x hq => ?_⟩
  · obtain ⟨hmb, haxiom⟩ := seed_rows_sound hb
    exact ⟨haxiom, hmb ▸ Reaches.refl _⟩
  · obtain ⟨hdx, haxiom⟩ := seed_pending_sound hq
    exact ⟨haxiom, hdx ▸ Reaches.refl _⟩

private theorem foldl_propagateStep_grew_list (axiomName : Name) :
    ∀ (deps : List Name) (state : Std.HashMap Name (Std.HashSet Name) × Array (Name × Name)),
      RowsGrew state.1 (deps.foldl (propagateStep axiomName) state).1
  | [], _ => RowsGrew.refl _
  | dep :: rest, state => by
    rw [List.foldl_cons]
    exact RowsGrew.trans (propagateStep_grew axiomName state dep)
      (foldl_propagateStep_grew_list axiomName rest _)

/-- What one step changes: the queue grows only by appending, and any row it
    adds is queued in exactly that appended part. Stated in the shape the fold
    below composes with. -/
private theorem propagateStep_shape (axiomName : Name)
    (acc : Std.HashMap Name (Std.HashSet Name)) (pending : Array (Name × Name))
    (dependent : Name) :
    ∃ extra : List (Name × Name),
      (propagateStep axiomName (acc, pending) dependent).2.toList
          = pending.toList ++ extra ∧
      ∀ n a : Name,
        a ∈ (propagateStep axiomName (acc, pending) dependent).1[n]?.getD
          ({} : Std.HashSet Name) →
          a ∈ acc[n]?.getD ({} : Std.HashSet Name) ∨ (n, a) ∈ extra := by
  rw [propagateStep_eq]
  by_cases hcontains :
      (acc[dependent]?.getD ({} : Std.HashSet Name)).contains axiomName = true
  · rw [if_pos hcontains]
    exact ⟨[], by rw [List.append_nil], fun _ _ h => Or.inl h⟩
  · rw [if_neg hcontains]
    refine ⟨[(dependent, axiomName)], Array.toList_push, fun n a h => ?_⟩
    rw [Std.HashMap.getElem?_insert] at h
    cases hbeq : dependent == n with
    | false => rw [if_neg (by rw [hbeq]; exact nofun)] at h; exact Or.inl h
    | true =>
      rw [if_pos (by rw [hbeq]), Option.getD_some] at h
      have hdn : dependent = n := eq_of_beq hbeq
      rcases Std.HashSet.mem_insert.mp h with heq | hold
      · exact Or.inr (List.mem_singleton.mpr (by rw [hdn, eq_of_beq heq]))
      · exact Or.inl (hdn ▸ hold)

/-- The same for a whole fold over a dependent list. -/
private theorem foldl_propagateStep_shape (axiomName : Name) :
    ∀ (deps : List Name) (acc : Std.HashMap Name (Std.HashSet Name))
      (pending : Array (Name × Name)),
      ∃ extra : List (Name × Name),
        (deps.foldl (propagateStep axiomName) (acc, pending)).2.toList
            = pending.toList ++ extra ∧
        ∀ n a : Name,
          a ∈ (deps.foldl (propagateStep axiomName) (acc, pending)).1[n]?.getD
            ({} : Std.HashSet Name) →
            a ∈ acc[n]?.getD ({} : Std.HashSet Name) ∨ (n, a) ∈ extra
  | [], acc, pending => ⟨[], by rw [List.foldl_nil, List.append_nil], fun _ _ h => Or.inl h⟩
  | dep :: rest, acc, pending => by
    rw [List.foldl_cons]
    obtain ⟨head, hheadList, hheadRows⟩ := propagateStep_shape axiomName acc pending dep
    obtain ⟨tail, htailList, htailRows⟩ :=
      foldl_propagateStep_shape axiomName rest
        (propagateStep axiomName (acc, pending) dep).1
        (propagateStep axiomName (acc, pending) dep).2
    refine ⟨head ++ tail, by rw [htailList, hheadList, List.append_assoc], fun n a hrow => ?_⟩
    rcases htailRows n a hrow with hprev | hnew
    · rcases hheadRows n a hprev with hold | hhead
      · exact Or.inl hold
      · exact Or.inr (List.mem_append_left _ hhead)
    · exact Or.inr (List.mem_append_right _ hnew)

/-- After the fold, every dependent in the list carries the axiom. -/
private theorem foldl_propagateStep_covers (axiomName : Name) :
    ∀ (deps : List Name) (acc : Std.HashMap Name (Std.HashSet Name))
      (pending : Array (Name × Name)) (m : Name), m ∈ deps →
      axiomName ∈ (deps.foldl (propagateStep axiomName) (acc, pending)).1[m]?.getD
        ({} : Std.HashSet Name)
  | dep :: rest, acc, pending, m, hm => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hrest
    · -- the head step puts it in, and the rest of the fold only grows rows
      refine foldl_propagateStep_grew_list axiomName rest
        (propagateStep axiomName (acc, pending) m) m axiomName ?_
      rw [propagateStep_eq]
      by_cases hcontains :
          (acc[m]?.getD ({} : Std.HashSet Name)).contains axiomName = true
      · rw [if_pos hcontains]
        exact Std.HashSet.contains_iff_mem.mp hcontains
      · rw [if_neg hcontains]
        show axiomName ∈ (acc.insert m _)[m]?.getD ({} : Std.HashSet Name)
        rw [Std.HashMap.getElem?_insert, if_pos (beq_self_eq_true m), Option.getD_some]
        exact Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true axiomName))
    · exact foldl_propagateStep_covers axiomName rest _ _ m hrest

/-- Reverse buckets only grow across one constant's contribution. -/
private theorem alterFold_reverse_grew_list (name : Name) :
    ∀ (edges : List Name) (rev : Std.HashMap Name (Array Name)) (d m : Name),
      m ∈ rev[d]?.getD #[] →
      m ∈ (edges.foldl (init := rev) (fun r dependency =>
        r.alter dependency fun dependents => some ((dependents.getD #[]).push name)))[d]?.getD #[]
  | [], _, _, _, h => h
  | edge :: rest, rev, d, m, h => by
    rw [List.foldl_cons]
    refine alterFold_reverse_grew_list name rest _ d m ?_
    rw [Std.HashMap.getElem?_alter]
    cases hbeq : edge == d with
    | false => rw [if_neg nofun]; exact h
    | true =>
      rw [if_pos rfl, Option.getD_some]
      have hed : edge = d := eq_of_beq hbeq
      exact Array.mem_push.mpr (Or.inl (hed ▸ h))

/-- Every edge of a constant's stored body lands in that dependency's bucket. -/
private theorem alterFold_reverse_complete_list (name : Name) :
    ∀ (edges : List Name) (rev : Std.HashMap Name (Array Name)) (d : Name), d ∈ edges →
      name ∈ (edges.foldl (init := rev) (fun r dependency =>
        r.alter dependency fun dependents => some ((dependents.getD #[]).push name)))[d]?.getD #[]
  | edge :: rest, rev, d, hd => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hd with rfl | hrest
    · refine alterFold_reverse_grew_list name rest _ d name ?_
      rw [Std.HashMap.getElem?_alter, if_pos (beq_self_eq_true d), Option.getD_some]
      exact Array.mem_push.mpr (Or.inr rfl)
    · exact alterFold_reverse_complete_list name rest _ d hrest

/-- Rows and worklist entries are seeded together, so a seeded row is queued. -/
theorem seed_rows_pending {cs : Std.HashMap Name Lean.ConstantInfo} {n a : Name}
    (h : a ∈ (propagationSeed cs).axiomsByName[n]?.getD ({} : Std.HashSet Name)) :
    (n, a) ∈ (propagationSeed cs).pending := by
  have general : ∀ (l : List (Name × Lean.ConstantInfo)) (seed : PropagationSeed),
      (∀ m b : Name, b ∈ seed.axiomsByName[m]?.getD ({} : Std.HashSet Name) →
        (m, b) ∈ seed.pending) →
      ∀ m b : Name,
        b ∈ (l.foldl (fun s p => seedStep s p.1 p.2) seed).axiomsByName[m]?.getD
          ({} : Std.HashSet Name) →
          (m, b) ∈ (l.foldl (fun s p => seedStep s p.1 p.2) seed).pending := by
    intro l
    induction l with
    | nil => intro seed hseed m b hb; exact hseed m b hb
    | cons p rest ih =>
      intro seed hseed m b hb
      refine ih _ ?_ m b hb
      intro m' b' hb'
      rw [seedStep_axiomsByName] at hb'
      rw [seedStep_pending]
      cases hinfo : p.2 with
      | axiomInfo val =>
        rw [hinfo] at hb'
        simp only at hb' ⊢
        rw [Std.HashMap.getElem?_alter] at hb'
        cases hbeq : p.1 == m' with
        | false =>
          rw [if_neg (by rw [hbeq]; exact nofun)] at hb'
          exact Array.mem_push.mpr (Or.inl (hseed m' b' hb'))
        | true =>
          rw [if_pos (by rw [hbeq]), Option.getD_some] at hb'
          have hpm : p.1 = m' := eq_of_beq hbeq
          rcases Std.HashSet.mem_insert.mp hb' with heq | hold
          · exact Array.mem_push.mpr (Or.inr (by rw [← hpm, ← eq_of_beq heq]))
          · exact Array.mem_push.mpr (Or.inl
              (hseed m' b' (by rw [← hpm]; exact hold)))
      | _ =>
        rw [hinfo] at hb'
        exact hseed m' b' hb'
  rw [propagationSeed, Std.HashMap.fold_eq_foldl_toList] at h ⊢
  exact general cs.toList {} (fun m b hb => absurd hb (by
    simp only [Std.HashMap.getElem?_empty, Option.getD_none,
      Std.HashSet.not_mem_empty, not_false_eq_true])) n a h

/-- Reverse buckets only grow across the whole seed fold. -/
private theorem seedFold_reverse_grew :
    ∀ (l : List (Name × Lean.ConstantInfo)) (seed : PropagationSeed) (d m : Name),
      m ∈ seed.reverse[d]?.getD #[] →
      m ∈ (l.foldl (fun s p => seedStep s p.1 p.2) seed).reverse[d]?.getD #[]
  | [], _, _, _, h => h
  | p :: rest, seed, d, m, h => by
    rw [List.foldl_cons]
    refine seedFold_reverse_grew rest _ d m ?_
    rw [seedStep_reverse, ← Array.foldl_toList]
    exact alterFold_reverse_grew_list p.1 (axiomEdges p.2).toList seed.reverse d m h

/-- Rows only grow across the whole seed fold. -/
private theorem seedFold_rows_grew :
    ∀ (l : List (Name × Lean.ConstantInfo)) (seed : PropagationSeed) (n a : Name),
      a ∈ seed.axiomsByName[n]?.getD ({} : Std.HashSet Name) →
      a ∈ (l.foldl (fun s p => seedStep s p.1 p.2) seed).axiomsByName[n]?.getD
        ({} : Std.HashSet Name)
  | [], _, _, _, h => h
  | p :: rest, seed, n, a, h => by
    rw [List.foldl_cons]
    refine seedFold_rows_grew rest _ n a ?_
    rw [seedStep_axiomsByName]
    cases hinfo : p.2 with
    | axiomInfo val =>
      simp only
      rw [Std.HashMap.getElem?_alter]
      cases hbeq : p.1 == n with
      | false => rw [if_neg nofun]; exact h
      | true =>
        rw [if_pos rfl, Option.getD_some]
        refine Std.HashSet.mem_insert.mpr (Or.inr ?_)
        rw [← eq_of_beq hbeq] at h
        exact h
    | _ => exact h

/-- **Every reverse edge is recorded.** If `n`'s stored body names `d`, then `n`
    is listed under `d`. The completeness companion to `reverse_sound`. -/
theorem reverse_complete {cs : Std.HashMap Name Lean.ConstantInfo} {n d : Name}
    (h : UsesStored cs n d) : n ∈ (propagationSeed cs).reverse[d]?.getD #[] := by
  obtain ⟨info, hfind, hedge⟩ := h
  have hmem : (n, info) ∈ cs.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hfind
  rw [propagationSeed, Std.HashMap.fold_eq_foldl_toList]
  have general : ∀ (l : List (Name × Lean.ConstantInfo)) (seed : PropagationSeed),
      (n, info) ∈ l →
      n ∈ (l.foldl (fun s p => seedStep s p.1 p.2) seed).reverse[d]?.getD #[] := by
    intro l
    induction l with
    | nil => intro _ hl; exact absurd hl (List.not_mem_nil)
    | cons p rest ih =>
      intro seed hl
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hl with rfl | hrest
      · refine seedFold_reverse_grew rest _ d n ?_
        rw [seedStep_reverse, ← Array.foldl_toList]
        exact alterFold_reverse_complete_list n (axiomEdges info).toList seed.reverse d
          (Array.mem_def.mp hedge)
      · exact ih _ hrest
  exact general cs.toList {} hmem

/-- **Every axiom seeds its own row.** The completeness companion to
    `seed_rows_sound`. -/
theorem seed_rows_complete {cs : Std.HashMap Name Lean.ConstantInfo} {a : Name}
    (h : IsAxiom cs a) : a ∈ (propagationSeed cs).axiomsByName[a]?.getD ({} : Std.HashSet Name) := by
  obtain ⟨val, hfind⟩ := h
  have hmem : (a, Lean.ConstantInfo.axiomInfo val) ∈ cs.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hfind
  rw [propagationSeed, Std.HashMap.fold_eq_foldl_toList]
  have general : ∀ (l : List (Name × Lean.ConstantInfo)) (seed : PropagationSeed),
      (a, Lean.ConstantInfo.axiomInfo val) ∈ l →
      a ∈ (l.foldl (fun s p => seedStep s p.1 p.2) seed).axiomsByName[a]?.getD
        ({} : Std.HashSet Name) := by
    intro l
    induction l with
    | nil => intro _ hl; exact absurd hl (List.not_mem_nil)
    | cons p rest ih =>
      intro seed hl
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hl with rfl | hrest
      · refine seedFold_rows_grew rest _ a a ?_
        rw [seedStep_axiomsByName]
        simp only
        rw [Std.HashMap.getElem?_alter, if_pos (beq_self_eq_true a), Option.getD_some]
        exact Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true a))
      · exact ih _ hrest
  exact general cs.toList {} hmem

/-- Every recorded pair is either already pushed to all of its dependents, or
    still waiting in the unprocessed tail of the worklist. -/
def Frontier (reverse : Std.HashMap Name (Array Name))
    (acc : Std.HashMap Name (Std.HashSet Name)) (pending : Array (Name × Name))
    (cursor : Nat) : Prop :=
  ∀ n a : Name, a ∈ acc[n]?.getD ({} : Std.HashSet Name) →
    (∀ m ∈ reverse[n]?.getD #[], a ∈ acc[m]?.getD ({} : Std.HashSet Name)) ∨
      (n, a) ∈ pending.toList.drop cursor

/-- At a drained exit the tail is empty, so the first disjunct holds outright:
    the result is closed under reverse edges. -/
private theorem drainWorklist_closed (reverse : Std.HashMap Name (Array Name)) :
    ∀ (fuel cursor : Nat) (acc : Std.HashMap Name (Std.HashSet Name))
      (pending : Array (Name × Name)) (result : Std.HashMap Name (Std.HashSet Name)),
      Frontier reverse acc pending cursor →
      drainWorklist reverse fuel cursor acc pending = some result →
      ∀ n a : Name, a ∈ result[n]?.getD ({} : Std.HashSet Name) →
        ∀ m ∈ reverse[n]?.getD #[], a ∈ result[m]?.getD ({} : Std.HashSet Name)
  | 0, _, _, _, _, _, h => by rw [drainWorklist] at h; exact absurd h nofun
  | fuel + 1, cursor, acc, pending, result, hfront, h => by
    rw [drainWorklist] at h
    split at h
    · next hlt =>
      refine drainWorklist_closed reverse fuel (cursor + 1) _ _ result ?_ h
      obtain ⟨extra, hextra, hrows⟩ :=
        foldl_propagateStep_shape (pending[cursor]'hlt).2
          (reverse[(pending[cursor]'hlt).1]?.getD #[]).toList acc pending
      have hdrop : List.drop (cursor + 1) (pending.toList ++ extra)
          = List.drop (cursor + 1) pending.toList ++ extra :=
        List.drop_append_of_le_length (by rw [Array.length_toList]; exact hlt)
      intro n a ha
      rw [← Array.foldl_toList] at ha
      rcases hrows n a ha with hold | hnew
      · rcases hfront n a hold with hall | hpend
        · left
          intro m hm
          rw [← Array.foldl_toList]
          exact foldl_propagateStep_grew_list _ _ (acc, pending) m a (hall m hm)
        · -- the pair is in the unprocessed tail; either it is the one at the
          -- cursor (now discharged by the fold) or it is still further along
          rw [List.drop_eq_getElem_cons (by rw [Array.length_toList]; exact hlt)] at hpend
          rcases List.mem_cons.mp hpend with hhead | htail
          · left
            intro m hm
            rw [← Array.foldl_toList]
            have hn : n = (pending[cursor]'hlt).1 := by
              rw [← Array.getElem_toList (i := cursor)] at *
              exact congrArg Prod.fst hhead
            have ha2 : a = (pending[cursor]'hlt).2 := by
              rw [← Array.getElem_toList (i := cursor)] at *
              exact congrArg Prod.snd hhead
            rw [ha2]
            refine foldl_propagateStep_covers _ _ acc pending m ?_
            rw [← hn]
            exact Array.mem_def.mp hm
          · right
            rw [← Array.foldl_toList, hextra, hdrop]
            exact List.mem_append_left _ htail
      · right
        rw [← Array.foldl_toList, hextra, hdrop]
        exact List.mem_append_right _ hnew
    · next hge =>
      rw [← Option.some.inj h]
      intro n a ha m hm
      rcases hfront n a ha with hall | hpend
      · exact hall m hm
      · exact absurd (List.drop_eq_nil_iff.mpr (by
          rw [Array.length_toList]; exact Nat.le_of_not_lt hge) ▸ hpend) (List.not_mem_nil)

/-- **A drained result is closed under reverse edges.** If `d` carries an axiom
    and `n`'s stored body names `d`, then `n` carries it too. -/
theorem propagatedAxioms_closed {cs : Std.HashMap Name Lean.ConstantInfo}
    {result : Std.HashMap Name (Std.HashSet Name)} {d n a : Name}
    (hrun : propagatedAxioms cs = some result)
    (hmem : a ∈ result[d]?.getD ({} : Std.HashSet Name))
    (hrev : n ∈ (propagationSeed cs).reverse[d]?.getD #[]) :
    a ∈ result[n]?.getD ({} : Std.HashSet Name) := by
  rw [propagatedAxioms] at hrun
  refine drainWorklist_closed (propagationSeed cs).reverse _ 0
    (propagationSeed cs).axiomsByName (propagationSeed cs).pending result ?_ hrun d a hmem n hrev
  intro m b hb
  exact Or.inr (by rw [List.drop_zero]; exact Array.mem_def.mp (seed_rows_pending hb))

/-- **No false negatives.** Every axiom reachable from a declaration along
    stored-body edges is filed under it. With `propagatedAxioms_sound` this
    pins the axiom rows exactly — which is what the gate's axiom-dependency arm
    reports, and what `docs/overview.md`'s trust claim rests on.

    The `some` hypothesis is load-bearing and is the reason `drainWorklist`
    refuses on exhaustion: a truncated map satisfies soundness while missing
    exactly the axiom that mattered. -/
theorem propagatedAxioms_complete {cs : Std.HashMap Name Lean.ConstantInfo}
    {result : Std.HashMap Name (Std.HashSet Name)} {n a : Name}
    (hrun : propagatedAxioms cs = some result)
    (haxiom : IsAxiom cs a) (hreach : Reaches cs n a) :
    a ∈ result[n]?.getD ({} : Std.HashSet Name) := by
  -- `Reaches` before `IsAxiom` so the induction leaves the axiom hypothesis a
  -- binder in each case rather than generalizing it away.
  have aux : ∀ {m b : Name}, Reaches cs m b → IsAxiom cs b →
      b ∈ result[m]?.getD ({} : Std.HashSet Name) := by
    intro m b hr
    induction hr with
    | refl k =>
      intro hax
      have hdrain := hrun
      rw [propagatedAxioms] at hdrain
      exact drainWorklist_grew (propagationSeed cs).reverse
        (propagationFuel cs (propagationSeed cs)) 0
        (propagationSeed cs).axiomsByName (propagationSeed cs).pending result hdrain k k
        (seed_rows_complete hax)
    | step edge _ ih =>
      intro hax
      exact propagatedAxioms_closed hrun (ih hax) (reverse_complete edge)
  exact aux hreach haxiom

end Tl.Verify
