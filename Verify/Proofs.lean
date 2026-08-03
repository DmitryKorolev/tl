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
  /-- Landmark observation preserved the policy list one for one. -/
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
    direction rules out a gate that fails on a clean checkout. -/
theorem analyze_clean_iff (cfg : Config) (o : Observation) :
    (analyze cfg o).errors = #[] ↔ GateClean cfg o := by
  rw [analyze_errors_eq_empty_iff_arms, replayFindings_eq_empty_iff,
    missingModuleFindings_eq_empty_iff, unexpectedModuleFindings_eq_empty_iff,
    vacuityFindings_eq_empty_iff, landmarkPolicyFindings_eq_empty_iff,
    landmarkKindFindings_eq_empty_iff, duplicateLandmarkFindings_eq_empty_iff,
    axiomDeclarationFindings_eq_empty_iff, axiomDependencyFindings_eq_empty_iff]
  constructor
  · rintro ⟨himports, hreplay, hexpected, hlocal,
      ⟨hmodules, hdecls, hreplayed, hedges⟩,
      hpolicy, hkinds, hdistinct, hnoaxiom, hdependencies⟩
    exact {
      importAuditClean := himports
      replayClean := hreplay
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
    exact ⟨clean.importAuditClean, clean.replayClean, clean.everyExpectedModuleImported,
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
