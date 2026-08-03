/- Project trust policy and landmark set, imported by the verifier so these
   declarations are themselves inside an inspected module.  Names use the
   unresolved syntax deliberately: loading this policy must not load or run
   the code that it is about to inspect. -/
import Lean
import Verify.Report

open Lean

namespace Tl.Verify

def allowedAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

structure ImportPolicy where
  ordinaryPrefixes : Array Name
  mathlibModules : Array Name
  deriving Inhabited

def importPolicy : ImportPolicy := {
  ordinaryPrefixes := #[`Init, `Lean, `Std, `Batteries]
  mathlibModules := #[`Tl.Kernel.Path, `Tl.Kernel.Reach, `Tl.Kernel.ReachBFS]
}

def directImportAllowed (policy : ImportPolicy) (definingModule importedModule : Name)
    (importedIsProjectModule : Bool := false) : Bool :=
  importedIsProjectModule ||
    policy.ordinaryPrefixes.any (fun candidate =>
      Name.isPrefixOf candidate importedModule) ||
    (policy.mathlibModules.contains definingModule &&
      Name.isPrefixOf `Mathlib importedModule)

/-- The ADR-0009 findings for a scope, over stored import-graph rows
    `(module, that module's direct imports)`.  Pure so the violation branch is
    testable without a loaded environment: since the CI source greps were
    retired this is the only ADR-0009 enforcement left, and a traversal that
    silently stops reporting would leave every other check passing. -/
def importViolations (policy : ImportPolicy) (scope : String)
    (projectModules : Std.HashSet Name)
    (rows : Array (Name × Array Name)) : Array String := Id.run do
  let mut errors := #[]
  for (definingModule, importedModules) in rows do
    for importedModule in importedModules do
      unless directImportAllowed policy definingModule importedModule
          (projectModules.contains importedModule) do
        errors := errors.push s!"trust verification ({scope}): {definingModule} directly imports {importedModule}, outside the ADR-0009 dependency policy. Use Lean/Std/Batteries, route Mathlib proofs through an allowlisted reachability module, or amend ADR-0009 deliberately."
  return errors

def landmarkTheorems : Array Name := #[
  `Tl.Kernel.State.merge_comm,
  `Tl.Kernel.State.merge_assoc,
  `Tl.Kernel.State.merge_idem,
  `Tl.Kernel.fold_eq_of_mem_iff,
  `Tl.Kernel.fold_perm,
  `Tl.Kernel.fold_append,
  `Tl.Kernel.fold_append_self,
  `Tl.Kernel.mem_ready_iff,
  `Tl.Kernel.State.readyLe_total,
  `Tl.Kernel.State.ready_sorted,
  `Tl.Kernel.liveness,
  `Tl.Kernel.deadlock_exists,
  `Tl.Kernel.onCycle_kindSucc_iff,
  `Tl.Kernel.onCycle_precSucc_iff,
  `Tl.Kernel.State.sccWitnesses_same_witness_iff,
  `Tl.Kernel.effectiveStatus_epic,
  `Tl.Kernel.State.effStatusAux_epic_zero_ne_done,
  `Tl.Kernel.invariant_apply,
  `Tl.Kernel.close_cancel_monotone,
  `Tl.Kernel.effectiveStatus_metaSet,
  `Tl.Kernel.effectiveStatus_labelAdd,
  `Tl.Kernel.le_apply,
  `Tl.Kernel.fold_le_of_subset,
  `Tl.Kernel.apply_idem,
  `Tl.Kernel.ready_time_mono,
  `Tl.Kernel.mem_why_iff,
  `Tl.Kernel.State.mem_unblocks_iff,
  `Tl.Kernel.claimWonB_iff,
  `Tl.Kernel.claimWon_merge_iff,
  `Tl.Clock.Skew.skew_converges,
  `Tl.Kernel.foldFast_eq_fold,
  `Tl.Kernel.State.readyFast_eq,
  `Tl.Crdt.OrSet.presentElements_eq_ref,
  `Tl.Crdt.OrSet.entryLive_eq_ref,
  `Tl.Crdt.AssocList.ascending_of_sorted,
  `Tl.Cli.mem_applyFacets_iff,
  `Tl.Cli.applyFacets_sublist,
  `Tl.Cli.readyFacets_cannot_widen,
  `Tl.Cli.labelFacet_pred_eq_true_iff,
  `Tl.Cli.assigneeFacet_pred_eq_true_iff
]

def config : Config := { allowedAxioms }

end Tl.Verify
