/-
`Tl.Kernel.CyclesFast` — the fast cycle diagnostics and their refinement
bridge.

The spec (`Cycles.lean`) pays per node: `onCycle` runs a full
non-saturating closure whose successor function re-derives `presentEdges`
per call, `sameSCC` runs two more closures per candidate pair, and the
`≺`-relation's successors (`precSucc`) read `effClosed` — the fuel rollup —
per blocker per step. The fast forms hoist the present issues/edges once
per call, read rollups through the batched map, and saturate every closure
(`reachFix`). The bridge (`cyclesFast_eq` / `precCyclesFast_eq` /
`hasCycleFast_eq` / `hasDeadlockFast_eq`) makes them pointwise EQUAL to the
spec, so the SCC-witness theorems (ADR-0004 thm 6) transfer untouched.
-/
import Tl.Kernel.Cycles
import Tl.Kernel.ReadyFast

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ## Saturating SCC detection over an explicit successor function -/

/-- `onCycle` with the saturating closure. -/
def onCycleF (n : Nat) (succ : IssueId → List IssueId) (v : IssueId) : Bool :=
  decide (v ∈ reachFix succ n (succ v))

theorem onCycleF_eq (s : State) (succ : IssueId → List IssueId) (v : IssueId) :
    onCycleF s.presentIssues.length succ v = s.onCycle succ v := by
  unfold State.onCycleF State.onCycle
  rw [reachFix_eq]

/-- `sameSCC` with the saturating closure. -/
def sameSCCF (n : Nat) (succ : IssueId → List IssueId) (u v : IssueId) : Bool :=
  decide (u ∈ reachFix succ n [v]) && decide (v ∈ reachFix succ n [u])

theorem sameSCCF_eq (s : State) (succ : IssueId → List IssueId) (u v : IssueId) :
    sameSCCF s.presentIssues.length succ u v = s.sameSCC succ u v := by
  unfold State.sameSCCF State.sameSCC State.reachSet
  rw [reachFix_eq, reachFix_eq]

/-- `groupSCCGo` over an explicit same-component test. -/
def groupSCCGoF (same : IssueId → IssueId → Bool) (cyclic : List IssueId) :
    List IssueId → List IssueId → List (List IssueId)
  | [], _ => []
  | v :: vs, covered =>
    if v ∈ covered then groupSCCGoF same cyclic vs covered
    else
      let scc := cyclic.filter (fun u => same u v)
      scc :: groupSCCGoF same cyclic vs (scc ++ covered)

theorem groupSCCGoF_eq (s : State) (succ : IssueId → List IssueId)
    (cyclic : List IssueId) :
    (wl covered : List IssueId) →
    groupSCCGoF (fun u v => s.sameSCC succ u v) cyclic wl covered
      = groupSCCGo s succ cyclic wl covered
  | [], _ => rfl
  | v :: vs, covered => by
    unfold State.groupSCCGoF State.groupSCCGo
    by_cases h : v ∈ covered
    · rw [if_pos h, if_pos h]
      exact groupSCCGoF_eq s succ cyclic vs covered
    · rw [if_neg h, if_neg h]
      dsimp only
      rw [groupSCCGoF_eq s succ cyclic vs _]

/-- `sccWitnesses` with hoisted inputs and saturating closures. -/
def sccWitnessesF (present : List IssueId) (n : Nat)
    (succ : IssueId → List IssueId) : List (List IssueId) :=
  let cyclic := present.filter (onCycleF n succ)
  groupSCCGoF (sameSCCF n succ) cyclic cyclic []

theorem sccWitnessesF_eq (s : State) (succ : IssueId → List IssueId) :
    sccWitnessesF s.presentIssues s.presentIssues.length succ
      = s.sccWitnesses succ := by
  unfold State.sccWitnessesF State.sccWitnesses
  rw [List.filter_congr (fun v _ => onCycleF_eq s succ v),
    show (sameSCCF s.presentIssues.length succ)
       = (fun u v => s.sameSCC succ u v) from funext (fun u => funext (fun v =>
         sameSCCF_eq s succ u v)),
    groupSCCGoF_eq]

/-! ## The per-kind and `≺` graphs over hoisted views -/

/-- `kindSucc` over a hoisted edge list. -/
def kindSuccE (edges : List Edge) (s : State) (k : EdgeKind) (i : IssueId) :
    List IssueId :=
  ((edges.filter (fun e => decide (e.2.2 = k ∧ e.1 = i))).map (·.2.1)).filter
    (fun j => decide (s.hasIssue j))

theorem kindSuccE_eq (s : State) (k : EdgeKind) (i : IssueId) :
    kindSuccE s.presentEdges s k i = s.kindSucc k i := rfl

/-- `precSucc` over hoisted views and the rollup map: live blockers plus —
    for an epic — live children, rollups through the batched map. -/
def precSuccF (m : AMap IssueId Status) (edges : List Edge)
    (pe : List (IssueId × IssueId)) (s : State) (i : IssueId) : List IssueId :=
  liveSuccE m edges s i
    ++ (if !(kidsOfEdges pe i).isEmpty
        then (kidsOfEdges pe i).filter (fun c => !effClosedWith m s c) else [])

theorem precSuccF_eq (s : State) (i : IssueId) :
    precSuccF (s.effStatusAll) s.presentEdges s.parentEdges s i = s.precSucc i := by
  unfold State.precSuccF State.precSucc State.liveChildrenSucc State.isEpic
  rw [liveSuccE_eq, kidsOfEdges_parentEdges,
    List.filter_congr (fun c _ => by rw [effClosedWith_eq])]

/-- The fast per-kind cycle witnesses. -/
def cyclesFast (s : State) (k : EdgeKind) : List (List IssueId) :=
  let edges := s.presentEdges
  sccWitnessesF s.presentIssues s.presentIssues.length (kindSuccE edges s k)

theorem cyclesFast_eq (s : State) (k : EdgeKind) : cyclesFast s k = s.cycles k := by
  unfold State.cyclesFast State.cycles
  dsimp only
  rw [show kindSuccE s.presentEdges s k = s.kindSucc k from
    funext (fun i => kindSuccE_eq s k i), sccWitnessesF_eq]

/-- The fast readiness-deadlock witnesses. -/
def precCyclesFast (m : AMap IssueId Status) (s : State) : List (List IssueId) :=
  let edges := s.presentEdges
  let pe := s.parentEdges
  sccWitnessesF s.presentIssues s.presentIssues.length (precSuccF m edges pe s)

theorem precCyclesFast_eq (s : State) :
    precCyclesFast (s.effStatusAll) s = s.precCycles := by
  unfold State.precCyclesFast State.precCycles
  dsimp only
  rw [show precSuccF (s.effStatusAll) s.presentEdges s.parentEdges s = s.precSucc from
    funext (fun i => precSuccF_eq s i), sccWitnessesF_eq]

/-- The fast cycle-presence flag. -/
def hasCycleFast (s : State) (k : EdgeKind) : Bool := !(cyclesFast s k).isEmpty

theorem hasCycleFast_eq (s : State) (k : EdgeKind) :
    hasCycleFast s k = s.hasCycle k := by
  unfold State.hasCycleFast State.hasCycle
  rw [cyclesFast_eq]

/-- The fast deadlock flag. -/
def hasDeadlockFast (m : AMap IssueId Status) (s : State) : Bool :=
  !(precCyclesFast m s).isEmpty

theorem hasDeadlockFast_eq (s : State) :
    hasDeadlockFast (s.effStatusAll) s = s.hasDeadlock := by
  unfold State.hasDeadlockFast State.hasDeadlock
  rw [precCyclesFast_eq]

end State

end Tl.Kernel
