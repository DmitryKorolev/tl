/-
`Tl.Kernel.CyclesFast` — the fast cycle diagnostics and their refinement
bridge.

The spec (`Cycles.lean`) pays per node: `onCycle` runs a full
non-saturating closure whose successor function re-derives `presentEdges`
per call, `sameSCC` runs two more closures per candidate pair, and the
`≺`-relation's successors (`precSucc`) read `effClosed` — the fuel rollup —
per blocker per step. The fast forms hoist the present issues/edges once
per call, read rollups through the batched map, cache one saturating closure
per present issue (`reachFix`), and answer `onCycle`/`sameSCC` from that
cache. The bridge (`cyclesFast_eq` / `precCyclesFast_eq` /
`hasCycleFast_eq` / `hasDeadlockFast_eq`) makes them pointwise EQUAL to the
spec, so the SCC-witness theorems (ADR-0004 thm 6) transfer untouched.
-/
import Tl.Kernel.Reach
import Tl.Kernel.ReadyFast

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ## Cached saturating SCC detection over an explicit successor function -/

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

/-- Lookup in a precomputed closure cache, falling back to the exact closure if
    the key is absent. The fallback makes the cache extensionally transparent. -/
def lookupCached (fallback : IssueId → List IssueId) (v : IssueId) :
    List (IssueId × List IssueId) → List IssueId
  | [] => fallback v
  | (k, r) :: rest => if k = v then r else lookupCached fallback v rest

theorem lookupCached_map_self (f : IssueId → List IssueId) (v : IssueId) :
    (nodes : List IssueId) →
    lookupCached f v (nodes.map (fun x => (x, f x))) = f v
  | [] => rfl
  | x :: xs => by
    change (if x = v then f x else lookupCached f v (xs.map (fun x => (x, f x)))) = f v
    by_cases h : x = v
    · rw [if_pos h, h]
    · rw [if_neg h, lookupCached_map_self f v xs]

/-- One cached successor list per node. -/
def succCache (nodes : List IssueId)
    (succ : IssueId → List IssueId) : List (IssueId × List IssueId) :=
  nodes.map (fun v => (v, succ v))

def succCached (succ : IssueId → List IssueId)
    (cache : List (IssueId × List IssueId)) (v : IssueId) : List IssueId :=
  lookupCached succ v cache

theorem succCached_succCache_eq (nodes : List IssueId)
    (succ : IssueId → List IssueId) (v : IssueId) :
    succCached succ (succCache nodes succ) v = succ v := by
  unfold State.succCached State.succCache
  exact lookupCached_map_self succ v nodes

/-- One cached closure per node. -/
def reachCache (nodes : List IssueId) (n : Nat)
    (succ : IssueId → List IssueId) : List (IssueId × List IssueId) :=
  nodes.map (fun v => (v, reachFix succ n [v]))

def reachCached (n : Nat) (succ : IssueId → List IssueId)
    (cache : List (IssueId × List IssueId)) (v : IssueId) : List IssueId :=
  lookupCached (fun x => reachFix succ n [x]) v cache

theorem reachCached_reachCache_eq (nodes : List IssueId) (n : Nat)
    (succ : IssueId → List IssueId) (v : IssueId) :
    reachCached n succ (reachCache nodes n succ) v = reachFix succ n [v] := by
  unfold State.reachCached State.reachCache
  exact lookupCached_map_self (fun x => reachFix succ n [x]) v nodes

/-- Closure from a seed list is the union of closures from each seed, at the
    saturated `presentIssues.length` fuel used by cycle diagnostics. -/
theorem mem_reachFix_seed_iff (s : State) {succ : IssueId → List IssueId}
    (hsucc : ∀ x, succ x ⊆ s.presentIssues) (seed : List IssueId)
    (hseed : seed ⊆ s.presentIssues) (a : IssueId) :
    a ∈ reachFix succ s.presentIssues.length seed
      ↔ ∃ b ∈ seed, a ∈ reachFix succ s.presentIssues.length [b] := by
  constructor
  · intro h
    rw [reachFix_eq,
      mem_reachClosure_iff hseed (fun x _ => hsucc x)] at h
    obtain ⟨b, hb, hba⟩ := h
    refine ⟨b, hb, ?_⟩
    have hsingle : [b] ⊆ s.presentIssues := by
      intro x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ hseed hb
    rw [reachFix_eq,
      mem_reachClosure_iff hsingle (fun x _ => hsucc x)]
    exact ⟨b, List.mem_singleton.mpr rfl, hba⟩
  · rintro ⟨b, hb, hbfix⟩
    have hsingle : [b] ⊆ s.presentIssues := by
      intro x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ hseed hb
    rw [reachFix_eq,
      mem_reachClosure_iff hsingle (fun x _ => hsucc x)] at hbfix
    obtain ⟨x, hx, hxa⟩ := hbfix
    rw [List.mem_singleton] at hx
    rw [reachFix_eq,
      mem_reachClosure_iff hseed (fun x _ => hsucc x)]
    exact ⟨b, hb, hx ▸ hxa⟩

/-- `onCycle` through the cached one-root closures. -/
def onCycleCached (n : Nat) (succ : IssueId → List IssueId)
    (cache : List (IssueId × List IssueId)) (v : IssueId) : Bool :=
  (succ v).any (fun b => decide (v ∈ reachCached n succ cache b))

theorem onCycleCached_reachCache_eq (s : State) {succ : IssueId → List IssueId}
    (hsucc : ∀ x, succ x ⊆ s.presentIssues) (v : IssueId) :
    onCycleCached s.presentIssues.length succ
        (reachCache s.presentIssues s.presentIssues.length succ) v
      = onCycleF s.presentIssues.length succ v := by
  apply Bool.eq_iff_iff.mpr
  unfold State.onCycleCached State.onCycleF
  rw [List.any_eq_true, decide_eq_true_iff,
    mem_reachFix_seed_iff s hsucc (succ v) (hsucc v) v]
  constructor
  · rintro ⟨b, hb, hbmem⟩
    rw [reachCached_reachCache_eq] at hbmem
    exact ⟨b, hb, of_decide_eq_true hbmem⟩
  · rintro ⟨b, hb, hbmem⟩
    refine ⟨b, hb, ?_⟩
    rw [reachCached_reachCache_eq]
    exact decide_eq_true_iff.mpr hbmem

/-- `sameSCC` through the cached one-root closures. -/
def sameSCCCached (n : Nat) (succ : IssueId → List IssueId)
    (cache : List (IssueId × List IssueId)) (u v : IssueId) : Bool :=
  decide (u ∈ reachCached n succ cache v) && decide (v ∈ reachCached n succ cache u)

theorem sameSCCCached_reachCache_eq (nodes : List IssueId) (n : Nat)
    (succ : IssueId → List IssueId) (u v : IssueId) :
    sameSCCCached n succ (reachCache nodes n succ) u v = sameSCCF n succ u v := by
  unfold State.sameSCCCached State.sameSCCF
  rw [reachCached_reachCache_eq, reachCached_reachCache_eq]

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

/-- `sccWitnesses` with hoisted inputs and cached saturating closures. -/
def sccWitnessesF (present : List IssueId) (n : Nat)
    (succ : IssueId → List IssueId) : List (List IssueId) :=
  let succs := succCache present succ
  let succ' := succCached succ succs
  let cache := reachCache present n succ'
  let cyclic := present.filter (onCycleCached n succ' cache)
  groupSCCGoF (sameSCCCached n succ' cache) cyclic cyclic []

theorem sccWitnessesF_eq (s : State) (succ : IssueId → List IssueId)
    (hsucc : ∀ x, succ x ⊆ s.presentIssues) :
    sccWitnessesF s.presentIssues s.presentIssues.length succ
      = s.sccWitnesses succ := by
  unfold State.sccWitnessesF State.sccWitnesses
  dsimp only
  rw [show succCached succ (succCache s.presentIssues succ) = succ from
    funext (fun v => succCached_succCache_eq s.presentIssues succ v)]
  rw [List.filter_congr (fun v _ =>
      (onCycleCached_reachCache_eq s hsucc v).trans (onCycleF_eq s succ v)),
    show sameSCCCached s.presentIssues.length succ
        (reachCache s.presentIssues s.presentIssues.length succ)
       = sameSCCF s.presentIssues.length succ from
      funext (fun u => funext (fun v =>
        sameSCCCached_reachCache_eq s.presentIssues s.presentIssues.length succ u v)),
    show (sameSCCF s.presentIssues.length succ)
       = (fun u v => s.sameSCC succ u v) from
      funext (fun u => funext (fun v => sameSCCF_eq s succ u v)),
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
    funext (fun i => kindSuccE_eq s k i), sccWitnessesF_eq s (s.kindSucc k) (kindSucc_subset_present s k)]

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
    funext (fun i => precSuccF_eq s i), sccWitnessesF_eq s s.precSucc (precSucc_subset_present s)]

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
