/-
`Tl.Kernel.CyclesFast` — the fast cycle diagnostics and their refinement
bridge.

The spec (`Cycles.lean`) pays per node: `onCycle` runs a full
non-saturating closure whose successor function re-derives `presentEdges`
per call, `sameSCC` runs two more closures per candidate pair, and the
`≺`-relation's successors (`precSucc`) read `effClosed` — the fuel rollup —
per blocker per step. The shipped path (`sccWitnessesT`) makes detection
near-linear: one unverified Tarjan pass (`Tarjan.lean`) validated by the
proved certificate checker (`SccFast.lean`), answering `onCycle`/`sameSCC`
from component indices, over successor functions whose edge/rollup/presence
views are hoisted into hash structures once per call. A rejected
certificate falls back to the proved cached-closure path (`sccWitnessesF`),
so correctness never depends on the Tarjan core — only speed does, and
that is pinned by tests. One accepted residual, recorded as a tracked
task: witness grouping (`groupSCCH`, a hash covered-set over
`groupSCCGoF`'s recursion) filters the cyclic set once per emitted
component — Θ(cyclic-nodes × cycle-components). That is zero on a healthy
graph and linear for one big cycle, but quadratic when the cyclic set
shatters into many small components.

The bridge (`cyclesFast_eq` / `precCyclesFast_eq` / `hasCycleFast_eq` /
`hasDeadlockFast_eq`) makes the shipped forms pointwise EQUAL to the spec,
so the SCC-witness theorems (ADR-0004 thm 6) transfer untouched.
-/
import Tl.Kernel.Reach
import Tl.Kernel.ReadyFast
import Tl.Kernel.SccFast
import Tl.Kernel.Tarjan

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ## Cached saturating SCC detection over an explicit successor function -/

/-- `onCycle` with the O(V+E) frontier closure. -/
def onCycleF (n : Nat) (succ : IssueId → List IssueId) (v : IssueId) : Bool :=
  decide (v ∈ reachBFS succ n (succ v))

theorem onCycleF_eq (s : State) (succ : IssueId → List IssueId) (v : IssueId) :
    onCycleF s.presentIssues.length succ v = s.onCycle succ v := by
  unfold State.onCycleF State.onCycle
  exact decide_eq_decide.mpr (mem_reachBFS_iff s.presentIssues.length (succ v) v)

/-- `sameSCC` with the O(V+E) frontier closure. -/
def sameSCCF (n : Nat) (succ : IssueId → List IssueId) (u v : IssueId) : Bool :=
  decide (u ∈ reachBFS succ n [v]) && decide (v ∈ reachBFS succ n [u])

theorem sameSCCF_eq (s : State) (succ : IssueId → List IssueId) (u v : IssueId) :
    sameSCCF s.presentIssues.length succ u v = s.sameSCC succ u v := by
  unfold State.sameSCCF State.sameSCC State.reachSet
  rw [decide_eq_decide.mpr (mem_reachBFS_iff s.presentIssues.length [v] u),
    decide_eq_decide.mpr (mem_reachBFS_iff s.presentIssues.length [u] v)]

/-- Lookup in a precomputed closure cache, falling back to the exact closure if
    the key is absent. The fallback makes the cache extensionally transparent.
    COST NOTE (ADR-0023, accepted): this assoc-list scan + per-miss `fallback`
    closure is super-quadratic, but it is only on the witness-reconstruction path
    that runs when Tarjan's SCC certificate is REJECTED — which the certificate
    tests pin does not occur on real graphs; the hot path uses the hash views. The
    fallback's cost is accepted as correctness-only (a transparent reference), not
    optimized. -/
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
  nodes.map (fun v => (v, reachBFS succ n [v]))

def reachCached (n : Nat) (succ : IssueId → List IssueId)
    (cache : List (IssueId × List IssueId)) (v : IssueId) : List IssueId :=
  lookupCached (fun x => reachBFS succ n [x]) v cache

theorem reachCached_reachCache_eq (nodes : List IssueId) (n : Nat)
    (succ : IssueId → List IssueId) (v : IssueId) :
    reachCached n succ (reachCache nodes n succ) v = reachBFS succ n [v] := by
  unfold State.reachCached State.reachCache
  exact lookupCached_map_self (fun x => reachBFS succ n [x]) v nodes

/-- Closure from a seed list is the union of closures from each seed, at the
    saturated `presentIssues.length` fuel used by cycle diagnostics. Stated over
    `reachBFS` membership (the cycle check reads only membership), so it holds for
    the possibly-duplicated `precSucc` seed. -/
theorem mem_reachBFS_seed_iff (s : State) {succ : IssueId → List IssueId}
    (hsucc : ∀ x, succ x ⊆ s.presentIssues) (seed : List IssueId)
    (hseed : seed ⊆ s.presentIssues) (a : IssueId) :
    a ∈ reachBFS succ s.presentIssues.length seed
      ↔ ∃ b ∈ seed, a ∈ reachBFS succ s.presentIssues.length [b] := by
  constructor
  · intro h
    rw [mem_reachBFS_iff, mem_reachClosure_iff hseed (fun x _ => hsucc x)] at h
    obtain ⟨b, hb, hba⟩ := h
    refine ⟨b, hb, ?_⟩
    have hsingle : [b] ⊆ s.presentIssues := by
      intro x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ hseed hb
    rw [mem_reachBFS_iff, mem_reachClosure_iff hsingle (fun x _ => hsucc x)]
    exact ⟨b, List.mem_singleton.mpr rfl, hba⟩
  · rintro ⟨b, hb, hbfix⟩
    have hsingle : [b] ⊆ s.presentIssues := by
      intro x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ hseed hb
    rw [mem_reachBFS_iff, mem_reachClosure_iff hsingle (fun x _ => hsucc x)] at hbfix
    obtain ⟨x, hx, hxa⟩ := hbfix
    rw [List.mem_singleton] at hx
    rw [mem_reachBFS_iff, mem_reachClosure_iff hseed (fun x _ => hsucc x)]
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
    mem_reachBFS_seed_iff s hsucc (succ v) (hsucc v) v]
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

/-! ## The certificate fast path

`tarjanSCC` proposes a partition; `sccCertOk` (proved sound, `SccFast.lean`)
validates it; an accepted certificate answers `onCycle`/`sameSCC` from
component indices. Rejection falls back to `sccWitnessesF` above, so the
result is unconditionally the spec's. -/

/-- The grouping is invariant under tests that agree on the cyclic nodes. -/
theorem groupSCCGoF_congr {same₁ same₂ : IssueId → IssueId → Bool}
    {cyclic : List IssueId}
    (h : ∀ u ∈ cyclic, ∀ v ∈ cyclic, same₁ u v = same₂ u v) :
    (wl : List IssueId) → wl ⊆ cyclic → (covered : List IssueId) →
    groupSCCGoF same₁ cyclic wl covered = groupSCCGoF same₂ cyclic wl covered
  | [], _, _ => rfl
  | v :: vs, hwl, covered => by
    unfold State.groupSCCGoF
    have hvs : vs ⊆ cyclic := fun x hx => hwl (List.mem_cons_of_mem v hx)
    by_cases hv : v ∈ covered
    · rw [if_pos hv, if_pos hv]
      exact groupSCCGoF_congr h vs hvs covered
    · rw [if_neg hv, if_neg hv]
      have hvc : v ∈ cyclic := hwl (List.mem_cons_self ..)
      have hflt : cyclic.filter (fun u => same₁ u v)
                = cyclic.filter (fun u => same₂ u v) :=
        List.filter_congr (fun u hu => h u hu v hvc)
      dsimp only
      rw [hflt, groupSCCGoF_congr h vs hvs _]

/-- `groupSCCGoF` with the covered set as a hash set — the list form pays a
    linear scan per worklist node, quadratic on one giant SCC. -/
def groupSCCH (same : IssueId → IssueId → Bool) (cyclic : List IssueId) :
    List IssueId → Std.HashSet IssueId → List (List IssueId)
  | [], _ => []
  | v :: vs, covered =>
    if covered.contains v then groupSCCH same cyclic vs covered
    else
      let scc := cyclic.filter (fun u => same u v)
      scc :: groupSCCH same cyclic vs (scc.foldl (fun s x => s.insert x) covered)

theorem groupSCCH_eq (same : IssueId → IssueId → Bool) (cyclic : List IssueId) :
    (wl : List IssueId) → (cov : Std.HashSet IssueId) → (covL : List IssueId) →
    (∀ x, x ∈ cov ↔ x ∈ covL) →
    groupSCCH same cyclic wl cov = groupSCCGoF same cyclic wl covL
  | [], _, _, _ => rfl
  | v :: vs, cov, covL, h => by
    unfold groupSCCH State.groupSCCGoF
    by_cases hv : v ∈ covL
    · rw [if_pos (Std.HashSet.contains_iff_mem.mpr ((h v).mpr hv)), if_pos hv]
      exact groupSCCH_eq same cyclic vs cov covL h
    · rw [if_neg (fun hc => hv ((h v).mp (Std.HashSet.contains_iff_mem.mp hc))),
        if_neg hv]
      dsimp only
      rw [groupSCCH_eq same cyclic vs _
        (cyclic.filter (fun u => same u v) ++ covL)
        (fun x => by rw [mem_foldl_insert, List.mem_append, h x])]

/-- The witnesses, reconstructed from an accepted certificate: cyclic nodes
    are those with a successor in their own component, grouped by
    component-index equality. -/
def sccFromCert (present : List IssueId) (succ : IssueId → List IssueId)
    (comps : List (List IssueId)) : List (List IssueId) :=
  let cidx := cidxOf comps
  let cyclic := present.filter (fun v =>
    (succ v).any (fun w => cidx[w]? == cidx[v]?))
  groupSCCH (fun u v => cidx[u]? == cidx[v]?) cyclic cyclic ∅

theorem sccFromCert_eq (s : State) (succ : IssueId → List IssueId)
    (hsucc : ∀ x, succ x ⊆ s.presentIssues)
    {comps : List (List IssueId)}
    (hcert : sccCertOk s.presentIssues succ comps = true) :
    sccFromCert s.presentIssues succ comps = s.sccWitnesses succ := by
  show groupSCCH (fun u v => (cidxOf comps)[u]? == (cidxOf comps)[v]?)
      (s.presentIssues.filter (fun v =>
        (succ v).any (fun w => (cidxOf comps)[w]? == (cidxOf comps)[v]?)))
      (s.presentIssues.filter (fun v =>
        (succ v).any (fun w => (cidxOf comps)[w]? == (cidxOf comps)[v]?)))
      ∅
    = s.sccWitnesses succ
  rw [groupSCCH_eq _ _ _ ∅ []
    (fun x => ⟨fun hx => absurd hx (Std.HashSet.not_mem_empty),
      fun hx => nomatch hx⟩)]
  have hcyc : s.presentIssues.filter (fun v =>
        (succ v).any (fun w => (cidxOf comps)[w]? == (cidxOf comps)[v]?))
      = s.presentIssues.filter (s.onCycle succ) :=
    List.filter_congr (fun v hv => (cert_onCycle hsucc hcert hv).symm)
  rw [hcyc]
  rw [groupSCCGoF_congr (same₂ := fun u v => s.sameSCC succ u v)
      (fun u hu v hv =>
        (cert_sameSCC hsucc hcert (List.mem_of_mem_filter hu)
          (List.mem_of_mem_filter hv)).symm)
      _ (fun x hx => hx) []]
  rw [groupSCCGoF_eq]
  rfl

/-- The shipped SCC witnesses: Tarjan, validated; the proved cached-closure
    path on rejection. Unconditionally equal to the spec. -/
def sccWitnessesT (present : List IssueId) (n : Nat)
    (succ : IssueId → List IssueId) : List (List IssueId) :=
  let comps := tarjanSCC present succ
  if sccCertOk present succ comps then sccFromCert present succ comps
  else sccWitnessesF present n succ

theorem sccWitnessesT_eq (s : State) (succ : IssueId → List IssueId)
    (hsucc : ∀ x, succ x ⊆ s.presentIssues) :
    sccWitnessesT s.presentIssues s.presentIssues.length succ
      = s.sccWitnesses succ := by
  show (if sccCertOk s.presentIssues succ (tarjanSCC s.presentIssues succ)
        then sccFromCert s.presentIssues succ (tarjanSCC s.presentIssues succ)
        else sccWitnessesF s.presentIssues s.presentIssues.length succ)
      = s.sccWitnesses succ
  by_cases hc : sccCertOk s.presentIssues succ (tarjanSCC s.presentIssues succ) = true
  · rw [if_pos hc]
    exact sccFromCert_eq s succ hsucc hc
  · rw [if_neg hc]
    exact sccWitnessesF_eq s succ hsucc

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

/-! ## Hash-hoisted successor views

`kindSuccE`/`precSuccF` still rescan the full edge list per node — Θ(V·E)
across a diagnostic pass. These views bucket each graph's adjacency once
and probe presence/rollup through hash structures, pointwise equal to the
spec successors. -/

/-- The kind-`k` adjacency, bucketed by source. -/
def kindAdj (edges : List Edge) (k : EdgeKind) : Std.HashMap IssueId (List IssueId) :=
  bucketBy ((edges.filter (fun e => e.2.2 == k)).map (fun e => (e.1, e.2.1)))

/-- A bucketed successor function, presence-filtered. -/
def succOfAdj (adj : Std.HashMap IssueId (List IssueId))
    (pset : Std.HashSet IssueId) (i : IssueId) : List IssueId :=
  ((adj[i]?.getD []).reverse).filter (fun j => pset.contains j)

theorem succOfAdj_kindAdj_eq (s : State) (k : EdgeKind) (i : IssueId) :
    succOfAdj (kindAdj s.presentEdges k) (hashSetOf s.presentIssues) i
      = s.kindSucc k i := by
  unfold succOfAdj kindAdj State.kindSucc
  rw [getD_bucketBy, List.filter_map, List.filter_map, List.filter_map,
    List.map_map, List.filter_filter, List.filter_filter, List.filter_map,
    List.filter_filter]
  dsimp only [Function.comp]
  rw [List.filter_congr (q := fun e : Edge =>
      decide (s.hasIssue e.2.1) && decide (e.2.2 = k ∧ e.1 = i))
    (fun e _ => by
      rw [contains_hashSetOf_present s e.2.1]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff]
      exact ⟨fun ⟨⟨hh, hf⟩, hk⟩ => ⟨hh, hk, hf⟩,
        fun ⟨hh, hk, hf⟩ => ⟨⟨hh, hf⟩, hk⟩⟩)]
  exact List.map_congr_left (fun e _ => rfl)

/-- The blockers adjacency (`Blocks` edges bucketed by target). -/
def blocksAdj (edges : List Edge) : Std.HashMap IssueId (List IssueId) :=
  bucketBy ((edges.filter (fun e => e.2.2 == EdgeKind.Blocks)).map
    (fun e => (e.2.1, e.1)))

theorem blocksAdj_eq (edges : List Edge) (x : IssueId) :
    ((blocksAdj edges)[x]?.getD []).reverse = blockersOfE edges x := by
  unfold blocksAdj State.blockersOfE
  rw [getD_bucketBy, List.filter_map, List.map_map, List.filter_filter]
  dsimp only [Function.comp]
  rw [List.filter_congr (q := fun e : Edge =>
      decide (e.2.2 = EdgeKind.Blocks ∧ e.2.1 = x))
    (fun e _ => by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩)]
  exact List.map_congr_left (fun e _ => rfl)

/-- The children adjacency is the parent-edge bucket as-is. -/
theorem kidsOfEdges_bucketBy (pe : List (IssueId × IssueId)) (i : IssueId) :
    ((bucketBy pe)[i]?.getD []).reverse = kidsOfEdges pe i := by
  unfold State.kidsOfEdges
  rw [getD_bucketBy]

/-- `precSucc` over hash-hoisted views: bucketed blockers and children, the
    rollup through a hash copy, presence through a hash set. -/
def precSuccH (mh : Std.HashMap IssueId Status)
    (badj kadj : Std.HashMap IssueId (List IssueId))
    (pset : Std.HashSet IssueId) (s : State) (i : IssueId) : List IssueId :=
  let kids := (kadj[i]?.getD []).reverse
  ((badj[i]?.getD []).reverse).filter (fun b =>
    pset.contains b && !(Status.closed ((mh[b]?).getD (s.effectiveStatus b))))
    ++ (if !kids.isEmpty
        then kids.filter (fun c =>
          !(Status.closed ((mh[c]?).getD (s.effectiveStatus c)))) else [])

/-- The hash rollup probe agrees with `effClosedWith`. -/
theorem closedH_eq (m : AMap IssueId Status) (s : State) (b : IssueId) :
    Status.closed (((hashAssoc m.toList)[b]?).getD (s.effectiveStatus b))
      = effClosedWith m s b := by
  unfold State.effClosedWith State.effStatusWith
  rw [getElem?_hashAssoc_amap]

theorem precSuccH_eq (m : AMap IssueId Status) (s : State) (i : IssueId) :
    precSuccH (hashAssoc m.toList) (blocksAdj s.presentEdges)
        (bucketBy s.parentEdges) (hashSetOf s.presentIssues) s i
      = precSuccF m s.presentEdges s.parentEdges s i := by
  show ((blocksAdj s.presentEdges)[i]?.getD []).reverse.filter (fun b =>
      (hashSetOf s.presentIssues).contains b
        && !(Status.closed (((hashAssoc m.toList)[b]?).getD (s.effectiveStatus b))))
    ++ (if !((bucketBy s.parentEdges)[i]?.getD []).reverse.isEmpty
        then ((bucketBy s.parentEdges)[i]?.getD []).reverse.filter (fun c =>
          !(Status.closed (((hashAssoc m.toList)[c]?).getD (s.effectiveStatus c))))
        else [])
    = precSuccF m s.presentEdges s.parentEdges s i
  unfold State.precSuccF State.liveSuccE
  rw [blocksAdj_eq, kidsOfEdges_bucketBy]
  have hb : (blockersOfE s.presentEdges i).filter (fun b =>
      (hashSetOf s.presentIssues).contains b
        && !(Status.closed (((hashAssoc m.toList)[b]?).getD (s.effectiveStatus b))))
    = (blockersOfE s.presentEdges i).filter (fun b =>
        decide (s.hasIssue b) && !effClosedWith m s b) :=
    List.filter_congr (fun b _ => by
      rw [contains_hashSetOf_present s b, closedH_eq m s b])
  have hk : (kidsOfEdges s.parentEdges i).filter (fun c =>
      !(Status.closed (((hashAssoc m.toList)[c]?).getD (s.effectiveStatus c))))
    = (kidsOfEdges s.parentEdges i).filter (fun c => !effClosedWith m s c) :=
    List.filter_congr (fun c _ => by rw [closedH_eq m s c])
  rw [hb, hk]

/-- The fast per-kind cycle witnesses over PRE-HOISTED views: the caller
    passes `present = s.presentIssues` and `edges = s.presentEdges` (each a
    Θ(N²)/Θ(E²) OR-Set scan) computed once and shared, instead of re-deriving
    them per call. `cyclesFast` is the convenience wrapper that derives them;
    a command running several diagnostics shares one `present`/`edges`. -/
def cyclesFastWith (present : List IssueId) (edges : List Edge) (k : EdgeKind) :
    List (List IssueId) :=
  sccWitnessesT present present.length
    (succOfAdj (kindAdj edges k) (hashSetOf present))

/-- The fast per-kind cycle witnesses. -/
def cyclesFast (s : State) (k : EdgeKind) : List (List IssueId) :=
  cyclesFastWith s.presentIssues s.presentEdges k

theorem cyclesFast_eq (s : State) (k : EdgeKind) : cyclesFast s k = s.cycles k := by
  show sccWitnessesT s.presentIssues s.presentIssues.length
      (succOfAdj (kindAdj s.presentEdges k) (hashSetOf s.presentIssues))
    = s.cycles k
  rw [show succOfAdj (kindAdj s.presentEdges k) (hashSetOf s.presentIssues)
        = s.kindSucc k from funext (succOfAdj_kindAdj_eq s k),
    sccWitnessesT_eq s (s.kindSucc k) (kindSucc_subset_present s k)]
  rfl

/-- The fast readiness-deadlock witnesses over PRE-HOISTED views (see
    `cyclesFastWith`): `present`/`edges`/`pe` are passed in once. `s` is still
    taken, but only for `precSuccH`'s rollup-miss fallback — never a view scan. -/
def precCyclesFastWith (m : AMap IssueId Status) (present : List IssueId)
    (edges : List Edge) (pe : List (IssueId × IssueId)) (s : State) :
    List (List IssueId) :=
  sccWitnessesT present present.length
    (precSuccH (hashAssoc m.toList) (blocksAdj edges) (bucketBy pe)
      (hashSetOf present) s)

/-- The fast readiness-deadlock witnesses. -/
def precCyclesFast (m : AMap IssueId Status) (s : State) : List (List IssueId) :=
  precCyclesFastWith m s.presentIssues s.presentEdges s.parentEdges s

theorem precCyclesFast_eq (s : State) :
    precCyclesFast (s.effStatusAll) s = s.precCycles := by
  show sccWitnessesT s.presentIssues s.presentIssues.length
      (precSuccH (hashAssoc (s.effStatusAll).toList) (blocksAdj s.presentEdges)
        (bucketBy s.parentEdges) (hashSetOf s.presentIssues) s)
    = s.precCycles
  rw [show precSuccH (hashAssoc (s.effStatusAll).toList) (blocksAdj s.presentEdges)
        (bucketBy s.parentEdges) (hashSetOf s.presentIssues) s
      = s.precSucc from funext (fun i =>
        (precSuccH_eq (s.effStatusAll) s i).trans (precSuccF_eq s i)),
    sccWitnessesT_eq s s.precSucc (precSucc_subset_present s)]
  rfl

/-! ## Certificate-branch acceptance (the fast-path guard)

`sccWitnessesT` takes the certificate-checked fast Tarjan path iff `sccCertOk`
accepts the proposed partition, else it falls back to the proved (slow) closure.
These predicates expose that decision so the acceptance tests assert the fast
branch is taken by consuming a PRODUCTION entry point — not a hand-rolled
successor copy in a test file that silently goes stale when the wiring changes
(letting production drop to the slow path while the test keeps passing).

The successor composition is INLINE here (mirroring `cyclesFastWith`/
`precCyclesFastWith` directly above), not factored into a shared named def: a
`def … : … → IssueId → List IssueId` returning that partial application is a
perf trap — it rebuilds `kindAdj`/`blocksAdj` per successor query (Θ(N·E)/call,
even `@[inline]`), where the inline `let`-bound form builds them once. The
composition reads the same shared `kindAdj`/`succOfAdj`/`precSuccH`/`blocksAdj`
primitives, so a change to those moves both; keep the one-line composition in
sync with the two functions above (they sit adjacent for exactly that). -/

/-- Is the per-kind cycle path's fast cert branch accepted, over hoisted views? -/
def cyclesCertAcceptedWith (present : List IssueId) (edges : List Edge) (k : EdgeKind) : Bool :=
  let succ := succOfAdj (kindAdj edges k) (hashSetOf present)
  sccCertOk present succ (tarjanSCC present succ)

/-- Is the per-kind cycle path's fast cert branch accepted for `s`? -/
def cyclesCertAccepted (s : State) (k : EdgeKind) : Bool :=
  cyclesCertAcceptedWith s.presentIssues s.presentEdges k

/-- Is the readiness-deadlock path's fast cert branch accepted, over hoisted views? -/
def precCyclesCertAcceptedWith (m : AMap IssueId Status) (present : List IssueId)
    (edges : List Edge) (pe : List (IssueId × IssueId)) (s : State) : Bool :=
  let succ := precSuccH (hashAssoc m.toList) (blocksAdj edges) (bucketBy pe) (hashSetOf present) s
  sccCertOk present succ (tarjanSCC present succ)

/-- Is the readiness-deadlock path's fast cert branch accepted for `s`? -/
def precCyclesCertAccepted (m : AMap IssueId Status) (s : State) : Bool :=
  precCyclesCertAcceptedWith m s.presentIssues s.presentEdges s.parentEdges s

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
