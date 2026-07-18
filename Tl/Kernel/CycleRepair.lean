/-
`Tl.Kernel.CycleRepair` — the `dep cycles` → `dep remove` repair loop terminates
(ADR-0003 §2, ADR-0004 thm 6).

Acyclicity is reported, never enforced, so the *repair* story is a protocol on
top of the diagnostic: read a witness from `cycles`, remove a present kind-`k`
edge inside it, repeat. This module proves that protocol sound and terminating,
in the corrected **edge-count** form (the SCC-count measure is wrong: one
removal can split an SCC into several, so the witness count may *grow* while
the loop still converges):

* **(a) strict decrease** — a repair step (a well-formed remove of a present
  kind-`k` edge) strictly decreases the present kind-`k` edge count
  (`kindEdgeCount_repairStep_lt`);
* **(b) no new cycle + refinement** — an `edgeRemove` (any `observed` set)
  never puts a node on a kind-`k` cycle that was not already on one
  (`onCycle_edgeRemove`, `hasCycle_edgeRemove`), and every cyclic SCC after the
  removal is contained in a prior cyclic SCC (`cycles_edgeRemove_refine`);
* **(c) termination** — no chain of effective repair steps is longer than the
  number of present kind-`k` edges internal to reported witnesses
  (`effectiveChain_length_le`), a chain within that bound reaching
  `hasCycle = false` exists (`repair_terminates`), and every *maximal* run —
  wherever it stops being extendable — ends cycle-free within the bound
  (`effectiveChain_maximal_terminates`);
* **(d) progress** — every reported witness is nonempty and contains a present
  in-kind edge (`cycles_witness_edge_exists`), so a state with no effective
  step available is already cycle-free
  (`hasCycle_eq_false_of_no_effectiveStep`).

The two loop hypotheses are encoded structurally, not as side conditions:

* *(i) no concurrent kind-`k` `edgeAdd`* — each theorem analyzes a single
  `apply` of an `Op.edgeRemove` on an arbitrary materialized state (the loop
  invariant carried between steps), and `EffectiveChain` composes only such
  steps. Nothing else is folded between diagnostic and repair. This is the
  regime of the local CLI loop (re-read state, remove, repeat; no other
  writer). It deliberately excludes *all* interleaved ops, not just kind-`k`
  adds: a concurrent `create` can materialize a dangling endpoint and thereby
  activate inert kind-`k` edges into a brand-new cycle, so "anything but a
  kind-`k` add" would be unsound, not merely harder.
* *(ii) each remove carries every live tag of its edge* — `repairStep` fixes
  `observed := s.edges.tagsOf e`, exactly the CLI's well-formed shape
  (`dep remove` sends `.depRemove e (s.edges.tagsOf e)` and noops when the
  edge is not present — mirrored by `EffectiveStep` requiring presence).

Everything is total on arbitrary states — cyclic graphs and dangling edges
included (the `Cycles` contract): no acyclicity and no endpoint-existence
precondition anywhere. The counts and chains here are proof scaffolding for
the protocol, never a command path — the CLI keeps calling `cyclesFast`.

Statements are at the state/op level (`apply`, `Op.edgeRemove`, `Present`,
`tagsOf`, `cycles`) and never mention the OR-Set tombstone representation; the
proofs cross into the OR-Set only through the named `edges_edgeRemove`
projection (Frame) onto OrSet's public tombstone theorems — this module never
reads the representation itself.
-/
import Tl.Kernel.SccProps
import Tl.Kernel.ReachBFS
import Tl.Kernel.Frame

namespace Tl.Kernel

open Tl.Crdt

/-! ## Generic counting and reachability helpers -/

/-- A duplicate-free list contained in `l` but missing one of `l`'s members is
    strictly shorter than `l`. -/
theorem length_lt_of_nodup_subset_missing {α : Type _} [DecidableEq α]
    {l' l : List α} (hnd : l'.Nodup) (hsub : l' ⊆ l) {a : α}
    (ha : a ∈ l) (ha' : a ∉ l') : l'.length < l.length := by
  have hcard : l'.toFinset.card < l.toFinset.card := by
    apply Finset.card_lt_card
    refine ⟨fun x hx => List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hx)),
      fun hcon => ?_⟩
    exact ha' (List.mem_toFinset.mp (hcon (List.mem_toFinset.mpr ha)))
  calc l'.length = l'.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ < l.toFinset.card := hcard
    _ ≤ l.length := List.toFinset_card_le l

/-- Reachability is monotone in the successor map: fewer edges, fewer paths.
    (`StepRel` is an abbrev, so `ReflTransGen.mono` applies definitionally.) -/
theorem reflTransGen_mono_succ {succ' succ : IssueId → List IssueId}
    (h : ∀ i, succ' i ⊆ succ i) {a b : IssueId}
    (hab : Relation.ReflTransGen (StepRel succ') a b) :
    Relation.ReflTransGen (StepRel succ) a b :=
  Relation.ReflTransGen.mono (fun x _ hxy => h x hxy) _ _ hab

/-! ## The repair protocol -/

/-- One well-formed repair step: remove `e` carrying every tag the state holds
    for it — hypothesis (ii), the CLI's `dep remove` shape. -/
def repairStep (s : State) (e : Edge) : State :=
  apply s (Op.edgeRemove e (s.edges.tagsOf e))

/-- An *effective* repair step on `s`: the removed edge is kind-`k`, actually
    present (a non-present pair is the CLI's explicit noop, not an effective
    step), and internal to a reported witness. -/
def EffectiveStep (s : State) (k : EdgeKind) (e : Edge) : Prop :=
  e.2.2 = k ∧ s.edges.Present e ∧ ∃ W ∈ s.cycles k, e.1 ∈ W ∧ e.2.1 ∈ W

/-- The state after a sequence of repair steps. -/
def repairChain (s : State) (es : List Edge) : State :=
  es.foldl repairStep s

/-- Every step of the sequence is effective at its point of application — the
    loop invariant form of hypothesis (i): only repair removes are folded. -/
def EffectiveChain (k : EdgeKind) : State → List Edge → Prop
  | _, [] => True
  | s, e :: es => EffectiveStep s k e ∧ EffectiveChain k (repairStep s e) es

namespace State

/-! ## The measures (proof scaffolding, not a command path) -/

/-- The number of present kind-`k` edges — the strictly decreasing measure of
    obligation (a). -/
def kindEdgeCount (s : State) (k : EdgeKind) : Nat :=
  (s.presentEdges.filter (fun e => decide (e.2.2 = k))).length

/-- The present kind-`k` edges internal to some reported witness — the edges
    the repair loop may ever effectively remove. -/
def inWitnessKindEdges (s : State) (k : EdgeKind) : List Edge :=
  s.presentEdges.filter (fun e =>
    decide (e.2.2 = k) && decide (∃ W ∈ s.cycles k, e.1 ∈ W ∧ e.2.1 ∈ W))

/-- The termination bound of obligation (c). -/
def inWitnessKindEdgeCount (s : State) (k : EdgeKind) : Nat :=
  (s.inWitnessKindEdges k).length

/-! ## The kind-successor characterization -/

/-- A kind-`k` successor is exactly a present kind-`k` edge to a present
    target. -/
theorem mem_kindSucc_iff (s : State) (k : EdgeKind) (i j : IssueId) :
    j ∈ s.kindSucc k i ↔ (i, j, k) ∈ s.presentEdges ∧ s.hasIssue j := by
  unfold State.kindSucc
  rw [List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p, hp, hpj⟩, hiss⟩
    rw [List.mem_filter, decide_eq_true_eq] at hp
    obtain ⟨hpmem, hpk, hpi⟩ := hp
    have hpe : p = (i, j, k) := Prod.ext hpi (Prod.ext hpj hpk)
    rw [hpe] at hpmem
    exact ⟨hpmem, hiss⟩
  · rintro ⟨hmem, hiss⟩
    refine ⟨⟨(i, j, k), ?_, rfl⟩, hiss⟩
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨hmem, rfl, rfl⟩

/-! ## Bridge: presence across an `edgeRemove`

Both lemmas cross from `State` into the OR-Set through the named projection
`edges_edgeRemove` (Frame) and land on OrSet's public tombstone theorems
(`present_mergeTombstonesAt_mono`,
`not_present_mergeTombstonesAt_of_observed_all`); the representation is never
read here, so a reshaped delta fails at the named boundary, legibly. -/

/-- An `edgeRemove` — any observed set — never makes an edge present:
    presence only shrinks (a `tombstonesAt` delta adds no tags and only grows
    the tombstones). -/
theorem present_edgeRemove_mono (s : State) (e : Edge) (obs : FinSet Stamp)
    {x : Edge} (h : (apply s (Op.edgeRemove e obs)).edges.Present x) :
    s.edges.Present x := by
  rw [edges_edgeRemove] at h
  exact OrSet.present_mergeTombstonesAt_mono s.edges e obs h

/-- A well-formed remove kills its edge: carrying every held tag of `e`
    (hypothesis (ii)) leaves `e` with no live tag — whether `e` was present,
    already removed, or never added. Direct from removal effectiveness with
    the full tag set observed. -/
theorem repairStep_not_present (s : State) (e : Edge) :
    ¬ (repairStep s e).edges.Present e := by
  show ¬ (apply s (Op.edgeRemove e (s.edges.tagsOf e))).edges.Present e
  rw [edges_edgeRemove]
  exact OrSet.not_present_mergeTombstonesAt_of_observed_all s.edges e (s.edges.tagsOf e)
    (fun _ hst => hst)

/-! ## Frame: what an `edgeRemove` leaves fixed, and what only shrinks -/

/-- Issue membership is untouched by an `edgeRemove` (its issue delta is
    empty), so the node universe of every diagnostic is stable. -/
theorem presentIssues_edgeRemove (s : State) (e : Edge) (obs : FinSet Stamp) :
    (apply s (Op.edgeRemove e obs)).presentIssues = s.presentIssues := by
  unfold State.presentIssues
  rw [issues_edgeRemove s e obs]

/-- The present edge list only shrinks under an `edgeRemove`. -/
theorem presentEdges_edgeRemove_subset (s : State) (e : Edge) (obs : FinSet Stamp) :
    (apply s (Op.edgeRemove e obs)).presentEdges ⊆ s.presentEdges := by
  intro x hx
  have hx' : (apply s (Op.edgeRemove e obs)).edges.Present x :=
    (OrSet.mem_presentElements _ x).mp hx
  exact (OrSet.mem_presentElements s.edges x).mpr (present_edgeRemove_mono s e obs hx')

/-- Kind-`k` successors only shrink under an `edgeRemove` (fewer present
    edges, same present issues). -/
theorem kindSucc_edgeRemove_subset (s : State) (e : Edge) (obs : FinSet Stamp)
    (k : EdgeKind) (i : IssueId) :
    (apply s (Op.edgeRemove e obs)).kindSucc k i ⊆ s.kindSucc k i := by
  intro j hj
  rw [mem_kindSucc_iff] at hj ⊢
  obtain ⟨hmem, hiss⟩ := hj
  refine ⟨presentEdges_edgeRemove_subset s e obs hmem, ?_⟩
  unfold State.hasIssue at hiss ⊢
  rw [← issues_edgeRemove s e obs]
  exact hiss

/-! ## (b) A removal creates no cycle; surviving SCCs refine prior ones -/

/-- Mutual kind-`k` reachability after an `edgeRemove` implies it before (the
    graph only lost edges). -/
theorem sameSCC_edgeRemove (s : State) (e : Edge) (obs : FinSet Stamp) (k : EdgeKind)
    {u v : IssueId} (hu : u ∈ s.presentIssues) (hv : v ∈ s.presentIssues)
    (h : (apply s (Op.edgeRemove e obs)).sameSCC
      ((apply s (Op.edgeRemove e obs)).kindSucc k) u v = true) :
    s.sameSCC (s.kindSucc k) u v = true := by
  have hu' : u ∈ (apply s (Op.edgeRemove e obs)).presentIssues := by
    rw [presentIssues_edgeRemove s e obs]; exact hu
  have hv' : v ∈ (apply s (Op.edgeRemove e obs)).presentIssues := by
    rw [presentIssues_edgeRemove s e obs]; exact hv
  obtain ⟨hvu, huv⟩ :=
    (sameSCC_iff (kindSucc_subset_present (apply s (Op.edgeRemove e obs)) k) hu' hv').mp h
  exact (sameSCC_iff (kindSucc_subset_present s k) hu hv).mpr
    ⟨reflTransGen_mono_succ (kindSucc_edgeRemove_subset s e obs k) hvu,
     reflTransGen_mono_succ (kindSucc_edgeRemove_subset s e obs k) huv⟩

/-- **(b), no new cycle**: a node on a kind-`k` cycle after an `edgeRemove` was
    already on one before — for *any* observed set, well-formed or not. -/
theorem onCycle_edgeRemove (s : State) (e : Edge) (obs : FinSet Stamp) (k : EdgeKind)
    (v : IssueId)
    (h : (apply s (Op.edgeRemove e obs)).onCycle
      ((apply s (Op.edgeRemove e obs)).kindSucc k) v = true) :
    s.onCycle (s.kindSucc k) v = true := by
  rw [onCycle_kindSucc_iff] at h ⊢
  obtain ⟨b, hb, hbv⟩ := h
  exact ⟨b, kindSucc_edgeRemove_subset s e obs k v hb,
    reflTransGen_mono_succ (kindSucc_edgeRemove_subset s e obs k) hbv⟩

/-- **(b), refinement**: every cyclic SCC after an `edgeRemove` is contained in
    a cyclic SCC before it (a removal can split witnesses, never grow or merge
    them). -/
theorem cycles_edgeRemove_refine (s : State) (e : Edge) (obs : FinSet Stamp) (k : EdgeKind)
    {W' : List IssueId} (hW' : W' ∈ (apply s (Op.edgeRemove e obs)).cycles k) :
    ∃ W ∈ s.cycles k, W' ⊆ W := by
  have hface : ∀ u ∈ W', u ∈ s.presentIssues ∧ s.onCycle (s.kindSucc k) u = true := by
    intro u hu
    have huflat : u ∈ ((apply s (Op.edgeRemove e obs)).cycles k).flatten :=
      List.mem_flatten.mpr ⟨W', hW', hu⟩
    obtain ⟨hupres', hucyc'⟩ := (mem_flatten_cycles_iff _ k u).mp huflat
    refine ⟨?_, onCycle_edgeRemove s e obs k u hucyc'⟩
    rw [← presentIssues_edgeRemove s e obs]
    exact hupres'
  have hne : W' ≠ [] :=
    sccWitnesses_ne_nil (kindSucc_subset_present (apply s (Op.edgeRemove e obs)) k) hW'
  obtain ⟨u0, hu0⟩ := List.exists_mem_of_ne_nil W' hne
  obtain ⟨hu0pres, hu0cyc⟩ := hface u0 hu0
  have hu0flat : u0 ∈ (s.cycles k).flatten :=
    (mem_flatten_cycles_iff s k u0).mpr ⟨hu0pres, hu0cyc⟩
  obtain ⟨W, hW, hu0W⟩ := List.mem_flatten.mp hu0flat
  refine ⟨W, hW, fun u hu => ?_⟩
  obtain ⟨hupres, hucyc⟩ := hface u hu
  have hsame' : (apply s (Op.edgeRemove e obs)).sameSCC
      ((apply s (Op.edgeRemove e obs)).kindSucc k) u u0 = true :=
    sccWitnesses_sameSCC (kindSucc_subset_present (apply s (Op.edgeRemove e obs)) k)
      hW' hu hu0
  have hsame : s.sameSCC (s.kindSucc k) u u0 = true :=
    sameSCC_edgeRemove s e obs k hupres hu0pres hsame'
  exact mem_sccWitness_of_sameSCC (kindSucc_subset_present s k) hW hu0W hupres hucyc hsame

/-- A true `hasCycle` yields a witness (the report is nonempty). -/
private theorem exists_witness_of_hasCycle {s : State} {k : EdgeKind}
    (h : s.hasCycle k = true) : ∃ W, W ∈ s.cycles k := by
  unfold State.hasCycle at h
  cases hcs : s.cycles k with
  | nil => rw [hcs] at h; exact nomatch h
  | cons W rest => exact ⟨W, List.mem_cons_self ..⟩

/-- Any witness makes `hasCycle` true. -/
private theorem hasCycle_of_mem_cycles {s : State} {k : EdgeKind} {W : List IssueId}
    (hW : W ∈ s.cycles k) : s.hasCycle k = true := by
  unfold State.hasCycle
  cases hcs : s.cycles k with
  | nil => rw [hcs] at hW; exact nomatch hW
  | cons _ _ => rfl

/-- **(b), summary form**: an `edgeRemove` cannot introduce a kind-`k` cycle. -/
theorem hasCycle_edgeRemove (s : State) (e : Edge) (obs : FinSet Stamp) (k : EdgeKind)
    (h : (apply s (Op.edgeRemove e obs)).hasCycle k = true) :
    s.hasCycle k = true := by
  obtain ⟨W', hW'⟩ := exists_witness_of_hasCycle h
  obtain ⟨W, hW, _⟩ := cycles_edgeRemove_refine s e obs k hW'
  exact hasCycle_of_mem_cycles hW

/-! ## (a) A repair step strictly decreases the present kind-`k` edge count -/

/-- **(a)**: removing a present kind-`k` edge with every held tag carried
    strictly decreases the present kind-`k` edge count. (The in-witness
    condition of an effective step is not needed for the decrease.) -/
theorem kindEdgeCount_repairStep_lt (s : State) {e : Edge} {k : EdgeKind}
    (hk : e.2.2 = k) (hpres : s.edges.Present e) :
    (repairStep s e).kindEdgeCount k < s.kindEdgeCount k := by
  unfold State.kindEdgeCount
  have hsub : (repairStep s e).presentEdges.filter (fun x => decide (x.2.2 = k))
      ⊆ s.presentEdges.filter (fun x => decide (x.2.2 = k)) := by
    intro x hx
    rw [List.mem_filter] at hx ⊢
    exact ⟨presentEdges_edgeRemove_subset s e (s.edges.tagsOf e) hx.1, hx.2⟩
  have hein : e ∈ s.presentEdges.filter (fun x => decide (x.2.2 = k)) :=
    List.mem_filter.mpr ⟨(OrSet.mem_presentElements s.edges e).mpr hpres, decide_eq_true hk⟩
  have henot : e ∉ (repairStep s e).presentEdges.filter (fun x => decide (x.2.2 = k)) := by
    intro hmem
    exact repairStep_not_present s e
      ((OrSet.mem_presentElements _ e).mp (List.mem_of_mem_filter hmem))
  exact length_lt_of_nodup_subset_missing
    (List.Nodup.filter _ (presentEdges_nodup (repairStep s e))) hsub hein henot

/-- **(a), spec form**: an effective repair step strictly decreases the present
    kind-`k` edge count. -/
theorem kindEdgeCount_effectiveStep_lt (s : State) {e : Edge} {k : EdgeKind}
    (h : EffectiveStep s k e) :
    (repairStep s e).kindEdgeCount k < s.kindEdgeCount k := by
  obtain ⟨hk, hpres, _⟩ := h
  exact kindEdgeCount_repairStep_lt s hk hpres

/-! ## (d) Progress: a nonempty witness holds a present in-witness edge -/

/-- **(d)**: every reported kind-`k` witness contains a present kind-`k` edge
    with both endpoints inside it — the repair loop always has an effective
    step to take while a witness exists. -/
theorem cycles_witness_edge_exists (s : State) (k : EdgeKind)
    {W : List IssueId} (hW : W ∈ s.cycles k) :
    ∃ i ∈ W, ∃ j ∈ W, s.edges.Present (i, j, k) := by
  have hsucc := kindSucc_subset_present s k
  have hne : W ≠ [] := sccWitnesses_ne_nil hsucc hW
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil W hne
  have hvflat : v ∈ (s.cycles k).flatten := List.mem_flatten.mpr ⟨W, hW, hv⟩
  obtain ⟨hvpres, hvcyc⟩ := (mem_flatten_cycles_iff s k v).mp hvflat
  obtain ⟨b, hbsucc, hbv⟩ := (onCycle_kindSucc_iff s k v).mp hvcyc
  obtain ⟨hedge, _⟩ := (mem_kindSucc_iff s k v b).mp hbsucc
  have hbpres : b ∈ s.presentIssues := hsucc v hbsucc
  have hbcyc : s.onCycle (s.kindSucc k) b = true := by
    rw [onCycle_kindSucc_iff]
    rcases Relation.ReflTransGen.cases_head hbv with heq | ⟨c, hc, hcv⟩
    · subst heq
      exact ⟨b, hbsucc, Relation.ReflTransGen.refl⟩
    · exact ⟨c, hc, hcv.tail hbsucc⟩
  have hsame : s.sameSCC (s.kindSucc k) b v = true :=
    (sameSCC_iff hsucc hbpres hvpres).mpr ⟨Relation.ReflTransGen.single hbsucc, hbv⟩
  have hbW : b ∈ W := mem_sccWitness_of_sameSCC hsucc hW hv hbpres hbcyc hsame
  exact ⟨v, hv, b, hbW, (OrSet.mem_presentElements s.edges _).mp hedge⟩

/-- **(d), step form**: a state with a kind-`k` cycle admits an effective
    repair step. -/
theorem effectiveStep_exists_of_hasCycle (s : State) (k : EdgeKind)
    (h : s.hasCycle k = true) : ∃ e : Edge, EffectiveStep s k e := by
  obtain ⟨W, hW⟩ := exists_witness_of_hasCycle h
  obtain ⟨i, hiW, j, hjW, hpres⟩ := cycles_witness_edge_exists s k hW
  refine ⟨(i, j, k), ?_⟩
  show (i, j, k).2.2 = k ∧ s.edges.Present (i, j, k)
    ∧ ∃ W ∈ s.cycles k, (i, j, k).1 ∈ W ∧ (i, j, k).2.1 ∈ W
  exact ⟨rfl, hpres, W, hW, hiW, hjW⟩

/-- **(d), loop-exit honesty**: if no effective step is available, the state is
    already kind-`k` cycle-free — the loop never stalls on a live cycle. -/
theorem hasCycle_eq_false_of_no_effectiveStep (s : State) (k : EdgeKind)
    (h : ∀ e : Edge, ¬ EffectiveStep s k e) : s.hasCycle k = false := by
  cases hc : s.hasCycle k with
  | false => rfl
  | true =>
    obtain ⟨e, he⟩ := effectiveStep_exists_of_hasCycle s k hc
    exact absurd he (h e)

/-! ## (c) Termination: the in-witness edge count bounds every repair run -/

/-- An effective step strictly decreases the in-witness present kind-`k` edge
    count: the removed edge leaves the pool, and no edge enters it (presence
    only shrinks, witnesses only refine). -/
theorem inWitnessKindEdgeCount_effectiveStep_lt (s : State) {k : EdgeKind} {e : Edge}
    (h : EffectiveStep s k e) :
    (repairStep s e).inWitnessKindEdgeCount k < s.inWitnessKindEdgeCount k := by
  obtain ⟨hk, hpres, hwit⟩ := h
  unfold State.inWitnessKindEdgeCount
  have hsub : (repairStep s e).inWitnessKindEdges k ⊆ s.inWitnessKindEdges k := by
    intro x hx
    simp only [State.inWitnessKindEdges, List.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq] at hx ⊢
    obtain ⟨hxmem, hxk, W', hW', hx1, hx2⟩ := hx
    refine ⟨presentEdges_edgeRemove_subset s e (s.edges.tagsOf e) hxmem, hxk, ?_⟩
    obtain ⟨W, hW, hWsub⟩ := cycles_edgeRemove_refine s e (s.edges.tagsOf e) k hW'
    exact ⟨W, hW, hWsub hx1, hWsub hx2⟩
  have hein : e ∈ s.inWitnessKindEdges k := by
    simp only [State.inWitnessKindEdges, List.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨(OrSet.mem_presentElements s.edges e).mpr hpres, hk, hwit⟩
  have henot : e ∉ (repairStep s e).inWitnessKindEdges k := by
    intro hmem
    have hxmem : e ∈ (repairStep s e).presentEdges := by
      simp only [State.inWitnessKindEdges, List.mem_filter] at hmem
      exact hmem.1
    exact repairStep_not_present s e ((OrSet.mem_presentElements _ e).mp hxmem)
  exact length_lt_of_nodup_subset_missing
    (List.Nodup.filter _ (presentEdges_nodup (repairStep s e))) hsub hein henot

end State

/-- **(c), universal bound**: no chain of effective repair steps is longer than
    the initial number of present kind-`k` edges internal to reported
    witnesses. -/
theorem effectiveChain_length_le (k : EdgeKind) :
    ∀ (es : List Edge) (s : State), EffectiveChain k s es →
      es.length ≤ s.inWitnessKindEdgeCount k
  | [], _, _ => Nat.zero_le _
  | e :: es, s, h => by
    have hh : EffectiveStep s k e ∧ EffectiveChain k (repairStep s e) es := h
    obtain ⟨hstep, hrest⟩ := hh
    have hle := effectiveChain_length_le k es (repairStep s e) hrest
    have hlt := State.inWitnessKindEdgeCount_effectiveStep_lt s hstep
    calc (e :: es).length = es.length + 1 := List.length_cons ..
      _ ≤ (repairStep s e).inWitnessKindEdgeCount k + 1 := Nat.add_le_add_right hle 1
      _ ≤ s.inWitnessKindEdgeCount k := Nat.succ_le_of_lt hlt

/-- Cycle-free already: the empty run is complete. -/
private theorem repair_done {s : State} {k : EdgeKind} (hc : s.hasCycle k = false) :
    ∃ es : List Edge, EffectiveChain k s es ∧ (repairChain s es).hasCycle k = false :=
  ⟨[], True.intro, hc⟩

/-- Termination existence, on an explicit bound for the decreasing measure. The
    chain-length bound is not re-proved here — `effectiveChain_length_le`
    supplies it for any chain, so `repair_terminates` composes the two. -/
theorem repair_terminates_aux (k : EdgeKind) :
    ∀ (n : Nat) (s : State), s.inWitnessKindEdgeCount k ≤ n →
      ∃ es : List Edge, EffectiveChain k s es
        ∧ (repairChain s es).hasCycle k = false
  | 0, s, hn => by
    cases hc : s.hasCycle k with
    | false => exact repair_done hc
    | true =>
      obtain ⟨e, hstep⟩ := State.effectiveStep_exists_of_hasCycle s k hc
      have hlt := State.inWitnessKindEdgeCount_effectiveStep_lt s hstep
      exact absurd (Nat.lt_of_lt_of_le hlt hn) (Nat.not_lt_zero _)
  | n + 1, s, hn => by
    cases hc : s.hasCycle k with
    | false => exact repair_done hc
    | true =>
      obtain ⟨e, hstep⟩ := State.effectiveStep_exists_of_hasCycle s k hc
      have hlt := State.inWitnessKindEdgeCount_effectiveStep_lt s hstep
      have hle' : (repairStep s e).inWitnessKindEdgeCount k ≤ n :=
        Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt hn)
      obtain ⟨es', hchain', hcyc'⟩ := repair_terminates_aux k n (repairStep s e) hle'
      refine ⟨e :: es', ?_, ?_⟩
      · show EffectiveStep s k e ∧ EffectiveChain k (repairStep s e) es'
        exact ⟨hstep, hchain'⟩
      · show (repairChain (repairStep s e) es').hasCycle k = false
        exact hcyc'

/-- **(c), termination**: from any state — cyclic and dangling edges included —
    some chain of at most `inWitnessKindEdgeCount` effective repair steps ends
    with no kind-`k` cycle. -/
theorem repair_terminates (s : State) (k : EdgeKind) :
    ∃ es : List Edge, EffectiveChain k s es
      ∧ (repairChain s es).hasCycle k = false
      ∧ es.length ≤ s.inWitnessKindEdgeCount k := by
  obtain ⟨es, hchain, hcyc⟩ :=
    repair_terminates_aux k (s.inWitnessKindEdgeCount k) s (Nat.le_refl _)
  exact ⟨es, hchain, hcyc, effectiveChain_length_le k es s hchain⟩

/-- **(c), maximal-run form**: every maximal repair run — one no effective step
    can extend — ends kind-`k` cycle-free, within the in-witness edge bound.
    The `dep cycles` → `dep remove` loop, whatever edges it picks, reaches
    `hasCycle = false` in at most `inWitnessKindEdgeCount` effective steps. -/
theorem effectiveChain_maximal_terminates (k : EdgeKind) (s : State) (es : List Edge)
    (hchain : EffectiveChain k s es)
    (hmax : ∀ e : Edge, ¬ EffectiveStep (repairChain s es) k e) :
    (repairChain s es).hasCycle k = false ∧ es.length ≤ s.inWitnessKindEdgeCount k :=
  ⟨State.hasCycle_eq_false_of_no_effectiveStep (repairChain s es) k hmax,
   effectiveChain_length_le k es s hchain⟩

end Tl.Kernel
