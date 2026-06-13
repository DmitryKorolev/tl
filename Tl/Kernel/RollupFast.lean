/-
`Tl.Kernel.RollupFast` — the fast rollup and its refinement bridge
(ADR-0003 §3 amendment).

Three pieces, named accordingly: the *spec* is the fuel form in
`Rollup.lean`; the *fast implementation* here is a memoized recursion —
`path` (the current descent chain) detects a parent cycle at the exact node,
`memo` caches completed statuses, and the parent-edge view is hoisted once
per pass; the *refinement bridge* is `effStatusAll_find` /
`effStatusWith_eq`: the fast form is pointwise EQUAL to `effectiveStatus`,
so every spec theorem (ready soundness, close-monotonicity, the frame
lemmas) transfers to the shipped path with no re-proof.

The bridge leans on two spec-side facts: the unconditional recurrence
(`RollupSat.effectiveStatus_recurrence` — the fuel is saturated at the
working depth) closes the inductive step, and live-cycle conservatism
(`RollupSpec.effStatusAux_open_on_liveCycle`) makes the path cutoff *exact*:
a re-encountered node is a member of a cycle of non-cancelled epics, whose
effective status IS `Open` — treating it as not-closed loses nothing. The
walk's structural once-per-pass property is `rollupVisit_find_hit`.
-/
import Tl.Kernel.RollupSat
import Tl.Kernel.Ready
import Tl.Kernel.HashMapView

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ## The fast implementation

`effectiveStatus` (`Rollup.lean`) is the *spec*: fuel-bounded, proved correct, but it
recomputes `presentIssues` (for the fuel) and `presentChildren` (a fresh
`presentEdges` scan) per node per call — Θ(N³) across a `list`. The shipped
read path is the memoized recursion below: the parent-edge view is hoisted
once per pass, `path` (the current descent chain) detects a parent cycle at
the exact node — a global visited set would mistake shared DAG children for
cycles — and `memo` caches completed statuses so each node is evaluated once
per pass. `effStatusAll_find` below proves the memo pointwise equal to
`effectiveStatus`, so every spec theorem transfers; the structural
once-per-pass property is `rollupVisit_find_hit`. -/

/-- The hoisted parent-edge view: `(parent, child)` for every present `Parent`
    edge whose child is present — computed once per rollup pass. -/
def parentEdges (s : State) : List (IssueId × IssueId) :=
  s.presentEdges.filterMap (fun e =>
    let (f, t, k) := e
    if decide (k = EdgeKind.Parent) && decide (s.hasIssue t) then some (f, t) else none)

/-- Children of `i` per the hoisted view (= `presentChildren i`,
    `kidsOfEdges_parentEdges`). -/
def kidsOfEdges (pe : List (IssueId × IssueId)) (i : IssueId) : List IssueId :=
  (pe.filter (fun p => p.1 == i)).map (·.2)

theorem length_kidsOfEdges_le (pe : List (IssueId × IssueId)) (i : IssueId) :
    (kidsOfEdges pe i).length ≤ pe.length := by
  unfold kidsOfEdges
  rw [List.length_map]
  exact List.length_filter_le _ _

/-- The bucketed kids lookup equals `kidsOfEdges` exactly (order included) — the
    O(1)-amortized runtime form, bridged to the list form so termination and
    soundness reason over `kidsOfEdges`/`pe` unchanged (ADR-0024 §4). -/
theorem kidsBucket_eq {pe : List (IssueId × IssueId)}
    {bucket : Std.HashMap IssueId (List IssueId)} (hb : bucket = bucketBy pe)
    (i : IssueId) : (bucket[i]?.getD []).reverse = kidsOfEdges pe i := by
  subst hb
  rw [getD_bucketBy]
  rfl

/-- Filter-length monotonicity under predicate implication. -/
theorem length_filter_le_of_imp {α : Type _} (p q : α → Bool)
    (h : ∀ a, q a = true → p a = true) :
    (l : List α) → (l.filter q).length ≤ (l.filter p).length
  | [] => Nat.le_refl _
  | x :: xs => by
    by_cases hq : q x = true
    · rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos (h x hq),
        List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (length_filter_le_of_imp p q h xs)
    · rw [List.filter_cons_of_neg hq]
      by_cases hp : p x = true
      · rw [List.filter_cons_of_pos hp, List.length_cons]
        exact Nat.le_succ_of_le (length_filter_le_of_imp p q h xs)
      · rw [List.filter_cons_of_neg hp]
        exact length_filter_le_of_imp p q h xs

/-- Strict decrease of the unvisited measure: additionally excluding a member
    of the filtered list shortens it. -/
theorem length_filter_lt_of_mem {α : Type _} [BEq α] [LawfulBEq α]
    (p : α → Bool) (c : α) : (l : List α) → c ∈ l → p c = true →
    (l.filter (fun x => p x && x != c)).length < (l.filter p).length
  | x :: xs, hc, hpc => by
    have himp : ∀ a, ((fun x => p x && x != c) a = true) → p a = true := fun a ha =>
      ((Bool.and_eq_true ..).mp ha).1
    rcases List.mem_cons.mp hc with rfl | hmem
    · have hneg : ¬ ((fun x => p x && x != c) c = true) := by
        show ¬ ((p c && c != c) = true)
        rw [bne_self_eq_false, Bool.and_false]
        exact Bool.false_ne_true
      rw [List.filter_cons_of_neg (p := fun x => p x && x != c) hneg,
        List.filter_cons_of_pos hpc, List.length_cons]
      exact Nat.lt_succ_of_le (length_filter_le_of_imp p _ himp xs)
    · by_cases hpx : p x = true
      · by_cases hxc : (x != c) = true
        · have hpos : ((fun x => p x && x != c) x = true) := by
            show (p x && x != c) = true
            rw [hpx, hxc]
            rfl
          rw [List.filter_cons_of_pos (p := fun x => p x && x != c) hpos,
            List.filter_cons_of_pos hpx, List.length_cons, List.length_cons]
          exact Nat.succ_lt_succ (length_filter_lt_of_mem p c xs hmem hpc)
        · have hneg : ¬ ((fun x => p x && x != c) x = true) := by
            show ¬ ((p x && x != c) = true)
            intro h
            exact hxc ((Bool.and_eq_true ..).mp h).2
          rw [List.filter_cons_of_neg (p := fun x => p x && x != c) hneg,
            List.filter_cons_of_pos hpx, List.length_cons]
          exact Nat.lt_succ_of_lt (length_filter_lt_of_mem p c xs hmem hpc)
      · have hneg : ¬ ((fun x => p x && x != c) x = true) := fun h => hpx (himp x h)
        rw [List.filter_cons_of_neg (p := fun x => p x && x != c) hneg,
          List.filter_cons_of_neg hpx]
        exact length_filter_lt_of_mem p c xs hmem hpc

/-- Excluding the head of the path is the same filter as filtering by the
    extended path (the measure-preservation step of the descent). -/
theorem filter_path_cons (l : List IssueId) (path : List IssueId) (i : IssueId) :
    l.filter (fun x => !(i :: path).contains x)
      = l.filter (fun x => !path.contains x && x != i) := by
  apply List.filter_congr
  intro x _
  show (!(i :: path).contains x) = (!path.contains x && x != i)
  rw [List.contains_cons, Bool.not_or, Bool.and_comm]
  rfl

mutual

/-- Memoized rollup of one node. `path` is the descent chain (head = the
    immediate parent of `i`); a kid found on it closes a parent cycle of
    non-cancelled epics, whose members are `Open` by
    `effStatusAux_open_on_liveCycle` — so treating it as not-closed is exact,
    not just conservative. Entered only with `i ∉ path`. Terminates
    lexicographically: descending into a fresh present kid shrinks the
    unvisited-present set; walking the kid list shrinks the list. -/
def rollupVisit (s : State) (pe : List (IssueId × IssueId))
    (bucket : Std.HashMap IssueId (List IssueId)) (hb : bucket = bucketBy pe)
    (path : List IssueId) (memo : Std.HashMap IssueId Status) (i : IssueId) :
    Std.HashMap IssueId Status × Status :=
  match memo[i]? with
  | some v => (memo, v)
  | none =>
    if (s.issueData i).statusOf = Status.Cancelled then
      (memo.insert i Status.Cancelled, Status.Cancelled)
    else
      let kids := (bucket[i]?.getD []).reverse
      if kids.isEmpty then
        let v := (s.issueData i).statusOf
        (memo.insert i v, v)
      else
        let r := rollupKids s pe bucket hb (i :: path) memo kids
        let v := if r.2 then Status.Done else Status.Open
        (r.1.insert i v, v)
termination_by
  ((s.presentIssues.filter (fun x => !path.contains x && x != i)).length, pe.length + 1)
decreasing_by
  -- visit → kids: the extended path absorbs `i` (equal measure), and the bucketed
  -- kid list equals `kidsOfEdges pe i` (kidsBucket_eq), bounded by the edge list
  rw [← filter_path_cons]
  apply Prod.Lex.right
  apply Nat.lt_succ_of_le
  rw [kidsBucket_eq hb i]
  exact length_kidsOfEdges_le pe i

/-- The kid loop: thread the memo left-to-right, conjoin closed-ness. A kid on
    the path is a cycle re-encounter (`Open`, exact — see `rollupVisit`); a
    non-present kid cannot arise from `kidsOfEdges` and reads its stored
    status without recursing (defensive arm, unreachable in `effStatusAll`). -/
def rollupKids (s : State) (pe : List (IssueId × IssueId))
    (bucket : Std.HashMap IssueId (List IssueId)) (hb : bucket = bucketBy pe)
    (path : List IssueId) (memo : Std.HashMap IssueId Status) (cs : List IssueId) :
    Std.HashMap IssueId Status × Bool :=
  match cs with
  | [] => (memo, true)
  | c :: cs' =>
    let r :=
      match memo[c]? with
      | some v => (memo, v)
      | none =>
        if _hcon : path.contains c then (memo, Status.Open)
        else if _hpres : s.hasIssue c then rollupVisit s pe bucket hb path memo c
        else (memo, (s.issueData c).statusOf)
    let r' := rollupKids s pe bucket hb path r.1 cs'
    (r'.1, Status.closed r.2 && r'.2)
termination_by
  ((s.presentIssues.filter (fun x => !path.contains x)).length, cs.length)
decreasing_by
  · -- kids → visit: a fresh present kid strictly shrinks the unvisited set
    apply Prod.Lex.left
    apply length_filter_lt_of_mem
    · exact (Tl.Crdt.OrSet.mem_presentElements s.issues c).mpr _hpres
    · show (!path.contains c) = true
      cases hpath : path.contains c with
      | true => exact absurd hpath _hcon
      | false => rfl
  · -- kids → kids: same path, shorter list
    exact Prod.Lex.right _ (Nat.lt_succ_self _)

end

/-- The batched rollup memo: one memoized pass over every present issue,
    threaded through a `Std.HashMap` (O(1)-amortized find/insert). -/
def effStatusAllH (s : State) : Std.HashMap IssueId Status :=
  let pe := s.parentEdges
  let bucket := bucketBy pe
  s.presentIssues.foldl (fun memo i => (rollupVisit s pe bucket rfl [] memo i).1) ∅

/-- The batched rollup, materialized to the canonical `AMap` once at the end
    (`amapOfHashMap`). The shipped form for the read path (ADR-0003 §3 amendment);
    pointwise equal to `effectiveStatus` (`effStatusAll_find` below). -/
def effStatusAll (s : State) : AMap IssueId Status :=
  amapOfHashMap s.effStatusAllH

/-- Effective status through a rollup map, with the spec as the (dangling-id)
    fallback. With `m = effStatusAll s` this *is* `effectiveStatus`
    (`effStatusWith_eq`), the map just makes it one lookup. -/
def effStatusWith (m : AMap IssueId Status) (s : State) (i : IssueId) : Status :=
  (m.find i).getD (s.effectiveStatus i)

/-- `effClosed` through a rollup map. -/
def effClosedWith (m : AMap IssueId Status) (s : State) (i : IssueId) : Bool :=
  Status.closed (effStatusWith m s i)

/-! ## The refinement bridge -/

/-- The hoisted view agrees with the spec's `presentChildren` — list-equal,
    order included. -/
theorem kidsOfEdges_parentEdges (s : State) (i : IssueId) :
    kidsOfEdges (s.parentEdges) i = s.presentChildren i := by
  unfold kidsOfEdges parentEdges State.presentChildren State.childrenOf
  generalize s.presentEdges = l
  induction l with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨f, t, k⟩ := e
    by_cases hk : k = EdgeKind.Parent
    · by_cases ht : s.hasIssue t
      · have hpf : (fun e : Edge =>
            if decide (e.2.2 = EdgeKind.Parent) && decide (s.hasIssue e.2.1)
            then some (e.1, e.2.1) else none) (f, t, k) = some (f, t) := by
          show (if decide (k = EdgeKind.Parent) && decide (s.hasIssue t)
                then some (f, t) else none) = some (f, t)
          rw [decide_eq_true hk, decide_eq_true ht]
          rfl
        simp only [List.filterMap_cons, hpf]
        by_cases hf : f = i
        · have hkeep : (fun p : IssueId × IssueId => p.1 == i) (f, t) = true := by
            show (f == i) = true
            rw [hf]
            exact beq_self_eq_true i
          have hkeep' : (fun e : Edge =>
              decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i)) (f, t, k) = true :=
            decide_eq_true ⟨hk, hf⟩
          rw [List.filter_cons_of_pos (p := fun p : IssueId × IssueId => p.1 == i) hkeep, List.map_cons,
            List.filter_cons_of_pos (p := fun e : Edge => decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i))
              hkeep', List.map_cons,
            List.filter_cons_of_pos (p := fun c : IssueId => decide (s.hasIssue c))
              (decide_eq_true ht), ih]
        · have hdrop : ¬ ((fun p : IssueId × IssueId => p.1 == i) (f, t) = true) := by
            show ¬ ((f == i) = true)
            rw [beq_eq_false_iff_ne.mpr hf]
            exact Bool.false_ne_true
          have hdrop' : ¬ ((fun e : Edge =>
              decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i)) (f, t, k) = true) := by
            show ¬ (decide (k = EdgeKind.Parent ∧ f = i) = true)
            rw [decide_eq_false (fun h => hf h.2)]
            exact Bool.false_ne_true
          rw [List.filter_cons_of_neg (p := fun p : IssueId × IssueId => p.1 == i) hdrop,
            List.filter_cons_of_neg (p := fun e : Edge => decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i))
              hdrop', ih]
      · have hpf : (fun e : Edge =>
            if decide (e.2.2 = EdgeKind.Parent) && decide (s.hasIssue e.2.1)
            then some (e.1, e.2.1) else none) (f, t, k) = none := by
          show (if decide (k = EdgeKind.Parent) && decide (s.hasIssue t)
                then some (f, t) else none) = none
          rw [decide_eq_false ht, Bool.and_false]
          rfl
        simp only [List.filterMap_cons, hpf]
        by_cases hf : f = i
        · have hkeep' : (fun e : Edge =>
              decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i)) (f, t, k) = true :=
            decide_eq_true ⟨hk, hf⟩
          rw [List.filter_cons_of_pos (p := fun e : Edge => decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i))
              hkeep', List.map_cons,
            List.filter_cons_of_neg (p := fun c : IssueId => decide (s.hasIssue c)) (by
              show ¬ (decide (s.hasIssue t) = true)
              rw [decide_eq_false ht]
              exact Bool.false_ne_true), ih]
        · rw [List.filter_cons_of_neg (p := fun e : Edge => decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i)) (by
            show ¬ (decide (k = EdgeKind.Parent ∧ f = i) = true)
            rw [decide_eq_false (fun h => hf h.2)]
            exact Bool.false_ne_true), ih]
    · have hpf : (fun e : Edge =>
          if decide (e.2.2 = EdgeKind.Parent) && decide (s.hasIssue e.2.1)
          then some (e.1, e.2.1) else none) (f, t, k) = none := by
        show (if decide (k = EdgeKind.Parent) && decide (s.hasIssue t)
              then some (f, t) else none) = none
        rw [decide_eq_false hk, Bool.false_and]
        rfl
      simp only [List.filterMap_cons, hpf]
      rw [List.filter_cons_of_neg (p := fun e : Edge => decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i)) (by
          show ¬ (decide (k = EdgeKind.Parent ∧ f = i) = true)
          rw [decide_eq_false (fun h => hk h.1)]
          exact Bool.false_ne_true), ih]

/-- Memo coherence: every cached value is the spec's. -/
def Coherent (s : State) (m : Std.HashMap IssueId Status) : Prop :=
  ∀ k v, m[k]? = some v → v = s.effectiveStatus k

/-- The descent-chain invariant: the head of `path` is the parent of the
    current node, each member parents the one before it, and every member is
    non-cancelled (the walk only descends past the cancel check). -/
def ChainOk (s : State) : List IssueId → IssueId → Prop
  | [], _ => True
  | p :: rest, i => i ∈ s.presentChildren p ∧
      (s.issueData p).statusOf ≠ Status.Cancelled ∧ ChainOk s rest p

/-- The path prefix down to (and including) the re-encountered node. -/
def seg (path : List IssueId) (c : IssueId) : List IssueId :=
  match path with
  | [] => []
  | p :: rest => if p == c then [p] else p :: seg rest c

theorem mem_seg_self (c : IssueId) :
    (path : List IssueId) → c ∈ path → c ∈ seg path c
  | p :: rest, hc => by
    unfold seg
    by_cases hpc : (p == c) = true
    · rw [if_pos hpc]
      exact List.mem_singleton.mpr (eq_of_beq hpc).symm
    · rw [if_neg hpc]
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact absurd (beq_self_eq_true c) hpc
      · exact List.mem_cons_of_mem p (mem_seg_self c rest hmem)

/-- The walked chain closed at the re-encountered node is a live set: every
    member non-cancelled, with a present child among `a :: seg path c`. -/
theorem seg_liveSet (s : State) (c : IssueId) :
    (path : List IssueId) → (a : IssueId) → ChainOk s path a → c ∈ path →
    ∀ x ∈ seg path c, (s.issueData x).statusOf ≠ Status.Cancelled ∧
      ∃ x', x' ∈ a :: seg path c ∧ x' ∈ s.presentChildren x
  | p :: rest, a, ⟨hap, hpnc, hrest⟩, hc => by
    unfold seg
    by_cases hpc : (p == c) = true
    · rw [if_pos hpc]
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨hpnc, a, List.mem_cons_self .., hap⟩
    · rw [if_neg hpc]
      have hcrest : c ∈ rest := by
        rcases List.mem_cons.mp hc with rfl | hmem
        · exact absurd (beq_self_eq_true c) hpc
        · exact hmem
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxseg
      · exact ⟨hpnc, a, List.mem_cons_self .., hap⟩
      · obtain ⟨hnc, x', hx', hchild⟩ := seg_liveSet s c rest p hrest hcrest x hxseg
        rcases List.mem_cons.mp hx' with rfl | hx'seg
        · exact ⟨hnc, x', List.mem_cons_of_mem a (List.mem_cons_self ..), hchild⟩
        · exact ⟨hnc, x',
            List.mem_cons_of_mem a (List.mem_cons_of_mem p hx'seg), hchild⟩

/-- A kid found on the walked chain is effectively `Open` — the path cutoff is
    exact, not merely conservative. The witness cycle is the chain segment
    from the kid down to the current node, closed by the `(node, kid)` edge. -/
theorem effectiveStatus_open_of_reencounter (s : State) {path : List IssueId}
    {i c : IssueId} (hchain : ChainOk s path i)
    (hinc : (s.issueData i).statusOf ≠ Status.Cancelled)
    (hkid : c ∈ s.presentChildren i) (hmem : c ∈ i :: path) :
    s.effectiveStatus c = Status.Open := by
  rcases List.mem_cons.mp hmem with rfl | hpath
  · exact effectiveStatus_open_on_liveCycle s [c] (fun x hx => by
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨hinc, x, List.mem_singleton.mpr rfl, hkid⟩) c (List.mem_singleton.mpr rfl)
  · refine effectiveStatus_open_on_liveCycle s (i :: seg path c) ?_ c
      (List.mem_cons_of_mem i (mem_seg_self c path hpath))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxseg
    · exact ⟨hinc, c, List.mem_cons_of_mem x (mem_seg_self c path hpath), hkid⟩
    · exact seg_liveSet s c path i hchain hpath x hxseg

private theorem coherent_insert (s : State) {m : Std.HashMap IssueId Status}
    (hcoh : Coherent s m) {i : IssueId} {v : Status}
    (hv : v = s.effectiveStatus i) : Coherent s (m.insert i v) := by
  intro k w hkw
  rw [Std.HashMap.getElem?_insert] at hkw
  by_cases hki : k = i
  · rw [if_pos (beq_iff_eq.mpr hki.symm)] at hkw
    rw [← Option.some.inj hkw, hki]
    exact hv
  · rw [if_neg (fun h => hki (beq_iff_eq.mp h).symm)] at hkw
    exact hcoh k w hkw

private theorem isSome_insert_mono {m : Std.HashMap IssueId Status} {i : IssueId}
    {v : Status} (k : IssueId) (h : (m[k]?).isSome = true) :
    ((m.insert i v)[k]?).isSome = true := by
  rw [Std.HashMap.getElem?_insert]
  by_cases hki : k = i
  · rw [if_pos (beq_iff_eq.mpr hki.symm)]
    rfl
  · rw [if_neg (fun h => hki (beq_iff_eq.mp h).symm)]
    exact h

mutual

/-- **Refinement (node).** With a coherent memo and the chain invariant, the
    walk returns exactly `effectiveStatus`, keeps the memo coherent, never
    drops an entry, and records the node. -/
theorem rollupVisit_sound (s : State) (pe : List (IssueId × IssueId))
    (bucket : Std.HashMap IssueId (List IssueId)) (hb : bucket = bucketBy pe)
    (hpe : pe = s.parentEdges) (path : List IssueId) (memo : Std.HashMap IssueId Status)
    (i : IssueId) (hcoh : Coherent s memo) (hchain : ChainOk s path i) :
    Coherent s (rollupVisit s pe bucket hb path memo i).1
    ∧ (rollupVisit s pe bucket hb path memo i).2 = s.effectiveStatus i
    ∧ (∀ (k : IssueId), (memo[k]?).isSome = true →
        ((rollupVisit s pe bucket hb path memo i).1[k]?).isSome = true)
    ∧ ((rollupVisit s pe bucket hb path memo i).1[i]?).isSome = true := by
  unfold State.rollupVisit
  cases hfind : memo[i]? with
  | some v =>
    refine ⟨hcoh, hcoh i v hfind, fun k hk => hk, ?_⟩
    rw [hfind]
    rfl
  | none =>
    by_cases hcanc : (s.issueData i).statusOf = Status.Cancelled
    · rw [if_pos hcanc]
      exact ⟨coherent_insert s hcoh (effectiveStatus_cancelled s i hcanc).symm,
        (effectiveStatus_cancelled s i hcanc).symm,
        fun k hk => isSome_insert_mono k hk,
        by rw [Std.HashMap.getElem?_insert, if_pos (beq_self_eq_true i)]; rfl⟩
    · rw [if_neg hcanc, kidsBucket_eq hb i]
      have hkids_eq : kidsOfEdges pe i = s.presentChildren i := by
        rw [hpe]
        exact kidsOfEdges_parentEdges s i
      cases hkemp : (kidsOfEdges pe i).isEmpty with
      | true =>
        rw [if_pos hkemp]
        have hepic : s.isEpic i = false := by
          unfold State.isEpic
          rw [← hkids_eq, hkemp]
          rfl
        exact ⟨coherent_insert s hcoh (effectiveStatus_nonEpic s i hepic).symm,
          (effectiveStatus_nonEpic s i hepic).symm,
          fun k hk => isSome_insert_mono k hk,
          by rw [Std.HashMap.getElem?_insert, if_pos (beq_self_eq_true i)]; rfl⟩
      | false =>
        rw [if_neg (by rw [hkemp]; exact Bool.false_ne_true)]
        have hcs : ∀ c ∈ kidsOfEdges pe i, c ∈ s.presentChildren i := by
          intro c hcm
          rw [← hkids_eq]
          exact hcm
        obtain ⟨hcoh', hval, hmono⟩ :=
          rollupKids_sound s pe bucket hb hpe path i hchain hcanc memo (kidsOfEdges pe i) hcoh hcs
        have heff : (if (rollupKids s pe bucket hb (i :: path) memo (kidsOfEdges pe i)).2
            then Status.Done else Status.Open) = s.effectiveStatus i := by
          rw [hval, hkids_eq, effectiveStatus_recurrence s i, if_neg hcanc]
          have hpem : (s.presentChildren i).isEmpty = false := by
            rw [← hkids_eq]
            exact hkemp
          rw [hpem, if_neg Bool.false_ne_true]
        exact ⟨coherent_insert s hcoh' heff, heff,
          fun k hk => isSome_insert_mono k (hmono k hk),
          by rw [Std.HashMap.getElem?_insert, if_pos (beq_self_eq_true i)]; rfl⟩
termination_by
  ((s.presentIssues.filter (fun x => !path.contains x && x != i)).length, pe.length + 1)
decreasing_by
  rw [← filter_path_cons]
  exact Prod.Lex.right _ (Nat.lt_succ_of_le (length_kidsOfEdges_le pe i))

/-- **Refinement (kid loop).** The conjoined closed-ness is exactly
    `cs.all effClosed`: memo hits are coherent, path hits are `Open` by the
    re-encounter cycle, fresh kids recurse. -/
theorem rollupKids_sound (s : State) (pe : List (IssueId × IssueId))
    (bucket : Std.HashMap IssueId (List IssueId)) (hb : bucket = bucketBy pe)
    (hpe : pe = s.parentEdges) (path : List IssueId) (i : IssueId)
    (hchain : ChainOk s path i)
    (hinc : (s.issueData i).statusOf ≠ Status.Cancelled) :
    (memo : Std.HashMap IssueId Status) → (cs : List IssueId) → Coherent s memo →
    (∀ c ∈ cs, c ∈ s.presentChildren i) →
    Coherent s (rollupKids s pe bucket hb (i :: path) memo cs).1
    ∧ (rollupKids s pe bucket hb (i :: path) memo cs).2 = cs.all (fun c => s.effClosed c)
    ∧ ∀ (k : IssueId), (memo[k]?).isSome = true →
        ((rollupKids s pe bucket hb (i :: path) memo cs).1[k]?).isSome = true
  | memo, [], hcoh, _ => by
    unfold State.rollupKids
    exact ⟨hcoh, rfl, fun k hk => hk⟩
  | memo, c :: cs', hcoh, hcs => by
    unfold State.rollupKids
    have hckid : c ∈ s.presentChildren i := hcs c (List.mem_cons_self ..)
    cases hfind : memo[c]? with
    | some v =>
      dsimp only
      obtain ⟨hcoh', hval', hmono'⟩ := rollupKids_sound s pe bucket hb hpe path i hchain hinc
        memo cs' hcoh (fun x hx => hcs x (List.mem_cons_of_mem c hx))
      refine ⟨hcoh', ?_, hmono'⟩
      rw [List.all_cons, hval']
      have hv : Status.closed v = s.effClosed c := by
        unfold State.effClosed
        rw [hcoh c v hfind]
      rw [hv]
    | none =>
      dsimp only
      by_cases hcon : (i :: path).contains c = true
      · rw [dif_pos hcon]
        dsimp only
        obtain ⟨hcoh', hval', hmono'⟩ := rollupKids_sound s pe bucket hb hpe path i hchain hinc
          memo cs' hcoh (fun x hx => hcs x (List.mem_cons_of_mem c hx))
        refine ⟨hcoh', ?_, hmono'⟩
        rw [List.all_cons, hval']
        have hopen : s.effClosed c = false := by
          unfold State.effClosed
          rw [effectiveStatus_open_of_reencounter s hchain hinc hckid
            (List.contains_iff_mem.mp hcon)]
          rfl
        rw [hopen]
        rfl
      · rw [dif_neg hcon]
        have hpres : s.hasIssue c := (OrSet.mem_presentElements s.issues c).mp
          (presentChildren_subset_present s i hckid)
        rw [dif_pos hpres]
        have hchain' : ChainOk s (i :: path) c := ⟨hckid, hinc, hchain⟩
        obtain ⟨hcohV, hvalV, hmonoV, _⟩ :=
          rollupVisit_sound s pe bucket hb hpe (i :: path) memo c hcoh hchain'
        obtain ⟨hcoh', hval', hmono'⟩ := rollupKids_sound s pe bucket hb hpe path i hchain hinc
          (rollupVisit s pe bucket hb (i :: path) memo c).1 cs' hcohV
          (fun x hx => hcs x (List.mem_cons_of_mem c hx))
        refine ⟨hcoh', ?_, fun k hk => hmono' k (hmonoV k hk)⟩
        rw [List.all_cons, hval', hvalV]
        rfl
termination_by memo cs _ _ =>
  ((s.presentIssues.filter (fun x => !(i :: path).contains x)).length, cs.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (Nat.lt_succ_self _)
    | (apply Prod.Lex.left
       apply length_filter_lt_of_mem
       · exact presentChildren_subset_present s i (hcs c (List.mem_cons_self ..))
       · show (!(i :: path).contains c) = true
         cases hpath : (i :: path).contains c with
         | true => exact absurd hpath hcon
         | false => rfl)

end

/-- **Once-per-pass.** A memoized node returns without recomputation. -/
theorem rollupVisit_find_hit (s : State) (pe : List (IssueId × IssueId))
    (bucket : Std.HashMap IssueId (List IssueId)) (hb : bucket = bucketBy pe)
    (path : List IssueId) (memo : Std.HashMap IssueId Status) (i : IssueId) (v : Status)
    (h : memo[i]? = some v) : rollupVisit s pe bucket hb path memo i = (memo, v) := by
  unfold State.rollupVisit
  rw [h]

/-- Coherence of the empty memo (vacuous). -/
private theorem coherent_empty (s : State) : Coherent s ∅ := fun k v h => by
  rw [Std.HashMap.getElem?_empty] at h
  nomatch h

/-- The batched HashMap memo is coherent: every entry is the spec's value. -/
theorem effStatusAllH_coherent (s : State) : Coherent s s.effStatusAllH := by
  unfold State.effStatusAllH
  have main : ∀ (l : List IssueId) (memo : Std.HashMap IssueId Status), Coherent s memo →
      Coherent s (l.foldl (fun m j =>
        (rollupVisit s s.parentEdges (bucketBy s.parentEdges) rfl [] m j).1) memo) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons x xs ih =>
      intro memo h
      rw [List.foldl_cons]
      exact ih _ (rollupVisit_sound s s.parentEdges (bucketBy s.parentEdges) rfl rfl
        [] memo x h trivial).1
  exact main s.presentIssues ∅ (coherent_empty s)

/-- Completeness over the HashMap memo: every present issue is recorded. -/
theorem effStatusAllH_find (s : State) (i : IssueId) (hi : i ∈ s.presentIssues) :
    (s.effStatusAllH)[i]? = some (s.effectiveStatus i) := by
  have hsome : ((s.effStatusAllH)[i]?).isSome = true := by
    unfold State.effStatusAllH
    have main : ∀ (l : List IssueId) (memo : Std.HashMap IssueId Status), Coherent s memo →
        (i ∈ l ∨ (memo[i]?).isSome = true) →
        ((l.foldl (fun m j =>
            (rollupVisit s s.parentEdges (bucketBy s.parentEdges) rfl [] m j).1) memo)[i]?).isSome
          = true := by
      intro l
      induction l with
      | nil =>
        intro memo _ h
        rcases h with h | h
        · exact absurd h (List.not_mem_nil)
        · exact h
      | cons x xs ih =>
        intro memo hcoh h
        rw [List.foldl_cons]
        obtain ⟨hcoh', _, hmono, hself⟩ :=
          rollupVisit_sound s s.parentEdges (bucketBy s.parentEdges) rfl rfl [] memo x hcoh trivial
        rcases h with h | h
        · rcases List.mem_cons.mp h with rfl | hxs
          · exact ih _ hcoh' (Or.inr hself)
          · exact ih _ hcoh' (Or.inl hxs)
        · exact ih _ hcoh' (Or.inr (hmono i h))
    exact main s.presentIssues ∅ (coherent_empty s) (Or.inl hi)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  rw [hv, effStatusAllH_coherent s i v hv]

/-- The materialized `AMap` is coherent — via the `amapOfHashMap` bridge, so
    callers see the same `(s.effStatusAll).find k = some v → v = …` shape. -/
theorem effStatusAll_coherent (s : State) (k : IssueId) (v : Status)
    (h : (s.effStatusAll).find k = some v) : v = s.effectiveStatus k := by
  unfold State.effStatusAll at h
  rw [find_amapOfHashMap] at h
  exact effStatusAllH_coherent s k v h

/-- **The refinement bridge.** The batched rollup holds exactly
    `effectiveStatus` for every present issue. -/
theorem effStatusAll_find (s : State) (i : IssueId) (hi : i ∈ s.presentIssues) :
    (s.effStatusAll).find i = some (s.effectiveStatus i) := by
  unfold State.effStatusAll
  rw [find_amapOfHashMap]
  exact effStatusAllH_find s i hi

/-- `effStatusWith` over the batched map *is* `effectiveStatus` — for every
    id, present or dangling (an absent key falls back to the spec; a found
    key is coherent). Every spec theorem transfers through this equation. -/
theorem effStatusWith_eq (s : State) (i : IssueId) :
    effStatusWith (s.effStatusAll) s i = s.effectiveStatus i := by
  unfold State.effStatusWith
  cases hf : (s.effStatusAll).find i with
  | none => rfl
  | some v => exact effStatusAll_coherent s i v hf

/-- `effClosedWith` over the batched map is `effClosed`. -/
theorem effClosedWith_eq (s : State) (i : IssueId) :
    effClosedWith (s.effStatusAll) s i = s.effClosed i := by
  unfold State.effClosedWith State.effClosed
  rw [effStatusWith_eq]

/-- `blockerDischarged` through a rollup map. -/
def blockerDischargedWith (m : AMap IssueId Status) (s : State) (b : IssueId) : Bool :=
  !decide (s.hasIssue b) || effClosedWith m s b

theorem blockerDischargedWith_eq (s : State) (b : IssueId) :
    blockerDischargedWith (s.effStatusAll) s b = s.blockerDischarged b := by
  unfold State.blockerDischargedWith State.blockerDischarged
  rw [effClosedWith_eq]

/-- `isReady` through a rollup map — the per-row readiness the CLI renders. -/
def isReadyWith (m : AMap IssueId Status) (s : State) (now : Instant) (i : IssueId) : Bool :=
  decide (s.hasIssue i)
  && decide ((s.issueData i).statusOf = Status.Open)
  && !s.isEpic i
  && deferOk (s.issueData i) now
  && (s.blockersOf i).all (blockerDischargedWith m s ·)

theorem isReadyWith_eq (s : State) (now : Instant) (i : IssueId) :
    isReadyWith (s.effStatusAll) s now i = s.isReady now i := by
  unfold State.isReadyWith State.isReady
  rw [all_congr (blockerDischargedWith (s.effStatusAll) s ·) (s.blockerDischarged ·)
    (s.blockersOf i) (fun b _ => blockerDischargedWith_eq s b)]

end State

end Tl.Kernel
