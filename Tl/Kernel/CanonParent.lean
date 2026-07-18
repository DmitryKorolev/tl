/-
`Tl.Kernel.CanonParent` — the canonical display parent (ADR-0003 §4).

Concurrent reparenting converges to *several* surviving `parent` edges into a
child (reported, never rejected — a CRDT merge cannot reject the edge that adds
a second parent). Display derives one canonical parent deterministically: the
candidate whose surviving parent edge carries the greatest **live** add-tag,
with the parent id as the explicit tie-break.

This is the projection moved kernel-side under the ADR-0024 §3 bridge pattern:
a spec definition (`canonicalParent`, over `parentsOf` + `maxLiveTag`), a shared
selection core (`canonParentSelect`) the production/view path also calls, and a
pointwise bridge to that path (the shell's `canonicalParentE`, via the
key-generic `HashMapView.hashAssoc` probe at `K := Edge`).

The ranking is the lexicographic `(maxLiveTag, parentId)` order, and the pick is
its maximum (`maxOpt`) — total, and independent of the order the candidates are
enumerated (`canonParentSelect_perm`), with no distinct-stamps hypothesis. The
parent-id tie-break mirrors the LWW equal-stamp *value* tie-break (`tmax` on
`Stamp × V`, `Tl/Crdt/Lww.lean`). "Live" is the correction the graduated spec
bug forced: rank over the untombstoned tags only (`liveTagsOf`), never over
every observed tag — an edge kept present by a low surviving tag must not rank
by a tombstoned higher one.

Total on arbitrary states, dangling parent ids included: `canonicalParent`
selects only over *present* parent edges (edge presence, ADR-0003 §5), but never
requires the parent id itself to be a present issue.

This module imports only `HashMapView` (and, transitively, `State`), not
`RollupFast`, so it stays outside the ADR-0009 Mathlib cone; `List.Perm` and its
`filterMap`/`mem_iff` come from the standard library.
-/
import Tl.Kernel.HashMapView

namespace Tl.Kernel

open Tl.Crdt

/-! ## The order-maximum of a list (the reasoning form of the fold) -/

/-- The `≤`-greater accumulator only grows across a `tmax` fold. -/
theorem le_foldl_tmax_init {α : Type _} [TotalOrd α] (a : α) :
    (l : List α) → TotalOrd.le a (List.foldl TotalOrd.tmax a l)
  | [] => TotalOrd.le_refl a
  | b :: bs => by
    show TotalOrd.le a (List.foldl TotalOrd.tmax (TotalOrd.tmax a b) bs)
    exact TotalOrd.le_trans (TotalOrd.le_tmax_left a b) (le_foldl_tmax_init (TotalOrd.tmax a b) bs)

/-- A `tmax` fold lands on the initial value or a list member. -/
theorem foldl_tmax_mem {α : Type _} [TotalOrd α] (a : α) :
    (l : List α) → List.foldl TotalOrd.tmax a l ∈ a :: l
  | [] => List.mem_cons_self ..
  | b :: bs => by
    show List.foldl TotalOrd.tmax (TotalOrd.tmax a b) bs ∈ a :: b :: bs
    rcases List.mem_cons.mp (foldl_tmax_mem (TotalOrd.tmax a b) bs) with hm | hm
    · rw [hm]
      rcases TotalOrd.tmax_eq a b with he | he
      · rw [he]; exact List.mem_cons_self ..
      · rw [he]; exact List.mem_cons_of_mem a (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem a (List.mem_cons_of_mem b hm)

/-- Every list member is `≤` the `tmax` fold. -/
theorem le_foldl_tmax_of_mem {α : Type _} [TotalOrd α] (a : α) :
    (l : List α) → ∀ x ∈ l, TotalOrd.le x (List.foldl TotalOrd.tmax a l)
  | [], x, hx => nomatch hx
  | b :: bs, x, hx => by
    show TotalOrd.le x (List.foldl TotalOrd.tmax (TotalOrd.tmax a b) bs)
    rcases List.mem_cons.mp hx with he | hm
    · rw [he]
      exact TotalOrd.le_trans (TotalOrd.le_tmax_right a b)
        (le_foldl_tmax_init (TotalOrd.tmax a b) bs)
    · exact le_foldl_tmax_of_mem (TotalOrd.tmax a b) bs x hm

/-- The `≤`-greatest element of a list, `none` when empty. A `tmax` fold —
    commutative/associative/idempotent — so the value is the maximum and
    independent of order (`maxOpt_perm`). -/
def maxOpt {α : Type _} [TotalOrd α] : List α → Option α
  | [] => none
  | a :: as => some (List.foldl TotalOrd.tmax a as)

/-- `maxOpt` yields a member of the list. -/
theorem mem_maxOpt {α : Type _} [TotalOrd α] {l : List α} {m : α}
    (h : maxOpt l = some m) : m ∈ l := by
  match l, h with
  | a :: as, h =>
    rw [← Option.some.inj h]
    exact foldl_tmax_mem a as

/-- `maxOpt` yields an upper bound of the list. -/
theorem le_maxOpt {α : Type _} [TotalOrd α] {l : List α} {m : α}
    (h : maxOpt l = some m) : ∀ x ∈ l, TotalOrd.le x m := by
  match l, h with
  | a :: as, h =>
    have hm : List.foldl TotalOrd.tmax a as = m := Option.some.inj h
    intro x hx
    rcases List.mem_cons.mp hx with he | hmem
    · rw [← hm, he]; exact le_foldl_tmax_init a as
    · rw [← hm]; exact le_foldl_tmax_of_mem a as x hmem

/-- `maxOpt` is `none` exactly on the empty list. -/
theorem maxOpt_eq_none_iff {α : Type _} [TotalOrd α] {l : List α} :
    maxOpt l = none ↔ l = [] := by
  cases l with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons a as =>
    refine ⟨fun h => ?_, fun h => absurd h (List.cons_ne_nil a as)⟩
    exact absurd h (Option.some_ne_none (List.foldl TotalOrd.tmax a as))

/-- `maxOpt` is `some` exactly on a nonempty list. -/
theorem isSome_maxOpt_iff {α : Type _} [TotalOrd α] {l : List α} :
    (maxOpt l).isSome = true ↔ ∃ x, x ∈ l := by
  rw [Option.isSome_iff_ne_none, Ne, maxOpt_eq_none_iff]
  constructor
  · intro hne
    match l with
    | [] => exact absurd rfl hne
    | x :: xs => exact ⟨x, List.mem_cons_self ..⟩
  · rintro ⟨x, hx⟩ he; rw [he] at hx; exact nomatch hx

/-- **Order invariance of the maximum**: a permutation has the same `maxOpt`
    (the fold is over a commutative/associative/idempotent join). -/
theorem maxOpt_perm {α : Type _} [TotalOrd α] {l1 l2 : List α}
    (h : l1.Perm l2) : maxOpt l1 = maxOpt l2 := by
  cases h1 : maxOpt l1 with
  | none =>
    rw [maxOpt_eq_none_iff.mp h1] at h
    exact (maxOpt_eq_none_iff.mpr h.symm.eq_nil).symm
  | some m1 =>
    cases h2 : maxOpt l2 with
    | none =>
      rw [maxOpt_eq_none_iff.mp h2] at h
      rw [maxOpt_eq_none_iff.mpr h.eq_nil] at h1
      exact h1.symm
    | some m2 =>
      have hm1l2 : m1 ∈ l2 := h.mem_iff.mp (mem_maxOpt h1)
      have hm2l1 : m2 ∈ l1 := h.symm.mem_iff.mp (mem_maxOpt h2)
      exact congrArg some
        (TotalOrd.le_antisymm (le_maxOpt h2 m1 hm1l2) (le_maxOpt h1 m2 hm2l1))

namespace State

/-! ## Live tags and the corrected LWW key -/

/-- The live (untombstoned) add-tags of edge `e` — its surviving tags
    (ADR-0002 add-wins): the observed tags not tombstoned at `e`. -/
def liveTagsOf (s : State) (e : Edge) : List Stamp :=
  (AMap.keys (s.edges.tagsOf e)).filter (fun st => decide (st ∉ s.edges.removedOf e))

/-- The greatest live add-tag from an edge's observed tags and its tombstones —
    the order-max over the observed tags not in `removed`. The single fold the
    spec (`maxLiveTag`) and the hoisted production accessor (`View.maxTag`) both
    run, so the shell keeps no twin. -/
def maxLiveFold (tags removed : FinSet Stamp) : Option Stamp :=
  maxOpt ((AMap.keys tags).filter (fun st => decide (st ∉ removed)))

/-- The greatest live add-tag of `e` — the corrected canonical-parent LWW key
    (ADR-0003 §4, "surviving"). `none` iff `e` has no live tag, i.e. iff `e` is
    not `Present` (`maxLiveTag_isSome_iff_present`). -/
def maxLiveTag (s : State) (e : Edge) : Option Stamp :=
  maxLiveFold (s.edges.tagsOf e) (s.edges.removedOf e)

/-- `maxLiveTag` is definitionally the order-max over the live tags. -/
theorem maxLiveTag_eq (s : State) (e : Edge) : s.maxLiveTag e = maxOpt (s.liveTagsOf e) := rfl

/-- A tag is live iff it is an observed tag that is not tombstoned. -/
theorem mem_liveTagsOf (s : State) (e : Edge) (st : Stamp) :
    st ∈ s.liveTagsOf e ↔ st ∈ s.edges.tagsOf e ∧ st ∉ s.edges.removedOf e := by
  unfold State.liveTagsOf
  rw [List.mem_filter, decide_eq_true_eq, AMap.mem_keys, ← FinSet.mem_def]

/-- `maxLiveTag` is `some` exactly when the edge is present — presence *is* the
    existence of a live tag (ADR-0002, `present_iff_exists_live_tag`). -/
theorem maxLiveTag_isSome_iff_present (s : State) (e : Edge) :
    (s.maxLiveTag e).isSome = true ↔ s.edges.Present e := by
  rw [maxLiveTag_eq, isSome_maxOpt_iff, OrSet.present_iff_exists_live_tag]
  constructor
  · rintro ⟨st, hst⟩; exact ⟨st, (mem_liveTagsOf s e st).mp hst⟩
  · rintro ⟨st, hst⟩; exact ⟨st, (mem_liveTagsOf s e st).mpr hst⟩

/-! ## Candidate parents -/

/-- `p` is a candidate parent of `i` iff `(p, i, parent)` is a present edge —
    edge presence only, the parent id itself may be dangling. -/
theorem mem_parentsOf (s : State) (i p : IssueId) :
    p ∈ s.parentsOf i ↔ (p, i, EdgeKind.Parent) ∈ s.presentEdges := by
  unfold State.parentsOf
  rw [List.mem_map]
  constructor
  · rintro ⟨e, hmem, hfst⟩
    rw [List.mem_filter, decide_eq_true_eq] at hmem
    obtain ⟨he, hk, ht⟩ := hmem
    obtain ⟨f, t, k⟩ := e
    cases hfst; cases hk; cases ht; exact he
  · intro hmem
    exact ⟨(p, i, EdgeKind.Parent), List.mem_filter.mpr ⟨hmem, decide_eq_true ⟨rfl, rfl⟩⟩, rfl⟩

/-- A candidate parent's edge is present. -/
theorem present_of_mem_parentsOf (s : State) {i p : IssueId} (h : p ∈ s.parentsOf i) :
    s.edges.Present (p, i, EdgeKind.Parent) :=
  (OrSet.mem_presentElements s.edges _).mp ((mem_parentsOf s i p).mp h)

/-! ## The shared selection core and the spec canonical parent -/

/-- The canonical-parent selection: among candidate parents `cands`, the one
    whose `(rank p, p)` pair is lex-greatest, skipping candidates whose edge is
    not present (`rank p = none`). The `Stamp`-then-`IssueId` order is total, and
    the pick is its maximum, so the result does not depend on candidate order
    (`canonParentSelect_perm`); the id tie-break (greater id on equal tags)
    mirrors the LWW equal-stamp value tie-break (`tmax` on `Stamp × V`). -/
def canonParentSelect (rank : IssueId → Option Stamp) (cands : List IssueId) : Option IssueId :=
  (maxOpt (cands.filterMap (fun p => (rank p).map (fun t => (t, p))))).map (·.2)

/-- The canonical display parent (spec): candidates from `parentsOf` (the `from`
    of each present incoming `parent` edge), ranked by the greatest live tag of
    the candidate's edge. -/
def canonicalParent (s : State) (i : IssueId) : Option IssueId :=
  canonParentSelect (fun p => s.maxLiveTag (p, i, EdgeKind.Parent)) (s.parentsOf i)

/-- The pairs `canonParentSelect` ranks: a candidate `p` with a present edge
    contributes `(t, p)` at its greatest live tag `t`. -/
theorem mem_ranks {rank : IssueId → Option Stamp} {cands : List IssueId} {t : Stamp} {p : IssueId} :
    (t, p) ∈ cands.filterMap (fun q => (rank q).map (fun u => (u, q)))
      ↔ p ∈ cands ∧ rank p = some t := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, hmap⟩
    rw [Option.map_eq_some_iff] at hmap
    obtain ⟨u, hrq, hpair⟩ := hmap
    obtain ⟨hu, hqp⟩ : u = t ∧ q = p := ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
    exact ⟨hqp ▸ hq, by rw [← hqp, hrq, hu]⟩
  · rintro ⟨hp, hrp⟩
    exact ⟨p, hp, by rw [hrp, Option.map_some]⟩

/-! ## (a)–(c) + existence: the proved obligations -/

/-- **(a)**: the selected parent is the `from` of a *present* `parent` edge to
    `i` — edge presence only; the parent id itself may be dangling (ADR-0003 §5). -/
theorem canonicalParent_present (s : State) {i p : IssueId}
    (h : s.canonicalParent i = some p) : s.edges.Present (p, i, EdgeKind.Parent) := by
  unfold State.canonicalParent State.canonParentSelect at h
  cases hmax : maxOpt ((s.parentsOf i).filterMap
      (fun q => (s.maxLiveTag (q, i, EdgeKind.Parent)).map (fun u => (u, q)))) with
  | none => rw [hmax] at h; exact nomatch h
  | some r =>
    rw [hmax, Option.map_some] at h
    obtain ⟨t, p'⟩ := r
    have hp' : p' = p := Option.some.inj h
    have hmem := mem_maxOpt hmax
    rw [hp'] at hmem
    obtain ⟨_, hrank⟩ := mem_ranks.mp hmem
    have hrank2 : s.maxLiveTag (p, i, EdgeKind.Parent) = some t := hrank
    exact (maxLiveTag_isSome_iff_present s (p, i, EdgeKind.Parent)).mp (Option.isSome_iff_exists.mpr ⟨t, hrank2⟩)

/-- **(b)**: the winner owns the maximal live rank — its `(maxLiveTag, id)` pair
    is `≤`-greatest among all candidate parents of `i`. -/
theorem canonicalParent_maximal (s : State) {i p : IssueId}
    (h : s.canonicalParent i = some p) :
    ∃ tp, s.maxLiveTag (p, i, EdgeKind.Parent) = some tp ∧
      ∀ q ∈ s.parentsOf i, ∀ tq, s.maxLiveTag (q, i, EdgeKind.Parent) = some tq →
        TotalOrd.le ((tq, q) : Stamp × IssueId) (tp, p) := by
  unfold State.canonicalParent State.canonParentSelect at h
  cases hmax : maxOpt ((s.parentsOf i).filterMap
      (fun q => (s.maxLiveTag (q, i, EdgeKind.Parent)).map (fun u => (u, q)))) with
  | none => rw [hmax] at h; exact nomatch h
  | some r =>
    rw [hmax, Option.map_some] at h
    obtain ⟨tp, p'⟩ := r
    have hp' : p' = p := Option.some.inj h
    have hmem := mem_maxOpt hmax
    rw [hp'] at hmem
    obtain ⟨_, hrank⟩ := mem_ranks.mp hmem
    have hrank2 : s.maxLiveTag (p, i, EdgeKind.Parent) = some tp := hrank
    refine ⟨tp, hrank2, fun q hq tq htq => ?_⟩
    have hle := le_maxOpt hmax (tq, q) (mem_ranks.mpr ⟨hq, htq⟩)
    rw [hp'] at hle
    exact hle

/-- **(c)**: the selection is invariant under the order the candidates are
    enumerated — unconditional (no distinct-stamps hypothesis), because the pick
    is the order-maximum of a total order. -/
theorem canonParentSelect_perm (rank : IssueId → Option Stamp) {c1 c2 : List IssueId}
    (h : c1.Perm c2) : canonParentSelect rank c1 = canonParentSelect rank c2 := by
  unfold State.canonParentSelect
  rw [maxOpt_perm (h.filterMap _)]

/-- **Existence**: the canonical parent is present exactly when a present parent
    edge into `i` exists — the direction `(a)`/`(b)` do not pin (a `fun _ => none`
    rank satisfies them vacuously). -/
theorem canonicalParent_isSome_iff (s : State) (i : IssueId) :
    (s.canonicalParent i).isSome = true ↔ ∃ p : IssueId, s.edges.Present (p, i, EdgeKind.Parent) := by
  unfold State.canonicalParent State.canonParentSelect
  rw [Option.isSome_map, isSome_maxOpt_iff]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨t, p⟩ := r
    obtain ⟨_, hrank⟩ := mem_ranks.mp hr
    have hrank2 : s.maxLiveTag (p, i, EdgeKind.Parent) = some t := hrank
    exact ⟨p, (maxLiveTag_isSome_iff_present s (p, i, EdgeKind.Parent)).mp (Option.isSome_iff_exists.mpr ⟨t, hrank2⟩)⟩
  · rintro ⟨p, hpres⟩
    have hp : p ∈ s.parentsOf i :=
      (mem_parentsOf s i p).mpr ((OrSet.mem_presentElements s.edges _).mpr hpres)
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
      ((maxLiveTag_isSome_iff_present s (p, i, EdgeKind.Parent)).mpr hpres)
    exact ⟨(t, p), mem_ranks.mpr ⟨hp, ht⟩⟩

end State

end Tl.Kernel
