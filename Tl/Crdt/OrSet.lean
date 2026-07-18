/-
`Tl.Crdt.OrSet` — the observed-remove set (ADR-0002).

The collections that must support a convergent remove — the dependency-edge set
(`dep remove` is first-class, the forcing function for OR-Set over a grow-only
set) and the per-issue label sets — are OR-Sets. `adds` records, per element, the
set of add-tags observed for it (each add-tag is the adding op's `Stamp`,
ADR-0007/0008); `removed` tombstones, *per element*, the add-tags a remove of
that element has *observed*. An element is present iff it still has a live
(untombstoned) add-tag — concurrent add/remove resolves **add-wins** (an add the
remover never saw survives), the conservative bias for blockers (ADR-0002).

Tombstones are element-scoped, mirroring `adds`, because every remove op already
carries the element it removes: a remove can therefore *never* disturb any other
element's presence — by construction, not by an assumption that stamps never
collide across elements. This is what makes the `unrelate` frame lemma
(`Tl.Kernel.Frame`) unconditional, even against a malformed/adversarial
`observed` payload.

Issues are *resolved, not removed* (ADR-0002): the issue OR-Set is add-only in
practice, but the same construction backs it. The join is componentwise — both
per-element maps joined pointwise by `FinSet.union` — so commutativity/
associativity/idempotence are inherited.
-/
import Tl.Crdt.Map

namespace Tl.Crdt

open TotalOrd

universe u

/-- An observed-remove set over `α` (ADR-0002): observed add-tags per element,
    plus a mirror map of tombstoned add-tags per element. -/
structure OrSet (α : Type u) [TotalOrd α] where
  /-- Per element, the add-tags (op stamps) observed for it. -/
  adds : AMap α (FinSet Stamp)
  /-- Per element, the tombstoned add-tags (add-wins: only *observed* tags are
      tombstoned). Keyed by the element the remove op carries, so a remove
      cannot touch any other element's presence. -/
  removed : AMap α (FinSet Stamp)

namespace OrSet

variable {α : Type u} [TotalOrd α]

/-- The empty OR-Set. -/
def empty : OrSet α := ⟨AMap.empty, AMap.empty⟩

/-- The one-element delta `{e}` tagged `st` — an `add`'s contribution as a
    standalone OR-Set, joined into a state by `merge` (ADR-0001: apply = join with
    delta). -/
def singletonAdd (e : α) (st : Stamp) : OrSet α :=
  ⟨AMap.singleton e (FinSet.singleton st), AMap.empty⟩

/-- A pure-tombstone delta — a `remove`'s contribution: tombstone the observed
    add-tags `obs` *at the removed element `e`*, joined into a state by `merge`. -/
def tombstonesAt (e : α) (obs : FinSet Stamp) : OrSet α :=
  ⟨AMap.empty, AMap.singleton e obs⟩

/-- The add-tags observed for `e` (the empty set if `e` was never added). -/
def tagsOf (s : OrSet α) (e : α) : FinSet Stamp := (s.adds.find e).getD FinSet.empty

/-- The tombstoned add-tags of `e` (the empty set if `e` was never removed). -/
def removedOf (s : OrSet α) (e : α) : FinSet Stamp := (s.removed.find e).getD FinSet.empty

/-- `e` is present iff some observed add-tag of it is not tombstoned *at `e`*
    (add-wins). Stated over the tag list so it is decidable for enumeration
    (`ready`/`list`). -/
def Present (s : OrSet α) (e : α) : Prop :=
  ∃ p ∈ (s.tagsOf e).toList, p.1 ∉ s.removedOf e

instance (s : OrSet α) (e : α) : Decidable (Present s e) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A present element has an add-tag entry. (Add-wins *distinctness* — that two
    concurrent adds stay distinct — additionally relies on the carried nonce/stamp
    uniqueness assumption, ADR-0007/overview Trusted; the kernel does not guard it,
    but convergence holds regardless.) -/
theorem isSome_of_present {s : OrSet α} {e : α} (h : Present s e) :
    (s.adds.find e).isSome = true := by
  cases hf : s.adds.find e with
  | some _ => rfl
  | none =>
    exfalso
    unfold Present at h
    obtain ⟨p, hp, _⟩ := h
    unfold tagsOf at hp
    rw [hf] at hp
    exact nomatch hp

/-- Every element ever added (present or not) — the keys of the add map. -/
def elements (s : OrSet α) : List α := s.adds.keys

/-- The present (live) elements — the enumeration `ready`/`list` iterate, proved to
    coincide exactly with `Present` (`mem_presentElements`), so theorems stated over
    `Present` are about the very set the CLI walks.

    One pass over `adds.toList`: each entry already carries its tag set, so
    liveness is decided in-place — no `find` per key. The old form
    (`elements.filter (Present)`) re-`find`-ed the tags for every key, an O(N)
    lookup per element ⇒ Θ(N²) per enumeration (the dominant `list`/`ready`/
    `stats`/`doctor` cost at scale). The per-entry tombstone lookup
    (`removedOf`) scans only the *removed-element* map — empty for add-only
    sets (issues), and each tag then probes only its own element's tombstones. -/
def presentElements (s : OrSet α) : List α :=
  (s.adds.toList.filter
    (fun p => decide (∃ q ∈ p.2.toList, q.1 ∉ s.removedOf p.1))).map Prod.fst

/-- Filtering then projecting the first component equals projecting then
    filtering, when the entry predicate agrees with the key predicate per entry. -/
theorem map_fst_filter_comm {β : Type _} {γ : Type _} (P : β → Bool) (Q : β × γ → Bool) :
    (l : List (β × γ)) → (∀ p ∈ l, Q p = P p.1) →
    (l.filter Q).map Prod.fst = (l.map Prod.fst).filter P
  | [], _ => rfl
  | p :: ps, h => by
    have hrec := map_fst_filter_comm P Q ps (fun q hq => h q (List.mem_cons_of_mem p hq))
    have hpq : Q p = P p.1 := h p (List.mem_cons_self ..)
    rw [List.map_cons]
    by_cases hP : P p.1 = true
    · rw [List.filter_cons_of_pos (hpq.trans hP), List.map_cons,
        List.filter_cons_of_pos hP, hrec]
    · rw [List.filter_cons_of_neg (fun hq => hP (hpq ▸ hq)),
        List.filter_cons_of_neg hP, hrec]

/-- The fast `presentElements` equals the spec shape `keys.filter Present` — the
    bridge that lets the `Present`-stated frame lemmas reuse their proofs. -/
theorem presentElements_eq_keys_filter (s : OrSet α) :
    s.presentElements = s.elements.filter (fun e => decide (Present s e)) := by
  unfold presentElements elements AMap.keys
  refine map_fst_filter_comm _ _ s.adds.toList (fun p hp => ?_)
  have hfind : s.adds.find p.1 = some p.2 := AMap.find_eq_some_of_mem hp
  have htag : s.tagsOf p.1 = p.2 := by unfold tagsOf; rw [hfind]; rfl
  show decide (∃ q ∈ p.2.toList, q.1 ∉ s.removedOf p.1) = decide (Present s p.1)
  unfold Present
  simp only [htag]

theorem mem_presentElements (s : OrSet α) (e : α) : e ∈ s.presentElements ↔ Present s e := by
  unfold presentElements
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, hpe⟩
    rw [List.mem_filter] at hp
    obtain ⟨hmem, hdec⟩ := hp
    have hc : ∃ q ∈ p.2.toList, q.1 ∉ s.removedOf p.1 := of_decide_eq_true hdec
    rw [hpe] at hc
    have hmem' : (e, p.2) ∈ s.adds.toList := by rw [← hpe]; exact hmem
    have hfind : s.adds.find e = some p.2 := AMap.find_eq_some_of_mem hmem'
    show Present s e
    unfold Present tagsOf
    rw [hfind]
    exact hc
  · intro hpres
    obtain ⟨tags, htags⟩ := Option.isSome_iff_exists.mp (isSome_of_present hpres)
    have hc : ∃ q ∈ tags.toList, q.1 ∉ s.removedOf e := by
      unfold Present tagsOf at hpres
      rw [htags] at hpres
      exact hpres
    exact ⟨(e, tags), List.mem_filter.mpr ⟨AMap.mem_toList_of_find htags, decide_eq_true hc⟩, rfl⟩

/-- The CRDT join — componentwise: both per-element maps join pointwise by
    `FinSet.union`. -/
def merge (s t : OrSet α) : OrSet α :=
  ⟨AMap.merge FinSet.union s.adds t.adds, AMap.merge FinSet.union s.removed t.removed⟩

/-- Two OR-Sets are equal when both components are (the `structure` is its two
    fields). -/
theorem ext {s t : OrSet α} (ha : s.adds = t.adds) (hr : s.removed = t.removed) : s = t := by
  obtain ⟨sa, sr⟩ := s
  obtain ⟨ta, tr⟩ := t
  subst ha; subst hr; rfl

theorem merge_comm (s t : OrSet α) : merge s t = merge t s :=
  ext (AMap.merge_comm (fun a b => FinSet.union_comm a b) s.adds t.adds)
      (AMap.merge_comm (fun a b => FinSet.union_comm a b) s.removed t.removed)

theorem merge_assoc (s t u : OrSet α) :
    merge (merge s t) u = merge s (merge t u) :=
  ext (AMap.merge_assoc (fun a b c => FinSet.union_assoc a b c) s.adds t.adds u.adds)
      (AMap.merge_assoc (fun a b c => FinSet.union_assoc a b c) s.removed t.removed u.removed)

theorem merge_idem (s : OrSet α) : merge s s = s :=
  ext (AMap.merge_idem (fun a => FinSet.union_idem a) s.adds)
      (AMap.merge_idem (fun a => FinSet.union_idem a) s.removed)

theorem merge_empty_left (s : OrSet α) : merge empty s = s :=
  ext (AMap.merge_empty_left _ s.adds) (AMap.merge_empty_left _ s.removed)

theorem merge_empty_right (s : OrSet α) : merge s empty = s :=
  ext (AMap.merge_empty_right _ s.adds) (AMap.merge_empty_right _ s.removed)

/-! ### Merge projections

The per-element reads distribute over the join: a merged state's tag set (and
tombstone set) at `e` is the union of the two sides'. These let the
add-wins/re-add/effectiveness theorems below compute a composite state's
presence directly. -/

theorem tagsOf_merge (s t : OrSet α) (e : α) :
    (merge s t).tagsOf e = FinSet.union (s.tagsOf e) (t.tagsOf e) := by
  unfold tagsOf
  show ((AMap.merge FinSet.union s.adds t.adds).find e).getD FinSet.empty = _
  rw [AMap.find_merge]
  cases hs : s.adds.find e with
  | none =>
    cases ht : t.adds.find e with
    | none =>
      show FinSet.empty = FinSet.union FinSet.empty FinSet.empty
      exact (FinSet.union_empty_left FinSet.empty).symm
    | some b =>
      show b = FinSet.union FinSet.empty b
      exact (FinSet.union_empty_left b).symm
  | some a =>
    cases ht : t.adds.find e with
    | none =>
      show a = FinSet.union a FinSet.empty
      exact (FinSet.union_empty_right a).symm
    | some b => rfl

theorem removedOf_merge (s t : OrSet α) (e : α) :
    (merge s t).removedOf e = FinSet.union (s.removedOf e) (t.removedOf e) := by
  unfold removedOf
  show ((AMap.merge FinSet.union s.removed t.removed).find e).getD FinSet.empty = _
  rw [AMap.find_merge]
  cases hs : s.removed.find e with
  | none =>
    cases ht : t.removed.find e with
    | none =>
      show FinSet.empty = FinSet.union FinSet.empty FinSet.empty
      exact (FinSet.union_empty_left FinSet.empty).symm
    | some b =>
      show b = FinSet.union FinSet.empty b
      exact (FinSet.union_empty_left b).symm
  | some a =>
    cases ht : t.removed.find e with
    | none =>
      show a = FinSet.union a FinSet.empty
      exact (FinSet.union_empty_right a).symm
    | some b => rfl

/-- An add delta's tags at its own element: the singleton of the new stamp. -/
theorem tagsOf_singletonAdd_self (e : α) (st : Stamp) :
    (singletonAdd e st).tagsOf e = FinSet.singleton st := by
  unfold tagsOf singletonAdd
  rw [AMap.find_singleton, if_pos rfl]
  rfl

/-- An add delta tombstones nothing. -/
theorem removedOf_singletonAdd (e0 : α) (st : Stamp) (e : α) :
    (singletonAdd e0 st).removedOf e = FinSet.empty := rfl

/-- A tombstone delta adds no tags. -/
theorem tagsOf_tombstonesAt (e0 : α) (obs : FinSet Stamp) (e : α) :
    (tombstonesAt e0 obs).tagsOf e = FinSet.empty := rfl

/-- A tombstone delta's tombstones at its own element: exactly the observed set. -/
theorem removedOf_tombstonesAt_self (e : α) (obs : FinSet Stamp) :
    (tombstonesAt e obs).removedOf e = obs := by
  unfold removedOf tombstonesAt
  rw [AMap.find_singleton, if_pos rfl]
  rfl

/-- `Present` phrased over set membership instead of the enumeration list — the
    intro/elim form the add-wins/re-add/effectiveness theorems use. -/
theorem present_iff_exists_live_tag (s : OrSet α) (e : α) :
    Present s e ↔ ∃ st, st ∈ s.tagsOf e ∧ st ∉ s.removedOf e := by
  unfold Present
  constructor
  · rintro ⟨p, hp, hlive⟩
    refine ⟨p.1, ?_, hlive⟩
    show (AMap.find (s.tagsOf e) p.1).isSome = true
    rw [AMap.find_eq_some_of_mem hp]
    rfl
  · rintro ⟨st, hmem, hlive⟩
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hmem
    exact ⟨(st, u), AMap.mem_toList_of_find hu, hlive⟩

/-- Frame workhorse (ADR-0003 §side-channels): merging in a single-element *add*
    `{e0 ↦ st}` and then filtering the present elements by a predicate `P` that
    *rejects* `e0` leaves the filtered list unchanged. An add at `e0` only adds the
    tag `st` to `e0` (presence of every other element is untouched) and may add the
    key `e0` (dropped by `P`); `removed` is unchanged. This is what makes a `related`
    edge add invisible to the `Blocks`/`Parent`-filtered edge views. -/
theorem presentElements_mergeAdd_filter (se : OrSet α) (e0 : α) (st : Stamp)
    {P : α → Bool} (hP : P e0 = false) :
    ((merge se (singletonAdd e0 st)).presentElements).filter P
      = (se.presentElements).filter P := by
  -- `removed` is untouched, and tags are untouched away from `e0`
  have hrem : (merge se (singletonAdd e0 st)).removed = se.removed := by
    show AMap.merge FinSet.union se.removed AMap.empty = se.removed
    exact AMap.merge_empty_right FinSet.union se.removed
  have hpres : ∀ a, a ≠ e0 →
      decide (Present (merge se (singletonAdd e0 st)) a) = decide (Present se a) := by
    intro a ha
    have hfind : (merge se (singletonAdd e0 st)).adds.find a = se.adds.find a := by
      show AMap.find (AMap.merge FinSet.union se.adds (AMap.singleton e0 (FinSet.singleton st))) a
        = se.adds.find a
      rw [AMap.find_merge, AMap.find_singleton, if_neg ha, optCombine_none_right]
    have htag : (merge se (singletonAdd e0 st)).tagsOf a = se.tagsOf a := by
      unfold tagsOf; rw [hfind]
    have hremOf : (merge se (singletonAdd e0 st)).removedOf a = se.removedOf a := by
      unfold removedOf; rw [hrem]
    have hiff : Present (merge se (singletonAdd e0 st)) a ↔ Present se a := by
      unfold Present; rw [htag, hremOf]
    simp only [hiff]
  -- collapse the double filter, normalise the redex via `show`, swap list then predicate
  rw [presentElements_eq_keys_filter, presentElements_eq_keys_filter]
  rw [List.filter_filter, List.filter_filter]
  show List.filter (fun a => P a && decide (Present (merge se (singletonAdd e0 st)) a))
        (merge se (singletonAdd e0 st)).elements
     = List.filter (fun a => P a && decide (Present se a)) se.elements
  rw [show (merge se (singletonAdd e0 st)).elements
        = (AMap.merge FinSet.union se.adds (AMap.singleton e0 (FinSet.singleton st))).keys from rfl,
    AMap.keys_merge_singleton_filter se.adds e0 (FinSet.singleton st)
      (show (fun a => P a && decide (Present (merge se (singletonAdd e0 st)) a)) e0 = false by
        show (P e0 && decide (Present (merge se (singletonAdd e0 st)) e0)) = false
        rw [hP, Bool.false_and])]
  show se.elements.filter (fun a => P a && decide (Present (merge se (singletonAdd e0 st)) a))
     = se.elements.filter (fun a => P a && decide (Present se a))
  apply List.filter_congr
  intro a _
  by_cases ha : a = e0
  · subst ha; rw [hP, Bool.false_and, Bool.false_and]
  · rw [hpres a ha]

/-- Removal workhorse (the `unrelate` frame counterpart of
    `presentElements_mergeAdd_filter`): merging in a pure-tombstone delta keyed at
    `e0` and then filtering the present elements by a predicate `P` that *rejects*
    `e0` leaves the filtered list unchanged — for **any** observed payload `obs`,
    well-formed or not. The delta's `adds` leg is empty (keys and tags of every
    element are untouched) and its tombstones live only under the key `e0`, so
    only `e0`'s presence can change — and `P` drops `e0`. This is what makes an
    `unrelate` invisible to the `Blocks`/`Parent`-filtered edge views with no
    stamp-uniqueness side condition. -/
theorem presentElements_mergeTombstonesAt_filter (se : OrSet α) (e0 : α) (obs : FinSet Stamp)
    {P : α → Bool} (hP : P e0 = false) :
    ((merge se (tombstonesAt e0 obs)).presentElements).filter P
      = (se.presentElements).filter P := by
  -- `adds` is untouched, and tombstones are untouched away from `e0`
  have hadds : (merge se (tombstonesAt e0 obs)).adds = se.adds := by
    show AMap.merge FinSet.union se.adds AMap.empty = se.adds
    exact AMap.merge_empty_right FinSet.union se.adds
  have hpres : ∀ a, a ≠ e0 →
      decide (Present (merge se (tombstonesAt e0 obs)) a) = decide (Present se a) := by
    intro a ha
    have htag : (merge se (tombstonesAt e0 obs)).tagsOf a = se.tagsOf a := by
      unfold tagsOf; rw [hadds]
    have hremOf : (merge se (tombstonesAt e0 obs)).removedOf a = se.removedOf a := by
      show ((AMap.merge FinSet.union se.removed (AMap.singleton e0 obs)).find a).getD FinSet.empty
        = (se.removed.find a).getD FinSet.empty
      rw [AMap.find_merge, AMap.find_singleton, if_neg ha, optCombine_none_right]
    have hiff : Present (merge se (tombstonesAt e0 obs)) a ↔ Present se a := by
      unfold Present; rw [htag, hremOf]
    simp only [hiff]
  -- same key list on both sides (`adds` fixed); agree pointwise under the filter
  rw [presentElements_eq_keys_filter, presentElements_eq_keys_filter]
  rw [List.filter_filter, List.filter_filter]
  show List.filter (fun a => P a && decide (Present (merge se (tombstonesAt e0 obs)) a))
        (merge se (tombstonesAt e0 obs)).elements
     = List.filter (fun a => P a && decide (Present se a)) se.elements
  rw [show (merge se (tombstonesAt e0 obs)).elements = se.elements by
    unfold elements; rw [hadds]]
  apply List.filter_congr
  intro a _
  by_cases ha : a = e0
  · subst ha; rw [hP, Bool.false_and, Bool.false_and]
  · rw [hpres a ha]

/-! ## Add-wins, re-add, and removal effectiveness (ADR-0002)

ADR-0002's remove semantics, elevated from prose to theorems. Where a claim
leans on stamp freshness — a newly minted add-tag is in no earlier `observed`
set and no earlier tombstone — that reliance is an **explicit hypothesis**
(`st ∉ obs`, `st ∉ s.removedOf e`), never silent: in a live system those
hypotheses are discharged by the carried nonce/stamp-uniqueness assumption
(overview Trusted, ADR-0007), which is exactly where that assumption is
*allowed* to enter. Removal effectiveness needs no such hypothesis. -/

/-- **Add-wins** (ADR-0002): an add whose tag the concurrent remove did not
    observe survives the merge. `hunobserved` is the concurrency itself (the
    remover never saw `st`); `hfresh` — no earlier remove tombstoned the fresh
    mint at `e` — is the explicit stamp-freshness hypothesis. The join order is
    immaterial by `merge_comm`/`merge_assoc`. -/
theorem present_addWins (s : OrSet α) (e : α) (st : Stamp) (obs : FinSet Stamp)
    (hunobserved : st ∉ obs) (hfresh : st ∉ s.removedOf e) :
    Present (merge (merge s (singletonAdd e st)) (tombstonesAt e obs)) e := by
  apply (present_iff_exists_live_tag ..).mpr
  refine ⟨st, ?_, ?_⟩
  · rw [tagsOf_merge, tagsOf_merge, tagsOf_tombstonesAt, FinSet.union_empty_right,
      tagsOf_singletonAdd_self]
    exact (FinSet.mem_union ..).mpr (Or.inr ((FinSet.mem_singleton ..).mpr rfl))
  · rw [removedOf_merge, removedOf_merge, removedOf_singletonAdd, FinSet.union_empty_right,
      removedOf_tombstonesAt_self]
    intro hmem
    rcases (FinSet.mem_union ..).mp hmem with h | h
    · exact hfresh h
    · exact hunobserved h

/-- **Re-add** (ADR-0002): after a remove — even one whose `obs` covered *every*
    prior tag of `e`, wiping it (`not_present_mergeTombstonesAt_of_observed_all`
    below) — an add with a fresh tag makes `e` present again: an OR-Set is not a
    2P-set. Freshness of the new stamp (`st ∉ obs`, `st ∉ s.removedOf e`) is the
    explicit stamp-uniqueness hypothesis. -/
theorem present_readd (s : OrSet α) (e : α) (st : Stamp) (obs : FinSet Stamp)
    (hunobserved : st ∉ obs) (hfresh : st ∉ s.removedOf e) :
    Present (merge (merge s (tombstonesAt e obs)) (singletonAdd e st)) e := by
  apply (present_iff_exists_live_tag ..).mpr
  refine ⟨st, ?_, ?_⟩
  · rw [tagsOf_merge, tagsOf_merge, tagsOf_tombstonesAt, FinSet.union_empty_right,
      tagsOf_singletonAdd_self]
    exact (FinSet.mem_union ..).mpr (Or.inr ((FinSet.mem_singleton ..).mpr rfl))
  · rw [removedOf_merge, removedOf_merge, removedOf_tombstonesAt_self, removedOf_singletonAdd,
      FinSet.union_empty_right]
    intro hmem
    rcases (FinSet.mem_union ..).mp hmem with h | h
    · exact hfresh h
    · exact hunobserved h

/-- **Removal effectiveness** (ADR-0002): a remove that observed *all* of `e`'s
    add-tags makes `e` absent — tombstones genuinely remove; a `Present` that
    ignored them could not satisfy this. The hypothesis is precise for the
    *merged* state: the tombstone delta adds no tags (`tagsOf_tombstonesAt`), so
    `s.tagsOf e` *is* the merged state's tag set at `e`. Unconditional — no
    stamp-uniqueness enters. -/
theorem not_present_mergeTombstonesAt_of_observed_all (s : OrSet α) (e : α)
    (obs : FinSet Stamp) (hall : ∀ st, st ∈ s.tagsOf e → st ∈ obs) :
    ¬ Present (merge s (tombstonesAt e obs)) e := by
  intro hpres
  obtain ⟨st, hmem, hlive⟩ := (present_iff_exists_live_tag ..).mp hpres
  rw [tagsOf_merge, tagsOf_tombstonesAt, FinSet.union_empty_right] at hmem
  apply hlive
  rw [removedOf_merge, removedOf_tombstonesAt_self]
  exact (FinSet.mem_union ..).mpr (Or.inr (hall st hmem))

end OrSet

end Tl.Crdt
