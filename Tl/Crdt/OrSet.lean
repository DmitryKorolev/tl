/-
`Tl.Crdt.OrSet` — the observed-remove set (ADR-0002).

The collections that must support a convergent remove — the dependency-edge set
(`dep remove` is first-class, the forcing function for OR-Set over a grow-only
set) and the per-issue label sets — are OR-Sets. `adds` records, per element, the
set of add-tags observed for it (each add-tag is the adding op's `Stamp`,
ADR-0007/0008); `removed` tombstones the add-tags a remove has *observed*. An
element is present iff it still has a live (untombstoned) add-tag — concurrent
add/remove resolves **add-wins** (an add the remover never saw survives), the
conservative bias for blockers (ADR-0002).

Issues are *resolved, not removed* (ADR-0002): the issue OR-Set is add-only in
practice, but the same construction backs it. The join is componentwise — the
per-element add map joined by `FinSet.union`, the tombstone set joined by
`FinSet.union` — so commutativity/associativity/idempotence are inherited.
-/
import Tl.Crdt.Map

namespace Tl.Crdt

open TotalOrd

universe u

/-- An observed-remove set over `α` (ADR-0002): observed add-tags per element,
    plus a global tombstone set of removed add-tags. -/
structure OrSet (α : Type u) [TotalOrd α] where
  /-- Per element, the add-tags (op stamps) observed for it. -/
  adds : AMap α (FinSet Stamp)
  /-- Tombstoned add-tags (add-wins: only *observed* tags are tombstoned). -/
  removed : FinSet Stamp

namespace OrSet

variable {α : Type u} [TotalOrd α]

/-- The empty OR-Set. -/
def empty : OrSet α := ⟨AMap.empty, FinSet.empty⟩

/-- The one-element delta `{e}` tagged `st` — an `add`'s contribution as a
    standalone OR-Set, joined into a state by `merge` (ADR-0001: apply = join with
    delta). -/
def singletonAdd (e : α) (st : Stamp) : OrSet α :=
  ⟨AMap.singleton e (FinSet.singleton st), FinSet.empty⟩

/-- A pure-tombstone delta — a `remove`'s contribution: tombstone the observed
    add-tags `obs`, joined into a state by `merge`. -/
def tombstones (obs : FinSet Stamp) : OrSet α := ⟨AMap.empty, obs⟩

/-- The add-tags observed for `e` (the empty set if `e` was never added). -/
def tagsOf (s : OrSet α) (e : α) : FinSet Stamp := (s.adds.find e).getD FinSet.empty

/-- `e` is present iff some observed add-tag of it is not tombstoned (add-wins).
    Stated over the tag list so it is decidable for enumeration (`ready`/`list`). -/
def Present (s : OrSet α) (e : α) : Prop :=
  ∃ p ∈ (s.tagsOf e).toList, p.1 ∉ s.removed

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
    `stats`/`doctor` cost at scale). -/
def presentElements (s : OrSet α) : List α :=
  (s.adds.toList.filter (fun p => decide (∃ q ∈ p.2.toList, q.1 ∉ s.removed))).map Prod.fst

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
  show decide (∃ q ∈ p.2.toList, q.1 ∉ s.removed) = decide (Present s p.1)
  unfold Present
  simp only [htag]

theorem mem_presentElements (s : OrSet α) (e : α) : e ∈ s.presentElements ↔ Present s e := by
  unfold presentElements
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, hpe⟩
    rw [List.mem_filter] at hp
    obtain ⟨hmem, hdec⟩ := hp
    have hc : ∃ q ∈ p.2.toList, q.1 ∉ s.removed := of_decide_eq_true hdec
    have hmem' : (e, p.2) ∈ s.adds.toList := by rw [← hpe]; exact hmem
    have hfind : s.adds.find e = some p.2 := AMap.find_eq_some_of_mem hmem'
    show Present s e
    unfold Present tagsOf
    rw [hfind]
    exact hc
  · intro hpres
    obtain ⟨tags, htags⟩ := Option.isSome_iff_exists.mp (isSome_of_present hpres)
    have hc : ∃ q ∈ tags.toList, q.1 ∉ s.removed := by
      unfold Present tagsOf at hpres
      rw [htags] at hpres
      exact hpres
    exact ⟨(e, tags), List.mem_filter.mpr ⟨AMap.mem_toList_of_find htags, decide_eq_true hc⟩, rfl⟩

/-- The CRDT join — componentwise. -/
def merge (s t : OrSet α) : OrSet α :=
  ⟨AMap.merge FinSet.union s.adds t.adds, FinSet.union s.removed t.removed⟩

/-- Two OR-Sets are equal when both components are (the `structure` is its two
    fields). -/
theorem ext {s t : OrSet α} (ha : s.adds = t.adds) (hr : s.removed = t.removed) : s = t := by
  obtain ⟨sa, sr⟩ := s
  obtain ⟨ta, tr⟩ := t
  subst ha; subst hr; rfl

theorem merge_comm (s t : OrSet α) : merge s t = merge t s :=
  ext (AMap.merge_comm (fun a b => FinSet.union_comm a b) s.adds t.adds)
      (FinSet.union_comm s.removed t.removed)

theorem merge_assoc (s t u : OrSet α) :
    merge (merge s t) u = merge s (merge t u) :=
  ext (AMap.merge_assoc (fun a b c => FinSet.union_assoc a b c) s.adds t.adds u.adds)
      (FinSet.union_assoc s.removed t.removed u.removed)

theorem merge_idem (s : OrSet α) : merge s s = s :=
  ext (AMap.merge_idem (fun a => FinSet.union_idem a) s.adds)
      (FinSet.union_idem s.removed)

theorem merge_empty_left (s : OrSet α) : merge empty s = s :=
  ext (AMap.merge_empty_left _ s.adds) (FinSet.union_empty_left s.removed)

theorem merge_empty_right (s : OrSet α) : merge s empty = s :=
  ext (AMap.merge_empty_right _ s.adds) (FinSet.union_empty_right s.removed)

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
    show FinSet.union se.removed FinSet.empty = se.removed
    exact FinSet.union_empty_right se.removed
  have hpres : ∀ a, a ≠ e0 →
      decide (Present (merge se (singletonAdd e0 st)) a) = decide (Present se a) := by
    intro a ha
    have hfind : (merge se (singletonAdd e0 st)).adds.find a = se.adds.find a := by
      show AMap.find (AMap.merge FinSet.union se.adds (AMap.singleton e0 (FinSet.singleton st))) a
        = se.adds.find a
      rw [AMap.find_merge, AMap.find_singleton, if_neg ha, optCombine_none_right]
    have htag : (merge se (singletonAdd e0 st)).tagsOf a = se.tagsOf a := by
      unfold tagsOf; rw [hfind]
    have hiff : Present (merge se (singletonAdd e0 st)) a ↔ Present se a := by
      unfold Present; rw [htag, hrem]
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

end OrSet

end Tl.Crdt
