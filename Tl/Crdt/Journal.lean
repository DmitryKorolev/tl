/-
`Tl.Crdt.Journal` — the append-only notes journal (ADR-0027).

A journal is an OR-Set whose element IS the add-tag (each entry has exactly
one add-tag by construction — the add op's `(hlc, replica, nonce)` stamp),
plus a payload map keyed by the same tag. Nothing here is keyed by the
16-char user-facing handle: it is carried payload, so two records carrying
equal handle bytes from distinct stamps are two independent entries, and a
tombstone — keyed by tag — cannot reach a sibling under any payload bytes
(remove-exactness, unconditional).

Payloads of records sharing one complete stamp fold to one entry; that
entry's payload joins by the unconditional lexicographic max over the
canonical `(text, handle, actor)` tuple, `none` actor below every string —
`TotalOrd.tmax` under a pulled-back total order, the same realization
discipline as the LWW value tie-break (ADR-0002). Under honest writers the
rule never fires (one op, one payload); on adversarial or duplicated records
determinism, not any particular winner, is the guarantee.

The OR-Set is add-wins, but for the journal the distinction collapses: tags
are unique and never re-added — no op can re-add a removed entry's tag — so
the journal behaves as a 2P-set (tombstoned forever) on add-wins machinery
(ADR-0027, stated there so nobody "fixes" it).
-/
import Tl.Crdt.OrSet

namespace Tl.Crdt

open TotalOrd

/-- One entry's payload: the minted user-facing handle, the text, and the
    envelope actor — all carried data, none of it a kernel key. -/
structure NotePayload where
  /-- The minted 16-char note id (ADR-0027) — reference ergonomics only. -/
  handle : String
  /-- The immutable entry text. -/
  text : String
  /-- The envelope actor (provenance, ADR-0013; never authentication). -/
  actor : Option String
deriving Repr

namespace NotePayload

/-- The canonical join tuple `(text, handle, actor)`. It carries every field,
    so tuple equality is payload equality and the max below is antisymmetric. -/
def key (p : NotePayload) : String × String × Option String := (p.text, p.handle, p.actor)

theorem key_injective : Function.Injective key := by
  intro a b h
  cases a; cases b
  simp only [key, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1; subst h2; subst h3; rfl

/-- Payloads ordered by the canonical tuple: strings lexicographically (the
    project `String` order), `none` actor below every string (the `Option`
    order). -/
instance : TotalOrd NotePayload := TotalOrd.comap key key_injective

/-- The payload join: the `le`-greater payload — a semilattice max, so the
    per-tag payload map is a CRDT with no side condition. -/
def join (a b : NotePayload) : NotePayload := tmax a b

theorem join_comm (a b : NotePayload) : join a b = join b a := tmax_comm a b

theorem join_assoc (a b c : NotePayload) : join (join a b) c = join a (join b c) :=
  tmax_assoc a b c

theorem join_idem (a : NotePayload) : join a a = a := tmax_idem a

end NotePayload

/-- The notes journal (ADR-0027): entry membership as an OR-Set over the
    add-tags themselves, payloads keyed by the same tag. -/
structure Journal where
  /-- Entry membership; the element is the entry's add-tag. -/
  entries : OrSet Stamp
  /-- Per-tag payloads, joined by `NotePayload.join`. -/
  payloads : AMap Stamp NotePayload

namespace Journal

/-- The empty journal. -/
def empty : Journal := ⟨OrSet.empty, AMap.empty⟩

/-- A `noteAdd`'s contribution: the op's stamp is both the element and its one
    add-tag; the payload keyed by it. -/
def addDelta (st : Stamp) (p : NotePayload) : Journal :=
  ⟨OrSet.singletonAdd st st, AMap.singleton st p⟩

/-- The self-keyed tombstone map of an observed set: each observed tag `t`
    tombstones element `t` at tag `t` (the element is the tag). -/
def selfTombstones (obs : FinSet Stamp) : AMap Stamp (FinSet Stamp) :=
  obs.mapVal (fun t _ => FinSet.singleton t)

/-- A `noteRemove`'s contribution: tombstone each observed tag at itself. No
    adds, no payloads — a remove's own stamp is never materialized (ADR-0027:
    `noteRemove` does not bump `updatedAt`). -/
def removeDelta (obs : FinSet Stamp) : Journal :=
  ⟨⟨AMap.empty, selfTombstones obs⟩, AMap.empty⟩

/-- The CRDT join — componentwise: OR-Set merge on membership, pointwise
    `NotePayload.join` on payloads. -/
def merge (a b : Journal) : Journal :=
  ⟨OrSet.merge a.entries b.entries, AMap.merge NotePayload.join a.payloads b.payloads⟩

/-! Projection `rfl`-lemmas — expose the component joins to `rw`. -/

theorem entries_merge (a b : Journal) :
    (merge a b).entries = OrSet.merge a.entries b.entries := rfl

theorem payloads_merge (a b : Journal) :
    (merge a b).payloads = AMap.merge NotePayload.join a.payloads b.payloads := rfl

theorem entries_addDelta (st : Stamp) (p : NotePayload) :
    (addDelta st p).entries = OrSet.singletonAdd st st := rfl

theorem payloads_removeDelta (obs : FinSet Stamp) :
    (removeDelta obs).payloads = AMap.empty := rfl

/-- An entry is visible iff its element is present (its tag has a live,
    untombstoned add). -/
def Visible (j : Journal) (st : Stamp) : Prop := j.entries.Present st

instance (j : Journal) (st : Stamp) : Decidable (j.Visible st) :=
  inferInstanceAs (Decidable (j.entries.Present st))

/-- The payload recorded for a tag (visible or removed), if any add carried one. -/
def payloadOf (j : Journal) (st : Stamp) : Option NotePayload := j.payloads.find st

/-! ## Join laws — union convergence on both legs -/

theorem ext {a b : Journal} (he : a.entries = b.entries)
    (hp : a.payloads = b.payloads) : a = b := by
  obtain ⟨ae, ap⟩ := a
  obtain ⟨be, bp⟩ := b
  subst he; subst hp; rfl

theorem merge_comm (a b : Journal) : merge a b = merge b a :=
  ext (OrSet.merge_comm a.entries b.entries)
      (AMap.merge_comm (fun x y => NotePayload.join_comm x y) a.payloads b.payloads)

theorem merge_assoc (a b c : Journal) : merge (merge a b) c = merge a (merge b c) :=
  ext (OrSet.merge_assoc a.entries b.entries c.entries)
      (AMap.merge_assoc (fun x y z => NotePayload.join_assoc x y z)
        a.payloads b.payloads c.payloads)

theorem merge_idem (a : Journal) : merge a a = a :=
  ext (OrSet.merge_idem a.entries)
      (AMap.merge_idem (fun x => NotePayload.join_idem x) a.payloads)

theorem merge_empty_left (a : Journal) : merge empty a = a :=
  ext (OrSet.merge_empty_left a.entries) (AMap.merge_empty_left _ a.payloads)

theorem merge_empty_right (a : Journal) : merge a empty = a :=
  ext (OrSet.merge_empty_right a.entries) (AMap.merge_empty_right _ a.payloads)

/-- Delivery-order independence at the delta level: two deltas fold in either
    order to the same journal (with duplication handled by `merge_idem`, this
    is what the state-level fold permutation theorems instantiate). -/
theorem merge_right_comm (j a b : Journal) :
    merge (merge j a) b = merge (merge j b) a := by
  rw [merge_assoc, merge_comm a b, ← merge_assoc]

/-- Duplicate delivery of one add is one entry: folding the same delta twice
    is folding it once. -/
theorem merge_addDelta_duplicate (j : Journal) (st : Stamp) (p : NotePayload) :
    merge (merge j (addDelta st p)) (addDelta st p) = merge j (addDelta st p) := by
  rw [merge_assoc, merge_idem]

/-! ## Tombstone projections of the deltas -/

theorem removedOf_removeDelta_of_mem {obs : FinSet Stamp} {t : Stamp} (h : t ∈ obs) :
    (removeDelta obs).entries.removedOf t = FinSet.singleton t := by
  unfold OrSet.removedOf
  show ((selfTombstones obs).find t).getD FinSet.empty = FinSet.singleton t
  unfold selfTombstones
  rw [AMap.find_mapVal]
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
  rw [hu]
  rfl

theorem removedOf_removeDelta_of_not_mem {obs : FinSet Stamp} {t : Stamp} (h : t ∉ obs) :
    (removeDelta obs).entries.removedOf t = FinSet.empty := by
  unfold OrSet.removedOf
  show ((selfTombstones obs).find t).getD FinSet.empty = FinSet.empty
  unfold selfTombstones
  rw [AMap.find_mapVal]
  cases hf : AMap.find obs t with
  | none => rfl
  | some u =>
    exfalso
    exact h (by show (AMap.find obs t).isSome = true; rw [hf]; rfl)

/-! ## Visibility: adds, removes, exactness, no resurrection

Where a claim leans on tag freshness — a newly minted stamp is in no earlier
observed set and no earlier tombstone — that reliance is an explicit
hypothesis, discharged in a live system by the carried nonce/stamp-uniqueness
assumption (overview Trusted, ADR-0007). Remove-exactness and the hiding
theorems carry no such hypothesis on payloads: handles are not kernel keys. -/

/-- A fresh add is visible: joining `addDelta st p` into any journal that has
    not tombstoned `st` at itself makes `st` visible. `hfresh` is the explicit
    stamp-freshness hypothesis. -/
theorem visible_merge_addDelta (j : Journal) (st : Stamp) (p : NotePayload)
    (hfresh : st ∉ j.entries.removedOf st) :
    (merge j (addDelta st p)).Visible st := by
  apply (OrSet.present_iff_exists_live_tag ..).mpr
  refine ⟨st, ?_, ?_⟩
  · rw [entries_merge, OrSet.tagsOf_merge]
    exact (FinSet.mem_union ..).mpr
      (Or.inr (by rw [entries_addDelta, OrSet.tagsOf_singletonAdd_self]
                  exact (FinSet.mem_singleton ..).mpr rfl))
  · rw [entries_merge, OrSet.removedOf_merge, entries_addDelta,
      OrSet.removedOf_singletonAdd, FinSet.union_empty_right]
    exact hfresh

/-- Concurrent adds are all retained: after both deltas fold (either order —
    `merge_right_comm`), both entries are visible. No distinctness hypothesis:
    if the stamps coincide the two conjuncts name the same (visible) entry. -/
theorem visible_both_concurrent_adds (j : Journal) (st1 st2 : Stamp)
    (p1 p2 : NotePayload)
    (h1 : st1 ∉ j.entries.removedOf st1) (h2 : st2 ∉ j.entries.removedOf st2) :
    (merge (merge j (addDelta st1 p1)) (addDelta st2 p2)).Visible st1 ∧
    (merge (merge j (addDelta st1 p1)) (addDelta st2 p2)).Visible st2 := by
  constructor
  · rw [merge_right_comm]
    apply visible_merge_addDelta
    rw [entries_merge, OrSet.removedOf_merge, entries_addDelta,
      OrSet.removedOf_singletonAdd, FinSet.union_empty_right]
    exact h1
  · apply visible_merge_addDelta
    rw [entries_merge, OrSet.removedOf_merge, entries_addDelta,
      OrSet.removedOf_singletonAdd, FinSet.union_empty_right]
    exact h2

/-- Every journal reachable by folding note deltas carries only self-tags:
    element `e`'s tag set is `⊆ {e}` (an add contributes exactly its own stamp).
    The closure lemmas below discharge the `htags` hypotheses of the hiding
    theorems for every delta-folded state. -/
def SelfTagged (j : Journal) : Prop :=
  ∀ e t : Stamp, t ∈ j.entries.tagsOf e → t = e

theorem selfTagged_empty : SelfTagged empty := by
  intro e t ht
  exact absurd ht (FinSet.not_mem_empty t)

theorem selfTagged_addDelta (st : Stamp) (p : NotePayload) :
    SelfTagged (addDelta st p) := by
  intro e t ht
  unfold OrSet.tagsOf at ht
  rw [show (addDelta st p).entries.adds = AMap.singleton st (FinSet.singleton st) from rfl,
    AMap.find_singleton] at ht
  by_cases he : e = st
  · rw [ite_eq_left he] at ht
    have hts : t = st := (FinSet.mem_singleton ..).mp ht
    rw [he]
    exact hts
  · rw [ite_eq_right he] at ht
    exact absurd ht (FinSet.not_mem_empty t)

theorem selfTagged_removeDelta (obs : FinSet Stamp) :
    SelfTagged (removeDelta obs) := by
  intro e t ht
  exact absurd ht (FinSet.not_mem_empty t)

theorem selfTagged_merge {a b : Journal} (ha : SelfTagged a) (hb : SelfTagged b) :
    SelfTagged (merge a b) := by
  intro e t ht
  rw [entries_merge, OrSet.tagsOf_merge] at ht
  rcases (FinSet.mem_union ..).mp ht with h | h
  · exact ha e t h
  · exact hb e t h

/-- A remove hides its entry: after joining `removeDelta obs` with `st ∈ obs`,
    `st` is not visible — for **any** observed payload, provided the base
    journal carries only self-tags at `st` (true of every delta-folded journal;
    `SelfTagged`). -/
theorem not_visible_merge_removeDelta (j : Journal) (st : Stamp) (obs : FinSet Stamp)
    (hobs : st ∈ obs) (htags : ∀ t, t ∈ j.entries.tagsOf st → t = st) :
    ¬ (merge j (removeDelta obs)).Visible st := by
  intro hpres
  obtain ⟨t, hmem, hlive⟩ := (OrSet.present_iff_exists_live_tag ..).mp hpres
  rw [entries_merge, OrSet.tagsOf_merge] at hmem
  have ht : t = st := by
    rcases (FinSet.mem_union ..).mp hmem with h | h
    · exact htags t h
    · exact absurd h (FinSet.not_mem_empty t)
  subst ht
  apply hlive
  rw [entries_merge, OrSet.removedOf_merge, removedOf_removeDelta_of_mem hobs]
  exact (FinSet.mem_union ..).mpr (Or.inr ((FinSet.mem_singleton ..).mpr rfl))

/-- Removal is delivery-order independent: a remove folded **before** its add
    still hides the entry when the add arrives — the tombstone is taken from
    the record by tag value, not a presence check. -/
theorem not_visible_removeDelta_then_addDelta (j : Journal) (st : Stamp)
    (p : NotePayload) (obs : FinSet Stamp) (hobs : st ∈ obs)
    (htags : ∀ t, t ∈ j.entries.tagsOf st → t = st) :
    ¬ (merge (merge j (removeDelta obs)) (addDelta st p)).Visible st := by
  rw [merge_right_comm]
  apply not_visible_merge_removeDelta
  · exact hobs
  · intro t ht
    rw [entries_merge, OrSet.tagsOf_merge] at ht
    rcases (FinSet.mem_union ..).mp ht with h | h
    · exact htags t h
    · rw [entries_addDelta, OrSet.tagsOf_singletonAdd_self] at h
      exact (FinSet.mem_singleton ..).mp h

/-- Remove-exactness, unconditional: a remove affects exactly the tags it
    names. For any `st ∉ obs`, visibility is untouched — under any payload
    bytes, with no freshness or uniqueness hypothesis (handles are payload,
    never a kernel key; the tombstone map has no entry off `obs`). -/
theorem visible_merge_removeDelta_iff_of_not_mem (j : Journal) (obs : FinSet Stamp)
    (st : Stamp) (h : st ∉ obs) :
    ((merge j (removeDelta obs)).Visible st ↔ j.Visible st) := by
  show (merge j (removeDelta obs)).entries.Present st ↔ j.entries.Present st
  have htag : (merge j (removeDelta obs)).entries.tagsOf st = j.entries.tagsOf st := by
    rw [entries_merge, OrSet.tagsOf_merge,
      show (removeDelta obs).entries.tagsOf st = FinSet.empty from rfl,
      FinSet.union_empty_right]
  have hrem : (merge j (removeDelta obs)).entries.removedOf st = j.entries.removedOf st := by
    rw [entries_merge, OrSet.removedOf_merge, removedOf_removeDelta_of_not_mem h,
      FinSet.union_empty_right]
  unfold OrSet.Present
  rw [htag, hrem]

/-- Tombstones only grow under merge — half of no-resurrection. -/
theorem tombstone_mono (j k : Journal) {e t : Stamp}
    (h : t ∈ j.entries.removedOf e) : t ∈ (merge j k).entries.removedOf e := by
  rw [entries_merge, OrSet.removedOf_merge]
  exact (FinSet.mem_union ..).mpr (Or.inl h)

/-- No resurrection, merge-general: once `st` is tombstoned at itself, no
    further self-tagged journal — any fold of note deltas, per the closure
    lemmas above and `Tl.Kernel.selfTagged_fold` — can make it visible again. -/
theorem not_visible_merge_of_tombstoned {j k : Journal} (st : Stamp)
    (htomb : st ∈ j.entries.removedOf st)
    (hj : SelfTagged j) (hk : SelfTagged k) :
    ¬ (merge j k).Visible st := by
  intro hpres
  obtain ⟨t, hmem, hlive⟩ := (OrSet.present_iff_exists_live_tag ..).mp hpres
  have ht : t = st := selfTagged_merge hj hk st t hmem
  subst ht
  exact hlive (tombstone_mono j k htomb)

/-- The single-add instance: a tombstoned entry stays hidden under a re-add of
    its own tag (the only add any note op can contribute for that element). -/
theorem not_visible_merge_addDelta_of_tombstoned (j : Journal) (st : Stamp)
    (p : NotePayload) (htomb : st ∈ j.entries.removedOf st) (hj : SelfTagged j) :
    ¬ (merge j (addDelta st p)).Visible st :=
  not_visible_merge_of_tombstoned st htomb hj (selfTagged_addDelta st p)

/-- Removal never touches payloads — the payload half of remove-exactness: a
    `removeDelta` carries no payload map, so every recorded payload (visible or
    removed) is byte-identical after the merge. -/
theorem payloads_merge_removeDelta (j : Journal) (obs : FinSet Stamp) :
    (merge j (removeDelta obs)).payloads = j.payloads := by
  rw [payloads_merge, payloads_removeDelta]
  exact AMap.merge_empty_right NotePayload.join j.payloads

theorem payloadOf_merge_removeDelta (j : Journal) (obs : FinSet Stamp) (st : Stamp) :
    (merge j (removeDelta obs)).payloadOf st = j.payloadOf st := by
  show (merge j (removeDelta obs)).payloads.find st = j.payloads.find st
  rw [payloads_merge_removeDelta]

/-! ## Payload totality: every visible entry has a payload

`visibleEntries` skips an element without a payload; `PayloadTotal` (with its
closure set and the fold-level discharge `Tl.Kernel.payloadTotal_fold`) proves
that case unreachable for every state built from the op deltas — the skip is a
totality device, not a behavior. -/

/-- Every visible entry carries a payload. -/
def PayloadTotal (j : Journal) : Prop :=
  ∀ st, j.Visible st → (j.payloadOf st).isSome = true

/-- A merged state's visible entry was visible on (at least) one side: its
    witness tag lives in one side's adds, and that side's tombstones are a
    subset of the union's. -/
theorem visible_merge_cases {a b : Journal} {st : Stamp}
    (h : (merge a b).Visible st) : a.Visible st ∨ b.Visible st := by
  obtain ⟨t, hmem, hlive⟩ := (OrSet.present_iff_exists_live_tag ..).mp h
  rw [entries_merge, OrSet.tagsOf_merge] at hmem
  rw [entries_merge, OrSet.removedOf_merge] at hlive
  rcases (FinSet.mem_union ..).mp hmem with hm | hm
  · exact Or.inl ((OrSet.present_iff_exists_live_tag ..).mpr
      ⟨t, hm, fun hin => hlive ((FinSet.mem_union ..).mpr (Or.inl hin))⟩)
  · exact Or.inr ((OrSet.present_iff_exists_live_tag ..).mpr
      ⟨t, hm, fun hin => hlive ((FinSet.mem_union ..).mpr (Or.inr hin))⟩)

theorem payloadTotal_empty : PayloadTotal empty := by
  intro st h
  obtain ⟨t, hmem, _⟩ := (OrSet.present_iff_exists_live_tag ..).mp h
  exact absurd hmem (FinSet.not_mem_empty t)

theorem payloadTotal_addDelta (st : Stamp) (p : NotePayload) :
    PayloadTotal (addDelta st p) := by
  intro st' h
  obtain ⟨t, hmem, _⟩ := (OrSet.present_iff_exists_live_tag ..).mp h
  unfold OrSet.tagsOf at hmem
  rw [show (addDelta st p).entries.adds = AMap.singleton st (FinSet.singleton st) from rfl,
    AMap.find_singleton] at hmem
  by_cases he : st' = st
  · show ((addDelta st p).payloads.find st').isSome = true
    rw [show (addDelta st p).payloads = AMap.singleton st p from rfl,
      AMap.find_singleton, ite_eq_left he]
    rfl
  · rw [ite_eq_right he] at hmem
    exact absurd hmem (FinSet.not_mem_empty t)

theorem payloadTotal_removeDelta (obs : FinSet Stamp) :
    PayloadTotal (removeDelta obs) := by
  intro st h
  obtain ⟨t, hmem, _⟩ := (OrSet.present_iff_exists_live_tag ..).mp h
  exact absurd hmem (FinSet.not_mem_empty t)

theorem payloadTotal_merge {a b : Journal}
    (ha : PayloadTotal a) (hb : PayloadTotal b) : PayloadTotal (merge a b) := by
  intro st h
  show ((merge a b).payloads.find st).isSome = true
  rw [payloads_merge, AMap.find_merge]
  rcases visible_merge_cases h with hv | hv
  · obtain ⟨pa, hpa⟩ := Option.isSome_iff_exists.mp (ha st hv)
    rw [show a.payloads.find st = some pa from hpa]
    cases b.payloads.find st <;> rfl
  · obtain ⟨pb, hpb⟩ := Option.isSome_iff_exists.mp (hb st hv)
    rw [show b.payloads.find st = some pb from hpb]
    cases a.payloads.find st <;> rfl

/-! ## Rendering: the visible entries, stamp-ascending -/

/-- The reference form of `visibleEntries`: a `payloads.find` (linear scan) per
    present stamp — Θ(#present × #payloads). Proof-only (ADR-0024); the shipped
    `visibleEntries` is the merge-join below, bridged by `visibleEntries_eq_ref`. -/
private def visibleEntriesRef (j : Journal) : List (Stamp × NotePayload) :=
  j.entries.presentElements.filterMap (fun st => (j.payloads.find st).map ((st, ·)))

/-- The visible journal, oldest first: the present tags in ascending stamp
    order (the canonical map order — no sort step, no tie-breaks: between
    distinct entries the complete stamp is total outright), each with its
    payload. An element without a payload (unreachable through the op deltas,
    which add both together) is skipped, keeping the projection total.

    `presentElements` is ascending and `payloads` is the same ascending stamp
    map, so a single merge-join (`AssocList.zipLookup`) pairs each present stamp
    with its payload in O(#present + #payloads) — not the O(#present × #payloads)
    a `find` per stamp would cost. `visibleEntries_eq_ref` bridges the two. -/
def visibleEntries (j : Journal) : List (Stamp × NotePayload) :=
  (AssocList.zipLookup (j.entries.presentElements.map (fun st => (st, ()))) j.payloads.toList).filterMap
    (fun t => t.2.2.map (fun p => (t.1, p)))

/-- The merge-join `visibleEntries` equals its per-`find` reference form: the
    `zipLookup` annotation `(st, (), payloads.find st)` feeds each present stamp
    the same payload the reference looks up. -/
theorem visibleEntries_eq_ref (j : Journal) : j.visibleEntries = j.visibleEntriesRef := by
  unfold visibleEntries visibleEntriesRef
  rw [AssocList.zipLookup_eq _ j.payloads.toList
      (AssocList.sorted_attach _ (OrSet.presentElements_pairwise_lt j.entries)) j.payloads.sorted,
    List.map_map, List.filterMap_map]
  rfl

/-- `Pairwise` transfers through `filterMap` when the emitted values inherit
    the relation from their sources. -/
private theorem pairwise_filterMap {α β : Type _} {R : α → α → Prop}
    {S : β → β → Prop} (f : α → Option β)
    (hf : ∀ a b, R a b → ∀ x, f a = some x → ∀ y, f b = some y → S x y)
    {l : List α} (h : List.Pairwise R l) : List.Pairwise S (l.filterMap f) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons a as ha _ ih =>
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none => exact ih
    | some b =>
      refine List.Pairwise.cons ?_ ih
      intro y hy
      rw [List.mem_filterMap] at hy
      obtain ⟨a', ha', hfy⟩ := hy
      exact hf a a' (ha a' ha') b hfa y hfy

/-- The rendered order is strictly stamp-ascending — deterministic on every
    replica because it is the canonical form itself, and total between
    distinct entries with no tie-break levels. -/
theorem visibleEntries_pairwise_lt (j : Journal) :
    List.Pairwise (fun a b : Stamp × NotePayload => TotalOrd.lt a.1 b.1)
      j.visibleEntries := by
  rw [visibleEntries_eq_ref]
  unfold visibleEntriesRef
  refine pairwise_filterMap _ ?_ (OrSet.presentElements_pairwise_lt j.entries)
  intro a b hab x hx y hy
  cases hpa : (j.payloads.find a) with
  | none => rw [hpa] at hx; exact nomatch hx
  | some pa =>
    cases hpb : (j.payloads.find b) with
    | none => rw [hpb] at hy; exact nomatch hy
    | some pb =>
      rw [hpa] at hx
      rw [hpb] at hy
      cases hx; cases hy
      exact hab

/-- Membership characterization: `(st, p)` renders iff `st` is visible and `p`
    is its recorded payload. -/
theorem mem_visibleEntries (j : Journal) (st : Stamp) (p : NotePayload) :
    (st, p) ∈ j.visibleEntries ↔ j.Visible st ∧ j.payloadOf st = some p := by
  rw [visibleEntries_eq_ref]
  unfold visibleEntriesRef
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hfa⟩
    cases hpa : (j.payloads.find a) with
    | none => rw [hpa] at hfa; exact nomatch hfa
    | some pa =>
      rw [hpa] at hfa
      have hpair : (a, pa) = (st, p) := Option.some.inj hfa
      have ha' : a = st := congrArg Prod.fst hpair
      have hp' : pa = p := congrArg Prod.snd hpair
      subst ha'; subst hp'
      exact ⟨(OrSet.mem_presentElements ..).mp ha, hpa⟩
  · rintro ⟨hvis, hpay⟩
    refine ⟨st, (OrSet.mem_presentElements ..).mpr hvis, ?_⟩
    show (j.payloads.find st).map ((st, ·)) = some (st, p)
    rw [show j.payloads.find st = some p from hpay]
    rfl

/-- A visible entry with a payload renders. With `PayloadTotal` (discharged
    for every folded state) the hypothesis is free, so retention is rendering:
    every retained entry appears in the list. -/
theorem exists_mem_visibleEntries_of_visible (j : Journal) {st : Stamp}
    (h : j.Visible st) (hp : (j.payloadOf st).isSome = true) :
    ∃ p, (st, p) ∈ j.visibleEntries := by
  obtain ⟨p, hpe⟩ := Option.isSome_iff_exists.mp hp
  exact ⟨p, (mem_visibleEntries ..).mpr ⟨h, hpe⟩⟩

/-- Two distinct visible stamps render as two distinct rows — equal text from
    separate ops stays two entries in the output, never collapsed (the entry's
    identity is its stamp, not its payload). -/
theorem visibleEntries_distinct_rows (j : Journal) {st1 st2 : Stamp}
    (hne : st1 ≠ st2) (h1 : j.Visible st1) (h2 : j.Visible st2)
    (hp1 : (j.payloadOf st1).isSome = true) (hp2 : (j.payloadOf st2).isSome = true) :
    ∃ p1 p2, (st1, p1) ∈ j.visibleEntries ∧ (st2, p2) ∈ j.visibleEntries ∧
      (st1, p1) ≠ (st2, p2) := by
  obtain ⟨p1, hm1⟩ := exists_mem_visibleEntries_of_visible j h1 hp1
  obtain ⟨p2, hm2⟩ := exists_mem_visibleEntries_of_visible j h2 hp2
  exact ⟨p1, p2, hm1, hm2, fun hc => hne (congrArg Prod.fst hc)⟩

/-- Rendering is a pure function of the journal, so it inherits merge
    commutativity outright — with the state-level fold theorems (`fold_perm`,
    `fold_eq_of_mem_iff`, `foldFast_eq_fold`) this is what makes the rendered
    journal invariant under delivery order, duplication, and replica merge. -/
theorem visibleEntries_merge_comm (a b : Journal) :
    (merge a b).visibleEntries = (merge b a).visibleEntries := by
  rw [merge_comm]

/-! ## The `--all` placeholder view (ADR-0027)

`note list --all` shows every entry — visible ones plus removed placeholders
(provenance shown, text hidden). The reference form probes `payloadOf` and
`Visible` (two/three `find`s) per element → Θ(N²) per issue journal; the
shipped form merge-joins the add map against both the tombstone map and the
payload map (one co-traversal each) → O(N), bridged by `allEntries_eq_ref`. -/

/-- `filterMap` respects a per-member function agreement. -/
private theorem filterMap_congr_mem {γ δ : Type _} {f g : γ → Option δ} :
    (l : List γ) → (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: as, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr_mem as (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- The reference form of the `--all` view: `payloadOf` + `Visible` per element
    (each a `find`). Proof-only (ADR-0024); `allEntries` is the merge-join. -/
private def allEntriesRef (j : Journal) : List (Stamp × NotePayload × Bool) :=
  j.entries.elements.filterMap (fun st =>
    (j.payloadOf st).map (fun pl => (st, pl, !(decide (j.Visible st)))))

/-- Every journal entry (visible or removed) with its payload and a
    removed-flag, oldest first — the `note list --all` view. One merge-join of
    the add map against the tombstone map (for the removed-flag) and one against
    the payload map, zipped positionally (both walk `adds` in order): O(N). -/
def allEntries (j : Journal) : List (Stamp × NotePayload × Bool) :=
  ((AssocList.zipLookup j.entries.adds.toList j.entries.removed.toList).zip
    (AssocList.zipLookup j.entries.adds.toList j.payloads.toList)).filterMap
      (fun rp =>
        let ((e, tags, remOpt), (_, _, payOpt)) := rp
        payOpt.map (fun pl => (e, pl, !(OrSet.entryLive (e, tags, remOpt)))))

/-- The merge-join `--all` view equals its per-`find` reference form. The
    positional `zip` aligns because both `zipLookup`s walk `adds` in order; on
    each member entry `(e, tags)` the payload is `payloadOf e` and the
    removed-flag matches `¬Visible e` because `tagsOf e = tags` for a member. -/
theorem allEntries_eq_ref (j : Journal) : j.allEntries = j.allEntriesRef := by
  unfold allEntries allEntriesRef
  rw [AssocList.zipLookup_eq j.entries.adds.toList j.entries.removed.toList
      j.entries.adds.sorted j.entries.removed.sorted,
    AssocList.zipLookup_eq j.entries.adds.toList j.payloads.toList
      j.entries.adds.sorted j.payloads.sorted,
    List.zip_map']
  show (j.entries.adds.toList.map _).filterMap _
    = (OrSet.elements j.entries).filterMap _
  rw [List.filterMap_map]
  show j.entries.adds.toList.filterMap _
    = (j.entries.adds.toList.map Prod.fst).filterMap _
  rw [List.filterMap_map]
  apply filterMap_congr_mem
  intro e he
  -- `tagsOf e.1 = e.2` for a member, so the fast liveness matches `Visible e.1`
  have hfind : j.entries.adds.find e.1 = some e.2 := AMap.find_eq_some_of_mem he
  have htag : j.entries.tagsOf e.1 = e.2 := by unfold OrSet.tagsOf; rw [hfind]; rfl
  have hlive : e.2.toList.any (fun q =>
        decide (q.1 ∉ (AssocList.lookup e.1 j.entries.removed.toList).getD FinSet.empty))
      = decide (j.Visible e.1) := by
    rw [← List.decide_exists_mem]
    show decide (∃ q ∈ e.2.toList, q.1 ∉ j.entries.removedOf e.1)
       = decide (∃ q ∈ (j.entries.tagsOf e.1).toList, q.1 ∉ j.entries.removedOf e.1)
    rw [htag]
  show (AssocList.lookup e.1 j.payloads.toList).map
        (fun pl => (e.1, pl,
          !(OrSet.entryLive (e.1, e.2, AssocList.lookup e.1 j.entries.removed.toList))))
     = (j.payloadOf e.1).map (fun pl => (e.1, pl, !(decide (j.Visible e.1))))
  rw [OrSet.entryLive_eq_ref]
  show (AssocList.lookup e.1 j.payloads.toList).map
        (fun pl => (e.1, pl, !(e.2.toList.any (fun q =>
          decide (q.1 ∉ (AssocList.lookup e.1 j.entries.removed.toList).getD FinSet.empty)))))
     = (j.payloadOf e.1).map (fun pl => (e.1, pl, !(decide (j.Visible e.1))))
  rw [hlive]
  rfl

end Journal

end Tl.Crdt
