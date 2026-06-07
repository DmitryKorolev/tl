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

/-- Add `e` with add-tag `st` (the adding op's stamp). -/
def add (e : α) (st : Stamp) (s : OrSet α) : OrSet α :=
  ⟨AMap.merge FinSet.union s.adds (AMap.singleton e (FinSet.singleton st)), s.removed⟩

/-- Remove `e`, tombstoning the observed add-tags `obs`. -/
def remove (obs : FinSet Stamp) (s : OrSet α) : OrSet α :=
  ⟨s.adds, FinSet.union s.removed obs⟩

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

end OrSet

end Tl.Crdt
