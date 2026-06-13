/-
`Tl.Kernel.State` — the product-CRDT state (ADR-0002/0004).

`State` is: an OR-Set of issue ids (membership — `present` = materialized), a
per-id map of `IssueData` (each a record of typed LWW registers, a per-issue
label OR-Set, and a per-key-LWW meta map), and an OR-Set of typed dependency
edges. Per-id data is keyed *independently of membership*, so a field/label/meta
write folded before that issue's `create` is retained and inert until `create`
lands (ADR-0002) — the order-insensitivity that theorem 2 needs.

Illegal *intra-issue* states are unrepresentable by construction: `status` is a
closed enum, `priority` a `Fin 5`. So the only `Invariant` (ADR-0004 thm 3) is
trivially type-level; acyclicity and endpoint-existence are deliberately *not*
invariants — they are reported/derived (ADR-0003), tolerated at read time.

The state join is componentwise, so its commutativity/associativity/idempotence
(ADR-0004 thm 1) is inherited from the CRDT pieces.
-/
import Tl.Crdt.Lww
import Tl.Crdt.OrSet

namespace Tl.Kernel

open Tl.Crdt
open Tl.Crdt.TotalOrd

/-! ## Closed-domain enums (illegal values unrepresentable) -/

/-- Stored status (ADR-0002). Constructors are PascalCase to avoid the `open`
    keyword; the wire strings (`open`/`in_progress`/…) are the shell's concern. -/
inductive Status where
  | Open | InProgress | Done | Cancelled
deriving DecidableEq, Repr

/-- A close resolution (ADR-0008): `Duplicate` sets status `Cancelled`. -/
inductive CloseResolution where
  | Done | Cancelled | Duplicate
deriving DecidableEq, Repr

/-- Dependency-edge kind (ADR-0003). -/
inductive EdgeKind where
  | Blocks | Parent | Related
deriving DecidableEq, Repr, Hashable

/-- `Done`/`Cancelled` are *closed*; both discharge a blocker (ADR vision). -/
def Status.closed : Status → Bool
  | .Done | .Cancelled => true
  | _ => false

def Status.toNat : Status → Nat
  | .Open => 0 | .InProgress => 1 | .Done => 2 | .Cancelled => 3

def CloseResolution.toNat : CloseResolution → Nat
  | .Done => 0 | .Cancelled => 1 | .Duplicate => 2

def EdgeKind.toNat : EdgeKind → Nat
  | .Blocks => 0 | .Parent => 1 | .Related => 2

theorem Status.toNat_inj : Function.Injective Status.toNat := by
  intro a b h; cases a <;> cases b <;> first | rfl | nomatch h

theorem CloseResolution.toNat_inj : Function.Injective CloseResolution.toNat := by
  intro a b h; cases a <;> cases b <;> first | rfl | nomatch h

theorem EdgeKind.toNat_inj : Function.Injective EdgeKind.toNat := by
  intro a b h; cases a <;> cases b <;> first | rfl | nomatch h

instance : TotalOrd Status := TotalOrd.comap Status.toNat Status.toNat_inj
instance : TotalOrd CloseResolution := TotalOrd.comap CloseResolution.toNat CloseResolution.toNat_inj
instance : TotalOrd EdgeKind := TotalOrd.comap EdgeKind.toNat EdgeKind.toNat_inj

/-! ## Domain types -/

/-- An issue id: the flat Crockford hash (ADR-0007), opaque and ordered. -/
abbrev IssueId := String

/-- A categorical label (ADR-0002). -/
abbrev Label := String

/-- A wall-clock instant in ms since the Unix epoch — the kernel compares it only
    by `≤` (ADR-0010). Both `deferUntil` and the injected `now` are this type. -/
abbrev Instant := Nat

/-- A typed dependency edge key `(from, to, kind)` (ADR-0002/0003). For `Related`
    the shell canonicalizes endpoints before forming the key; the kernel just sees
    the key. -/
abbrev Edge := IssueId × IssueId × EdgeKind

/-! ## Per-issue data — a record of typed registers + label set + meta map -/

/-- All of one issue's mergeable data (ADR-0002). Each scalar is an LWW register
    of its tightest type; nullable scalars wrap `Option`. -/
structure IssueData where
  title : Reg String
  status : Reg Status
  priority : Reg (Fin 5)
  assignee : Reg (Option String)
  description : Reg (Option String)
  notes : Reg (Option String)
  slug : Reg (Option String)
  deferUntil : Reg (Option Instant)
  closeResolution : Reg (Option CloseResolution)
  labels : OrSet Label
  metadata : MetaMap

namespace IssueData

/-- No writes yet — every register unwritten, label/meta empty. -/
def empty : IssueData :=
  ⟨none, none, none, none, none, none, none, none, none, OrSet.empty, AMap.empty⟩

/-- Componentwise join. -/
def merge (a b : IssueData) : IssueData where
  title := Reg.merge a.title b.title
  status := Reg.merge a.status b.status
  priority := Reg.merge a.priority b.priority
  assignee := Reg.merge a.assignee b.assignee
  description := Reg.merge a.description b.description
  notes := Reg.merge a.notes b.notes
  slug := Reg.merge a.slug b.slug
  deferUntil := Reg.merge a.deferUntil b.deferUntil
  closeResolution := Reg.merge a.closeResolution b.closeResolution
  labels := OrSet.merge a.labels b.labels
  metadata := AMap.merge Reg.merge a.metadata b.metadata

theorem merge_comm (a b : IssueData) : merge a b = merge b a := by
  unfold merge
  rw [Reg.merge_comm a.title b.title, Reg.merge_comm a.status b.status,
    Reg.merge_comm a.priority b.priority, Reg.merge_comm a.assignee b.assignee,
    Reg.merge_comm a.description b.description, Reg.merge_comm a.notes b.notes,
    Reg.merge_comm a.slug b.slug, Reg.merge_comm a.deferUntil b.deferUntil,
    Reg.merge_comm a.closeResolution b.closeResolution,
    OrSet.merge_comm a.labels b.labels, MetaMap.merge_comm a.metadata b.metadata]

theorem merge_assoc (a b c : IssueData) : merge (merge a b) c = merge a (merge b c) := by
  unfold merge
  rw [Reg.merge_assoc a.title b.title c.title, Reg.merge_assoc a.status b.status c.status,
    Reg.merge_assoc a.priority b.priority c.priority,
    Reg.merge_assoc a.assignee b.assignee c.assignee,
    Reg.merge_assoc a.description b.description c.description,
    Reg.merge_assoc a.notes b.notes c.notes, Reg.merge_assoc a.slug b.slug c.slug,
    Reg.merge_assoc a.deferUntil b.deferUntil c.deferUntil,
    Reg.merge_assoc a.closeResolution b.closeResolution c.closeResolution,
    OrSet.merge_assoc a.labels b.labels c.labels, MetaMap.merge_assoc a.metadata b.metadata c.metadata]

theorem merge_idem (a : IssueData) : merge a a = a := by
  unfold merge
  rw [Reg.merge_idem a.title, Reg.merge_idem a.status, Reg.merge_idem a.priority,
    Reg.merge_idem a.assignee, Reg.merge_idem a.description, Reg.merge_idem a.notes,
    Reg.merge_idem a.slug, Reg.merge_idem a.deferUntil, Reg.merge_idem a.closeResolution,
    OrSet.merge_idem a.labels, MetaMap.merge_idem a.metadata]

/-! ### Materialized reads (with the ADR defaults)

`status` defaults to `Open` and `priority` to `2` at materialization (ADR-0008),
so these are total even before `create`'s seed write is folded; `deferUntil`
collapses "unwritten" and "cleared" to "not deferred". -/

/-- Materialized status (default `Open`). -/
def statusOf (d : IssueData) : Status := d.status.value.getD Status.Open

/-- Materialized priority (default `2`). -/
def priorityOf (d : IssueData) : Fin 5 := d.priority.value.getD 2

/-- Materialized defer instant: `none` if unwritten or cleared (ADR-0010). -/
def deferUntilOf (d : IssueData) : Option Instant := d.deferUntil.value.getD none

end IssueData

/-! ## The state -/

/-- The product-CRDT state (ADR-0004). -/
structure State where
  /-- Issue membership; `present id` ⇒ the issue is materialized. -/
  issues : OrSet IssueId
  /-- Per-id data, retained even before the issue's `create` (ADR-0002). -/
  data : AMap IssueId IssueData
  /-- Typed dependency edges. -/
  edges : OrSet Edge

namespace State

/-- The empty state. -/
def empty : State := ⟨OrSet.empty, AMap.empty, OrSet.empty⟩

/-- The state join — componentwise (ADR-0004 thm 1). A change to this join's
    semantics must bump `Tl.Store.cacheVersion` (a stale fold cache would
    deserialize state this join would no longer produce — Cache.lean header). -/
def merge (s t : State) : State :=
  ⟨OrSet.merge s.issues t.issues,
   AMap.merge IssueData.merge s.data t.data,
   OrSet.merge s.edges t.edges⟩

theorem ext {s t : State} (hi : s.issues = t.issues) (hd : s.data = t.data)
    (he : s.edges = t.edges) : s = t := by
  obtain ⟨si, sd, se⟩ := s; obtain ⟨ti, td, te⟩ := t
  subst hi; subst hd; subst he; rfl

theorem merge_comm (s t : State) : merge s t = merge t s :=
  ext (OrSet.merge_comm s.issues t.issues)
      (AMap.merge_comm (fun a b => IssueData.merge_comm a b) s.data t.data)
      (OrSet.merge_comm s.edges t.edges)

theorem merge_assoc (s t u : State) : merge (merge s t) u = merge s (merge t u) :=
  ext (OrSet.merge_assoc s.issues t.issues u.issues)
      (AMap.merge_assoc (fun a b c => IssueData.merge_assoc a b c) s.data t.data u.data)
      (OrSet.merge_assoc s.edges t.edges u.edges)

theorem merge_idem (s : State) : merge s s = s :=
  ext (OrSet.merge_idem s.issues)
      (AMap.merge_idem (fun a => IssueData.merge_idem a) s.data)
      (OrSet.merge_idem s.edges)

theorem merge_empty_left (s : State) : merge empty s = s :=
  ext (OrSet.merge_empty_left s.issues)
      (AMap.merge_empty_left _ s.data)
      (OrSet.merge_empty_left s.edges)

theorem merge_empty_right (s : State) : merge s empty = s :=
  ext (OrSet.merge_empty_right s.issues)
      (AMap.merge_empty_right _ s.data)
      (OrSet.merge_empty_right s.edges)

/-! ### State-level reads -/

/-- The data record for `id` (empty if no write has been folded). -/
def issueData (s : State) (id : IssueId) : IssueData := (s.data.find id).getD IssueData.empty

/-- Whether `id` is materialized (its `create` has been folded). -/
def hasIssue (s : State) (id : IssueId) : Prop := s.issues.Present id

instance (s : State) (id : IssueId) : Decidable (s.hasIssue id) :=
  inferInstanceAs (Decidable (s.issues.Present id))

/-! ### Enumeration and edge queries (the tracker layer's primitives)

`presentIssues`/`presentEdges` are the finite, duplicate-free node/edge sets the
total recursions in `Rollup`/`Ready`/`Cycles` walk. The edge-query accessors pin
the ADR-0003 §1 direction (`dep add A B` ⇒ edge `from=B, to=A`, i.e. B blocks A):
a *blocker* of `i` is the `from` of an incoming `Blocks` edge; a *child* of epic
`i` is the `to` of an outgoing `Parent` edge. They return ids even when the id is
not itself a present issue — a *dangling* endpoint — because endpoint-existence is
not an invariant (ADR-0003 §5); the read-time inertness of a dangling blocker is
applied at *discharge* time in `Ready`, not here. -/

/-- The materialized issue ids (present in the OR-Set). -/
def presentIssues (s : State) : List IssueId := s.issues.presentElements

/-- The live dependency edges. -/
def presentEdges (s : State) : List Edge := s.edges.presentElements

/-- The issues blocking `i` — `from` of each present incoming `Blocks` edge. -/
def blockersOf (s : State) (i : IssueId) : List IssueId :=
  (s.presentEdges.filter (fun e => decide (e.2.2 = EdgeKind.Blocks ∧ e.2.1 = i))).map (·.1)

/-- The issues `i` blocks (its dependents) — `to` of each present outgoing `Blocks`
    edge. Closing `i` discharges it as their blocker; the critical-path weight
    (ADR-0004 thm 4) and `unblocks` walk this direction. -/
def dependentsOf (s : State) (i : IssueId) : List IssueId :=
  (s.presentEdges.filter (fun e => decide (e.2.2 = EdgeKind.Blocks ∧ e.1 = i))).map (·.2.1)

/-- The children of epic `i` — `to` of each present outgoing `Parent` edge. -/
def childrenOf (s : State) (i : IssueId) : List IssueId :=
  (s.presentEdges.filter (fun e => decide (e.2.2 = EdgeKind.Parent ∧ e.1 = i))).map (·.2.1)

/-- The parents of `i` — `from` of each present incoming `Parent` edge (more than
    one is `multiParent`, ADR-0003 §4). -/
def parentsOf (s : State) (i : IssueId) : List IssueId :=
  (s.presentEdges.filter (fun e => decide (e.2.2 = EdgeKind.Parent ∧ e.2.1 = i))).map (·.1)

end State

end Tl.Kernel
