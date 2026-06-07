/-
`Tl.Crdt.Lww` — the last-writer-wins register (ADR-0002).

A scalar field is a register: the optional winning write `(stamp, value)`. The
join keeps the write greatest in the total order, with the value as the
equal-stamp tie-break (`tmax` on `Stamp × V`) — so the register join is a *total*
commutative/associative/idempotent function with no nonce-uniqueness side
condition (that carried assumption, ADR-0007/overview Trusted, only guarantees the
winner is the genuine last writer; it is never needed for the join to be
well-defined). The laws are inherited directly from `optCombine` + `tmax`.

`none` means "never written"; a written `none` *value* — a clear (`undefer`,
`reopen` dropping `closeResolution`, …) — is `some (stamp, none)` with `V`
itself an `Option` (ADR-0002), distinct from key-absence and arbitrated by the
ordinary order.
-/
import Tl.Crdt.Map

namespace Tl.Crdt

open TotalOrd

universe v

/-- An LWW register over `V`: the optional winning `(stamp, value)`. -/
abbrev Reg (V : Type v) := Option (Stamp × V)

namespace Reg

variable {V : Type v} [TotalOrd V]

/-- A write of `v` stamped `s`. -/
def write (s : Stamp) (v : V) : Reg V := some (s, v)

/-- The materialized value (the winning write's value), or `none` if unwritten. -/
def value : Reg V → Option V := Option.map Prod.snd

/-- The register join: keep the lex-greater `(stamp, value)`. -/
def merge (a b : Reg V) : Reg V := optCombine tmax a b

theorem merge_comm (a b : Reg V) : merge a b = merge b a :=
  optCombine_comm (fun x y => tmax_comm x y) a b

theorem merge_assoc (a b c : Reg V) : merge (merge a b) c = merge a (merge b c) :=
  optCombine_assoc (fun x y z => tmax_assoc x y z) a b c

theorem merge_idem (a : Reg V) : merge a a = a :=
  optCombine_idem (fun x => tmax_idem x) a

@[simp] theorem merge_none_left (a : Reg V) : merge none a = a := rfl

@[simp] theorem merge_none_right (a : Reg V) : merge a none = a := optCombine_none_right _ a

end Reg

/-- The per-key-LWW metadata map (ADR-0002): a map of registers, its join the
    register join applied key-wise. Values are `Option String` so a `metaSet …
    null` (clear) is a written `none`, distinct from key-absence (ADR-0008). A
    side-channel; no kernel theorem depends on it (the frame lemma). Convergence is
    `AMap.merge_*` with `Reg.merge`. -/
abbrev MetaMap := AMap String (Reg (Option String))

namespace MetaMap

theorem merge_comm (m1 m2 : MetaMap) :
    AMap.merge Reg.merge m1 m2 = AMap.merge Reg.merge m2 m1 :=
  AMap.merge_comm (fun a b => Reg.merge_comm a b) m1 m2

theorem merge_assoc (m1 m2 m3 : MetaMap) :
    AMap.merge Reg.merge (AMap.merge Reg.merge m1 m2) m3
      = AMap.merge Reg.merge m1 (AMap.merge Reg.merge m2 m3) :=
  AMap.merge_assoc (fun a b c => Reg.merge_assoc a b c) m1 m2 m3

theorem merge_idem (m : MetaMap) : AMap.merge Reg.merge m m = m :=
  AMap.merge_idem (fun a => Reg.merge_idem a) m

end MetaMap

end Tl.Crdt
