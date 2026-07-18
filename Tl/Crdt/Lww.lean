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

/-- A merge keeps one of the two writes' values — the winner's. (The basis for
    close-monotonicity: merging a closed write never produces a third value.) -/
theorem merge_value_cases (R W : Reg V) :
    (merge R W).value = R.value ∨ (merge R W).value = W.value := by
  match R, W with
  | none, none => exact Or.inl rfl
  | none, some _ => exact Or.inr rfl
  | some _, none => exact Or.inl rfl
  | some r, some w =>
    rcases tmax_eq r w with h | h
    · exact Or.inl (congrArg (Option.map Prod.snd) (congrArg some h))
    · exact Or.inr (congrArg (Option.map Prod.snd) (congrArg some h))

/-- Merging a write that no existing entry exceeds installs that write. -/
theorem merge_write_right {R : Reg V} {st : Stamp} {v : V}
    (h : ∀ e, R = some e → le e (st, v)) :
    merge R (write st v) = write st v := by
  match R with
  | none => rfl
  | some e =>
    show some (tmax e (st, v)) = some (st, v)
    unfold tmax
    rw [if_pos (h e rfl)]

/-- The merged register holds exactly the write `(st, v)` iff one side holds it
    and neither side exceeds it — the join arbitrates a write's survival
    exactly. -/
theorem merge_eq_write_iff (R W : Reg V) (st : Stamp) (v : V) :
    merge R W = write st v ↔
      ((R = write st v ∨ W = write st v)
        ∧ (∀ e, R = some e → le e (st, v))
        ∧ (∀ e, W = some e → le e (st, v))) := by
  constructor
  · intro h
    match R, W with
    | none, none =>
      exact nomatch h
    | none, some w =>
      cases Option.some.inj h
      refine ⟨Or.inr rfl, ⟨fun e he => ?_, fun e he => ?_⟩⟩
      · exact nomatch he
      · cases Option.some.inj he
        exact le_refl _
    | some r, none =>
      cases Option.some.inj h
      refine ⟨Or.inl rfl, ⟨fun e he => ?_, fun e he => ?_⟩⟩
      · cases Option.some.inj he
        exact le_refl _
      · exact nomatch he
    | some r, some w =>
      have hm : tmax r w = (st, v) := Option.some.inj h
      have hler : le r (st, v) := by rw [← hm]; exact le_tmax_left r w
      have hlew : le w (st, v) := by rw [← hm]; exact le_tmax_right r w
      have hside : r = (st, v) ∨ w = (st, v) := by
        rcases tmax_eq r w with he | he
        · rw [he] at hm
          exact Or.inl hm
        · rw [he] at hm
          exact Or.inr hm
      refine ⟨?_, ⟨fun e he => ?_, fun e he => ?_⟩⟩
      · rcases hside with he | he
        · exact Or.inl (congrArg some he)
        · exact Or.inr (congrArg some he)
      · cases Option.some.inj he
        exact hler
      · cases Option.some.inj he
        exact hlew
  · intro h
    obtain ⟨hor, hR, hW⟩ := h
    match R, W with
    | none, none =>
      rcases hor with h' | h' <;>
        exact nomatch h'
    | none, some w =>
      have hw : w = (st, v) := by
        rcases hor with h' | h'
        · exact nomatch h'
        · exact Option.some.inj h'
      cases hw
      rfl
    | some r, none =>
      have hr : r = (st, v) := by
        rcases hor with h' | h'
        · exact Option.some.inj h'
        · exact nomatch h'
      cases hr
      rfl
    | some r, some w =>
      show some (tmax r w) = some (st, v)
      have h1 : le r (st, v) := hR r rfl
      have h2 : le w (st, v) := hW w rfl
      rcases hor with h' | h'
      · cases Option.some.inj h'
        unfold tmax
        by_cases hc : le (st, v) w
        · rw [if_pos hc, le_antisymm h2 hc]
        · rw [if_neg hc]
      · cases Option.some.inj h'
        unfold tmax
        rw [if_pos h1]

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
