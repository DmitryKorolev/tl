/-
`Tl.Crdt.Order` — the decidable total order the whole CRDT rests on.

ADR-0002/0007: every LWW-register join keeps the write greatest in the total
order on `(hlc, replica, nonce)`, and every OR-Set add-tag is that same triple.
If that key order were not *total*, the register join would not be a well-defined
function and convergence (ADR-0004 thm 1) would fail. ADR-0002: "this obligation
is discharged in the kernel proof (LWW join is a function because the key order
is total)." This module discharges it.

We deliberately do not depend on Mathlib's order/lattice hierarchy (ADR-0009);
`TotalOrd` is a small, self-contained, decidable linear order, and `tmax` is the
join the LWW register uses. Proofs are explicit `calc`/`cases`/named-lemma style,
no `omega`/`decide`/`aesop`/bare-`simp` closers (AGENTS.md).

The kernel consumes `Stamp` as an opaque, totally-ordered key; the tested shell
mints and validates the concrete bytes (16-hex HLC, 13-char replica, 26-char
nonce — ADR-0007/0008) and is responsible (by test) for the encoding being
order-preserving, so kernel-side a `Stamp` is just a lexicographic triple of
`Nat`s.
-/

namespace Tl.Crdt

universe u v

/-- A decidable total order: reflexive, transitive, antisymmetric, total, with
    decidable `le`. This is all the CRDT joins need; `DecidableEq` and the strict
    order are derived. -/
class TotalOrd (α : Type u) where
  le : α → α → Prop
  decLe : (a b : α) → Decidable (le a b)
  le_refl : (a : α) → le a a
  le_trans : {a b c : α} → le a b → le b c → le a c
  le_antisymm : {a b : α} → le a b → le b a → a = b
  le_total : (a b : α) → le a b ∨ le b a
  /-- Decidable equality. Defaults to the `le`-derived procedure (two `decLe`
      walks); a type may override it with a faster native one (e.g. `String` →
      `String.decEq`). Both decide the *same* `Prop` `a = b`, so by
      `Subsingleton (Decidable …)` the choice is invisible to every proof — it
      only changes the executable cost (ADR-0004: shell-tested wall-clock, not
      proved). The le-based default keeps `instDecidableEq` total for every
      instance that does not care. -/
  decEq : DecidableEq α := fun a b =>
    match decLe a b, decLe b a with
    | isTrue hab, isTrue hba => isTrue (le_antisymm hab hba)
    | isFalse hab, _ => isFalse (fun he => hab (by subst he; exact le_refl a))
    | _, isFalse hba => isFalse (fun he => hba (by subst he; exact le_refl a))

namespace TotalOrd

/-- `le` is decidable, so `if le a b then … else …` and `by_cases` work. -/
instance instDecidableLe [TotalOrd α] (a b : α) : Decidable (le a b) := decLe a b

/-- Equality is decidable in any total order — via the instance's `decEq` (the
    `le`-derived default, or a native override like `String.decEq`). Generic
    `AMap`/`AssocList` key-equality (`k = p.1` in every `lookup`/`insertWith`)
    dispatches through this, so a `String`-keyed map pays native equality rather
    than two `toList` lex walks. -/
instance instDecidableEq [TotalOrd α] : DecidableEq α := TotalOrd.decEq

/-- Strict order. -/
def lt [TotalOrd α] (a b : α) : Prop := le a b ∧ ¬ le b a

instance instDecidableLt [TotalOrd α] (a b : α) : Decidable (lt a b) :=
  inferInstanceAs (Decidable (le a b ∧ ¬ le b a))

theorem le_of_lt [TotalOrd α] {a b : α} (h : lt a b) : le a b := h.1

theorem lt_irrefl [TotalOrd α] (a : α) : ¬ lt a a := fun h => h.2 (le_refl a)

theorem ne_of_lt [TotalOrd α] {a b : α} (h : lt a b) : a ≠ b := by
  intro he; subst he; exact h.2 (le_refl _)

theorem lt_trans [TotalOrd α] {a b c : α} (h1 : lt a b) (h2 : lt b c) : lt a c :=
  ⟨le_trans h1.1 h2.1, fun hca => h1.2 (le_trans h2.1 hca)⟩

/-- Trichotomy: every pair is `<`, `=`, or `>`. -/
theorem trichotomy [TotalOrd α] (a b : α) : lt a b ∨ a = b ∨ lt b a := by
  by_cases hab : le a b
  · by_cases hba : le b a
    · exact Or.inr (Or.inl (le_antisymm hab hba))
    · exact Or.inl ⟨hab, hba⟩
  · rcases le_total a b with h | h
    · exact absurd h hab
    · exact Or.inr (Or.inr ⟨h, hab⟩)

/-! ### `tmax` — the join the LWW register uses

`tmax a b` is the `le`-greater of the two. It is the binary join of a
join-semilattice: commutative, associative, idempotent — exactly what makes the
LWW-register merge a CRDT (ADR-0002/0004 thm 1). -/

/-- The `le`-greater of two elements. -/
def tmax [TotalOrd α] (a b : α) : α := if le a b then b else a

theorem le_tmax_left [TotalOrd α] (a b : α) : le a (tmax a b) := by
  unfold tmax; split
  · assumption
  · exact le_refl a

theorem le_tmax_right [TotalOrd α] (a b : α) : le b (tmax a b) := by
  unfold tmax; split
  · exact le_refl b
  · rename_i h; rcases le_total a b with h' | h'
    · exact absurd h' h
    · exact h'

theorem tmax_eq [TotalOrd α] (a b : α) : tmax a b = a ∨ tmax a b = b := by
  unfold tmax; split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem tmax_le [TotalOrd α] {a b c : α} (ha : le a c) (hb : le b c) : le (tmax a b) c := by
  unfold tmax; split
  · exact hb
  · exact ha

theorem tmax_idem [TotalOrd α] (a : α) : tmax a a = a := by
  unfold tmax; split <;> rfl

theorem tmax_comm [TotalOrd α] (a b : α) : tmax a b = tmax b a := by
  unfold tmax
  by_cases hab : le a b
  · by_cases hba : le b a
    · rw [if_pos hab, if_pos hba]; exact (le_antisymm hab hba).symm
    · rw [if_pos hab, if_neg hba]
  · by_cases hba : le b a
    · rw [if_neg hab, if_pos hba]
    · rcases le_total a b with h | h
      · exact absurd h hab
      · exact absurd h hba

theorem tmax_assoc [TotalOrd α] (a b c : α) :
    tmax (tmax a b) c = tmax a (tmax b c) := by
  apply le_antisymm
  · apply tmax_le
    · apply tmax_le
      · exact le_tmax_left a (tmax b c)
      · exact le_trans (le_tmax_left b c) (le_tmax_right a (tmax b c))
    · exact le_trans (le_tmax_right b c) (le_tmax_right a (tmax b c))
  · apply tmax_le
    · exact le_trans (le_tmax_left a b) (le_tmax_left (tmax a b) c)
    · apply tmax_le
      · exact le_trans (le_tmax_right a b) (le_tmax_left (tmax a b) c)
      · exact le_tmax_right (tmax a b) c

/-! ### Combinators -/

/-- Pull a total order back along an injection. Used to give `Stamp` its order
    from the `Nat`-triple key, and `String` its order from `List Char`. -/
@[reducible] def comap [TotalOrd β] (f : α → β) (hf : Function.Injective f) : TotalOrd α where
  le a b := le (f a) (f b)
  decLe a b := decLe (f a) (f b)
  le_refl a := le_refl (f a)
  le_trans h1 h2 := le_trans h1 h2
  le_antisymm h1 h2 := hf (le_antisymm h1 h2)
  le_total a b := le_total (f a) (f b)

end TotalOrd

open TotalOrd

/-- `Nat` carries the canonical total order; every other base order is built from
    it (the encoded HLC/replica/nonce integers, string char codes, instants). -/
instance : TotalOrd Nat where
  le := Nat.le
  decLe := Nat.decLe
  le_refl := Nat.le_refl
  le_trans := Nat.le_trans
  le_antisymm := Nat.le_antisymm
  le_total := Nat.le_total

/-- Lexicographic order on a product: compare first components, tie-break by
    second. Reused for the LWW entry order `Stamp × Value`, the edge key, and the
    `Stamp` triple itself. -/
instance instTotalOrdProd [TotalOrd α] [TotalOrd β] : TotalOrd (α × β) where
  le p q := lt p.1 q.1 ∨ (p.1 = q.1 ∧ le p.2 q.2)
  decLe p q := inferInstanceAs (Decidable (lt p.1 q.1 ∨ (p.1 = q.1 ∧ le p.2 q.2)))
  le_refl p := Or.inr ⟨rfl, le_refl p.2⟩
  le_trans := by
    intro a b c hab hbc
    rcases hab with hab | ⟨he1, hle1⟩
    · rcases hbc with hbc | ⟨he2, _⟩
      · exact Or.inl (lt_trans hab hbc)
      · exact Or.inl (he2 ▸ hab)
    · rcases hbc with hbc | ⟨he2, hle2⟩
      · exact Or.inl (he1 ▸ hbc)
      · exact Or.inr ⟨he1.trans he2, le_trans hle1 hle2⟩
  le_antisymm := by
    intro a b hab hba
    rcases hab with hab | ⟨he1, hle1⟩
    · rcases hba with hba | ⟨he2, _⟩
      · exact absurd (lt_trans hab hba) (lt_irrefl a.1)
      · exact absurd (he2 ▸ hab) (lt_irrefl a.1)
    · rcases hba with hba | ⟨_, hle2⟩
      · exact absurd (he1 ▸ hba) (lt_irrefl a.1)
      · have h2 : a.2 = b.2 := le_antisymm hle1 hle2
        exact Prod.ext he1 h2
  le_total := by
    intro p q
    rcases trichotomy p.1 q.1 with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total p.2 q.2 with h2 | h2
      · exact Or.inl (Or.inr ⟨h, h2⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
    · exact Or.inr (Or.inl h)

/-! ### `Stamp` — the `(hlc, replica, nonce)` ordering/identity triple (ADR-0007)

Kernel-side, a `Stamp` is the decoded integer triple; the shell encodes it as the
16-hex / 13-char / 26-char canonical strings (ADR-0008) and is responsible by
test for that encoding being order-preserving. It is both an LWW comparison key
(by the total order) and an OR-Set add-tag (by `DecidableEq`). -/

/-- The ordering/identity triple carried by every op (ADR-0007/0008). -/
structure Stamp where
  /-- Hybrid logical clock, packed 64-bit value (ADR-0007). -/
  hlc : Nat
  /-- Replica id, decoded 64-bit value. -/
  replica : Nat
  /-- Per-op nonce, decoded 128-bit value — the final tie-break. -/
  nonce : Nat
deriving Repr

namespace Stamp

/-- The triple key the order is pulled back from. -/
def key (s : Stamp) : Nat × Nat × Nat := (s.hlc, s.replica, s.nonce)

theorem key_injective : Function.Injective key := by
  intro a b h
  cases a; cases b
  simp only [key, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1; subst h2; subst h3; rfl

end Stamp

/-- The total order on `Stamp`: lexicographic on `(hlc, replica, nonce)`. This is
    the order ADR-0002's "the tie-break is mandatory" obligation refers to. -/
instance : TotalOrd Stamp := TotalOrd.comap Stamp.key Stamp.key_injective

/-! ### Orders on the concrete value types stored in registers and OR-Sets

Issue ids, slugs, labels, and edge endpoints are `String`; textual fields too;
priorities are `Fin 5`; instants are `Nat`. Each needs a total order for two
reasons: the collections (issue/edge/label OR-Sets and the per-id maps) are kept
canonical (sorted, deduplicated) by it so the join laws are genuine equalities
(ADR-0004 thm 1–2), and it is the equal-stamp tie-break keeping the LWW join a
total function even on a duplicate stamp that the carried nonce-uniqueness
assumption (ADR-0007, overview Trusted) would otherwise rule out. -/

namespace TotalOrd

/-- Lexicographic order on lists: a proper prefix precedes its extensions, and at
    the first differing position the smaller element wins. -/
def listLe [TotalOrd α] : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs => lt a b ∨ (a = b ∧ listLe as bs)

instance instDecidableListLe [TotalOrd α] : (as bs : List α) → Decidable (listLe as bs)
  | [], _ => isTrue trivial
  | _ :: _, [] => isFalse nofun
  | a :: as, b :: bs =>
    have : Decidable (listLe as bs) := instDecidableListLe as bs
    inferInstanceAs (Decidable (lt a b ∨ (a = b ∧ listLe as bs)))

theorem listLe_refl [TotalOrd α] : (as : List α) → listLe as as
  | [] => trivial
  | _ :: as => Or.inr ⟨rfl, listLe_refl as⟩

theorem listLe_trans [TotalOrd α] : {as bs cs : List α} →
    listLe as bs → listLe bs cs → listLe as cs
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, hab, _ => hab.elim
  | _ :: _, _ :: _, [], _, hbc => hbc.elim
  | _ :: _, _ :: _, _ :: _, hab, hbc => by
    rcases hab with hab | ⟨he1, hle1⟩
    · rcases hbc with hbc | ⟨he2, _⟩
      · exact Or.inl (lt_trans hab hbc)
      · exact Or.inl (he2 ▸ hab)
    · rcases hbc with hbc | ⟨he2, hle2⟩
      · exact Or.inl (he1 ▸ hbc)
      · exact Or.inr ⟨he1.trans he2, listLe_trans hle1 hle2⟩

theorem listLe_antisymm [TotalOrd α] : {as bs : List α} →
    listLe as bs → listLe bs as → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, _, hba => hba.elim
  | _ :: _, [], hab, _ => hab.elim
  | _ :: _, _ :: _, hab, hba => by
    rcases hab with hab | ⟨he1, hle1⟩
    · rcases hba with hba | ⟨he2, _⟩
      · exact absurd (lt_trans hab hba) (lt_irrefl _)
      · subst he2; exact absurd hab (lt_irrefl _)
    · rcases hba with hba | ⟨_, hle2⟩
      · subst he1; exact absurd hba (lt_irrefl _)
      · have hcons := listLe_antisymm hle1 hle2
        rw [he1, hcons]

theorem listLe_total [TotalOrd α] : (as bs : List α) → listLe as bs ∨ listLe bs as
  | [], _ => Or.inl trivial
  | _ :: _, [] => Or.inr trivial
  | a :: as, b :: bs => by
    rcases trichotomy a b with h | h | h
    · exact Or.inl (Or.inl h)
    · subst h
      rcases listLe_total as bs with h' | h'
      · exact Or.inl (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr (Or.inr ⟨rfl, h'⟩)
    · exact Or.inr (Or.inl h)

/-- `none < some`, then by the element order. The placement of `none` is
    immaterial to behaviour (it is only the never-fired equal-stamp tie-break);
    it just has to be a total order. -/
def optionLe [TotalOrd α] : Option α → Option α → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => le a b

instance instDecidableOptionLe [TotalOrd α] : (a b : Option α) → Decidable (optionLe a b)
  | none, _ => isTrue trivial
  | some _, none => isFalse nofun
  | some a, some b => inferInstanceAs (Decidable (le a b))

theorem optionLe_refl [TotalOrd α] : (a : Option α) → optionLe a a
  | none => trivial
  | some a => le_refl a

theorem optionLe_trans [TotalOrd α] : {a b c : Option α} →
    optionLe a b → optionLe b c → optionLe a c
  | none, _, _, _, _ => trivial
  | some _, none, _, hab, _ => hab.elim
  | some _, some _, none, _, hbc => hbc.elim
  | some _, some _, some _, hab, hbc => le_trans hab hbc

theorem optionLe_antisymm [TotalOrd α] : {a b : Option α} →
    optionLe a b → optionLe b a → a = b
  | none, none, _, _ => rfl
  | none, some _, _, hba => hba.elim
  | some _, none, hab, _ => hab.elim
  | some _, some _, hab, hba => congrArg some (le_antisymm hab hba)

theorem optionLe_total [TotalOrd α] : (a b : Option α) → optionLe a b ∨ optionLe b a
  | none, _ => Or.inl trivial
  | some _, none => Or.inr trivial
  | some a, some b => le_total a b

end TotalOrd

instance instTotalOrdList [TotalOrd α] : TotalOrd (List α) where
  le := TotalOrd.listLe
  decLe := TotalOrd.instDecidableListLe
  le_refl := TotalOrd.listLe_refl
  le_trans := TotalOrd.listLe_trans
  le_antisymm := TotalOrd.listLe_antisymm
  le_total := TotalOrd.listLe_total

instance instTotalOrdOption [TotalOrd α] : TotalOrd (Option α) where
  le := TotalOrd.optionLe
  decLe := TotalOrd.instDecidableOptionLe
  le_refl := TotalOrd.optionLe_refl
  le_trans := TotalOrd.optionLe_trans
  le_antisymm := TotalOrd.optionLe_antisymm
  le_total := TotalOrd.optionLe_total

/-- `Char` ordered by its code point. -/
instance : TotalOrd Char :=
  TotalOrd.comap (fun c => c.val.toNat) (fun _ _ h => Char.ext (UInt32.toNat_inj.mp h))

/-- `String` ordered lexicographically by its characters (the canonical issue-id,
    slug, label, and field order). The `le` is exactly `comap String.toList`'s —
    `TotalOrd.le` on the char lists, so every order proof is unchanged — but the
    instance overrides `decEq` with native `String.decEq`: `String` keys are the
    hot map key everywhere (issue ids, edge endpoints, labels), and equality is
    the most frequent comparison (`lookup`'s `k = p.1`). -/
instance : TotalOrd String where
  le a b := TotalOrd.le a.toList b.toList
  decLe a b := TotalOrd.decLe a.toList b.toList
  le_refl a := TotalOrd.le_refl a.toList
  le_trans h1 h2 := TotalOrd.le_trans h1 h2
  le_antisymm h1 h2 := String.toList_injective (TotalOrd.le_antisymm h1 h2)
  le_total a b := TotalOrd.le_total a.toList b.toList
  decEq := String.decEq

/-- `Fin n` ordered by value — used for `priority : Fin 5` (ADR-0002). -/
instance (n : Nat) : TotalOrd (Fin n) :=
  TotalOrd.comap Fin.val (fun _ _ h => Fin.eq_of_val_eq h)

end Tl.Crdt
