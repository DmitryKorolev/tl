/-
`Tl.Clock.Skew` — the HLC skew-window admission predicate and its
convergence-safety theorems (ADR-0007 skew window).

The fold (`Tl/Store/Materialize`) *defers* a foreign op whose physical time is
beyond the window `now + W`. This module proves the **safety** of that deferral
as Lean theorems rather than prose (AGENTS.md principle 1 — a provable property
is proved, not merely tested):

- admission is **monotone** in `now` (`admitted_mono_now`), so the deferred set
  only shrinks as clocks advance — a deferred op is never re-deferred, so
  deferral is *eventual*, never permanent;
- once every replica's clock has passed an op's physical time the filter is the
  **identity** (`filter_admittedB_eq_self`); hence by the kernel's
  set-insensitive fold (`fold_eq_of_mem_iff`) the replicas **converge**
  (`skew_converges`).

Crucially every result holds for any window `W` and *regardless of clock
accuracy*: a wrong clock changes only when an op becomes visible, never the
eventual state. So convergence is independent of the window value; `W` tunes
only timeliness (and the carried system-clock assumption bears only on that).

`admittedB` is the exact Bool the fold loop branches on, so these theorems are
about the real predicate, not a parallel copy. Pure (no I/O); batteries only,
and kernel-free — the monotonicity core needs nothing from the kernel; the
convergence corollary that composes with `fold` lives in `Tl.Clock.SkewConverge`.
-/

namespace Tl.Clock.Skew

/-- A foreign op with packed HLC `hlc` is *admitted* against the skew bound `b`
    (`= now + W`, the window's physical-ms ceiling) iff its physical component
    (`hlc / 2^16`) is within the window. The fold defers exactly `¬ Admitted`.
    Reducible so `decide` finds the `≤` `Decidable` instance through it. -/
@[reducible] def Admitted (hlc b : Nat) : Prop := hlc / 2 ^ 16 ≤ b

/-- The Bool form the fold loop branches on (`Tl/Store/Materialize`). -/
def admittedB (hlc b : Nat) : Bool := decide (Admitted hlc b)

theorem admittedB_eq_true {hlc b : Nat} : admittedB hlc b = true ↔ Admitted hlc b := by
  simp only [admittedB, decide_eq_true_eq]

/-- Monotone in the bound: a wider window admits everything a narrower one did. -/
theorem admitted_mono {hlc b b' : Nat} (h : Admitted hlc b) (hb : b ≤ b') : Admitted hlc b' :=
  Nat.le_trans h hb

/-- Monotone in `now` (the bound is `now + W`): a later observation admits
    everything an earlier one did — so a deferred op is never *re*-deferred, and
    the deferral is eventual rather than permanent. -/
theorem admitted_mono_now {hlc now now' W : Nat} (h : Admitted hlc (now + W))
    (ht : now ≤ now') : Admitted hlc (now' + W) :=
  admitted_mono h (Nat.add_le_add_right ht W)

/-- Eventual admission: once local time reaches an op's physical time, the op is
    admitted by any window — a deferred op always becomes visible in the limit. -/
theorem admitted_of_physical_le {hlc now W : Nat} (h : hlc / 2 ^ 16 ≤ now) :
    Admitted hlc (now + W) :=
  Nat.le_trans h (Nat.le_add_right now W)

/-- Past the threshold (every element's physical time ≤ `now`), the admission
    filter keeps the whole list — the deferred set is empty, so the fold sees
    the full op set. Abstract over the physical projection `phys`. -/
theorem filter_admittedB_eq_self {α} (phys : α → Nat) (l : List α) (now W : Nat)
    (h : ∀ a ∈ l, phys a / 2 ^ 16 ≤ now) :
    l.filter (fun a => admittedB (phys a) (now + W)) = l := by
  apply List.filter_eq_self.mpr
  intro a ha
  exact admittedB_eq_true.mpr (admitted_of_physical_le (h a ha))

end Tl.Clock.Skew
