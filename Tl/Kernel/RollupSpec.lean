/-
`Tl.Kernel.RollupSpec` — epic-rollup correctness against its spec (ADR-0003 §3).

`effectiveStatus` is *defined* by a fuel-bounded descent (`Rollup.lean`); this file
proves it meets its intended spec. Three branches of the spec are *unconditional*
(no acyclicity needed) and proved here:

  * **manual cancel precedence** — a stored-`Cancelled` issue rolls up to `Cancelled`;
  * **non-epic = stored** — an issue with no present children rolls up to its stored
    status;
  * **one-step fuel congruence** — if every present child rolls up identically at two
    fuels, the parent does at one-higher fuel (the bridge to fuel-irrelevance).

The remaining branch (an epic that is not cancelled is `Done` iff every present child
is effectively closed) is *exact only when the parent descent is acyclic*, since the
fuel must outlast the longest descending chain; on a parent cycle the fuel is spent
and the rollup falls back *conservatively*: a manual `Cancelled` is honoured, a
non-epic reads its stored status, and an epic falls back to `Open` — never its
(possibly merge-injected `Done`) stored status (`effStatusAux_epic_zero_ne_done`),
so a cycle-trapped epic cannot spuriously discharge a blocker; `dep cycles` reports
the cycle. The fuel-adequacy step on acyclic graphs is proved in `RollupAcyclic.lean`.
-/
import Tl.Kernel.Rollup

namespace Tl.Kernel

open Tl.Crdt

namespace State

/-! ## Manual-cancel precedence (unconditional) -/

/-- A stored-`Cancelled` issue rolls up to `Cancelled` at every fuel. -/
theorem effStatusAux_cancelled (s : State) (i : IssueId)
    (h : (s.issueData i).statusOf = Status.Cancelled) :
    (fuel : Nat) → s.effStatusAux fuel i = Status.Cancelled
  | 0 => by unfold State.effStatusAux; rw [if_pos h]
  | _ + 1 => by unfold State.effStatusAux; rw [if_pos h]

/-- Manual cancel takes precedence over the rollup (ADR-0003 §3). -/
theorem effectiveStatus_cancelled (s : State) (i : IssueId)
    (h : (s.issueData i).statusOf = Status.Cancelled) :
    s.effectiveStatus i = Status.Cancelled :=
  effStatusAux_cancelled s i h _

/-! ## Non-epic = stored status (unconditional) -/

/-- An issue with no present children rolls up to its stored status, at every fuel. -/
theorem effStatusAux_nonEpic (s : State) (i : IssueId) (h : s.isEpic i = false) :
    (fuel : Nat) → s.effStatusAux fuel i = (s.issueData i).statusOf
  | 0 => by
    have hempty : (s.presentChildren i).isEmpty = true := by
      cases hb : (s.presentChildren i).isEmpty with
      | true => rfl
      | false => unfold State.isEpic at h; rw [hb, Bool.not_false] at h; exact Bool.noConfusion h
    unfold State.effStatusAux
    by_cases hc : (s.issueData i).statusOf = Status.Cancelled
    · rw [if_pos hc, hc]
    · rw [if_neg hc]
      show (if (s.presentChildren i).isEmpty then (s.issueData i).statusOf else Status.Open)
            = (s.issueData i).statusOf
      rw [hempty, if_pos rfl]
  | _ + 1 => by
    have hempty : (s.presentChildren i).isEmpty = true := by
      cases hb : (s.presentChildren i).isEmpty with
      | true => rfl
      | false => unfold State.isEpic at h; rw [hb, Bool.not_false] at h; exact Bool.noConfusion h
    unfold State.effStatusAux
    by_cases hc : (s.issueData i).statusOf = Status.Cancelled
    · rw [if_pos hc, hc]
    · rw [if_neg hc]
      show (if (s.presentChildren i).isEmpty then (s.issueData i).statusOf
            else if (s.presentChildren i).all (fun c => Status.closed (s.effStatusAux _ c))
                 then Status.Done else Status.Open) = (s.issueData i).statusOf
      rw [hempty, if_pos rfl]

/-- A non-epic's effective status is its stored status (ADR-0003 §3). -/
theorem effectiveStatus_nonEpic (s : State) (i : IssueId) (h : s.isEpic i = false) :
    s.effectiveStatus i = (s.issueData i).statusOf :=
  effStatusAux_nonEpic s i h _

/-- **Conservative fuel-exhaustion guarantee (ADR-0003 §3).** An epic at exhausted fuel
    (only reachable on a parent *cycle*) never rolls up to `Done` — it falls back to
    `Cancelled` (manual cancel) or `Open`, never its possibly merge-injected stored
    `Done`. Since a child read as non-closed makes its parent's rollup non-`Done` too,
    this propagates: a cycle-trapped epic can never spuriously read `Done` and so never
    spuriously discharges a blocker. -/
theorem effStatusAux_epic_zero_ne_done (s : State) (i : IssueId) (h : s.isEpic i = true) :
    s.effStatusAux 0 i ≠ Status.Done := by
  have hne : (s.presentChildren i).isEmpty = false := by
    cases hb : (s.presentChildren i).isEmpty with
    | false => rfl
    | true => unfold State.isEpic at h; rw [hb, Bool.not_true] at h; exact Bool.noConfusion h
  unfold State.effStatusAux
  by_cases hc : (s.issueData i).statusOf = Status.Cancelled
  · rw [if_pos hc]; exact fun heq => Status.noConfusion heq
  · rw [if_neg hc, hne, if_neg Bool.false_ne_true]
    exact fun heq => Status.noConfusion heq

/-! ## One-step fuel congruence (unconditional)

`effStatusAux` reads `fuel` only to evaluate the present children at one-lower fuel,
so if the children agree at two fuels the parent agrees at one-higher fuel. This is
the inductive step that lets fuel-irrelevance descend the parent graph. -/

/-- `List.all` agrees when the predicates agree on every element. -/
private theorem all_congr {α : Type _} (p q : α → Bool) :
    (l : List α) → (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.all_cons, List.all_cons, h x (List.mem_cons_self ..),
      all_congr p q xs (fun c hc => h c (List.mem_cons_of_mem x hc))]

/-- If every present child of `i` rolls up identically at fuels `a` and `b`, then `i`
    rolls up identically at `a+1` and `b+1`. -/
theorem effStatusAux_fuel_congr (s : State) (i : IssueId) {a b : Nat}
    (hkids : ∀ c ∈ s.presentChildren i, s.effStatusAux a c = s.effStatusAux b c) :
    s.effStatusAux (a + 1) i = s.effStatusAux (b + 1) i := by
  have hall := all_congr (fun c => Status.closed (s.effStatusAux a c))
    (fun c => Status.closed (s.effStatusAux b c)) (s.presentChildren i)
    (fun c hc => by
      show Status.closed (s.effStatusAux a c) = Status.closed (s.effStatusAux b c)
      rw [hkids c hc])
  unfold State.effStatusAux
  show (if (s.issueData i).statusOf = Status.Cancelled then Status.Cancelled
        else if (s.presentChildren i).isEmpty then (s.issueData i).statusOf
        else if (s.presentChildren i).all (fun c => Status.closed (s.effStatusAux a c))
             then Status.Done else Status.Open)
     = (if (s.issueData i).statusOf = Status.Cancelled then Status.Cancelled
        else if (s.presentChildren i).isEmpty then (s.issueData i).statusOf
        else if (s.presentChildren i).all (fun c => Status.closed (s.effStatusAux b c))
             then Status.Done else Status.Open)
  rw [hall]

/-! ## The epic-`Done` branch, modulo fuel-stability

The last spec branch — an epic that is not cancelled is `Done` iff every present
child is effectively closed — holds once the present children are *fuel-stable* at
`presentIssues.length - 1` (their rollup there already equals their `effectiveStatus`).
That stability is exactly the fuel-adequacy step, which holds on an acyclic parent
graph (the longest descending chain is shorter than the present-issue count) and is
the tracked residual. This theorem isolates the residual to that single hypothesis:
the rollup *logic* is correct; only fuel-adequacy is open. -/

/-- An epic, non-cancelled issue's effective status matches the spec (`Done` iff every
    present child is effectively closed) whenever its present children are fuel-stable
    at `presentIssues.length - 1` (ADR-0003 §3). -/
theorem effectiveStatus_epic_of_stable (s : State) (i : IssueId) (N : Nat)
    (hN : s.presentIssues.length = N + 1)
    (hepic : s.isEpic i = true)
    (hcanc : (s.issueData i).statusOf ≠ Status.Cancelled)
    (hstable : ∀ c ∈ s.presentChildren i, s.effStatusAux N c = s.effectiveStatus c) :
    s.effectiveStatus i
      = (if (s.presentChildren i).all (fun c => s.effClosed c) then Status.Done else Status.Open) := by
  have hne : (s.presentChildren i).isEmpty = false := by
    cases hb : (s.presentChildren i).isEmpty with
    | false => rfl
    | true => unfold State.isEpic at hepic; rw [hb, Bool.not_true] at hepic; exact Bool.noConfusion hepic
  have hall : (s.presentChildren i).all (fun c => Status.closed (s.effStatusAux N c))
            = (s.presentChildren i).all (fun c => s.effClosed c) :=
    all_congr _ _ (s.presentChildren i) (fun c hc => by
      show Status.closed (s.effStatusAux N c) = s.effClosed c
      unfold State.effClosed; rw [hstable c hc])
  unfold State.effectiveStatus
  rw [hN]
  unfold State.effStatusAux
  rw [if_neg hcanc]
  show (if (s.presentChildren i).isEmpty then (s.issueData i).statusOf
        else if (s.presentChildren i).all (fun c => Status.closed (s.effStatusAux N c))
             then Status.Done else Status.Open)
     = (if (s.presentChildren i).all (fun c => s.effClosed c) then Status.Done else Status.Open)
  rw [hne, if_neg Bool.false_ne_true, hall]

end State

end Tl.Kernel
