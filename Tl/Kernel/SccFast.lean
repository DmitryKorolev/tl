/-
`Tl.Kernel.SccFast` — the proved certificate checker behind the near-linear
cycle diagnostics.

The diagnostics need the SCC structure of present-bounded graphs (`kindSucc`
per kind, `precSucc`). Per-node closures cost Θ(V·(V+E)); the linear-time
algorithms (Tarjan/Kosaraju) have famously intricate invariants. This module
takes the checked-certificate road instead: an UNTRUSTED candidate partition
(`tarjanSCC`, `Tarjan.lean`) is validated by `sccCertOk`, whose acceptance
proves the spec's SCC characterizations on present nodes — the candidate
need not even be a true partition (phantom or duplicated components can
slip through the checks, but provably never matter, because every consumer
quantifies over present nodes only):

  * coverage — every present node carries a component index (`certCovers`);
  * condensation order — no edge increases the component index
    (`certOrdered`), so distinct components are never mutually reachable;
  * strong connectivity — per component, a forward and a backward frontier
    BFS from its root cover it (`compOk`), so same-component nodes are
    mutually reachable. The only reachability input is `bfsGo`'s, itself
    proved (`bfsGo_sound`).

Together these characterize the spec predicates with O(1)-amortized hash
probes: `sameSCC u v = (index u == index v)` (`cert_sameSCC`) and
`onCycle v = (succ v).any (index · == index v)` (`cert_onCycle`). The
checker proves SOUNDNESS only — a wrong candidate is rejected, never
trusted. That a correct Tarjan run is accepted is covered by tests; a
rejection costs speed, not correctness (the caller falls back to the proved
per-node-closure path).

Generic over any `succ` whose successors stay within `presentIssues`; the
per-graph hoisted views live in `CyclesFast.lean`.
-/
import Tl.Kernel.SccProps
import Tl.Kernel.HashMapView
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

namespace Tl.Kernel

open Tl.Crdt

/-! ## Frontier reachability (the only reachability the checker trusts) -/

/-- Frontier BFS with a hash visited set: each node expands at most once
    (`reachFix` re-derives the whole accumulated set per step; this does
    not). Fuel-total; the checker never needs completeness, so exhausted
    fuel merely under-covers and the certificate is rejected. -/
def bfsGo (succ : IssueId → List IssueId) :
    Nat → List IssueId → Std.HashSet IssueId → Std.HashSet IssueId
  | 0, _, vis => vis
  | _ + 1, [], vis => vis
  | n + 1, x :: front, vis =>
    if vis.contains x then bfsGo succ n front vis
    else bfsGo succ n (succ x ++ front) (vis.insert x)

/-- Everything `bfsGo` marks visited is reachable from `r`, provided the
    frontier and the already-visited set are. -/
theorem bfsGo_sound {succ : IssueId → List IssueId} {r : IssueId} :
    (fuel : Nat) → (front : List IssueId) → (vis : Std.HashSet IssueId) →
    (∀ x ∈ front, Relation.ReflTransGen (StepRel succ) r x) →
    (∀ x ∈ vis, Relation.ReflTransGen (StepRel succ) r x) →
    ∀ x ∈ bfsGo succ fuel front vis, Relation.ReflTransGen (StepRel succ) r x
  | 0, _, _, _, hv => hv
  | _ + 1, [], _, _, hv => hv
  | n + 1, x :: front, vis, hf, hv => by
    intro y hy
    unfold bfsGo at hy
    by_cases hx : vis.contains x = true
    · rw [if_pos hx] at hy
      exact bfsGo_sound n front vis (fun z hz => hf z (List.mem_cons_of_mem x hz)) hv y hy
    · rw [if_neg hx] at hy
      refine bfsGo_sound n (succ x ++ front) (vis.insert x) ?_ ?_ y hy
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact (hf x (List.mem_cons_self ..)).tail hz
        · exact hf z (List.mem_cons_of_mem x hz)
      · intro z hz
        rcases Std.HashSet.mem_insert.mp hz with hz | hz
        · exact (beq_iff_eq.mp hz) ▸ hf x (List.mem_cons_self ..)
        · exact hv z hz

/-- Reversing a reflexive-transitive walk over the flipped relation. -/
theorem reflTransGen_flip {rel : IssueId → IssueId → Prop} {a b : IssueId}
    (h : Relation.ReflTransGen (fun x y => rel y x) a b) :
    Relation.ReflTransGen rel b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc ih

/-! ## The component-index map -/

/-- Index every member of every candidate component by the component's
    position. Later bindings overwrite earlier ones, so soundness needs no
    disjointness from the untrusted candidate. -/
def cidxFrom : Nat → List (List IssueId) → Std.HashMap IssueId Nat →
    Std.HashMap IssueId Nat
  | _, [], m => m
  | i, c :: cs, m => cidxFrom (i + 1) cs (c.foldl (fun m x => m.insert x i) m)

def cidxOf (comps : List (List IssueId)) : Std.HashMap IssueId Nat :=
  cidxFrom 0 comps ∅

theorem getElem?_foldl_insertConst (c : List IssueId) (i : Nat)
    (m : Std.HashMap IssueId Nat) (u : IssueId) :
    (c.foldl (fun m x => m.insert x i) m)[u]? = if u ∈ c then some i else m[u]? := by
  induction c generalizing m with
  | nil => rw [List.foldl_nil, if_neg (fun h => nomatch h)]
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    by_cases hu : u ∈ as
    · rw [if_pos hu, if_pos (List.mem_cons_of_mem a hu)]
    · rw [if_neg hu, Std.HashMap.getElem?_insert]
      by_cases ha : a = u
      · rw [if_pos (beq_iff_eq.mpr ha), if_pos (ha ▸ List.mem_cons_self ..)]
      · rw [if_neg (fun h => ha (beq_iff_eq.mp h)),
          if_neg (fun h => (List.mem_cons.mp h).elim (fun he => ha he.symm) hu)]

theorem cidxFrom_sound : (j : Nat) → (cs : List (List IssueId)) →
    (m : Std.HashMap IssueId Nat) → (u : IssueId) → (i : Nat) →
    (cidxFrom j cs m)[u]? = some i →
    m[u]? = some i ∨ ∃ C, cs[i - j]? = some C ∧ u ∈ C ∧ j ≤ i
  | _, [], _, _, _, h => Or.inl h
  | j, c :: cs, m, u, i, h => by
    rcases cidxFrom_sound (j + 1) cs _ u i h with h' | ⟨C, hC, huC, hji⟩
    · rw [getElem?_foldl_insertConst] at h'
      by_cases hu : u ∈ c
      · rw [if_pos hu] at h'
        have hij : j = i := Option.some_inj.mp h'
        refine Or.inr ⟨c, ?_, hu, Nat.le_of_eq hij⟩
        rw [← hij, Nat.sub_self, List.getElem?_cons_zero]
      · rw [if_neg hu] at h'
        exact Or.inl h'
    · refine Or.inr ⟨C, ?_, huC, Nat.le_of_succ_le hji⟩
      have hpos : 0 < i - j := Nat.sub_pos_of_lt (Nat.lt_of_succ_le hji)
      have hd : (i - (j + 1)) + 1 = i - j := by
        rw [Nat.sub_succ]
        exact Nat.succ_pred_eq_of_pos hpos
      rw [← hd, List.getElem?_cons_succ]
      exact hC

theorem cidxOf_sound {comps : List (List IssueId)} {u : IssueId} {i : Nat}
    (h : (cidxOf comps)[u]? = some i) : ∃ C, comps[i]? = some C ∧ u ∈ C := by
  rcases cidxFrom_sound 0 comps ∅ u i h with h' | ⟨C, hC, huC, _⟩
  · rw [Std.HashMap.getElem?_empty] at h'
    exact nomatch h'
  · rw [Nat.sub_zero] at hC
    exact ⟨C, hC, huC⟩

/-! ## The certificate checker -/

/-- BFS fuel that over-covers any valid certificate's walk: one expansion
    per present node (`present.length`) plus one frontier entry per edge
    (the folded `Σ |succ v|`). The `+ 2` is constant slack covering the
    single seed push and the `n+1`-shaped fuel decrement so the bound is a
    strict over-cover, never an off-by-one underrun. An invalid certificate
    may still exhaust it — under-coverage only ever rejects, never misvalidates. -/
def certFuel (present : List IssueId) (succ : IssueId → List IssueId) : Nat :=
  present.foldl (fun a v => a + (succ v).length) (present.length + 2)

/-- Coverage: every present node carries a component index. -/
def certCovers (present : List IssueId) (cidx : Std.HashMap IssueId Nat) : Bool :=
  present.all (fun v => (cidx[v]?).isSome)

/-- Condensation order: no edge increases the component index. -/
def certOrdered (present : List IssueId) (succ : IssueId → List IssueId)
    (cidx : Std.HashMap IssueId Nat) : Bool :=
  present.all (fun v => (succ v).all (fun w =>
    decide (cidx[w]?.getD 0 ≤ cidx[v]?.getD 0)))

/-- One component's strong-connectivity check: from the root (its head), a
    forward BFS and a backward BFS — both restricted to the component —
    must each cover it. -/
def compOk (succ preds : IssueId → List IssueId) (cidx : Std.HashMap IssueId Nat)
    (fuel : Nat) (i : Nat) (comp : List IssueId) : Bool :=
  match comp with
  | [] => true
  | r :: rest =>
    let inComp := fun w => cidx[w]? == some i
    let fwd := bfsGo (fun x => (succ x).filter inComp) fuel [r] ∅
    let bwd := bfsGo (fun x => (preds x).filter inComp) fuel [r] ∅
    (r :: rest).all (fun x => fwd.contains x && bwd.contains x)

def compsOk (succ preds : IssueId → List IssueId) (cidx : Std.HashMap IssueId Nat)
    (fuel : Nat) : Nat → List (List IssueId) → Bool
  | _, [] => true
  | i, c :: cs =>
    compOk succ preds cidx fuel i c && compsOk succ preds cidx fuel (i + 1) cs

/-- The whole certificate. Acceptance proves the SCC characterizations
    below; rejection is only ever a fallback signal. -/
def sccCertOk (present : List IssueId) (succ : IssueId → List IssueId)
    (comps : List (List IssueId)) : Bool :=
  let cidx := cidxOf comps
  let preds := bucketBy (present.flatMap (fun v => (succ v).map (fun w => (w, v))))
  certCovers present cidx && certOrdered present succ cidx
    && compsOk succ (fun x => preds[x]?.getD []) cidx (certFuel present succ) 0 comps

theorem sccCertOk_parts {present : List IssueId} {succ : IssueId → List IssueId}
    {comps : List (List IssueId)} (h : sccCertOk present succ comps = true) :
    certCovers present (cidxOf comps) = true
    ∧ certOrdered present succ (cidxOf comps) = true
    ∧ compsOk succ
        (fun x => (bucketBy (present.flatMap (fun v =>
          (succ v).map (fun w => (w, v)))))[x]?.getD [])
        (cidxOf comps) (certFuel present succ) 0 comps = true := by
  have h' : (certCovers present (cidxOf comps)
      && certOrdered present succ (cidxOf comps)
      && compsOk succ
          (fun x => (bucketBy (present.flatMap (fun v =>
            (succ v).map (fun w => (w, v)))))[x]?.getD [])
          (cidxOf comps) (certFuel present succ) 0 comps) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

/-! ## Soundness of the accepted certificate -/

theorem certCovers_sound {present : List IssueId} {cidx : Std.HashMap IssueId Nat}
    (h : certCovers present cidx = true) {v : IssueId} (hv : v ∈ present) :
    (cidx[v]?).isSome = true := by
  unfold certCovers at h
  rw [List.all_eq_true] at h
  exact h v hv

theorem certOrd_edge {present : List IssueId} {succ : IssueId → List IssueId}
    {cidx : Std.HashMap IssueId Nat} (h : certOrdered present succ cidx = true)
    {v : IssueId} (hv : v ∈ present) {w : IssueId} (hw : w ∈ succ v) :
    cidx[w]?.getD 0 ≤ cidx[v]?.getD 0 := by
  unfold certOrdered at h
  rw [List.all_eq_true] at h
  have hv' := h v hv
  rw [List.all_eq_true] at hv'
  exact of_decide_eq_true (hv' w hw)

/-- Along any walk, the component index never increases — and the endpoint
    stays present. -/
theorem certOrd_reach {present : List IssueId} {succ : IssueId → List IssueId}
    {cidx : Std.HashMap IssueId Nat} (hsucc : ∀ x, succ x ⊆ present)
    (h : certOrdered present succ cidx = true)
    {u v : IssueId} (hu : u ∈ present)
    (huv : Relation.ReflTransGen (StepRel succ) u v) :
    cidx[v]?.getD 0 ≤ cidx[u]?.getD 0 ∧ v ∈ present := by
  induction huv with
  | refl => exact ⟨Nat.le_refl _, hu⟩
  | tail _ hbc ih =>
    obtain ⟨hle, hbp⟩ := ih
    exact ⟨Nat.le_trans (certOrd_edge h hbp hbc) hle, hsucc _ hbc⟩

/-- An accepted component check makes its members mutually reachable. -/
theorem compOk_sound {succ preds : IssueId → List IssueId}
    (hpred : ∀ x y, y ∈ preds x → x ∈ succ y)
    {cidx : Std.HashMap IssueId Nat} {fuel : Nat} {i : Nat} {C : List IssueId}
    (h : compOk succ preds cidx fuel i C = true)
    {u v : IssueId} (hu : u ∈ C) (hv : v ∈ C) :
    Relation.ReflTransGen (StepRel succ) u v := by
  match C, hu, hv with
  | r :: rest, hu, hv =>
    have h' : ((r :: rest).all (fun x =>
        (bfsGo (fun x => (succ x).filter (fun w => cidx[w]? == some i))
          fuel [r] ∅).contains x
        && (bfsGo (fun x => (preds x).filter (fun w => cidx[w]? == some i))
          fuel [r] ∅).contains x)) = true := h
    rw [List.all_eq_true] at h'
    have hu' := h' u hu
    have hv' := h' v hv
    rw [Bool.and_eq_true] at hu' hv'
    have hseed : ∀ (f : IssueId → List IssueId), ∀ x ∈ [r],
        Relation.ReflTransGen (StepRel f) r x := by
      intro f x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ Relation.ReflTransGen.refl
    have hempty : ∀ (f : IssueId → List IssueId), ∀ x ∈ (∅ : Std.HashSet IssueId),
        Relation.ReflTransGen (StepRel f) r x :=
      fun f x hx => absurd hx (Std.HashSet.not_mem_empty)
    -- u reaches r: the backward BFS walks the flipped relation
    have hur : Relation.ReflTransGen (StepRel succ) u r := by
      have hmem := Std.HashSet.contains_iff_mem.mp hu'.2
      have hr := bfsGo_sound fuel [r] ∅ (hseed _) (hempty _) u hmem
      have hflip : Relation.ReflTransGen (fun x y => StepRel succ y x) r u :=
        Relation.ReflTransGen.mono
          (fun x y hxy => hpred x y (List.mem_of_mem_filter hxy)) hr
      exact reflTransGen_flip hflip
    -- r reaches v: the forward BFS, restriction dropped
    have hrv : Relation.ReflTransGen (StepRel succ) r v := by
      have hmem := Std.HashSet.contains_iff_mem.mp hv'.1
      have hr := bfsGo_sound fuel [r] ∅ (hseed _) (hempty _) v hmem
      exact Relation.ReflTransGen.mono
        (fun x y hxy => List.mem_of_mem_filter hxy) hr
    exact hur.trans hrv

theorem compsOk_get {succ preds : IssueId → List IssueId}
    {cidx : Std.HashMap IssueId Nat} {fuel : Nat} :
    (j : Nat) → (cs : List (List IssueId)) →
    compsOk succ preds cidx fuel j cs = true →
    ∀ {i : Nat} {C : List IssueId}, cs[i]? = some C →
    compOk succ preds cidx fuel (j + i) C = true
  | _, [], _, i, C, hC => by
    rw [List.getElem?_nil] at hC
    exact nomatch hC
  | j, c :: cs, h, i, C, hC => by
    have h' : (compOk succ preds cidx fuel j c
        && compsOk succ preds cidx fuel (j + 1) cs) = true := h
    rw [Bool.and_eq_true] at h'
    match i, hC with
    | 0, hC =>
      rw [List.getElem?_cons_zero] at hC
      rw [Nat.add_zero]
      exact (Option.some_inj.mp hC) ▸ h'.1
    | i + 1, hC =>
      rw [List.getElem?_cons_succ] at hC
      have hrec := compsOk_get (j + 1) cs h'.2 hC
      rw [show j + (i + 1) = j + 1 + i by rw [Nat.add_assoc, Nat.add_comm 1 i]]
      exact hrec

/-- Pairs bucketed for the backward BFS decode back to real edges. -/
theorem predPairs_sound {present : List IssueId} {succ : IssueId → List IssueId}
    {x y : IssueId}
    (h : y ∈ (bucketBy (present.flatMap (fun v =>
      (succ v).map (fun w => (w, v)))))[x]?.getD []) :
    x ∈ succ y := by
  have hp := mem_bucketBy h
  obtain ⟨v, _, hmem⟩ := List.mem_flatMap.mp hp
  obtain ⟨w, hw, heq⟩ := List.mem_map.mp hmem
  have hwx : w = x := congrArg Prod.fst heq
  have hvy : v = y := congrArg Prod.snd heq
  exact hwx ▸ hvy ▸ hw

/-- Equal component indices make nodes mutually reachable (one direction
    shown; swap the hypotheses for the other). -/
theorem cert_mutual {present : List IssueId} {succ : IssueId → List IssueId}
    {comps : List (List IssueId)}
    (hcomps : compsOk succ
      (fun x => (bucketBy (present.flatMap (fun v =>
        (succ v).map (fun w => (w, v)))))[x]?.getD [])
      (cidxOf comps) (certFuel present succ) 0 comps = true)
    {u v : IssueId} {i : Nat}
    (hu : (cidxOf comps)[u]? = some i) (hv : (cidxOf comps)[v]? = some i) :
    Relation.ReflTransGen (StepRel succ) u v := by
  obtain ⟨Cu, hCu, huC⟩ := cidxOf_sound hu
  obtain ⟨Cv, hCv, hvC⟩ := cidxOf_sound hv
  have hCC : Cu = Cv := Option.some_inj.mp (hCu.symm.trans hCv)
  have hok := compsOk_get 0 comps hcomps hCu
  rw [Nat.zero_add] at hok
  exact compOk_sound (fun x y hy => predPairs_sound hy) hok huC (hCC ▸ hvC)

/-! ## The spec characterizations under an accepted certificate -/

/-- `sameSCC` is component-index equality. -/
theorem cert_sameSCC {s : State} {succ : IssueId → List IssueId}
    (hsucc : ∀ x, succ x ⊆ s.presentIssues)
    {comps : List (List IssueId)}
    (hcert : sccCertOk s.presentIssues succ comps = true)
    {u v : IssueId} (hu : u ∈ s.presentIssues) (hv : v ∈ s.presentIssues) :
    s.sameSCC succ u v = ((cidxOf comps)[u]? == (cidxOf comps)[v]?) := by
  obtain ⟨hcov, hord, hcomps⟩ := sccCertOk_parts hcert
  apply Bool.eq_iff_iff.mpr
  rw [State.sameSCC_iff hsucc hu hv, beq_iff_eq]
  constructor
  · rintro ⟨hvu, huv⟩
    have h1 := (certOrd_reach hsucc hord hu huv).1
    have h2 := (certOrd_reach hsucc hord hv hvu).1
    have heq : (cidxOf comps)[u]?.getD 0 = (cidxOf comps)[v]?.getD 0 :=
      Nat.le_antisymm h2 h1
    obtain ⟨iu, hiu⟩ := Option.isSome_iff_exists.mp (certCovers_sound hcov hu)
    obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.mp (certCovers_sound hcov hv)
    rw [hiu, hiv]
    rw [hiu, hiv, Option.getD_some, Option.getD_some] at heq
    rw [heq]
  · intro h
    obtain ⟨iu, hiu⟩ := Option.isSome_iff_exists.mp (certCovers_sound hcov hu)
    have hiv : (cidxOf comps)[v]? = some iu := h ▸ hiu
    exact ⟨cert_mutual hcomps hiv hiu, cert_mutual hcomps hiu hiv⟩

/-- `onCycle` is "some successor shares my component". -/
theorem cert_onCycle {s : State} {succ : IssueId → List IssueId}
    (hsucc : ∀ x, succ x ⊆ s.presentIssues)
    {comps : List (List IssueId)}
    (hcert : sccCertOk s.presentIssues succ comps = true)
    {v : IssueId} (hv : v ∈ s.presentIssues) :
    s.onCycle succ v
      = (succ v).any (fun w => (cidxOf comps)[w]? == (cidxOf comps)[v]?) := by
  obtain ⟨hcov, hord, hcomps⟩ := sccCertOk_parts hcert
  apply Bool.eq_iff_iff.mpr
  rw [onCycle_iff hsucc v, List.any_eq_true]
  constructor
  · rintro ⟨b, hb, hbv⟩
    refine ⟨b, hb, ?_⟩
    rw [beq_iff_eq]
    have hbp : b ∈ s.presentIssues := hsucc v hb
    have h1 := (certOrd_reach hsucc hord hbp hbv).1
    have h2 := certOrd_edge hord hv hb
    have heq : (cidxOf comps)[b]?.getD 0 = (cidxOf comps)[v]?.getD 0 :=
      Nat.le_antisymm h2 h1
    obtain ⟨ib, hib⟩ := Option.isSome_iff_exists.mp (certCovers_sound hcov hbp)
    obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.mp (certCovers_sound hcov hv)
    rw [hib, hiv]
    rw [hib, hiv, Option.getD_some, Option.getD_some] at heq
    rw [heq]
  · rintro ⟨w, hw, hbeq⟩
    rw [beq_iff_eq] at hbeq
    obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.mp (certCovers_sound hcov hv)
    have hwi : (cidxOf comps)[w]? = some iv := hbeq.trans hiv
    exact ⟨w, hw, cert_mutual hcomps hwi hiv⟩

end Tl.Kernel
