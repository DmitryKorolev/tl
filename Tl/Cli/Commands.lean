/-
`Tl.Cli.Commands` — the stage-1 verbs (vision §stage 1, ADR-0020 shapes).

Every command returns `CmdOut` — the `--json` `data`, the human text, and
stderr notes (foreign-segment refusal disclosures, clamp warnings). Errors
travel as structured `Tl.Error`s; the dispatch layer owns streams and exit
codes. Write verbs run their guards *inside* the locked `transact` build
(against the under-lock state), so a refusal happens before any byte is
written; the pinned guard inventory (ADR-0008 §write-time guards) is exactly
`not-claimable` (claim of a non-ready target), and `not-closeable` (epic
`--as done`, self-duplicate). Re-closing with the same resolution (and, for
duplicate, the same canonical target) appends nothing and succeeds.
-/
import Tl.Cli.Project
import Tl.Cli.Render
import Tl.Cli.Resolve
import Tl.Cli.Init
import Tl.Cli.Licenses
import Tl.Kernel.Path
import Tl.Kernel.Claim
-- `ready_sorted`: the ranked queue is `readyLe`-ordered, which the read facets
-- then have to preserve (`readyRanked_sorted`).
import Tl.Kernel.Ranking
import Tl.Sync.Local
import Tl.Sync.Remote
import Tl.Sync.AutoSync
import Tl.Import.Bulk

namespace Tl.Cli

open Tl.Store
open Tl.Kernel
open Tl.Format
open Tl.Crdt
open Lean (Json)

structure CmdOut where
  data : Json
  human : String
  notes : List String := []
  /-- Style-parameterized human rendering (ADR-0017). When present, `run`
      resolves the `Style` from flags/env/TTY and uses this instead of the
      plain `human` (which stays the `Style.plain` fallback). -/
  render : Option (Style → String) := none

/-- Load the read view (no lock — ADR-0015 §5). Before folding, run the
    read-time refresh (ADR-0016 §3): absorb any sibling's published changes
    from the shared `refs/tl/log` so a worktree sees its siblings without an
    explicit `tl sync`. Best-effort and lock-free — it never fails the read. -/
def loadView (dirOverride : Option String) (skipBad : Bool := false) : TlM View := do
  let d ← discover dirOverride
  let replica ← loadReplica d
  -- the read-time refresh returns a `degraded` reason when it could not run
  -- (git absent, read-only FS); surface it rather than serve a silently-stale
  -- view (ADR-0008). A racing concurrent refresher does not trip this — the
  -- foreign-segment writeback uses a per-call CSPRNG temp suffix + atomic
  -- rename (ADR-0016 §3 hardening), so `degraded` reflects a real inability to
  -- read the ref, not benign contention.
  let refresh ← Tl.Sync.refreshFromRef d (replica.map (·.id))
  let now ← liftSys (fun e => .mk' .internal s!"clock read failed: {e}") nowMs
  -- skew-check foreign segments against `now` (ADR-0007): a future-dated
  -- foreign op is deferred from the fold until local time catches up; the
  -- fold itself runs through the content-keyed cache (ADR-0022)
  let loaded ← readStateCached d skipBad (some now) (replica.map (·.id))
  -- the hoisted collections and their indexed copies come from the single pure
  -- constructor, so each is bound once (`effStatusAll`/`provenanceMap`/
  -- `parentEdgesFast` run one pass) and each field is provably the summary of
  -- *this* state (`View.rollup_ofLoaded` and friends)
  return View.ofLoaded d loaded now replica
    (refresh.degraded.map (fun r =>
      s!"served a moment-stale read: could not refresh from the shared ref ({r}) — fix git/filesystem access, then `tl sync` to catch up"))

/-- The disclosure for a skew-deferred op (ADR-0007), shared by the read and
    write paths so neither silently drops a future-dated op (ADR-0008
    loud-not-silent — a fold computed without some ops always says so). The op
    is not lost; it folds once local wall-clock passes its HLC. -/
def deferredNote (rid : String) (n : Nat) : String :=
  s!"segment {rid}.jsonl line {n}: held back — its HLC is beyond the clock-skew window ({rid}'s clock is ahead of yours); it folds once local time catches up — run `tl doctor`"

/-- The ADR-0008 command-level refusal policy for reads: a refused *own*
    segment fails the command; foreign refusals are disclosed on stderr and the
    read succeeds (folding the others). The all-refused catch-all only fires
    when there is *no own replica to anchor a partial read* — with an own
    replica present (even with no own segment yet), an all-*foreign* refusal is
    a disclosure, not a failure: read-time refresh (ADR-0016 §3) now routinely
    materializes sibling segments, so a single bad sibling segment must not
    take down a worktree whose own state is fine/empty. (`doctor` is exempt.) -/
def cleanReadNotes (v : View) : TlM (List String) := do
  if let some own := v.replica then
    if let some r := v.loaded.refused.find? (·.replicaId == own.id) then
      throw r.error
  if v.replica.isNone && !v.loaded.refused.isEmpty
      && v.loaded.refused.length == v.loaded.segmentCount then
    throw (v.loaded.refused.head?.map (·.error)
      |>.getD (.mk' .internal "every segment refused — repair or remove the damaged segments under .tl/log/"))
  return v.refreshNote.toList
    ++ v.loaded.refused.map (fun r =>
      s!"segment {r.replicaId}.jsonl refused (line {r.line}): folded the others; its owner repairs or re-syncs it")
    ++ v.loaded.warnings ++ v.loaded.skipped.map (fun (rid, n) =>
      s!"--skip-bad: dropped segment {rid}.jsonl line {n}")
    ++ v.loaded.deferred.map (fun (rid, n) => deferredNote rid n)

/-- The disclosure notes a write surfaces (ADR-0008: loud, never silent): a
    refused foreign segment OR a skew-deferred future op means the guards and
    echo were computed from a fold that dropped those ops. (An own-segment
    refusal already failed the transact.) Mirrors `cleanReadNotes`' drop
    categories so neither path silently omits a dropped op. -/
def writeNotes (ctx : TxContext) : List String :=
  ctx.loaded.refused.map (fun r =>
    s!"segment {r.replicaId}.jsonl refused (line {r.line}): this write was checked against a fold without it; its owner repairs or re-syncs it")
  ++ ctx.loaded.warnings
  ++ ctx.loaded.deferred.map (fun (rid, n) => deferredNote rid n)

/-- The post-write view: the pre-state plus the appended records. -/
def postView (v : TxContext) (parsed : List ParsedOp) (now : Nat) : View :=
  let state := parsed.foldl (fun s p => Tl.Kernel.apply s p.kernelOp) v.loaded.state
  let ops := v.loaded.ops ++ parsed
  View.ofLoaded v.dirs { v.loaded with state, ops } now (some v.replica)

private def listPayload (key : String) (total : Nat) (rows : List Json) : Json :=
  Json.mkObj [("count", jnum total), (key, Json.arr rows.toArray)]

/-! ## Read verbs -/

/-- The styled one-line listing + footer (ADR-0017 §1/§3), shared by ready
    and list. `summary` is the footer's one-line; `total` drives the
    truncation disclosure. -/
private def listRender (v : View) (rows : List IssueId) (total : Nat) (summary empty : String)
    : Style → String := fun st =>
  if rows.isEmpty && total == 0 then empty
  else String.intercalate "\n" (rows.map (styledLine st v))
    ++ "\n" ++ footer st summary rows.length total

/-- The freshness window after which `ready` nudges to sync (ADR-0011 §2):
    a generous default — sync is opt-in (`--sync`), this only reminds. -/
def syncStaleWindowMs : Nat := 60 * 60 * 1000

/-- The plain stderr line emitted right before `tl sync`'s network leg, so an
    interactive sync over a slow remote is not silent. A one-shot notice, not a
    spinner or a timer; the resolved remote name interpolated for context. -/
def remoteSyncNotice (remote : String) : String :=
  s!"syncing with remote '{remote}'…"

/-- The process-global sink the remote-leg progress notice fires into. The
    default prints the sanitized notice to stderr (the remote name is
    attacker-influenceable git-config data, and this bypasses `Main`'s stderr
    chokepoint). An `IO.Ref` so an in-process embedder — the test harness —
    can install a silent or recording sink instead of spraying notices onto
    the developer's terminal. -/
initialize syncProgressSink : IO.Ref (String → IO Unit) ←
  IO.mkRef (fun remote => IO.eprintln s!"tl: {sanitizeSingle (remoteSyncNotice remote)}")

/-- A full `tl sync` (local leg, the remote leg in a git repo, then a second
    local leg to absorb the remote's additions), recording the last-sync marker
    so `doctor`/`ready` never contact the remote themselves (ADR-0016). Shared by
    `cmdSync` and the `--sync` flag. -/
def performSync (d : Dirs) : TlM (Tl.Sync.LocalOutcome × Tl.Sync.RemoteOutcome × List String) := do
  -- stealth (ADR-0001 §7): never publish or push. Explicit `tl sync` fails closed
  -- earlier (`cmdSync`); the best-effort `--sync`/`--verify` brackets funnel here,
  -- so short-circuiting to a no-op note keeps *every* sharing path off the ref and
  -- the remote — a single chokepoint rather than a guard per write verb.
  if ← isStealth d then
    return ({ ran := false, published := false, absorbed := [], tip := none },
            { ran := false, remote := "", pushed := false, pulled := false, tip := none },
            [s!"sync skipped: stealth repo — local-only, never shared (remove `{d.stealthDisplayPath}` to un-stealth)"])
  let own ← loadReplica d
  let ownId := own.map (·.id)
  let l ← Tl.Sync.syncLocal d ownId
  -- announce the remote leg before the (possibly multi-second) network
  -- fetch/push, via the installed `syncProgressSink`. The notice fires only when
  -- a remote resolves; stdout JSON stays a single atomic object (progress is
  -- stderr-only in the default sink).
  let r ← if l.ran then Tl.Sync.syncRemote d (announce := fun remote => do
            (← syncProgressSink.get) remote)
          else pure { ran := false, remote := "", pushed := false, pulled := false, tip := none }
  -- a second local leg after a remote that ran materializes what the fetch added
  -- (it can pull a new replica). Best-effort — the push already succeeded, so
  -- never fail here; a failure self-heals on the next read's refresh. Fold its
  -- absorb into the reported local outcome so a remote-pulled replica is not
  -- silently dropped from `absorbed`; disclose a failure (loud-not-silent).
  let (l, pnotes) ← if r.ran then
      (try
        let l2 ← Tl.Sync.syncLocal d ownId
        pure ({ l with absorbed := (l.absorbed ++ l2.absorbed).eraseDups, tip := l2.tip }, ([] : List String))
       catch e => pure (l, [s!"reconciled with the remote, but materializing the pulled changes locally failed ({e.message}) — the next read or `tl sync` will catch up"]))
    else pure (l, [])
  -- record last-sync only when the remote leg actually reconciled: lastSync means
  -- "last reconciled with the remote", so a local-only sync (no remote, or a
  -- remote added later) must not mark the view clean-vs-remote (a false-clean source).
  if r.ran then
    let now ← liftSys (fun e => .mk' .internal s!"{e}") nowMs
    try storeLastSync d now r.tip catch _ => pure ()
  return (l, r, pnotes)

/-- The local-only sync posture (no remote contact): the resolved upstream name
    (git config), the last-sync time, and how many `refs/tl/log` commits the local
    ref sits ahead of that last sync (unpushed). The live *behind* count needs the
    remote, so it is `--sync`'s job (sync then read), not this. -/
structure SyncPosture where
  upstream : Option String
  lastSyncMs : Option Nat
  ahead : Nat

/-- This replica's own-segment ops written since the last sync: lines (= ops) in
    `.tl/log/<own>.jsonl` on disk now, minus those in that segment at the synced
    ref tip. Both local (a fs read + a `cat-file`), no network — and it counts the
    *segment* ops, so it is correct in the main worktree too (where writes don't
    advance `refs/tl/log` until a sync, so a commit-based count reads a false 0). -/
private def ownOpsSince (d : Dirs) (own : String) (syncedTip : Option String) : TlM Nat := do
  let (segs, _) ← readSegments d
  let localLines := (segs.find? (·.replicaId == own)).elim 0 (fun sd => (completeLines sd.bytes).length)
  -- ops in the own segment at the synced tip; 0 when that sync left no ref (an
  -- empty / first sync) — then all local ops are unsynced, never a false 0.
  let syncedLines ← match syncedTip with
    | some t => pure (((← Tl.Sync.readRefAt d t).find? (·.replicaId == own)).elim 0
        (fun sd => (completeLines sd.bytes).length))
    | none => pure 0
  -- Nat subtraction clamps to 0 if the synced ref held more own-segment lines
  -- than disk — only possible under same-replica-id divergence, which ADR-0007
  -- rules out; the clamp is then a safe "not ahead" rather than a wrong count.
  return localLines - syncedLines

def syncPostureOf (d : Dirs) : TlM SyncPosture := do
  let upstream ← Tl.Sync.resolveRemote d
  let ls ← loadLastSync d
  let own := (← loadReplica d).map (·.id)
  let ahead ← match ls, own with
    | some (_, syncedTip), some o => ownOpsSince d o syncedTip
    | _, _ => pure 0  -- never synced ⇒ the "never synced" message/advisory covers it
  return { upstream, lastSyncMs := ls.map (·.1), ahead }

/-- `ready`'s staleness advisory from the local posture (`now` = the view clock).
    `none` ⇒ no advisory. Fires only with a configured remote, and reports the
    first applicable reason: never-synced, unsynced local changes, or a stale
    last-sync. -/
def stalenessMsg (p : SyncPosture) (now : Nat) : Option String :=
  match p.upstream with
  | none => none
  | some name =>
    match p.lastSyncMs with
    | none => some s!"view may be stale — never synced with '{name}'; run `tl sync` (or rerun with --sync)"
    | some ms =>
      if p.ahead > 0 then some s!"view may be stale — {p.ahead} local change(s) since last sync; run `tl sync`"
      else if now - ms > syncStaleWindowMs then some s!"view may be stale — last synced {(now - ms) / 60000}m ago; run `tl sync`"
      else none

/-! ### Shared read filter facets (ADR-0020)

`ready` and `list` take the same `--label`/`--assignee` facets with the same
semantics, so the predicates and the echoed human clause live here once and
both verbs call them — the two surfaces cannot drift. -/

/-- One read filter facet (`--label`/`--deferred`/`--stale`/`--status`/
    `--assignee`/`--priority`/`--blocked`): a predicate over the sorted set,
    gated by whether the facet is even in play (`active` — an absent/empty
    flag is a no-op, not a false-matching filter), plus whether a match on it
    already licenses showing a closed/rolled-up issue. `applyFacets`/
    `facetsBypassGate` fold a `List ListFacet` in place of what used to be one
    hand-threaded `let sorted := if active then sorted.filter pred else
    sorted` reassignment per facet, plus a separately-maintained gate
    condition (`showAll || staleArg.isSome || deferred || …`) — a new facet is
    one list entry, not two edits kept in sync only by a comment. -/
structure ListFacet where
  active : Bool
  pred : IssueId → Bool
  /-- `--deferred`/`--stale`/`--status` all select *into* the closed/rolled-up
      set on purpose, so an active match there licenses standing down the
      default effClosed gate; `--label`/`--assignee`/`--priority`/`--blocked`
      only ever refine the existing open set, so they leave the gate standing
      (`false`, the default). `ready` never consults this — its set is
      workable-only by construction, so nothing there can bypass a gate. -/
  bypassClosedGate : Bool := false

/-- Every active facet's predicate, ANDed onto `sorted`. One pass per active
    facet; the result is a single conjunctive filter of the input, so neither
    the fold order nor the order of the facet list changes it
    (`applyFacets_eq_filter`, `applyFacets_of_perm`). -/
def applyFacets (facets : List ListFacet) (sorted : List IssueId) : List IssueId :=
  facets.foldl (fun acc f => if f.active then acc.filter f.pred else acc) sorted

/-- Whether any active facet in the list licenses bypassing the default
    effClosed gate. -/
def facetsBypassGate (facets : List ListFacet) : Bool :=
  facets.any (fun f => f.active && f.bypassClosedGate)

/-! #### The facet algebra, proved

The claims the read verbs make about `applyFacets` — ADR-0020's "different
facets compose with AND", the `ListFacet` docstring's "an absent/empty flag is a
no-op, not a false-matching filter", and `cmdReady`'s "filter keeps order, so
`count` stays the post-filter total and `items` the ranked head of it" — are
properties of a pure total fold, so they are theorems here rather than sampled
rows in the CLI suite (ADR-0004 tiering: prove what is provable).

All of them decompose from **one** characterization: the fold *is* a single
`List.filter` by the conjunction of every active facet's predicate
(`applyFacets_eq_filter`). Membership, order, multiplicity and the empty-flag
reading are then corollaries of that one statement rather than four independent
laws — an implementation that deduplicated its survivors would satisfy the
membership and sublist corollaries but not the characterization. (Reordering is
already ruled out by the sublist corollary, since `List.Sublist` is
order-preserving.) The cross-layer consequence follows too: no facet can widen
`ready`'s workable set.

The CLI suite keeps its facet rows, but as a regression net over the compiled
code and the flag wiring (`cliReadyFacetTests` / `cliListFacetComposeTests`
through the binary, `readyRankedTests` in-process), never as the evidence for
the algebra. -/

theorem applyFacets_nil (sorted : List IssueId) : applyFacets [] sorted = sorted := rfl

theorem applyFacets_cons (f : ListFacet) (facets : List ListFacet) (sorted : List IssueId) :
    applyFacets (f :: facets) sorted
      = applyFacets facets (if f.active then sorted.filter f.pred else sorted) := rfl

/-- **The characterization.** The fold is exactly one `List.filter` by the
    conjunction of every *active* facet's predicate — an inactive facet
    contributes the `true` clause. Everything else about `applyFacets` (which
    elements survive, in which order, how many copies of each, and what an
    absent flag does) is a corollary of this single equation, so no
    reimplementation that changes any of those can satisfy it. -/
theorem applyFacets_eq_filter (facets : List ListFacet) (sorted : List IssueId) :
    applyFacets facets sorted
      = sorted.filter (fun i => facets.all (fun f => !f.active || f.pred i)) := by
  induction facets generalizing sorted with
  | nil => exact (List.filter_true sorted).symm
  | cons f fs ih =>
    rw [applyFacets_cons]
    cases hf : f.active with
    | true =>
      rw [if_pos rfl, ih, List.filter_filter]
      refine List.filter_congr (fun x _ => ?_)
      rw [List.all_cons, hf]
      simp only [Bool.not_true, Bool.false_or]
      exact Bool.and_comm _ _
    | false =>
      rw [if_neg Bool.false_ne_true, ih]
      refine List.filter_congr (fun x _ => ?_)
      rw [List.all_cons, hf]
      simp only [Bool.not_false, Bool.true_or, Bool.true_and]

/-- **AND-composition, and no-op inactivity.** Membership after the fold is
    membership before it conjoined with every *active* facet's predicate: the
    facets compose with AND regardless of order, and an inactive facet
    contributes nothing (rather than filtering everything out). -/
theorem mem_applyFacets_iff (facets : List ListFacet) (sorted : List IssueId) (i : IssueId) :
    i ∈ applyFacets facets sorted
      ↔ i ∈ sorted ∧ ∀ f ∈ facets, f.active = true → f.pred i = true := by
  rw [applyFacets_eq_filter, List.mem_filter]
  constructor
  · intro h
    refine ⟨h.1, fun f hf hact => ?_⟩
    have hfa : (!f.active || f.pred i) = true := List.all_eq_true.mp h.2 f hf
    rw [hact] at hfa
    simp only [Bool.not_true, Bool.false_or] at hfa
    exact hfa
  · intro h
    refine ⟨h.1, List.all_eq_true.mpr (fun f hf => ?_)⟩
    cases hact : f.active with
    | false => simp only [Bool.not_false, Bool.true_or]
    | true =>
      simp only [Bool.not_true, Bool.false_or]
      exact h.2 f hf hact

/-- **The no-op reading, at list-identity strength.** `mem_applyFacets_iff`
    settles membership; this settles the list. When no facet is in play the
    fold returns its input *unchanged* — an absent or empty flag cannot even
    reorder or deduplicate the set, let alone filter it to nothing. -/
theorem applyFacets_eq_self_of_inactive (facets : List ListFacet) (sorted : List IssueId)
    (h : ∀ f ∈ facets, f.active = false) : applyFacets facets sorted = sorted := by
  rw [applyFacets_eq_filter, List.filter_congr (q := fun _ => true)
    (fun x _ => List.all_eq_true.mpr (fun f hf => by rw [h f hf]; rfl))]
  exact List.filter_true sorted

/-- **The facet list is a set, not a pipeline.** Reordering the facets — which
    predicate the fold runs first — cannot change the result, because the result
    is the conjunctive filter of all of them. -/
theorem applyFacets_of_perm {facets facets' : List ListFacet} (h : facets.Perm facets')
    (sorted : List IssueId) : applyFacets facets sorted = applyFacets facets' sorted := by
  rw [applyFacets_eq_filter, applyFacets_eq_filter]
  refine List.filter_congr (fun x _ => ?_)
  cases hg : facets'.all (fun f => !f.active || f.pred x) with
  | true => exact List.all_eq_true.mpr (fun f hf => List.all_eq_true.mp hg f (h.mem_iff.mp hf))
  | false =>
    obtain ⟨f, hf, hpf⟩ := List.all_eq_false.mp hg
    cases hfs : facets.all (fun f => !f.active || f.pred x) with
    | false => rfl
    | true => exact absurd (List.all_eq_true.mp hfs f (h.mem_iff.mpr hf)) hpf

/-- **Order and multiplicity preservation.** The filtered list is a sublist of
    the input: facets remove elements, and change nothing else — not the order
    of the survivors, and not how many copies of each survive (a `filter` keeps
    every copy that passes; `applyFacets_eq_filter` is what rules out a
    deduplicating fold, which this sublist law alone would permit). This is what
    makes a read verb's post-filter list still the *ranked* list — `cmdReady`
    reports `ranked.length` as the total and renders `readyPage ranked limit`
    from it, both of which need the ranking to survive the fold. -/
theorem applyFacets_sublist (facets : List ListFacet) (sorted : List IssueId) :
    (applyFacets facets sorted).Sublist sorted := by
  rw [applyFacets_eq_filter]
  exact List.filter_sublist

/-- The closed-gate bypass is exactly "some active facet selects into the closed
    set" — the condition `cmdList` stands the default effClosed gate down on. An
    inactive facet cannot license it, so an unused `--status`/`--stale`/
    `--deferred` flag never widens the default open-set view. -/
theorem facetsBypassGate_eq_true_iff (facets : List ListFacet) :
    facetsBypassGate facets = true
      ↔ ∃ f ∈ facets, f.active = true ∧ f.bypassClosedGate = true := by
  simp only [facetsBypassGate, List.any_eq_true, Bool.and_eq_true]

/-- **`ready`'s post-facet queue.** The proved workable set for a view, narrowed
    by the read facets — the one expression `cmdReady` reports `count` and
    `items` from. It is a named production definition rather than an inline
    `let` so that the laws below are stated about the code that runs: an edit to
    the *derivation* — a different rollup, another queue, an extra filter — is an
    edit to this definition and breaks the theorems instead of quietly orphaning
    them. What it does not mechanize is `cmdReady` continuing to call it; that
    much stays a review obligation. -/
def readyRanked (v : View) (facets : List ListFacet) : List IssueId :=
  applyFacets facets (State.readyFast v.rollup v.state v.now)

/-- **The queue, characterized at the production expression.** The narrowing
    laws below are one-directional by design, and on their own a `readyRanked`
    that returned `[]` would satisfy every one of them — under-reporting is the
    failure a queue verb's users actually suffer. This is the iff that rules it
    out: a row is in `ready`'s output exactly when the kernel calls it ready and
    every supplied facet accepts it. `readyRanked_cannot_widen` is its forward
    half. -/
theorem mem_readyRanked_iff (v : View) (facets : List ListFacet) (i : IssueId)
    (hv : v.rollup = v.state.effStatusAll) :
    i ∈ readyRanked v facets
      ↔ i ∈ v.state.ready v.now ∧ ∀ f ∈ facets, f.active = true → f.pred i = true := by
  rw [readyRanked, mem_applyFacets_iff, hv, State.readyFast_eq]

/-- …with the rollup hypothesis discharged at production's only view
    constructor, so nothing is assumed about the view beyond how it was built. -/
theorem mem_readyRanked_ofLoaded_iff (facets : List ListFacet) (i : IssueId)
    (dirs : Dirs) (loaded : Loaded) (now : Nat) (replica : Option Tl.Clock.Replica)
    (refreshNote : Option String) :
    i ∈ readyRanked (View.ofLoaded dirs loaded now replica refreshNote) facets
      ↔ i ∈ (View.ofLoaded dirs loaded now replica refreshNote).state.ready now
        ∧ ∀ f ∈ facets, f.active = true → f.pred i = true :=
  mem_readyRanked_iff _ facets i (View.rollup_ofLoaded dirs loaded now replica refreshNote)

/-- **No facet can widen `ready`.** `cmdReady` folds its facets over the fast
    workable queue; every survivor is still in the proved `ready` set. Composes
    the AND-law above (a facet only ever removes) with the kernel's refinement
    bridge `State.readyFast_eq`; `hrollup` is `loadView`'s construction of
    `v.rollup` (`= v.state.effStatusAll`). -/
theorem readyFacets_cannot_widen (facets : List ListFacet) (rollup : AMap IssueId Status)
    (s : State) (now : Instant) (i : IssueId) (hrollup : rollup = s.effStatusAll)
    (h : i ∈ applyFacets facets (State.readyFast rollup s now)) : i ∈ s.ready now := by
  subst hrollup
  rw [← State.readyFast_eq s now]
  exact ((mem_applyFacets_iff facets _ i).mp h).1

/-- The same bound read through `mem_ready_iff`: a facet survivor is a
    materialized issue satisfying the full readiness predicate (open, non-epic,
    non-deferred, every blocker discharged). A filtered `tl ready` row is never
    a row `tl ready` could not have shown unfiltered. -/
theorem readyFacets_isReady (facets : List ListFacet) (rollup : AMap IssueId Status)
    (s : State) (now : Instant) (i : IssueId) (hrollup : rollup = s.effStatusAll)
    (h : i ∈ applyFacets facets (State.readyFast rollup s now)) :
    i ∈ s.presentIssues ∧ s.isReady now i = true :=
  (mem_ready_iff s now i).mp (readyFacets_cannot_widen facets rollup s now i hrollup h)

/-- **The ranking survives the facets.** A sublist of a sorted list is sorted, so
    the filtered queue is still ordered by the kernel's `readyLe` ranking — the
    step `cmdReady`'s "still the ranked list" comment needs and that
    `applyFacets_sublist` alone does not give. `readyPage_sorted` carries it
    through the `--limit` cap, so the rendered head is the top of that
    ranking. -/
theorem readyFacets_sorted (facets : List ListFacet) (rollup : AMap IssueId Status)
    (s : State) (now : Instant) (hrollup : rollup = s.effStatusAll) :
    List.Pairwise (fun a b => s.readyLe a b = true)
      (applyFacets facets (State.readyFast rollup s now)) := by
  subst hrollup
  have hsub : (applyFacets facets (State.readyFast s.effStatusAll s now)).Sublist (s.ready now) :=
    (State.readyFast_eq s now) ▸ applyFacets_sublist facets (State.readyFast s.effStatusAll s now)
  exact List.Pairwise.sublist hsub (State.ready_sorted s now)

/-- The bound at the production expression: every row `cmdReady` can report is a
    row of the proved `ready` set. `hv` is the view-construction invariant
    (`View.rollup_ofLoaded`), discharged in `readyRanked_cannot_widen_ofLoaded`. -/
theorem readyRanked_cannot_widen (v : View) (facets : List ListFacet) (i : IssueId)
    (hv : v.rollup = v.state.effStatusAll) (h : i ∈ readyRanked v facets) :
    i ∈ v.state.ready v.now :=
  readyFacets_cannot_widen facets v.rollup v.state v.now i hv h

/-- …with the hypothesis discharged at production's only view construction: a
    view `loadView` built (the only kind `cmdReady` is ever handed) carries the
    batched rollup of its own state, so a facet survivor is a genuine `ready`
    row with nothing assumed about the view beyond how it was built. -/
theorem readyRanked_cannot_widen_ofLoaded (facets : List ListFacet) (i : IssueId)
    (dirs : Dirs) (loaded : Loaded) (now : Nat) (replica : Option Tl.Clock.Replica)
    (refreshNote : Option String)
    (h : i ∈ readyRanked (View.ofLoaded dirs loaded now replica refreshNote) facets) :
    i ∈ (View.ofLoaded dirs loaded now replica refreshNote).state.ready now :=
  readyRanked_cannot_widen _ facets i
    (View.rollup_ofLoaded dirs loaded now replica refreshNote) h

/-- Half of `cmdReady`'s `count`/`items` discipline, at the production
    expression: the reported list is a subsequence of the workable queue, so
    `ranked.length` is the post-filter total of that queue and never more. The
    `items` half belongs to `readyPage_prefix` below, which is stated about the
    cap `cmdReady` actually renders through. -/
theorem readyRanked_sublist (v : View) (facets : List ListFacet) :
    (readyRanked v facets).Sublist (State.readyFast v.rollup v.state v.now) :=
  applyFacets_sublist facets _

/-- …and it is still ranked. -/
theorem readyRanked_sorted (v : View) (facets : List ListFacet)
    (hv : v.rollup = v.state.effStatusAll) :
    List.Pairwise (fun a b => v.state.readyLe a b = true) (readyRanked v facets) :=
  readyFacets_sorted facets v.rollup v.state v.now hv

/-- **`ready`'s rendered page.** `--limit` applied to the ranked queue, with `0`
    meaning uncapped (ADR-0020). Named for the reason `readyRanked` is: the cap
    is the last step between the proved queue and what the user sees, so it
    belongs inside the perimeter rather than living as an anonymous `let` that
    the prefix law only resembles. It takes the already-computed queue rather
    than rebuilding it, so naming it costs no second fold. -/
def readyPage (ranked : List IssueId) (limit : Nat) : List IssueId :=
  if limit == 0 then ranked else ranked.take limit

/-- The page is a prefix of the queue — including the uncapped `--limit 0`
    branch, which the bare `take` law does not reach. With `readyPage_length`
    that is exactly "uncapped, or the first `limit` rows"; on its own the prefix
    law would also admit an empty page. -/
theorem readyPage_prefix (ranked : List IssueId) (limit : Nat) :
    (readyPage ranked limit).IsPrefix ranked := by
  unfold readyPage
  by_cases h : (limit == 0) = true
  · rw [if_pos h]
  · rw [if_neg h]
    exact List.take_prefix limit ranked

/-- **The page is as long as the cap allows.** With `readyPage_prefix` this is
    exactly "uncapped, or the first `limit` rows": a prefix is pinned by its
    length. Each half rules out a degenerate page the other permits — an empty
    page satisfies the prefix law, and the *bottom* `limit` rows satisfy this
    one — so both are load-bearing and neither landmark may be retired alone. -/
theorem readyPage_length (ranked : List IssueId) (limit : Nat) :
    (readyPage ranked limit).length
      = if limit == 0 then ranked.length else min limit ranked.length := by
  unfold readyPage
  by_cases h : (limit == 0) = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact List.length_take

/-- The cap cannot introduce a row: every row `cmdReady` renders is still in the
    proved `ready` set, at the exact expression it renders from. -/
theorem mem_readyPage_ready (v : View) (facets : List ListFacet) (limit : Nat) (i : IssueId)
    (hv : v.rollup = v.state.effStatusAll)
    (h : i ∈ readyPage (readyRanked v facets) limit) : i ∈ v.state.ready v.now :=
  readyRanked_cannot_widen v facets i hv
    ((readyPage_prefix (readyRanked v facets) limit).sublist.subset h)

/-- …and the page is still ranked. -/
theorem readyPage_sorted (v : View) (facets : List ListFacet) (limit : Nat)
    (hv : v.rollup = v.state.effStatusAll) :
    List.Pairwise (fun a b => v.state.readyLe a b = true)
      (readyPage (readyRanked v facets) limit) :=
  List.Pairwise.sublist (readyPage_prefix (readyRanked v facets) limit).sublist
    (readyRanked_sorted v facets hv)

/-- `--label` (repeatable ⇒ **AND**, exact membership: an issue can carry many
    labels — ADR-0020). Shared by `ready` and `list`. -/
def labelFacet (v : View) (labels : List String) : ListFacet :=
  { active := !labels.isEmpty
    pred := fun i => labels.all (v.issueData i).labels.presentElements.contains }

/-- `--assignee` (repeatable ⇒ **OR**, exact/case-sensitive: an identity is
    discrete, not free text, and an issue holds one — ADR-0020). `targets` are
    the already-`me`-resolved names. Shared by `ready` and `list`. -/
def assigneeFacet (v : View) (targets : List String) : ListFacet :=
  { active := !targets.isEmpty
    pred := fun i => match (v.issueData i).assignee.value.getD none with
      | some a => targets.contains a
      | none => false }

/-! #### The two shared facets, proved

`mem_applyFacets_iff` fixes how facets compose *with each other* (AND). The
other half of ADR-0020's composition rule is how a *repeated* facet composes
with itself — AND for `--label` (an issue carries many labels), OR for
`--assignee` (an issue holds one) — together with the reading of an absent
flag. Both are properties of these two predicates, so they are theorems here. -/

/-- **`--label` repeats are AND.** An issue passes iff it carries *every*
    requested label; the membership test is exact (the present-element view of
    its label OR-Set), never a prefix or substring match. -/
theorem labelFacet_pred_eq_true_iff (v : View) (labels : List String) (i : IssueId) :
    (labelFacet v labels).pred i = true
      ↔ ∀ l ∈ labels, (v.issueData i).labels.presentElements.contains l = true := by
  simp only [labelFacet, List.all_eq_true]

/-- **`--assignee` repeats are OR.** An issue passes iff it *has* an assignee
    and that one value is among the (already-`me`-resolved) targets. -/
theorem assigneeFacet_pred_eq_true_iff (v : View) (targets : List String) (i : IssueId) :
    (assigneeFacet v targets).pred i = true
      ↔ ∃ a, (v.issueData i).assignee.value.getD none = some a ∧ targets.contains a = true := by
  simp only [assigneeFacet]
  cases ha : (v.issueData i).assignee.value.getD none with
  | none =>
    constructor
    · intro hc; exact Bool.noConfusion hc
    · intro hc
      obtain ⟨a, hsome, _⟩ := hc
      exact (Option.some_ne_none a hsome.symm).elim
  | some a =>
    constructor
    · intro hc; exact ⟨a, rfl, hc⟩
    · intro hc
      obtain ⟨b, hsome, hb⟩ := hc
      rw [Option.some.injEq] at hsome
      subst hsome
      exact hb

/-- An *unassigned* issue is never a `--assignee` match — the facet selects
    into the assigned set, so it can only ever narrow. -/
theorem assigneeFacet_pred_unassigned (v : View) (targets : List String) (i : IssueId)
    (h : (v.issueData i).assignee.value.getD none = none) :
    (assigneeFacet v targets).pred i = false := by
  simp only [assigneeFacet, h]

/-- **A flag is in play exactly when it was supplied.** The `→` direction is
    what makes an absent flag a no-op (by `mem_applyFacets_iff` /
    `applyFacets_eq_self_of_inactive`) rather than a filter that matches
    nothing; the `←` direction is its dual, and the one that rules out the
    opposite defect — a supplied `--label`/`--assignee` that is silently
    ignored would pass every narrowing law here, since a facet that never runs
    can never widen anything either. -/
theorem labelFacet_active_iff (v : View) (labels : List String) :
    (labelFacet v labels).active = true ↔ labels ≠ [] := by
  cases labels with
  | nil =>
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; exact absurd rfl h
  | cons l ls =>
    constructor
    · intro _; exact List.cons_ne_nil l ls
    · intro _; rfl

theorem assigneeFacet_active_iff (v : View) (targets : List String) :
    (assigneeFacet v targets).active = true ↔ targets ≠ [] := by
  cases targets with
  | nil =>
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; exact absurd rfl h
  | cons t ts =>
    constructor
    · intro _; exact List.cons_ne_nil t ts
    · intro _; rfl

theorem labelFacet_nil_inactive (v : View) : (labelFacet v []).active = false := rfl

theorem assigneeFacet_nil_inactive (v : View) : (assigneeFacet v []).active = false := rfl

/-- **The two shared facets, composed — `ready`'s facet list.** A survivor was
    in the input, carries *every* requested label, and — when `--assignee` was
    actually supplied — holds one of the requested assignees. Both flags absent
    leaves the right-hand side vacuous, which is the no-op reading; either flag
    supplied makes its clause a real obligation (via the `active` iffs above),
    which is the "a supplied flag filters" reading.

    Scope note: this is the pair `cmdReady` evaluates. `cmdList` shares the same
    two facets but folds them inside a longer list with its own five, so it does
    not instantiate *this* statement; what covers `list` is `mem_applyFacets_iff`
    over that longer list, together with `labelFacet_pred_eq_true_iff` and
    `assigneeFacet_pred_eq_true_iff` for the two shared clauses. -/
theorem mem_readyFacets_iff (v : View) (labels targets : List String)
    (sorted : List IssueId) (i : IssueId) :
    i ∈ applyFacets [labelFacet v labels, assigneeFacet v targets] sorted
      ↔ i ∈ sorted
        ∧ (∀ l ∈ labels, (v.issueData i).labels.presentElements.contains l = true)
        ∧ (targets ≠ [] →
            ∃ a, (v.issueData i).assignee.value.getD none = some a
              ∧ targets.contains a = true) := by
  rw [mem_applyFacets_iff]
  constructor
  · intro h
    obtain ⟨hs, hall⟩ := h
    refine ⟨hs, ?_, ?_⟩
    · intro l hl
      by_cases hne : labels = []
      · exact absurd (hne ▸ hl) List.not_mem_nil
      · have hact : (labelFacet v labels).active = true := (labelFacet_active_iff v labels).mpr hne
        exact (labelFacet_pred_eq_true_iff v labels i).mp
          (hall (labelFacet v labels) (List.mem_cons.mpr (Or.inl rfl)) hact) l hl
    · intro hne
      have hact : (assigneeFacet v targets).active = true :=
        (assigneeFacet_active_iff v targets).mpr hne
      exact (assigneeFacet_pred_eq_true_iff v targets i).mp
        (hall (assigneeFacet v targets)
          (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))) hact)
  · intro h
    obtain ⟨hs, hlab, hasg⟩ := h
    refine ⟨hs, fun f hf hact => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact (labelFacet_pred_eq_true_iff v labels i).mpr hlab
    · rcases List.mem_cons.mp hf' with rfl | hf''
      · exact (assigneeFacet_pred_eq_true_iff v targets i).mpr
          (hasg ((assigneeFacet_active_iff v targets).mp hact))
      · exact absurd hf'' List.not_mem_nil

/-- `tl ready` with neither flag returns the ranked queue verbatim. -/
theorem applyFacets_readyFacets_nil (v : View) (sorted : List IssueId) :
    applyFacets [labelFacet v [], assigneeFacet v []] sorted = sorted :=
  applyFacets_eq_self_of_inactive _ sorted (by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact labelFacet_nil_inactive v
    · rcases List.mem_cons.mp hf' with rfl | hf''
      · exact assigneeFacet_nil_inactive v
      · exact absurd hf'' (List.not_mem_nil))

/-- Neither shared facet licenses standing down the closed gate: both refine an
    existing open set rather than selecting into the closed one. Stated per
    facet rather than about one particular list, because the consumer is
    `cmdList` — the only caller of `facetsBypassGate` — and `cmdList` folds
    these two inside a seven-facet list with its own five. With
    `facetsBypassGate_eq_true_iff` (a bypass must come from *some* facet that
    asks for one) these two lemmas are what says sharing the facets with `ready`
    cannot introduce a gate bypass into `list`'s default open-set view, whatever
    else that list holds. (`cmdReady` never consults the flag at all: its queue
    is workable-only by construction, which is `readyFacets_isReady`.) -/
theorem labelFacet_no_bypass (v : View) (labels : List String) :
    (labelFacet v labels).bypassClosedGate = false := rfl

theorem assigneeFacet_no_bypass (v : View) (targets : List String) :
    (assigneeFacet v targets).bypassClosedGate = false := rfl

/-- The corollary at `ready`'s own pair. -/
theorem readyFacets_bypassGate_false (v : View) (labels targets : List String) :
    facetsBypassGate [labelFacet v labels, assigneeFacet v targets] = false := by
  simp only [facetsBypassGate, labelFacet, assigneeFacet, List.any_cons, List.any_nil,
    Bool.and_false, Bool.or_false]

/-- `--assignee me` resolves to the ambient actor for the *filter*; the raw
    tokens (including `me`) stay for the human echo (ADR-0013/ADR-0020). -/
def resolveAssigneeTargets (assignees : List String) (meActor : Option String) : List String :=
  assignees.map (fun t => if t == "me" then meActor.getD t else t)

/-- The one representation used to echo a facet value. A raw value may be
    entirely removed by the render sanitizer while still being a legitimate,
    exact-match stored value (for example a control-only imported label or an
    explicit actor). Keep that value filterable, but render a visible placeholder
    rather than the ambiguous dangling `label ` / `assignee ` clause. -/
def facetDisplayValue (value : String) : String :=
  let shown := sanitizeSingle value
  if shown.trimAscii.isEmpty then "(empty after sanitization)" else shown

/-- The `[filtered by …]` clause appended to a read verb's human summary: a
    stable clause order, each echoed value sanitized (the values are untrusted
    free text — Tl/Cli/Sanitize.lean), and `me` echoed verbatim rather than
    resolved. Empty when no filter is active. Shared by `ready` and `list` so
    the two footers read alike.

    The assembled clause runs through `sanitizeSingle` a second time: the
    per-value pass bounds each value at 1 KiB, but a caller repeating a facet a
    few hundred times would still compose a multi-hundred-KB one-line footer, so
    the whole suffix carries the same 1 KiB bound (with the same inline
    truncation disclosure) that every other rendered field and error message
    does. The separators are plain ASCII, so re-sanitizing changes nothing else. -/
def filterSuffix (clauses : List (String × List String)) (extras : List String) : String :=
  let named := clauses.flatMap (fun (k, vs) =>
    if vs.isEmpty then [] else
      [s!"{k} {String.intercalate ", " (vs.map facetDisplayValue)}"])
  let all := named ++ extras
  if all.isEmpty then ""
  else s!" [filtered by {sanitizeSingle (String.intercalate "; " all)}]"

def cmdReady (dirOverride : Option String) (limit : Nat) (skipBad : Bool) (sync : Bool)
    (labels assignees : List String) (meActor : Option String) : TlM CmdOut := do
  let d ← discover dirOverride
  -- --sync reconciles first, best-effort: a read must not fail on a remote
  -- hiccup, so a sync error degrades to a note and the (still-useful) listing.
  let syncNotes ← if sync then
      (try (do let (_, _, pn) ← performSync d; pure pn)
       catch e => pure [s!"could not reconcile with the remote ({e.message}) — showing local state; run `tl sync`"])
    else pure []
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  -- the proved workable set, then the read facets narrow it (ADR-0020: facets
  -- change membership, never the shape) — `readyRanked`, so the laws proved
  -- above are about this list and not a copy of its derivation, and
  -- `readyPage` for the cap for the same reason. Membership is characterized
  -- both ways (`mem_readyRanked_iff`): no row can fall outside the proved
  -- `ready` set, and none that belongs is dropped. The ranking survives
  -- (`readyPage_sorted`), so `count` stays the post-filter total and `items`
  -- the ranked head of it (`readyPage_prefix`). No facet here can bypass a
  -- closed gate: `readyFast` already excludes closed/rolled-up issues, so
  -- `bypassClosedGate` is moot.
  let facets : List ListFacet :=
    [ labelFacet v labels, assigneeFacet v (resolveAssigneeTargets assignees meActor) ]
  let ranked := readyRanked v facets
  let capped := readyPage ranked limit
  let suffix := filterSuffix [("label", labels), ("assignee", assignees)] []
  -- staleness advisory (ADR-0011 §2): always derived from the posture after any
  -- --sync. A successful sync makes it clean (ahead 0, lastSync now ⇒ none); a
  -- failed --sync leaves genuine staleness, so it must still surface in
  -- data.staleness (agents read the field; humans also get the degrade note).
  let advisory ← (do pure (stalenessMsg (← syncPostureOf d) v.now))
  let r : Style → String := fun st =>
    (match advisory with | some a => st.paint "33" s!"({a})" ++ "\n" | none => "")
      ++ (listRender v capped ranked.length
            s!"Ready: {ranked.length} issue(s) with no active blockers{suffix}"
            (if suffix.isEmpty then "nothing is ready"
             else s!"nothing is ready{suffix}")) st
  let data := (listPayload "items" ranked.length (capped.map (issueRow v))).setObjVal!
                "staleness" (advisory.elim Json.null Json.str)
  return { data, human := r Style.plain, render := some r, notes := notes ++ syncNotes }

/-- When a claim goes stale: the epoch-ms instant `claimedAt + window`. `claimedAt`
    is an HLC, so its physical-ms component is `hlc / 2^16` (ADR-0007). Shared by
    `list --stale`, `claim --steal`, and `doctor`'s `staleClaims` so the staleness
    boundary cannot drift between them (ADR-0013). A claim is stale when `now` is
    past this. -/
def claimStaleDeadlineMs (claimedHlc windowMs : Nat) : Nat := claimedHlc / 2 ^ 16 + windowMs

/-- A single `--priority` value: a 0–4 priority, or a `usage` error. The sole home
    of the 0–4 contract and its message — shared by `create`/`update`'s
    `priorityFlag` and `list --priority`, so the same typo teaches the same fix
    everywhere (ADR-0008: a `message` says what to do next). -/
def parsePriorityValue (v : String) : Except Tl.Error Nat :=
  match v.toNat? with
  | some n => if n ≤ 4 then .ok n
      else .error (.mk' .usage s!"--priority must be 0-4 (got '{sanitizeSingle v}')")
  | none => .error (.mk' .usage s!"--priority must be 0-4 (got '{sanitizeSingle v}')")

/-- The raw and parsed `list` facet values as one unfalsifiable pair. Construct
    this before resolving `--assignee me` or discovering/loading a project, so
    every malformed value is a `usage` error with zero actor, filesystem, or
    log I/O while human rendering retains the exact accepted spellings. -/
structure ParsedListFacets where
  private mk ::
  labels : List String
  assignees : List String
  statusArgs : List String
  priorityArgs : List String
  staleArg : Option String
  statuses : List Status
  priorities : List Nat
  staleWindow : Option Nat

def parseListFacets (labels assignees statuses priorities : List String)
    (staleArg : Option String) : Except Tl.Error ParsedListFacets := do
  let parsedStatuses ← statuses.mapM fun s => match statusOfWire? s with
    | some st => pure st
    | none => .error (.mk' .usage
        s!"--status: '{sanitizeSingle s}' is not a status — use open, in_progress, done, or cancelled")
  let parsedPriorities ← priorities.mapM parsePriorityValue
  let staleWindow ← match staleArg with
    | none => pure none
    | some raw => match Time.parseDurationMs? raw with
      | some window => pure (some window)
      | none => .error (.mk' .usage
          s!"--stale: '{sanitizeSingle raw}' is not a valid duration — use e.g. 45m, 1h, 24h")
  return {
    labels, assignees, statusArgs := statuses, priorityArgs := priorities,
    staleArg, statuses := parsedStatuses, priorities := parsedPriorities, staleWindow }

def cmdList (dirOverride : Option String) (limit : Nat) (tree showAll skipBad : Bool)
    (deferred : Bool) (meActor : Option String) (blocked : Bool)
    (parsed : ParsedListFacets) : TlM CmdOut := do
  -- `runVerb` parsed every facet before resolving `me`; this command therefore
  -- begins its I/O only after the complete value grammar has succeeded.
  let wantStatuses := parsed.statuses
  let wantPriorities := parsed.priorities
  let staleWindow := parsed.staleWindow
  -- `--assignee me` matches the resolved current actor; other names match verbatim.
  -- The raw `assignees` (incl. `me`) are kept for the human summary.
  let assigneeTargets := resolveAssigneeTargets parsed.assignees meActor
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  -- every issue, oldest first; then by default hide effectively-closed
  -- issues (done/cancelled, incl. rolled-up epics) — `tl ready` shows
  -- workable, `tl list` shows open work, `tl list --all` shows everything
  -- (vision / ADR-0020 list-grammar decision).
  -- createdAt from the hoisted provenance map (one log pass), not s.createdAtOf
  -- (an O(N) add-tag find per issue ⇒ O(N²) over the sort). For a present issue
  -- both are the min create-tag HLC: createdAtOf is the min over add-tag HLCs,
  -- Prov.createdAt is the min-stamp create's HLC, and Stamp orders by HLC first,
  -- so they coincide (CrossTests pins it per seed). Default 0 = createdAtOf's nil.
  let createdAt := fun i => ((v.provFor i).createdAt).getD 0
  let sorted := (v.present.map (fun i => (createdAt i, i)))
    |>.mergeSort (fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2)))
    |>.map (·.2)
  -- The seven `list` facets — `--label` (repeatable ⇒ AND), `--deferred`
  -- (ADR-0010: open with a still-future `deferUntil`, the `v.deferred` derived
  -- view — the exact complement of `ready`'s defer conjunct), `--stale`
  -- (InProgress with a `claimedAt` older than the window, mirroring
  -- `doctor`/`claim --steal` via `claimStaleDeadlineMs`), `--status` (repeatable
  -- ⇒ OR over effectiveStatus — the shown column, ADR-0020), `--assignee`
  -- (repeatable ⇒ OR, exact/case-sensitive — an identity is discrete, not free
  -- text; `me` was resolved to the actor above), `--priority` (repeatable ⇒ OR,
  -- exact 0–4 — no threshold form is frozen), and `--blocked` (the derived
  -- `blocked` view — open issues with ≥1 unclosed blocker; not the inverse of
  -- `ready`, which additionally excludes epics, in-progress, and deferred
  -- items). `--deferred`/`--stale`/`--status` select *into* the closed/rolled-up
  -- set on purpose, so they bypass the effClosed gate below — `--stale` in
  -- particular must not re-hide a claim whose epic rolled up to done: that is
  -- exactly the lingering claim to surface, which `doctor`'s staleClaims (raw
  -- status, no effClosed gate) also lists, keeping the two surfaces in
  -- agreement (ADR-0013).
  let facets : List ListFacet :=
    [ labelFacet v parsed.labels,
      { active := deferred, pred := v.deferred, bypassClosedGate := true },
      { active := staleWindow.isSome, bypassClosedGate := true
        pred := fun i => match staleWindow with
          | none => false
          | some w => (v.issueData i).statusOf == .InProgress
              && match (v.provFor i).claimedAt with
                 | some h => v.now > claimStaleDeadlineMs h w
                 | none => false },
      { active := !wantStatuses.isEmpty, bypassClosedGate := true
        pred := fun i => wantStatuses.contains (v.effStatus i) },
      assigneeFacet v assigneeTargets,
      { active := !wantPriorities.isEmpty
        pred := fun i => wantPriorities.contains (v.issueData i).priorityOf.val },
      { active := blocked, pred := v.blocked } ]
  let sorted := applyFacets facets sorted
  let visible := if showAll || facetsBypassGate facets then sorted
    else sorted.filter (fun i => !v.effClosed i)
  let openN := (sorted.filter (fun i => (v.issueData i).statusOf == .Open)).length
  let inProg := (sorted.filter (fun i => (v.issueData i).statusOf == .InProgress)).length
  -- the human summary always names which filters produced the shown rows (the JSON
  -- `count` already reflects them); a stable clause order, `me` echoed verbatim. The
  -- distinctive deferred/stale headlines and the `--all` open/in-progress breakdown
  -- are preserved, with the filter clause appended to each.
  -- the values are untrusted (assignee/label are free text); sanitize every echoed
  -- token so no control/ANSI byte reaches the footer (Tl/Cli/Sanitize.lean contract)
  let facets :=
    [("status", parsed.statusArgs), ("label", parsed.labels),
     ("assignee", parsed.assignees), ("priority", parsed.priorityArgs)]
  let extras := if blocked then ["blocked"] else []
  let suffix := filterSuffix facets extras
  let anyFilter := !suffix.isEmpty
  -- the zero-result line names the filter too (parity with `ready`): with a
  -- typo'd facet value a bare "no issues" cannot be told apart from an empty
  -- backlog, so the empty line says which filter produced nothing. It also
  -- carries `--deferred`/`--stale`, which name themselves in the headlines
  -- below but have no headline to appear in when nothing matched.
  let emptySuffix := filterSuffix facets (extras ++
    (if deferred then ["deferred"] else []) ++
    parsed.staleArg.elim [] (fun window => [s!"stale {window}"]))
  let emptyLine := if emptySuffix.isEmpty then "no issues" else s!"no issues{emptySuffix}"
  let summary :=
    if deferred then
      s!"{visible.length} deferred issue(s) (open, deferred until a future time){suffix}"
    else if parsed.staleArg.isSome then
      s!"{visible.length} stale claim(s) (in progress, older than the --stale window){suffix}"
    else if showAll then s!"Total: {sorted.length} issues ({openN} open, {inProg} in progress){suffix}"
    else if !parsed.statusArgs.isEmpty then s!"{visible.length} issue(s){suffix}"
    else if anyFilter then s!"{visible.length} open issue(s) ({inProg} in progress){suffix}"
    else s!"{visible.length} open issues ({inProg} in progress) — --all includes closed"
  -- the --json data is the flat items array (the tree is a human browse mode
  -- only — ADR-0017 §2; a recursive JSON shape isn't pinned)
  let capped := if limit == 0 then visible else visible.take limit
  -- tree (the default render; `--flat` opts into one-line rows): a forest over
  -- the visible set. Roots = a visible issue with no visible canonical parent
  -- (an orphan, a dangling/cycle parent, or a parent hidden by the filter →
  -- top level, §2); closed children are pruned unless --all.
  let r : Style → String :=
    if tree then
      -- the visible set as a hash for O(1) "is the parent visible?" — the root
      -- test runs per visible issue, so a List `contains` here would be Θ(N²)
      let visSet := Tl.Kernel.hashSetOf visible
      let isRoot (i : IssueId) : Bool := match canonicalParentE v i with
        | none => true | some p => !visSet.contains p
      let roots := visible.filter isRoot
      -- a child renders iff it is in the visible (post-filter) set — so the tree
      -- shows exactly the filtered rows the --json `count` reports. This is
      -- `!v.effClosed` for the default and always-true for `--all` (both are then
      -- `visible`), and under a facet (--label/--stale/--deferred) it correctly
      -- hides a non-matching child of a matching parent (review).
      let keep : IssueId → Bool := visSet.contains
      fun st =>
        if roots.isEmpty then (if visible.isEmpty then emptyLine else "(no top-level issues)")
        else
          -- cap the rendered ROWS (issues, top-to-bottom), not the roots: a human
          -- asked for `limit` issues, not `limit` whole subtrees (capping roots
          -- barely bit, since a few epics expand their entire subtrees). Render the
          -- forest in reading order, then take the first `limit` lines; the footer
          -- discloses how many rows are hidden (a truncated subtree's dangling
          -- `├──` together with "Showing X of Y" reads as "more below").
          let allLines := treeForest st v roots keep v.kids
          let shown := if limit == 0 then allLines else allLines.take limit
          String.intercalate "\n" shown
            ++ "\n" ++ footer st summary shown.length allLines.length
    else listRender v capped visible.length summary emptyLine
  return { data := listPayload "items" visible.length (capped.map (issueRow v))
           human := r Style.plain, render := some r, notes }

/-- The `show` claim verdict: surfaces this replica's latest own claim on the
    issue as `(outcome, currentAssignee)` — one derivation behind both the
    JSON claim block and the human `claim:` line (parity). Decoupled from
    staleness (ADR-0013, amended) — your own claim provenance is shown
    regardless of age; the stale *window* is a `doctor` concern
    (`tl.staleAfter`), not a display gate here. `outcome`:
    - `won` — the actor's CURRENT claim holds: both registers carry one
      coherent winning claim by this actor (the kernel `claimWonB`, evaluated
      at the winning assignee stamp) — so a re-claim by the same actor from
      another replica still reads won after convergence, while the assignee
      register alone would misreport a concurrent close (which outstamps
      `status` but never writes `assignee`). The winner is at least the
      surfaced claim's own folded write, so its stamp is at/after the claim's
      and `claimWonB` pins its value — neither needs a separate check.
    - `ended` — not won, and this replica's own claim ran its course by the
      claimant's own successor write, with no lost race hidden underneath.
      Three conditions, all evaluated only on the not-won path:
      (a) *no contest* — no `status`/`assignee` write on this issue that the
      claimant did not author is stamped above the surfaced own claim. The
      contested ops are those whose delta touches either register — `create`
      (status seed), `claim`/steal (both), `close` (status), `reopen` (both,
      incl. the assignee clear); not `update`/`defer`/`meta`/edge/label. A
      register winner cannot represent contest history — a claimant's own later
      close or reopen buries the foreign write's stamp, whether that write was a
      foreign claim OR a foreign close/reopen — so the op log is scanned
      directly. (b) the winning *status* write is the claimant's own; (c) the
      *assignee* winner is the claimant's value or a clear the claimant authored
      (a reopen). All three read authorship through the single `opAuthoredByOwn`
      predicate below, so the contest test (a) is exactly its negation.
    - `superseded` — otherwise: a write the claimant did not make (or cannot be
      proven to have made) took either register, or a foreign status/assignee
      write raced and was later buried — the lost race stays visible under a
      burying close, a burying reopen, and an unattributable successor alike.
    `show`-only surface: the `claim` verb's own echo stays binary
    won/superseded (the ratified wire contract).

    Authorship for this classifier is the envelope `actor` ONLY: an actor-less
    op is *not* attributable — two parties can share a replica-id (the
    documented footgun, ADR-0013), so the replica is not proof of authorship —
    and `ended` asserts "your own successor write, no contention", which must
    never rest on unprovable authorship. So the unattributable cases (an
    actor-less op, or an origin absent under compaction) resolve toward
    `superseded` ("inspect"), never toward a false `ended`. -/
def opAuthoredByOwn (actor : String) (p : ParsedOp) : Bool := p.actor == some actor

/-- Did the claimant author the op whose stamp is `t`, among `ops`? Envelope
    actor only (`opAuthoredByOwn`); an absent origin (compaction) is likewise
    unattributable ⇒ `false`. -/
def stampAuthoredByOwn (ops : List ParsedOp) (actor : String) (t : Stamp) : Bool :=
  match ops.find? (fun p => decide (p.stamp = t)) with
  | some p => opAuthoredByOwn actor p
  | none => false

def claimVerdict (v : View) (i : IssueId) : Option (ClaimOutcome × Option String) := do
  let own ← v.replica
  let ownVal ← own.toNat?
  let claims := v.loaded.ops.filterMap (fun p =>
    match p.op with
    | .claim ci actor => if ci == i && p.stamp.replica == ownVal then some (p.stamp, actor) else none
    | _ => none)
  -- latest own claim by the full stamp order (the cross-op comparison rule,
  -- Tl/Cli/Project.lean §provenance). NB: like the contest scan below, this
  -- surfaces the own claim only by its physical presence in `v.loaded.ops` —
  -- once `tl compact` can trim ops, dropping it drops the whole claim block, so
  -- the own claim must survive compaction too (ADR-0008 open point (c)).
  let (ownClaimStamp, actor) ← claims.foldl (fun acc c =>
    match acc with
    | none => some c
    | some m => some (if Tl.Crdt.TotalOrd.le m.1 c.1 then c else m)) none
  let d := v.state.issueData i
  let current := d.assignee.value.getD none
  let won := match d.assignee with
    | some (t, _) => claimWonB d t actor
    | none => false
  let outcome : ClaimOutcome :=
    if won then .won
    else
      -- contention analysis — reached only when NOT won (the common path
      -- returns immediately, so the scans below never run on it).
      -- A register winner cannot carry contest history: a claimant's own later
      -- close/reopen buries a *foreign* status/assignee write, so scan the op
      -- log directly for one above the surfaced own claim the claimant did not
      -- author — exactly `!opAuthoredByOwn` (the authorship predicate negated).
      -- The registers a claim needs are `status` and `assignee`; the ops that
      -- write either are `create` (status seed), `claim`/steal (both), `close`
      -- (status), and `reopen` (both, incl. the assignee clear) — NOT
      -- update/defer/meta/edge/label. Matching all of them (not just `claim`)
      -- catches a foreign close or reopen that superseded the claim and was
      -- then buried under the claimant's own later reopen/close.
      --
      -- NB: this hand-enumerates the "writes status or assignee" op set whose
      -- source of truth is `WireOp.toOp` + `stripLifecycle` (Tl/Format/Codec.lean).
      -- If a new op writes `status` or `assignee` there, add its constructor
      -- here, or a foreign one of it will silently escape the contest scan and
      -- mask a lost race (mirrors the `updatedAtStamp` NB, Tl/Kernel/State.lean).
      --
      -- NB (compaction, deferred — ADR-0008 open point (c)): this scan sees the
      -- race-masking foreign op only by its physical presence in `v.loaded.ops`.
      -- Once `tl compact` can trim ops, dropping a dominated foreign
      -- status/assignee write (any of the create/claim/close/reopen enumerated
      -- above) while a later burying own reopen/close survives would flip this
      -- `superseded` to a false `ended`. The frontier must retain such an op, or
      -- this scan must gain a materialized contest backstop that survives
      -- compaction; ADR-0008 open point (c) pins the required shape. Not
      -- reachable today (compaction unshipped).
      let contested := v.loaded.ops.any (fun p =>
        let touchesThis := match p.op with
          | .create ci _ | .claim ci _ | .close ci _ | .reopen ci => ci == i
          | _ => false
        touchesThis && decide (Tl.Crdt.TotalOrd.lt ownClaimStamp p.stamp)
          && !opAuthoredByOwn actor p)
      let statusOwn := match d.status with
        | some (t, _) => stampAuthoredByOwn v.loaded.ops actor t
        | none => false
      let assigneeHeld := match d.assignee with
        | some (_, some a) => a == actor
        | some (t, none) => stampAuthoredByOwn v.loaded.ops actor t
        | none => false
      if !contested && statusOwn && assigneeHeld then .ended else .superseded
  some (outcome, current)

def cmdShow (dirOverride : Option String) (tok : String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let base := issueObj v i
  let verdict := claimVerdict v i
  let data := match verdict with
    | some (outcome, current) => base.setObjVal! "claim" (Json.mkObj
        [("outcome", Json.str outcome.wire),
         ("currentAssignee", current.elim Json.null (Json.str ∘ sanitizeSingle))])
    | none => base
  let r : Style → String := fun st => styledShow st v i (verdict.map (·.1))
  return { data, human := r Style.plain, render := some r, notes }

def cmdWhy (dirOverride : Option String) (tok : String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let s := v.state
  let d := s.issueData i
  if State.isReadyWith v.rollup s v.now i then
    return { data := Json.mkObj [("id", Json.str (displayId i)), ("ready", Json.bool true)]
             human := s!"{displayId i} is ready", notes }
  -- fuel = |presentIssues|; reuse the view's hoisted scan (one present pass, not redone here)
  let trans := State.whyFastH v.idx.btgt v.idx.presentH v.idx.rollupH s v.present.length i
  -- a node's children in the why-tree are its LIVE direct blockers (present and
  -- not effectively-closed) — the same liveSuccE relation whyFast's transitive
  -- closure is built from, so the tree's node set equals `trans` (the JSON set),
  -- just with the clear-this-first order, diamonds, and depth made visible.
  -- Every read indexed (btgt bucket + hashed discharge, like `View.blocked`), so
  -- the per-node tree descent stays O(deg) — never an O(E) edge rescan per node.
  let liveBlockers : IssueId → List IssueId := fun x =>
    (v.blockers x).filter (fun b =>
      !State.blockerDischargedH v.idx.presentH v.idx.rollupH v.state b)
  let direct := liveBlockers i
  let rows := trans.map (fun b =>
    let bd := s.issueData b
    Json.mkObj <|
      [("id", Json.str (displayId b)),
       ("status", Json.str (statusWire bd.statusOf)),
       ("effectiveStatus", Json.str (statusWire (State.effStatusWith v.rollup s b))),
       ("direct", Json.bool (direct.contains b))]
      ++ (match bd.title.value with
          | some t => [("title", Json.str (sanitizeSingle t))]
          | none => []))
  let data := Json.mkObj <|
    [("id", Json.str (displayId i)), ("ready", Json.bool false),
     ("status", Json.str (statusWire d.statusOf)),
     ("isEpic", Json.bool (s.isEpic i))]
    ++ (if rows.isEmpty then [] else [("blockedBy", Json.arr rows.toArray)])
    ++ (match d.deferUntilOf with
        | some t => if v.now < t then [("deferUntil", Json.str (Time.isoOfEpochMs t))] else []
        | none => [])
  -- human: the blocker chain as a tree (ADR-0017 §2) — single-rooted at `i`'s
  -- direct live blockers, each expanded over the same liveBlockers accessor;
  -- cycles render "↺", shared blockers render once and mark re-encounters.
  -- JSON stays the flat blockedBy refs above (agents don't read the tree).
  let r : Style → String := fun st =>
    if trans.isEmpty then s!"{displayId i} is not ready (no open blockers — check status/epic/defer)"
    else s!"{displayId i} waits on:\n" ++
      String.intercalate "\n" (treeForest st v direct (fun _ => true) liveBlockers)
  return { data, human := r Style.plain, render := some r, notes }

/-- `unblocks <id>` — the downward mirror of `why`: the issues that would
    become ready if `<id>` closed (the proved ready-diff `unblocksFast`,
    ADR-0004 thm 10). A dependent still pinned by another blocker is not freed
    and so does not appear. -/
def cmdUnblocks (dirOverride : Option String) (tok : String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let s := v.state
  let freed := State.unblocksFast s v.now i
  let rows := freed.map (fun b =>
    let bd := s.issueData b
    Json.mkObj <|
      [("id", Json.str (displayId b)),
       ("status", Json.str (statusWire bd.statusOf)),
       ("effectiveStatus", Json.str (statusWire (State.effStatusWith v.rollup s b)))]
      ++ (match bd.title.value with
          | some t => [("title", Json.str (sanitizeSingle t))]
          | none => []))
  let data := Json.mkObj
    [("id", Json.str (displayId i)),
     ("freed", Json.arr rows.toArray),
     ("count", jnum freed.length)]
  let human :=
    if freed.isEmpty then s!"closing {displayId i} would free nothing right now (no dependent becomes ready)"
    else s!"closing {displayId i} unblocks:\n" ++
      String.intercalate "\n" (freed.map (fun b => "  " ++ issueLine v b))
  return { data, human, notes }

def cmdDepCycles (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let s := v.state
  let entry (kind : String) (issues : List IssueId) : Json :=
    Json.mkObj [("kind", Json.str kind),
                ("issues", Json.arr (issues.map (Json.str ∘ displayId)).toArray)]
  -- each diagnostic computed exactly once per invocation (the fast forms,
  -- bridged to the spec by cyclesFast_eq/precCyclesFast_eq), and over the
  -- view's pre-hoisted present/edges/pedges so the present scans aren't
  -- redone per graph (cyclesFastWith/precCyclesFastWith)
  let blocksCycles := State.cyclesFastWith v.present v.edges EdgeKind.Blocks
  let parentCycles := State.cyclesFastWith v.present v.edges EdgeKind.Parent
  let structural := blocksCycles ++ parentCycles
  -- a ≺-cycle whose node set coincides with a structural witness is already
  -- diagnosed by that row; only genuinely mixed deadlocks add a readiness row
  let readiness := (State.precCyclesFastWith v.rollup v.present v.edges v.pedges s).filter
    (fun w => !structural.contains w)
  let rows := blocksCycles.map (entry "blocks")
    ++ parentCycles.map (entry "parent")
    ++ readiness.map (entry "readiness")
  -- the repair verb differs by kind: blocks edges are retracted with
  -- `dep remove`, parent edges with `parent remove`/`parent set`. A witness
  -- contributes the kinds of its *own* cycle relation, not of every present
  -- edge whose endpoints happen to sit inside it — an incidental edge of the
  -- other kind between two members is not part of the reported cycle, and
  -- removing it cannot break that cycle. Structural witnesses carry their
  -- kind by construction (their label); a readiness witness (pure-blocks or
  -- mixed, `precCycles`) contributes a kind only where a *live* ≺-step of
  -- that kind connects two of its members (`liveBlockersSucc` /
  -- `liveChildrenSucc`, probed through the view's hoisted rollup) — every
  -- ≺-step is one of the two kinds and a cyclic ≺-SCC steps inside itself,
  -- so a readiness witness always contributes a kind. The probe runs only
  -- when a readiness row exists; structural-only reports pay nothing.
  let human :=
    if rows.isEmpty then "no cycles"
    else
      let readinessStep (succ : IssueId → List IssueId) : Bool :=
        readiness.any (fun w => w.any (fun i => (succ i).any (fun j => w.contains j)))
      let occursBlocks := !blocksCycles.isEmpty
        || readinessStep (fun i => State.liveSuccE v.rollup v.edges s i)
      let occursParent := !parentCycles.isEmpty
        || readinessStep (fun i =>
            (State.kidsOfEdges v.pedges i).filter
              (fun c => !State.effClosedWith v.rollup s c))
      let hint :=
        match occursBlocks, occursParent with
        | true, false => "break each with `tl dep remove`"
        | false, true => "break each with `tl parent remove` (or move a member with `tl parent set`)"
        | _, _ => "break blocks edges with `tl dep remove` and parent edges with `tl parent remove` (or `tl parent set`)"
      s!"{rows.length} cycle(s) — {hint}"
  return { data := listPayload "cycles" rows.length rows
           human
           notes }

/-- The cycle count (structural per kind + the non-duplicate readiness
    deadlocks), shared with `doctor`'s graph check. Reads the view's
    pre-hoisted present/edges/pedges (one scan total, not three). -/
private def cycleCount (v : View) : Nat :=
  let s := v.state
  let structural := State.cyclesFastWith v.present v.edges EdgeKind.Blocks
    ++ State.cyclesFastWith v.present v.edges EdgeKind.Parent
  structural.length
    + ((State.precCyclesFastWith v.rollup v.present v.edges v.pedges s).filter
        (fun w => !structural.contains w)).length

def cmdStats (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let s := v.state
  let issues := v.present
  let byEff (st : Status) : Nat := (issues.filter (fun i => v.effStatus i == st)).length
  let ready := (State.readyFast v.rollup s v.now).length
  let blocked := (issues.filter v.blocked).length
  let deferred := (issues.filter v.deferred).length
  let cycles := cycleCount v
  -- count effective status (rollup-aware): a rolled-up epic counts as done,
  -- exactly as `list`/the glyphs render it — never the raw stored field, which
  -- would report a finished epic as still "open" and disagree with `list`
  -- (ADR-0020 §stats). `open` is split into epics vs tasks so a
  -- stored-open-but-rolled-up epic is never miscounted as workable.
  let openIssues := issues.filter (fun i => v.effStatus i == .Open)
  let openN := openIssues.length
  let openEpics := (openIssues.filter v.isEpic).length
  let openTasks := openN - openEpics
  let inProg := byEff .InProgress
  let doneN := byEff .Done
  let cancelledN := byEff .Cancelled
  let data := Json.mkObj
    [("total", jnum issues.length),
     ("open", jnum openN), ("openEpics", jnum openEpics), ("openTasks", jnum openTasks),
     ("inProgress", jnum inProg), ("done", jnum doneN), ("cancelled", jnum cancelledN),
     ("ready", jnum ready), ("blocked", jnum blocked),
     ("deferred", jnum deferred), ("cycles", jnum cycles)]
  let plural := fun (n : Nat) (w : String) => toString n ++ " " ++ w ++ (if n == 1 then "" else "s")
  let openBreak := plural openEpics "epic" ++ " · " ++ plural openTasks "task"
  -- a small labelled block (§5); §7: green marks the workable (ready) count, so
  -- the open row renders neutral and the derived ready count takes green
  let r : Style → String := fun st =>
    let c (ds : DState) (n : Nat) : String := st.paint ds.colorCode s!"{ds.word} {n}"
    s!"{issues.length} issues\n"
      ++ "  " ++ String.intercalate " · " [s!"open {openN} ({openBreak})", c .inProgress inProg, c .done doneN, c .cancelled cancelledN] ++ "\n"
      ++ "  " ++ String.intercalate " · "
           [st.paint DState.ready.colorCode s!"ready {ready}", c .blocked blocked, c .deferred deferred,
            (if cycles > 0 then st.paint "31" s!"cycles {cycles}" else s!"cycles {cycles}")]
  return { data, human := r Style.plain, render := some r, notes }

/-- The issue ids an op touches (for `tl log`'s per-issue filter and the
    entry's `targets`): the subject for scalar/meta/label ops, both endpoints
    for edge ops. -/
private def opTargets : WireOp → List IssueId
  | .create id _ | .update id _ | .claim id _ | .close id _ | .reopen id
  | .defer id _ | .undefer id | .metaSet id _ _
  | .labelAdd id _ | .labelRemove id _ _
  | .noteAdd id _ _ | .noteRemove id _ _ => [id]
  | .depAdd (f, t, _) | .relate (f, t, _)
  | .depRemove (f, t, _) _ | .unrelate (f, t, _) _ => [f, t]

/-- A resumable change-feed cursor (ADR-0025): for each replica (decoded id) the
    highest `(HLC, nonce)` already delivered. The log's intra-replica order is
    `(HLC, nonce)` — two ops can share an HLC and are separated by the nonce
    (ADR-0007) — so the cursor tracks both. An op is emitted iff its `(HLC, nonce)`
    exceeds its replica's threshold. A scalar high-water mark drops a late op below
    another replica's max; a per-replica HLC-only frontier drops a same-HLC tie;
    this drops neither. -/
private abbrev LogCursor := AMap Nat (Nat × Nat)

/-- A replica's threshold, or `none` when it was never delivered. An absent
    threshold is below everything — including a `(0, 0)` stamp — so an empty cursor
    is the full history, not "everything strictly above `(0, 0)`". -/
private def cursorThreshold (c : LogCursor) (replica : Nat) : Option (Nat × Nat) :=
  c.find replica

/-- An op's `(HLC, nonce)` is strictly after a threshold (lexicographic); an
    absent threshold (`none`) is below everything. -/
private def stampAfter (hlc nonce : Nat) (thr : Option (Nat × Nat)) : Bool :=
  match thr with
  | none => true
  | some (th, tn) => Nat.blt th hlc || (th == hlc && Nat.blt tn nonce)

/-- The greater of `(hlc, nonce)` and a threshold. -/
private def maxStamp (hlc nonce : Nat) (thr : Option (Nat × Nat)) : Nat × Nat :=
  if stampAfter hlc nonce thr then (hlc, nonce) else thr.getD (hlc, nonce)

/-- Fold ops into a cursor, keeping the per-replica maximum `(HLC, nonce)`. -/
private def advanceCursor (base : LogCursor) (ops : List ParsedOp) : LogCursor :=
  ops.foldl (fun m p =>
    m.insert p.stamp.replica (maxStamp p.stamp.hlc p.stamp.nonce (cursorThreshold m p.stamp.replica))) base

/-- An op's `(HLC, nonce)` is strictly before a threshold (lexicographic); an
    absent threshold (`none`) is *above* everything — the dual of `stampAfter`.
    For `--until` (backward) a replica with no recorded edge is unconstrained, so
    all of its ops are candidates, exactly as an empty cursor is full history. -/
private def stampBefore (hlc nonce : Nat) (thr : Option (Nat × Nat)) : Bool :=
  match thr with
  | none => true
  | some (th, tn) => Nat.blt hlc th || (hlc == th && Nat.blt nonce tn)

/-- The lesser of `(hlc, nonce)` and a threshold. -/
private def minStamp (hlc nonce : Nat) (thr : Option (Nat × Nat)) : Nat × Nat :=
  if stampBefore hlc nonce thr then (hlc, nonce) else thr.getD (hlc, nonce)

/-- Fold ops into a cursor, keeping the per-replica *minimum* `(HLC, nonce)` — the
    frontier just below the oldest delivered op (`min` is order-independent, so the
    page list may be in either sort order). Emitting `(hlc, nonce) < this` (per
    replica) yields the ops older than the page's oldest delivered op, and a replica
    absent from the page (unconstrained, `none`) keeps all its ops as candidates.
    In a newest-first page (plain / `--until`) the page is a top-suffix of the total
    order, so "older than the oldest delivered" is exactly the not-yet-shown
    remainder — backward paging is gap-free. In an oldest-first `--since` page the
    delivered slice is a bottom-prefix of the delta, so this edge points below the
    feed's oldest op (into pre-feed history); the *forward* remainder of a `--since`
    feed is reached by `cursor.since`, not this edge. The dual of `advanceCursor`. -/
private def retreatCursor (base : LogCursor) (ops : List ParsedOp) : LogCursor :=
  ops.foldl (fun m p =>
    m.insert p.stamp.replica (minStamp p.stamp.hlc p.stamp.nonce (cursorThreshold m p.stamp.replica))) base

/-- Serialize a cursor as comma-joined `<replica>:<hlc>:<nonce>` triples, the
    replica in its canonical 13-char Crockford form, sorted by replica
    (`AMap.toList`). -/
private def renderCursor (c : LogCursor) : String :=
  String.intercalate "," (c.toList.map (fun (r, hn) => s!"{toCrockford r 13}:{hn.1}:{hn.2}"))

/-- Parse a `--since`/`--until` cursor (`edge` is the flag/object field name,
    `"since"` or `"until"`): comma-joined `<replica>:<hlc>:<nonce>` triples (the
    matching edge of a prior `tl log`'s `cursor` object). A trimmed-empty token is
    the empty cursor (full history); anything else is validated as strictly as the
    wire decoder (`decodeStamp`) — an empty/extra `:`-segment, a stray comma, a
    non-canonical or `≥ 2^64` replica, an hlc `≥ 2^64` or nonce `≥ 2^128`, or a
    non-numeric hlc/nonce is a usage error that names the expected shape, never a
    silent full dump. -/
private def parseCursor (edge : String) (s : String) : Except Tl.Error LogCursor := do
  let t := s.trimAscii.toString
  if t.isEmpty then return AMap.empty
  let mut c : LogCursor := AMap.empty
  for piece in t.splitOn "," do
    match piece.splitOn ":" with
    | [rid, hstr, nstr] =>
      let ridT := rid.trimAscii.toString
      match ofCrockford? ridT, hstr.trimAscii.toString.toNat?, nstr.trimAscii.toString.toNat? with
      | some r, some h, some n =>
        -- mirror `decodeStamp`: a canonical 13-char Crockford replica below 2^64,
        -- the hlc below 2^64, the nonce below 2^128
        let okReplica := ridT.length == 13 && toCrockford r 13 == ridT && decide (r < 2 ^ 64)
        let okStamp := decide (h < 2 ^ 64) && decide (n < 2 ^ 128)
        if okReplica && okStamp then
          -- a self-produced cursor has one triple per replica (`renderCursor`),
          -- but a hand-edited one may repeat a replica; collapse to the most
          -- conservative bound — the tightest that never over-emits: the maximum
          -- for a lower bound (`since`), the minimum for an upper bound (`until`).
          let folded := if edge == "until" then minStamp h n (cursorThreshold c r)
                        else maxStamp h n (cursorThreshold c r)
          c := c.insert r folded
        else if !okReplica then
          throw (.mk' .usage
            s!"--{edge}: '{ridT}' is not a canonical 13-char replica id below 2^64 — pass the `cursor.{edge}` from a prior `tl log --json`")
        else
          throw (.mk' .usage
            s!"--{edge}: '{piece}' has an out-of-range hlc or nonce (hlc < 2^64, nonce < 2^128) — pass the `cursor.{edge}` from a prior `tl log --json`")
      | _, _, _ => throw (.mk' .usage
          s!"--{edge}: bad cursor segment '{piece}' (expected <replica>:<hlc>:<nonce>) — pass the `cursor.{edge}` from a prior `tl log --json`")
    | _ => throw (.mk' .usage
        s!"--{edge}: bad cursor segment '{piece}' (expected <replica>:<hlc>:<nonce>) — pass the `cursor.{edge}` from a prior `tl log --json`")
  return c

/-- A resolved `--since`/`--until` bound: either the exact per-replica version
    vector (`cursor`, the resumable machine form) or a wall-clock instant in ms
    (`timeMs`, the best-effort human form — compared against an op's HLC physical
    component). ADR-0025: the cursor is exact/resumable, a time is skew-sensitive. -/
private inductive LogBound where
  | cursor (c : LogCursor)
  | timeMs (ms : Nat)

private def boundFormHelp (edge got : String) : Tl.Error :=
  .mk' .usage
    s!"--{edge}: '{got}' is not a recognized bound — use a duration ago (1h, 7d), a date (2026-06-20), a timestamp (…Z or ±HH:MM), `all` (from the start), or the `cursor.{edge}` from a prior `tl log --json`"

/-- Resolve a `--since`/`--until` value by shape (ADR-0025 shared time grammar):
    empty or `all` ⇒ unbounded (the empty cursor); a duration ⇒ that long *ago*
    (`now − dur`, shared with `defer`, ADR-0010); a date ⇒ local start-of-day; a
    timestamp with an offset ⇒ that instant; otherwise a version-vector cursor
    (its own strict validation). A cursor-shaped token routes to the cursor parser
    for its detailed errors; anything else teaches the full set of forms. The
    date/timestamp resolution is exactly `defer`'s `parseUntilInstant?` — not a
    second parser. -/
private def parseLogBound (edge : String) (now : Nat) (offset : Int) (raw : String) :
    Except Tl.Error LogBound :=
  let t := raw.trimAscii.toString
  if t.isEmpty || t.toLower == "all" then .ok (.cursor AMap.empty)
  else match Time.parseDurationMs? t with
    -- a duration is "ago"; an over-large `--since` ago saturates `now - ms` to the
    -- epoch — "since before any op" = full history — and the dual over-large
    -- `--until` floors to 0 and matches nothing. Both are the intended limit.
    | some ms => .ok (.timeMs (now - ms))
    | none => match Time.parseUntilInstant? offset t with
      | some inst => .ok (.timeMs inst)
      | none =>
        -- route to the cursor parser only for a cursor-shaped token: a version
        -- vector is `:`-separated and never contains '-' (Crockford), whereas a
        -- malformed date/timestamp does — so the latter gets the form help, not a
        -- misleading "bad cursor segment" (review).
        if t.contains ':' && !t.contains '-' then LogBound.cursor <$> parseCursor edge t
        else .error (boundFormHelp edge t)

/-- `tl log [<id>] [--since <cursor>] [--until <cursor>]`: an HLC-ordered
    projection over the op log (ADR-0008), optionally filtered to ops touching one
    issue. Without bounds it lists newest-first (capped by `--limit`). `--since` is
    a resumable forward change-feed — every op after the lower cursor, oldest-first,
    exactly-once. `--until` browses history backward — every op before the upper
    cursor, newest-first, best-effort (a still-merging log can gain an op below a
    page already passed, ADR-0025). Given both, the bounds compose into a window.
    Every response carries a dual-edge `cursor` object `{ since, until }` (field
    names match the flags) so each page is self-navigating: pass `cursor.since` to
    `--since` to continue forward, `cursor.until` to `--until` to page older. The
    cursor is scoped to the `<id>` filter it was produced under: resume with the
    same filter.

    Each bound also accepts a *time* instead of a cursor (ADR-0025): a duration
    ago (`1h`, `7d`), a date (`2026-06-20`, local start-of-day), a timestamp
    (`…Z`/`±HH:MM`), or `all` (from the start). A time bound is best-effort over
    the op's HLC physical-ms component (skew-sensitive), inclusive on both edges
    — `--since` keeps ops at/after it, `--until` ops at/before it; the resumable
    `cursor` is still emitted from the delivered page. `--last N` is a count tail
    (the newest N, newest-first) and is mutually exclusive with `--limit`. -/
def cmdLog (dirOverride : Option String) (idTok : Option String) (limit : Nat)
    (lastN : Option Nat) (since untilC : Option String) (skipBad : Bool) : TlM CmdOut := do
  let sinceGiven := since.isSome
  let untilGiven := untilC.isSome
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  -- the injected UTC offset is needed only to resolve a bare-date bound to local
  -- start-of-day; read it (best-effort) only when a bound is in fact a bare date
  let isBareDate (o : Option String) : Bool :=
    (o.map (fun s => (Time.parseCivilDate? s.trimAscii.toString).isSome)).getD false
  let offset : Int ← if isBareDate since || isBareDate untilC then
      liftSys (fun e => .mk' .internal s!"timezone read failed: {e}") localOffsetMinutes
    else pure 0
  -- resolve each bound by shape (cursor vs duration/date/timestamp vs `all`)
  let sinceBound ← MonadExcept.ofExcept (parseLogBound "since" v.now offset (since.getD ""))
  let untilBound ← MonadExcept.ofExcept (parseLogBound "until" v.now offset (untilC.getD ""))
  let visible ← match idTok with
    | none => pure v.loaded.ops
    | some tok =>
      let i ← MonadExcept.ofExcept (resolveToken v.state tok)
      pure (v.loaded.ops.filter (fun p => (opTargets p.op).contains i))
  -- `--since` keeps ops after its lower bound, `--until` before its upper bound;
  -- together a window. A cursor bound is per-replica (HLC, nonce) (exact); a time
  -- bound compares the op's wall-clock instant — the HLC physical component
  -- (ADR-0007 packing), computed once per op — inclusive. Absent flag = no bound.
  let okSince (p : ParsedOp) (phys : Nat) : Bool := match sinceBound with
    | .cursor c => stampAfter p.stamp.hlc p.stamp.nonce (cursorThreshold c p.stamp.replica)
    | .timeMs t => decide (t ≤ phys)
  let okUntil (p : ParsedOp) (phys : Nat) : Bool := match untilBound with
    | .cursor c => stampBefore p.stamp.hlc p.stamp.nonce (cursorThreshold c p.stamp.replica)
    | .timeMs t => decide (phys ≤ t)
  let matching := visible.filter (fun p =>
    let phys := p.stamp.hlc / 2 ^ 16
    (!sinceGiven || okSince p phys) && (!untilGiven || okUntil p phys))
  -- `--since` (no `--last`) is a forward feed (oldest-first); plain log, `--until`,
  -- and any `--last` tail read newest-first. Both use the full stamp order
  -- (deterministic on equal HLCs).
  let newestFirst := lastN.isSome || !sinceGiven
  let ordered :=
    if newestFirst then matching.mergeSort (fun a b => decide (Tl.Crdt.TotalOrd.le b.stamp a.stamp))
    else matching.mergeSort (fun a b => decide (Tl.Crdt.TotalOrd.le a.stamp b.stamp))
  let effLimit := lastN.getD limit
  let capped := if effLimit == 0 then ordered else ordered.take effLimit
  -- Resume-forward (since) edge: in since-mode the lower cursor raised by the
  -- delivered (capped) page, so a paged resume never skips/replays; otherwise the
  -- full frontier of the visible log (a point to tail from the newest). Resume-back
  -- (until) edge: the per-replica minimum of the delivered page — the frontier just
  -- below the oldest delivered op — so `--until` pages strictly older. Both edges
  -- always bracket the *delivered* page, so no op is lost: in a `--since` feed the
  -- forward remainder is reached by `cursor.since` (the until edge then points into
  -- pre-feed history, and a one-op page makes the two edges coincide — expected,
  -- not a skip; see `cliLogUntilTests` (windowed forward + limit)).
  -- a time bound has no input version-vector base. For `--since` seed the base
  -- with the frontier of the ops BELOW the since-time (the history the time filter
  -- skipped), so resuming the returned `cursor.since` continues from the query
  -- point instead of replaying that already-skipped history (review). A time-based
  -- `--until` is best-effort backward browsing (ADR-0025), so its base stays empty
  -- (its resume-back edge is the delivered page's min frontier).
  let sinceBase := match sinceBound with
    | .cursor c => c
    | .timeMs t => advanceCursor AMap.empty (visible.filter (fun p => p.stamp.hlc / 2 ^ 16 < t))
  let untilBase := match untilBound with | .cursor c => c | .timeMs _ => AMap.empty
  let sinceEdge := if sinceGiven then advanceCursor sinceBase capped else advanceCursor AMap.empty visible
  -- accumulate from the input upper bound, not from empty: a replica bounded by a
  -- prior backward page must stay bounded, or paging further back re-delivers its
  -- already-seen ops (a replica absent from this page would otherwise reset to
  -- unconstrained). The dual of `advanceCursor sinceBase` for the forward feed.
  let untilEdge := retreatCursor untilBase capped
  let entry (p : ParsedOp) : Json :=
    Json.mkObj
      [("timestamp", Json.str (hlcIso p.stamp.hlc)),
       ("op", Json.str p.op.wire),
       ("actor", p.actor.elim Json.null (Json.str ∘ sanitizeSingle)),
       ("targets", Json.arr ((opTargets p.op).map (Json.str ∘ displayId)).toArray)]
  -- the human line shows each target's current title (ADR-0025): read through the
  -- O(1) indexed view (ADR-0024 `View.issueData`, not an O(N) per-op find),
  -- sanitized (attacker-controllable, ADR-0014) and truncated. A dangling or
  -- untitled target falls back to the bare id. The `--json` entry above stays
  -- id-keyed with no title (a deliberate human/json divergence, ADR-0025): the
  -- feed is an immutable op stream, the title is mutable state derived from the id.
  let titleSuffix (i : IssueId) : String :=
    match (v.issueData i).title.value with
    | none => ""
    | some raw =>
      let s := sanitizeSingle raw
      -- a title that sanitizes to nothing (all control/zero-width bytes) renders as
      -- the bare id too, not a dangling trailing space
      if s.isEmpty then ""
      else " " ++ (if s.length > 48 then String.ofList (s.toList.take 48) ++ "…" else s)
  let line (p : ParsedOp) : String :=
    -- actor is attacker-controllable (ADR-0014 T1) — sanitize for the human terminal,
    -- mirroring the `--json` arm above (titles/labels/meta all wrap it too)
    s!"{hlcIso p.stamp.hlc}  {p.op.wire}  {(p.actor.elim "—" sanitizeSingle)}  " ++
      String.intercalate ", " ((opTargets p.op).map (fun t => displayId t ++ titleSuffix t))
  let sinceStr := renderCursor sinceEdge
  let untilStr := renderCursor untilEdge
  -- newest-first pages (plain/`--until`/`--last`) overflow into "older"; the
  -- forward feed (`--since` without `--last`) overflows into "more".
  let overflowMore := if newestFirst then "older" else "more"
  let limitHint := if lastN.isSome then "raise --last" else "--limit 0 for all"
  let body :=
    if matching.isEmpty then "no ops"
    else String.intercalate "\n" (capped.map line)
      ++ (if capped.length < matching.length then
            s!"\n… {matching.length - capped.length} {overflowMore} ({limitHint})" else "")
  let cursorParts := (if sinceStr.isEmpty then [] else [s!"since={sinceStr}"])
                   ++ (if untilStr.isEmpty then [] else [s!"until={untilStr}"])
  return { data := Json.mkObj [("count", jnum matching.length),
                               ("entries", Json.arr (capped.map entry).toArray),
                               ("cursor", Json.mkObj [("since", Json.str sinceStr),
                                                      ("until", Json.str untilStr)])]
           human := body ++ (if cursorParts.isEmpty then ""
                             else "\ncursor: " ++ String.intercalate " " cursorParts)
           notes }

/-! ## Write verbs -/

private def writeNow (v : TxContext) (parsed : List ParsedOp) : View :=
  postView v parsed v.now

def cmdCreate (dirOverride : Option String) (title : String) (priority : Option Nat)
    (description slug : Option String) (actor : String)
    (blockedBy blocks parents related : List String) : TlM CmdOut := do
  let edgeCount := blockedBy.length + blocks.length + parents.length + related.length
  let prio : Option (Fin 5) := priority.map (fun p => ⟨min p 4, Nat.lt_succ_of_le (Nat.min_le_right p 4)⟩)
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor)
    (1 + edgeCount) (fun ctx stamps => do
      let some st := stamps.head? | .error (.mk' .internal "no stamp")
      let id := mintIssueId st
      let resolveAll (toks : List String) : Except Tl.Error (List IssueId) :=
        toks.mapM (resolveToken ctx.loaded.state)
      let bby ← resolveAll blockedBy
      let bls ← resolveAll blocks
      let pars ← resolveAll parents
      let rels ← resolveAll related
      let edgeOps : List WireOp :=
        bby.map (fun b => .depAdd (b, id, EdgeKind.Blocks))
        ++ bls.map (fun c => .depAdd (id, c, EdgeKind.Blocks))
        ++ pars.map (fun e => .depAdd (e, id, EdgeKind.Parent))
        ++ rels.map (fun r =>
            .relate (if decide (id ≤ r) then (id, r, EdgeKind.Related)
                     else (r, id, EdgeKind.Related)))
      .ok (WireOp.create id
        { title := some title, priority := prio, description := description.map some, slug := slug.map some }
        :: edgeOps))
  let v := writeNow ctx parsed
  let some newId := parsed.head?.bind (fun p =>
      match p.op with | .create i _ => some i | _ => none)
    | throw (.mk' .internal "create wrote no create record")
  return { data := issueObj v newId
           human := s!"Created {displayId newId}  {sanitizeSingle title}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- After a durable claim, re-derive the echo from the freshly-synced state via
    `reload`; if that reload fails (a transient FS / clock-read error), fall back to
    the post-write `fallback` view with a disclosure note — a durable claim must
    never report failure (an exit-code-branching agent would spuriously retry into a
    second claim). Extracted so the fallback branch is unit-testable without
    injecting a real FS failure. -/
def reloadOrFallback (reload : TlM View) (fallback : View) (i : IssueId) :
    TlM (View × List String) :=
  try (do let vf ← reload; pure (vf, ([] : List String)))
  catch e =>
    pure (fallback, [s!"the claim is recorded but the post-sync reload failed ({e.message}); this echo reflects local state — re-read with `tl show {displayId i}`"])

/-- The `claim` partial-survival explanation: the assignee write held but the
    status write lost. Worded from the ACTUAL winning status so it can never
    contradict itself: when that winner is itself `in_progress` (a concurrent
    equivalent write — e.g. a status-carrying imported or crafted `create`
    outstamping the claim), there is nothing to repair and the line says so,
    instead of the impossible "the issue is in_progress, not in_progress".
    Extracted so each status branch is unit-testable without staging the rare
    concurrent fold that reaches it through the command. -/
def partialClaimMessage (i : IssueId) (actor : String) (st : Status) : String :=
  if st == .InProgress then
    s!"claim of {displayId i} was superseded — {sanitizeSingle actor} still holds the assignee and the issue is already in_progress: this claim's own status write lost to a concurrent equivalent one; no action needed unless `tl log {displayId i}` shows a writer you don't expect"
  else
    s!"claim of {displayId i} was superseded — {sanitizeSingle actor} still holds the assignee, but a concurrent write outstamped the status: the issue is {statusWire st}, not in_progress; run `tl show {displayId i}` to inspect, then reopen or re-claim if the work is still intended"

def cmdClaim (dirOverride : Option String) (tok : String) (actor : String)
    (sync verify steal : Bool) (staleArg : Option String) : TlM CmdOut := do
  -- `--stale` only sets the window for `--steal`; alone it is a usage error so a
  -- typo (`--stale 1h` without `--steal`) never silently does a plain claim.
  if staleArg.isSome && !steal then
    throw (.mk' .usage "--stale sets the staleness window for --steal — pass --steal too, or drop --stale")
  -- freshness preflight (ADR-0001 §5): with --sync/--verify, reconcile against
  -- the remote before the take, so the not-claimable check sees the freshest
  -- reachable state. --verify warns-and-degrades when no remote is configured
  -- (it still checks against the freshest local state, via preWriteRefresh below).
  let preNotes ← if sync || verify then do
      let d0 ← discover dirOverride
      let hasRemote := (← Tl.Sync.resolveRemote d0).isSome
      -- --verify is a gate: a configured-but-unreachable remote fails the claim
      -- (verify-failed) so a take is never made against unverified state; with no
      -- remote it degrades (claiming locally is fine). --sync alone is best-effort:
      -- a reconcile failure degrades with a note, never blocking the take.
      (try
        let (_, _, pn) ← performSync d0
        if verify && !hasRemote then
          pure ("verified against local state only — no remote is configured to fetch from" :: pn)
        else pure pn
       catch e =>
        if verify then
          throw (.mk' .verifyFailed
            s!"could not verify against the remote ({e.message}) — retry when it is reachable, or run `tl claim` without --verify to take against local state")
        else
          pure [s!"claimed against local state — could not reconcile with the remote first ({e.message}); run `tl sync`"])
    else pure []
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  -- the staleness window for --steal: inline --stale wins over tl.staleAfter.
  -- Inline (explicit input) fails fast on a bad value; the config is LENIENT — a
  -- malformed tl.staleAfter never blocks a plain/ready/own claim (only the
  -- take-over-someone-else path needs a window, and it reports the bad config
  -- there). No --steal ⇒ no read, no window.
  let inlineMs : Option Nat ← match staleArg with
    | none => pure none
    | some raw =>
      match Time.parseDurationMs? raw with
      | some w => pure (some w)
      | none => throw (.mk' .usage s!"--stale: '{sanitizeSingle raw}' is not a valid duration — use e.g. 45m, 1h, 24h")
  let cfgRaw ← if steal && staleArg.isNone then Tl.Sync.gitConfig d "tl.staleAfter" else pure none
  let cfgMs : Option Nat := cfgRaw.bind Time.parseDurationMs?
  -- a set-but-unparseable config: surfaced only on the take-over path that needs it
  let cfgBadMsg : Option String := match cfgRaw with
    | some raw => if cfgMs.isNone then
        some s!"git config tl.staleAfter='{sanitizeSingle raw}' is not a valid duration — fix it or pass --stale" else none
    | none => none
  let thresholdMs : Option Nat := inlineMs.orElse (fun _ => cfgMs)
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    let rm := s.effStatusAll
    let dta := s.issueData i
    let direct := (s.blockersOf i).filter (fun b => !State.blockerDischargedWith rm s b)
    let claimedBy := dta.assignee.value.getD none
    let deferActive := match dta.deferUntilOf with | some t => ctx.now < t | none => false
    -- `--steal` overrides ONLY an existing claim (in_progress + assigned) on an
    -- otherwise-workable item (not epic/deferred/blocked).
    let onlyClaimObstacle := dta.statusOf == .InProgress && claimedBy.isSome
      && !s.isEpic i && !deferActive && direct.isEmpty
    let holder := (claimedBy.map sanitizeSingle).getD "someone"
    let reasons := Json.mkObj <|
      (if dta.statusOf != .Open then [("status", Json.str (statusWire dta.statusOf))] else [])
      ++ (match claimedBy with | some a => [("assignee", Json.str a)] | none => [])
      ++ (if s.isEpic i then [("isEpic", Json.bool true)] else [])
      ++ (match dta.deferUntilOf with
          | some t => if ctx.now < t then [("deferUntil", Json.str (Time.isoOfEpochMs t))] else []
          | none => [])
      ++ (if direct.isEmpty then [] else
          [("blockedBy", Json.arr (direct.map (Lean.Json.str ∘ displayId)).toArray)])
    let notClaimable : String → Tl.Error := fun msg =>
      { code := .notClaimable, message := msg,
        context := [("id", .str (displayId i)), ("reasons", reasons)] }
    -- the verdict for taking over someone else's claim: a stale-claim courtesy
    -- guard, never merge-enforced (ADR-0013) — concurrent steals reconcile by LWW
    -- and the loser reads "superseded".
    let stealVerdict : Except Tl.Error (List WireOp) :=
      match thresholdMs with
      | none => .error (.mk' .usage <| cfgBadMsg.getD
          s!"{displayId i} is claimed by {holder}; --steal needs a staleness window — pass --stale <duration> (e.g. 1h) or set `git config tl.staleAfter`")
      | some w =>
        match (provenanceOf ctx.loaded.ops i).claimedAt with
        | none => .error (notClaimable
            s!"{displayId i} is claimed by {holder} but carries no claim timestamp to age — claim something from `tl ready`")
        | some claimedHlc =>
          let deadline := claimStaleDeadlineMs claimedHlc w
          if ctx.now > deadline then .ok [.claim i actor]  -- stale: take it over
          else .error (notClaimable
            s!"{displayId i} is claimed by {holder} and not stale yet (~{max 1 ((deadline - ctx.now + 59999) / 60000)}m until the window elapses) — retry later, --steal with a shorter --stale, or claim something from `tl ready`")
    if State.isReadyWith rm s ctx.now i then .ok [.claim i actor]
    else if steal && onlyClaimObstacle && claimedBy == some actor then .ok [.claim i actor]
    else if steal && onlyClaimObstacle then stealVerdict
    else .error (notClaimable
      s!"{displayId i} is not claimable — run `tl why {displayId i}`, or claim something from `tl ready`"))
  let v := writeNow ctx parsed
  let some (i, claimStamp) := parsed.head?.bind (fun p =>
      match p.op with | .claim ci _ => some (ci, p.stamp) | _ => none)
    | throw (.mk' .internal "claim wrote no claim record")
  let auto ← Tl.Sync.autoSyncLocal d replica
  -- publish-around-claim (ADR-0001 §5): with --sync, push the take to the remote
  -- right away (after it is in the local ref), closing the cross-clone race
  -- window. Best-effort — the take is already recorded locally, so a publish
  -- failure degrades with a note rather than failing the (successful) claim.
  let postNotes ← if sync then
      (try (do let (_, _, pn) ← performSync d; pure pn)
       catch e => pure [s!"the take is recorded but could not be published to the remote ({e.message}) — run `tl sync`"])
    else pure []
  -- with --sync, the post-push reconcile may have pulled a competing claim, so
  -- re-derive the outcome from the freshly-reconciled state (re-fold) — the echo
  -- then reflects a sibling that won the race. The race can't be fully closed
  -- (distributed), but the report is as fresh as the post-push fetch. Without
  -- --sync, the just-written state is the freshest we have.
  let (vFinal, reloadNotes) ←
    if sync then reloadOrFallback (loadView dirOverride) v i else pure (v, ([] : List String))
  let dFinal := vFinal.state.issueData i
  let current := dFinal.assignee.value.getD none
  -- the outcome derives from BOTH registers (kernel `claimWonB`): the claim
  -- holds only while status and assignee both carry its exact stamped writes.
  -- The assignee alone would misreport a concurrent close — which outstamps
  -- `status` but never writes `assignee` — as a win on a closed issue.
  let won := claimWonB dFinal claimStamp actor
  -- the partial survival (assignee kept, status lost): still `superseded` on
  -- the wire (the outcome enum stays binary), but the human line explains it
  let partialWin := claimPartialB dFinal claimStamp actor
  -- the echo stays binary won/superseded, but spelled through the same
  -- `ClaimOutcome.wire` boundary as `show` so the surfaces cannot drift
  let echoOutcome : ClaimOutcome := if won then .won else .superseded
  let data := (issueObj vFinal i).setObjVal! "claim" (Json.mkObj
    [("outcome", Json.str echoOutcome.wire),
     ("currentAssignee", current.elim Json.null (Json.str ∘ sanitizeSingle))])
  -- a takeover: --steal won an item that was *in progress* under a different
  -- holder (read from ctx.loaded, the pre-fold state). Gating on the pre-state
  -- being InProgress keeps the disclosure honest — a plain claim of a ready
  -- (open) item that merely retained a stale assignee is "Claimed", not "Took
  -- over … stale", since no staleness test ran on the ready path.
  let priorHolder := (ctx.loaded.state.issueData i).assignee.value.getD none
  let tookOver := steal && won && priorHolder.isSome && priorHolder != some actor
    && (ctx.loaded.state.issueData i).statusOf == .InProgress
  -- mirror cmdClose: a folded foreign op can outstamp the fresh claim inside the
  -- skew window, so the human line must disclose supersession — not assume "Claimed"
  let human :=
    if tookOver then s!"Took over {displayId i} from {(priorHolder.map sanitizeSingle).getD "—"} as {sanitizeSingle actor} (its claim was stale)"
    else if won then s!"Claimed {displayId i} as {sanitizeSingle actor}"
    else if partialWin then partialClaimMessage i actor dFinal.statusOf
    else s!"claim of {displayId i} was superseded by a later concurrent write — it is now assigned to {current.elim "no one" sanitizeSingle}; rerun if still intended"
  return { data, human
           notes := preNotes ++ freshNotes ++ writeNotes ctx ++ auto ++ postNotes ++ reloadNotes }

def cmdClose (dirOverride : Option String) (tok : String) (asStr : String)
    (ofTok : Option String) (actor : String) : TlM CmdOut := do
  let some res := resolutionOfWire? asStr
    | throw (.mk' .usage s!"--as must be done|cancelled|duplicate (got '{asStr}')")
  -- a mode-scoped flag is usage-checked against its mode: --of names the
  -- duplicate's canonical issue and means nothing for done/cancelled
  if ofTok.isSome && res != .Duplicate then
    throw (.mk' .usage "--of names the canonical issue of a duplicate — it only pairs with --as duplicate")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 2 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    let target ← ofTok.mapM (resolveToken s)
    if target == some i then
      .error { code := .notCloseable
               message := s!"{displayId i} cannot be its own duplicate — name the canonical issue in --of, or close --as cancelled"
               context := [("id", .str (displayId i)),
                           ("reasons", Json.mkObj [("selfDuplicate", Json.bool true)])] }
    else if res == .Done && s.isEpic i then
      let rm := s.effStatusAll
      let openKids := (s.presentChildren i).filter (fun c => !State.effClosedWith rm s c)
      -- an epic is `done` by child rollup (ADR-0003), never closed `--as done`; word
      -- the refusal differently once all children are closed (open: 0 would read as a
      -- contradiction — "becomes done when its children close" but they already have)
      let msg :=
        if openKids.isEmpty then
          s!"{displayId i} is an epic and is already done via child rollup — no explicit close needed (`--as cancelled` is the only manual terminal)"
        else
          s!"{displayId i} is an epic — it becomes done when its children close (open: {openKids.length}); `--as cancelled` is the manual terminal"
      .error { code := .notCloseable
               message := msg
               context := [("id", .str (displayId i)),
                           ("reasons", Json.mkObj
                             [("isEpic", Json.bool true),
                              ("openChildren", Json.arr (openKids.map (Lean.Json.str ∘ displayId)).toArray)])] }
    else
      let dta := s.issueData i
      let sameTarget := match target with
        | none => true
        | some t => duplicateOf s i == some t
      if dta.statusOf.closed && dta.closeResolution.value.getD none == some res && sameTarget then
        .ok []  -- idempotent re-close (ADR-0008): appends nothing
      else
        .ok ([WireOp.close i res] ++ (match res, target with
          | .Duplicate, some t => [WireOp.metaSet i "duplicate-of" (some t)]
          | _, _ => []))
  )
  let v := writeNow ctx parsed
  -- the echo target: re-resolve against the post view (parsed may be empty)
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  -- compute the echo from the POST-fold state, not the assumed result: a
  -- concurrent later-stamped foreign claim/reopen can outrank this close in
  -- LWW, so the issue may not actually be closed. `unblocked` is the proved
  -- freed set over the post state, and the message reports what really held.
  let dPost := v.state.issueData i
  let actuallyClosed := dPost.statusOf.closed
  -- the outcome is VALUE-based (mirrors the claim task): the close *won* only
  -- when the issue is terminal AND the winning `closeResolution` is the one
  -- this close requested — and, for `--as duplicate`, the winning duplicate-of
  -- points where we asked. A concurrent foreign close with a DIFFERENT
  -- resolution (or a different duplicate target) that outstamps this write
  -- leaves the issue closed but not as requested: `superseded`, disclosed
  -- honestly rather than a "Closed as <losing-resolution>" lie. (Terminality
  -- alone — the old check — could not tell the two apart.)
  let resWinner := dPost.closeResolution.value.getD none
  let echoTarget := ofTok.bind (fun t => (resolveToken v.state t).toOption)
  let dupTargetOk := match res, echoTarget with
    | .Duplicate, some t => duplicateOf v.state i == some t
    | _, _ => true
  let resWon := actuallyClosed && resWinner == some res && dupTargetOk
  -- `unblocks` is the ready-diff `ready (withClosed s i) \ ready s`, so it is
  -- computed on the PRE-state (where i is still open — on the post-state the
  -- diff is empty). It is the PROVED freed set (ADR-0004 thm 10) and is gated
  -- on TERMINALITY alone: *any* terminal status discharges blockers regardless
  -- of which resolution or duplicate-of target won the LWW. Decoupled from the
  -- outcome gate on purpose — a superseded-but-terminal close (a concurrent
  -- write took a *different* resolution/target) still genuinely freed its
  -- dependents, so it honestly reports both `outcome: superseded` AND the freed
  -- set. Only a close that lost terminality entirely (a foreign reopen outran
  -- it) frees nothing.
  let freed := if actuallyClosed then (State.unblocksFast ctx.loaded.state ctx.now i).map (Json.str ∘ displayId)
               else []
  let closeOutcome : CloseOutcome := if resWon then .won else .superseded
  -- the `close` block mirrors claim's `{outcome, currentAssignee}`: the typed
  -- outcome plus the resolution that actually holds (null when not terminal),
  -- so an agent branches on the outcome and reads the winning resolution
  -- without re-deriving it. Additive field (ADR-0008 §additive-only).
  let closeBlock := Json.mkObj
    [("outcome", Json.str closeOutcome.wire),
     ("resolution", resWinner.elim Json.null (fun r => Json.str (resolutionWire r)))]
  let data := ((issueObj v i).setObjVal! "unblocked" (Json.arr freed.toArray)).setObjVal! "close" closeBlock
  let human :=
    if parsed.isEmpty then s!"{displayId i} already closed as {asStr} — nothing to do"
    else if !actuallyClosed then
      s!"close of {displayId i} was superseded by a later concurrent write — it is {statusWire dPost.statusOf}; rerun if still intended"
    else if resWon then s!"Closed {displayId i} as {asStr}" ++
      (if freed.isEmpty then "" else s!" (unblocked {freed.length})")
    else if resWinner == some res && res == .Duplicate then
      -- same resolution, different canonical: a concurrent duplicate close won
      -- the duplicate-of target. Word it in terms of the target, not the
      -- (identical) resolution, so it never reads "duplicate, not duplicate".
      let winDup := (duplicateOf v.state i).elim "another issue" displayId
      let reqDup := echoTarget.elim asStr displayId
      s!"close of {displayId i} was superseded by a later concurrent write — it is a duplicate of {winDup}, not of {reqDup}; rerun if still intended"
    else
      -- terminal, but not as this close asked: a concurrent close won the
      -- resolution register. Name what actually holds.
      let heldAs := match resWinner with
        | some r => resolutionWire r
        | none => statusWire dPost.statusOf
      s!"close of {displayId i} was superseded by a later concurrent write — it is closed as {heldAs}, not {asStr}; rerun if still intended"
  return { data, human, notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl update` writes the mutable scalar fields. The notes scalar is retired
    (ADR-0027): notes are an append-only journal of immutable entries, so
    `--notes` (replace) and `--append-notes` (a non-atomic read-modify-write
    that dropped a racing writer's line wholesale) are gone — each fails with a
    usage error that teaches the replacement, `tl note add`. -/
def cmdUpdate (dirOverride : Option String) (tok : String)
    (title description notes appendNotes slug : Option String)
    (priority : Option Nat) (actor : String) : TlM CmdOut := do
  if notes.isSome then
    throw (.mk' .usage
      "--notes is retired (ADR-0027): notes are an append-only journal — append an entry with `tl note add <id> <text>`; a correction is a new note, and `tl note remove <id> <note-id>` deletes one")
  if appendNotes.isSome then
    throw (.mk' .usage
      "--append-notes is retired (ADR-0027): `tl note add <id> <text>` appends an immutable entry with no lost-update race — concurrent appends are all retained")
  if title.isNone && description.isNone && slug.isNone && priority.isNone then
    throw (.mk' .usage
      "update needs at least one of --title, --priority, --description, --slug (notes moved to `tl note add`)")
  let prio : Option (Fin 5) := priority.map (fun p => ⟨min p 4, Nat.lt_succ_of_le (Nat.min_le_right p 4)⟩)
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    .ok [.update i { title, priority := prio,
                     description := description.map some, slug := slug.map some }])
  let v := writeNow ctx parsed
  let some i := parsed.head?.bind (fun p =>
      match p.op with | .update ui _ => some ui | _ => none)
    | throw (.mk' .internal "update wrote no record")
  return { data := issueObj v i, human := s!"Updated {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl reopen <id>`: a terminal issue back to `open`, clearing both
    `closeResolution` and the `assignee` as part of the closed→open transition
    (ADR-0008's reopen delta + ADR-0013: the prior claim ended with the close).
    Idempotent on *value equality* — a no-op only when the issue already equals
    reopen's whole target (open, no resolution, no assignee), mirroring the
    re-close guard. This is deliberately not narrowed to `status == open`:
    `status` and `assignee` are independent LWW registers, so a merge can
    materialize an open-but-assigned issue that no reopen produced — e.g. a
    `claim` (which writes `status:=in_progress` and `assignee` at one stamp)
    stamped *below* a later status write (a `create`/`reopen` under clock skew, or
    a crafted segment) loses the status LWW (→ `open`) but keeps the assignee LWW.
    No write-time guard can forbid that merge (CLAUDE.md §2). Firing reopen on it
    restores the claim-only invariant — the only CLI path back to open+unassigned. -/
def cmdReopen (dirOverride : Option String) (tok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    let dta := ctx.loaded.state.issueData i
    if dta.statusOf == .Open && (dta.closeResolution.value.getD none).isNone
        && (dta.assignee.value.getD none).isNone then .ok []
    else .ok [.reopen i])
  let v := writeNow ctx parsed
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  return { data := issueObj v i
           human := if parsed.isEmpty then s!"{displayId i} is already open"
                    else s!"Reopened {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- Where a `defer` lands: an absolute instant (`--until`, resolved before the
    lock) or a delay applied to the under-lock `now` (`--for`, so the deferral
    is measured from the same clock the stamp is minted against). -/
private inductive DeferTarget where
  | abs (ms : Nat)
  | after (durMs : Nat)

private def deferUntilHelp (got : String) : Tl.Error :=
  .mk' .usage
    s!"--until wants a date (YYYY-MM-DD, local start-of-day) or a timestamp with an explicit offset (e.g. 2026-07-01T09:00:00Z or …+02:00) — got '{got}'; for a relative delay use --for (e.g. --for 36h)"

/-- `tl defer <id> --until <date|timestamp>` / `--for <duration>`: set the
    `deferUntil` instant so `ready` excludes the issue until the time passes,
    then auto-resurfaces it (ADR-0010). Exactly one of `--until`/`--for`. A
    re-defer to the identical instant appends nothing (idempotent on value,
    mirroring re-close/reopen). The deferral is a field on an otherwise-open
    issue — no status guard (a merge could not honor one anyway, CLAUDE.md §2). -/
def cmdDefer (dirOverride : Option String) (tok : String)
    (untilArg forArg : Option String) (actor : String) : TlM CmdOut := do
  let target ← match untilArg, forArg with
    | some _, some _ =>
      throw (.mk' .usage "defer takes one of --until <date> or --for <duration>, not both")
    | none, none =>
      throw (.mk' .usage "defer needs --until <date> or --for <duration> (e.g. --until 2026-07-01, --for 36h)")
    | some u, none =>
      -- an offset-bearing timestamp carries its own zone — resolve it without
      -- touching the system tz; only a bare date needs the injected local offset
      if let some ms := Time.parseOffsetDateTime? u then
        pure (DeferTarget.abs ms)
      else do
        let off ← liftSys (fun e => .mk' .internal s!"timezone read failed: {e}") localOffsetMinutes
        match Time.parseUntilInstant? off u with
        | some ms => pure (DeferTarget.abs ms)
        | none => throw (deferUntilHelp u)
    | none, some f => do
      match Time.parseDurationMs? f with
      | some 0 => throw (.mk' .usage s!"--for needs a positive duration, not zero (got '{f}')")
      | some ms => pure (DeferTarget.after ms)
      | none => throw (.mk' .usage s!"--for wants a duration like 36h, 7d, or 90m (got '{f}')")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    let untilMs := match target with
      | .abs ms => ms
      | .after durMs => ctx.now + durMs
    -- reject an instant beyond the canonical wire range (`--for` can overflow):
    -- rendering a 5-digit year would make the next read refuse our own segment
    -- as malformed (Time.maxRenderableInstantMs)
    if untilMs > Time.maxRenderableInstantMs then
      .error (.mk' .usage "defer time is beyond the representable range (year 9999) — use a smaller --for duration or an absolute --until")
    -- idempotent: an LWW re-write of the same instant changes nothing
    else if (ctx.loaded.state.issueData i).deferUntilOf == some untilMs then .ok []
    else .ok [.defer i untilMs])
  let v := writeNow ctx parsed
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let untilIso := (v.issueData i).deferUntilOf.map Time.isoOfEpochMs |>.getD "—"
  -- a deferUntil at or before now defers nothing (the ready conjunct holds
  -- vacuously); say so loudly rather than let a past `--until` look effective
  let elapsedNote : List String := match (v.issueData i).deferUntilOf with
    | some t => if t ≤ v.now then
        [s!"deferUntil {untilIso} is already past — {displayId i} is not deferred (still workable); use a future time or --for"]
      else []
    | none => []
  return { data := issueObj v i
           human := if parsed.isEmpty then s!"{displayId i} is already deferred until {untilIso}"
                    else s!"Deferred {displayId i} until {untilIso}"
           notes := freshNotes ++ writeNotes ctx ++ elapsedNote ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl undefer <id>`: clear the `deferUntil`, making the issue workable now
    (ADR-0010). Idempotent — a no-op (and an honest "is not deferred") when no
    deferral is set, mirroring `reopen`'s already-open path. -/
def cmdUndefer (dirOverride : Option String) (tok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    match (ctx.loaded.state.issueData i).deferUntilOf with
    | none => .ok []
    | some _ => .ok [.undefer i])
  let v := writeNow ctx parsed
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  return { data := issueObj v i
           human := if parsed.isEmpty then s!"{displayId i} is not deferred"
                    else s!"Undeferred {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

def cmdDepAdd (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let a ← resolveToken s aTok
    let b ← resolveToken s bTok
    .ok [.depAdd (b, a, EdgeKind.Blocks)])
  let some (f, t, _) := parsed.head?.bind (fun p =>
      match p.op with | .depAdd e => some e | _ => none)
    | throw (.mk' .internal "dep add wrote no record — this is a bug in tl; please report it")
  return { data := Json.mkObj
            [("type", Json.str "blocks"), ("from", Json.str (displayId f)),
             ("to", Json.str (displayId t)), ("status", Json.str "added")]
           human := s!"{displayId t} is now blocked by {displayId f}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

def cmdDepRemove (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let a ← resolveToken s aTok
    let b ← resolveToken s bTok
    let e : Edge := (b, a, EdgeKind.Blocks)
    -- presence, not raw add-tags: a tombstoned tag still enumerates, but a
    -- non-present edge means there is nothing to retract (ADR-0020 "noop")
    if !decide (s.edges.Present e) then
      .ok []
    else
      .ok [.depRemove e (s.edges.tagsOf e)])
  -- recover endpoints for the ack (re-resolve on the pre state)
  let s := ctx.loaded.state
  let a ← MonadExcept.ofExcept (resolveToken s aTok)
  let b ← MonadExcept.ofExcept (resolveToken s bTok)
  let status := if parsed.isEmpty then "noop" else "removed"
  return { data := Json.mkObj
            [("type", Json.str "blocks"), ("from", Json.str (displayId b)),
             ("to", Json.str (displayId a)), ("status", Json.str status)]
           human :=
             if parsed.isEmpty then s!"{displayId a} was not blocked by {displayId b} — nothing to do"
             else s!"{displayId a} is no longer blocked by {displayId b}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `dep critical` — rank open issues by transitive dependent-count (the proved
    critical-path `weight`, ADR-0004 thm 4): the most-unblocking work first. Only
    issues that block at least one other appear. The weight is computed over the
    hoisted blocks adjacency — the same metric `ready` ranks by. -/
def cmdDepCritical (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let bsrc := v.idx.bsrc  -- already = blocksBySource v.edges (built once in the index)
  let pset := v.idx.presentH
  let n := v.present.length
  let weighted := (v.present.filter (fun i => v.effStatus i == .Open)).filterMap (fun i =>
    let w := State.weightFast bsrc pset n i
    if w == 0 then none else some (i, w))
  let le := fun (a b : IssueId × Nat) =>
    if a.2 != b.2 then decide (b.2 < a.2) else decide (TotalOrd.le a.1 b.1)
  let ranked := weighted.mergeSort le
  let rows := ranked.map (fun (i, w) =>
    Json.mkObj
      [("id", Json.str (displayId i)), ("weight", jnum w),
       ("status", Json.str (statusWire (v.effStatus i))),
       ("title", Json.str (sanitizeSingle ((v.issueData i).title.value.getD "")))])
  let data := Json.mkObj [("items", Json.arr rows.toArray), ("count", jnum ranked.length)]
  let human :=
    if ranked.isEmpty then "no open issue blocks another"
    else String.intercalate "\n" (ranked.map (fun (i, w) => s!"  {issueLine v i}  (blocks {w})"))
  return { data, human, notes }

/-- `dep path A B` — a witness `blocks`-edge path from A to B (A transitively
    blocks B), the cycle-breaking aid. Over the proved kernel extractor
    `State.blocksPath` (Tl/Kernel/Path.lean): `found` is true iff B is
    reach+-reachable from A over present blocks edges, and `path` is then a real
    consecutive-edge chain `[A, …, B]` (empty when none). Total on cyclic and
    dangling graphs. JSON `{from,to,path:[ids],found}`; human is an arrow line. -/
def cmdDepPath (dirOverride : Option String) (aTok bTok : String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let a ← MonadExcept.ofExcept (resolveToken v.state aTok)
  let b ← MonadExcept.ofExcept (resolveToken v.state bTok)
  let pathOpt := v.state.blocksPath a b
  let p := pathOpt.getD []
  let data := Json.mkObj
    [("from", Json.str (displayId a)), ("to", Json.str (displayId b)),
     ("path", Json.arr (p.map (Json.str ∘ displayId)).toArray),
     ("found", Json.bool pathOpt.isSome)]
  let human :=
    if pathOpt.isSome then String.intercalate " → " (p.map displayId)
    else s!"no blocks path from {displayId a} to {displayId b}"
  return { data, human, notes }

/-- `dep relate A B` — a symmetric informational link (canonicalized on the
    sorted endpoint pair, since `related` is undirected). Drives nothing (frame
    lemma); filter/display only. -/
def cmdDepRelate (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let a ← resolveToken s aTok
    let b ← resolveToken s bTok
    if a == b then .error (.mk' .usage "cannot relate an issue to itself — give two different ids")
    else .ok [.relate (if decide (a ≤ b) then (a, b, EdgeKind.Related) else (b, a, EdgeKind.Related))])
  let _ := parsed
  let s := ctx.loaded.state
  let a ← MonadExcept.ofExcept (resolveToken s aTok)
  let b ← MonadExcept.ofExcept (resolveToken s bTok)
  return { data := Json.mkObj
            [("type", Json.str "related"), ("from", Json.str (displayId a)),
             ("to", Json.str (displayId b)), ("status", Json.str "added")]
           human := s!"{displayId a} and {displayId b} are now related"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `dep unrelate A B` — retract the `related` link. A noop (nothing appended)
    when the pair is not currently related (ADR-0020). -/
def cmdDepUnrelate (dirOverride : Option String) (aTok bTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let a ← resolveToken s aTok
    let b ← resolveToken s bTok
    let e : Edge := if decide (a ≤ b) then (a, b, EdgeKind.Related) else (b, a, EdgeKind.Related)
    if !decide (s.edges.Present e) then .ok []
    else .ok [.unrelate e (s.edges.tagsOf e)])
  let s := ctx.loaded.state
  let a ← MonadExcept.ofExcept (resolveToken s aTok)
  let b ← MonadExcept.ofExcept (resolveToken s bTok)
  let status := if parsed.isEmpty then "noop" else "removed"
  return { data := Json.mkObj
            [("type", Json.str "related"), ("from", Json.str (displayId a)),
             ("to", Json.str (displayId b)), ("status", Json.str status)]
           human :=
             if parsed.isEmpty then s!"{displayId a} and {displayId b} were not related — nothing to do"
             else s!"{displayId a} and {displayId b} are no longer related"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-! ## parent verbs (reparenting) -/

/-- `tl parent set <child> <parent>`: move `<child>` under `<parent>` (the
    reparent operation). A local courtesy *replace*: it tombstones the
    child's present parent edge(s) other than `<parent>` and adds the new one in
    one transaction, so the child stays single-parented locally (no
    self-inflicted `multiParent`); a concurrent merge can still produce
    multi-parent, which `doctor` reports — never enforced, only reported
    (ADR-0003 §4 / the CRDT rule). Idempotent: a child already solely under
    `<parent>` appends nothing. A direct self-parent is a courtesy refusal;
    longer cycles stay reported by `tl dep cycles`, not rejected (matching
    `dep add`). -/
def cmdParentSet (dirOverride : Option String) (childTok parentTok : String)
    (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  -- size the stamp budget from a pre-read: at most (present parents to drop) + 1
  -- (the new edge). The build re-derives the exact ops under the lock; a rare
  -- concurrent parent-add to the same child in the window just retries.
  let now ← liftSys (fun e => .mk' .internal s!"clock read failed: {e}") nowMs
  let pre ← readStateCached d false (some now) (replica.map (·.id))
  let budget := match resolveToken pre.state childTok with
    | .ok child => (pre.state.parentsOf child).length + 1
    | .error _ => 1  -- resolution re-runs in the build and surfaces the real error
  let (ctx, parsed) ← transact d (some actor) budget (fun ctx _ => do
    let s := ctx.loaded.state
    let child ← resolveToken s childTok
    let parent ← resolveToken s parentTok
    if parent == child then
      .error (.mk' .usage
        s!"{displayId child} cannot be its own parent — name a different epic in <parent>")
    else
      -- drop every present parent edge of the child except the target, then add
      -- the target if absent (add-wins; the new edge is canonical by stamp)
      let drop := s.presentEdges.filter (fun e =>
        decide (e.2.2 = EdgeKind.Parent ∧ e.2.1 = child) && e.1 != parent)
      let needAdd := !(s.parentsOf child).contains parent
      .ok (drop.map (fun e => .depRemove e (s.edges.tagsOf e))
           ++ (if needAdd then [.depAdd (parent, child, EdgeKind.Parent)] else [])))
  let v := writeNow ctx parsed
  let child ← MonadExcept.ofExcept (resolveToken v.state childTok)
  let parent ← MonadExcept.ofExcept (resolveToken v.state parentTok)
  let replaced := parsed.filterMap (fun p => match p.op with
    | .depRemove (f, _, _) _ => some (displayId f) | _ => none)
  let status := if parsed.isEmpty then "noop" else "set"
  -- the issue object's own `parent` field already reflects the new canonical
  -- parent; `reparent` carries the action metadata
  let data := (issueObj v child).setObjVal! "reparent" (Json.mkObj
    [("status", Json.str status),
     ("replaced", Json.arr (replaced.map Json.str).toArray)])
  let human :=
    if parsed.isEmpty then s!"{displayId child} is already under {displayId parent} — nothing to do"
    else s!"Moved {displayId child} under {displayId parent}"
      ++ (if replaced.isEmpty then "" else s!" (was under {String.intercalate ", " replaced})")
  return { data, human, notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl parent remove <child> <parent>`: detach `<child>` from `<parent>` —
    retract that one parent edge if present, else a no-op (mirrors
    `dep remove`). To drop a child's only parent is to make it a root. -/
def cmdParentRemove (dirOverride : Option String) (childTok parentTok : String)
    (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let child ← resolveToken s childTok
    let parent ← resolveToken s parentTok
    let e : Edge := (parent, child, EdgeKind.Parent)
    if !decide (s.edges.Present e) then .ok []
    else .ok [.depRemove e (s.edges.tagsOf e)])
  let s := ctx.loaded.state
  let child ← MonadExcept.ofExcept (resolveToken s childTok)
  let parent ← MonadExcept.ofExcept (resolveToken s parentTok)
  let v := writeNow ctx parsed
  let status := if parsed.isEmpty then "noop" else "removed"
  let data := (issueObj v child).setObjVal! "reparent" (Json.mkObj
    [("status", Json.str status), ("removed", Json.str (displayId parent))])
  let human :=
    if parsed.isEmpty then s!"{displayId child} was not a child of {displayId parent} — nothing to do"
    else s!"{displayId child} is no longer a child of {displayId parent}"
  return { data, human, notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-! ## label verbs -/

def cmdLabelAdd (dirOverride : Option String) (tok label : String) (actor : String) : TlM CmdOut := do
  if label.trimAscii.isEmpty then
    throw (.mk' .usage "a label must be non-empty — `tl label add <id> <label>`")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    -- idempotent: an already-present label appends nothing (mirrors re-close)
    if (s.issueData i).labels.presentElements.contains label then .ok []
    else .ok [.labelAdd i label])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  let status := if parsed.isEmpty then "noop" else "added"
  return { data := Json.mkObj
            [("type", Json.str "label"), ("id", Json.str (displayId i)),
             ("label", Json.str (sanitizeSingle label)), ("status", Json.str status)]
           human := if parsed.isEmpty then s!"{displayId i} already has label '{sanitizeSingle label}'"
                    else s!"Labeled {displayId i} '{sanitizeSingle label}'"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

def cmdLabelRemove (dirOverride : Option String) (tok label : String) (actor : String) : TlM CmdOut := do
  if label.trimAscii.isEmpty then
    throw (.mk' .usage "a label must be non-empty — `tl label remove <id> <label>`")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    let lbls := (s.issueData i).labels
    -- presence, not raw add-tags: a non-present label has nothing to retract
    if !lbls.presentElements.contains label then .ok []
    else .ok [.labelRemove i label (lbls.tagsOf label)])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  let status := if parsed.isEmpty then "noop" else "removed"
  return { data := Json.mkObj
            [("type", Json.str "label"), ("id", Json.str (displayId i)),
             ("label", Json.str (sanitizeSingle label)), ("status", Json.str status)]
           human := if parsed.isEmpty then s!"{displayId i} had no label '{sanitizeSingle label}' — nothing to do"
                    else s!"Unlabeled {displayId i} '{sanitizeSingle label}'"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }


/-! ## The notes journal verbs (ADR-0027) -/

/-- The no-secure-deletion disclosure every removal carries (ADR-0027). -/
private def noteRemovalDisclosure : String :=
  "hidden from views; the text remains in the replicated log history and in already-synced clones"

/-- Resolve a `<note-id>` inside one issue's journal (ADR-0027): a full
    canonical tag string (`<hlc>.<replica>.<nonce>`, told apart by shape — its
    two dots) is the always-unique fallback; anything else is a handle prefix
    over the *live* entries, ASCII-case-folded and Crockford-aliased like issue
    ids. A collision refuses with the colliding entries' canonical tags.
    Returns the entry's tag, its stored handle, and whether it is already
    removed.

    A token that *looks* canonical (two dots) but is not a valid stamp — or
    names no entry here — is a bad CLI argument, so it surfaces a `usage` /
    `not-found` error that teaches `tl note list`; it never leaks the codec's
    `malformed-line` code and its "repair the line / --skip-bad" advice, which
    would misread a mistyped argument as log corruption. -/
private def resolveNoteToken (jn : Tl.Crdt.Journal) (noteTok : String) :
    Except Tl.Error (Tl.Crdt.Stamp × String × Bool) := do
  if (noteTok.splitOn ".").length == 3 then
    -- shaped like a canonical tag; parse it ourselves so a malformed one is a
    -- CLI `usage` error, not the wire codec's `malformed-line`
    let tag ← match stampOfTag noteTok with
      | .ok st => pure st
      | .error _ => throw (.mk' .usage
          s!"'{noteTok}' is not a valid note id or canonical tag for this issue — run `tl note list <id>` (or `--all`) to see the note ids")
    match jn.payloadOf tag with
    | some pl => return (tag, pl.handle, !(decide (jn.Visible tag)))
    | none => throw (.mk' .notFound
        s!"no note with tag '{noteTok}' in this issue's journal — `tl note list <id> --all` shows every entry with its tag")
  else
    let norm := normalizeIdToken noteTok
    if norm.isEmpty then
      throw (.mk' .usage
        "note remove needs a <note-id>: a handle (or unambiguous prefix) from `tl note list`, or a full canonical tag")
    let cands := jn.visibleEntries.filterMap (fun (st, pl) =>
      if (normalizeIdToken pl.handle).startsWith norm then some (st, pl.handle) else none)
    match cands with
    | [] => throw (.mk' .notFound
        s!"no visible note matches '{noteTok}' in this issue's journal — `tl note list <id>` shows the handles; a removed entry is reachable by its canonical tag (`--all`)")
    | [(st, h)] => return (st, h, false)
    | _ => throw (.mk' .usage
        (s!"note id '{noteTok}' is ambiguous here (it matches {cands.length} entries) — "
          ++ "use a longer prefix or a full canonical tag: "
          ++ String.intercalate ", " (cands.map (fun (st, _) => tagOfStamp st))))

/-- `tl note add <id> <text>`: append one immutable journal entry (ADR-0027).
    `-` as the text reads stdin (handled at dispatch, the `create` body
    convention). The note id is minted from the record's own stamp
    (`mintNoteId`); the envelope actor rides into the entry payload at fold
    time. Echoes the new entry. -/
def cmdNoteAdd (dirOverride : Option String) (tok text : String) (actor : String) : TlM CmdOut := do
  if text.trimAscii.isEmpty then
    throw (.mk' .usage
      "a note needs text — `tl note add <id> <text>` (`-` reads it from stdin)")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx stamps => do
    let i ← resolveToken ctx.loaded.state tok
    let some st := stamps.head?
      | .error (.mk' .internal
          "transact provided no stamp for note add — this is a bug in tl; please report it")
    .ok [.noteAdd i (mintNoteId st) text])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  let some (handle, st) := parsed.head?.bind (fun pp =>
      match pp.op with | .noteAdd _ note _ => some (note, pp.stamp) | _ => none)
    | throw (.mk' .internal "note add wrote no record — this is a bug in tl; please report it")
  let entry := noteEntryJson st ⟨handle, text, some actor⟩
  let data := Json.mkObj
    [("id", Json.str (displayId i)), ("note", entry), ("status", Json.str "added")]
  return { data, human := s!"Added note [{handle}] to {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl note list <id> [--all]`: the visible journal, oldest first
    (stamp-ascending — the proved kernel order); `--all` adds removed-entry
    placeholders in their true positions (provenance shown, text hidden — the
    log itself is the deliberate escape hatch). -/
def cmdNoteList (dirOverride : Option String) (tok : String) (all skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let jn := (v.issueData i).notes
  let rows : List (Tl.Crdt.Stamp × Tl.Crdt.NotePayload × Bool) :=
    if all then jn.allEntries
    else jn.visibleEntries.map (fun (st, pl) => (st, pl, false))
  let data := Json.mkObj
    [("id", Json.str (displayId i)), ("count", jnum rows.length),
     ("notes", Json.arr (rows.map (fun (st, pl, rem) => noteEntryJson st pl rem)).toArray)]
  let human :=
    if rows.isEmpty then s!"{displayId i} has no notes"
    else String.intercalate "\n" (rows.map (fun (st, pl, rem) => noteHumanLine st pl rem))
  return { data, human, notes }

/-- `tl note remove <id> <note-id>`: tombstone one entry — exactly the entry
    whose tag the resolved handle names (remove-exactness is a kernel
    theorem). The output carries the honesty disclosure: removal hides the
    entry from materialized views only (ADR-0027, no secure deletion). -/
def cmdNoteRemove (dirOverride : Option String) (tok noteTok : String) (actor : String) : TlM CmdOut := do
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    let jn := (s.issueData i).notes
    let (tag, handle, alreadyRemoved) ← resolveNoteToken jn noteTok
    if alreadyRemoved then .ok []
    else .ok [.noteRemove i handle (jn.entries.tagsOf tag)])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  -- Report the resolved 16-char handle in every outcome (removed / noop), so
  -- the `note` field shape never depends on whether the write fired. The
  -- noop path (an already-removed entry) carries no op to read it from, so
  -- re-resolve against the folded state — the same resolution the build saw.
  let handle ← MonadExcept.ofExcept (do
    let jn := (ctx.loaded.state.issueData i).notes
    let (_, h, _) ← resolveNoteToken jn noteTok
    pure h)
  let status := if parsed.isEmpty then "noop" else "removed"
  let data := Json.mkObj
    [("id", Json.str (displayId i)), ("note", Json.str (sanitizeSingle handle)),
     ("status", Json.str status), ("disclosure", Json.str noteRemovalDisclosure)]
  let human := (if parsed.isEmpty then
      s!"note [{handle}] in {displayId i} is already removed — nothing to do"
    else s!"Removed note [{handle}] from {displayId i}") ++ s!" ({noteRemovalDisclosure})"
  return { data, human
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl label list`: the label vocabulary — every present label with how many
    issues carry it (sorted by name, a deterministic read). -/
def cmdLabelList (dirOverride : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  -- one pass: each present issue's label set is computed once and the counts
  -- accumulate per label into a sorted assoc map; the JSON rows and the human
  -- lines read the same counted list (the old shape re-counted every label
  -- twice, each count rescanning every issue). `insertWith` keeps the list
  -- sorted by label as it goes, so the result is already name-ordered — no
  -- separate sort. An issue's label set is duplicate-free (presentElements of
  -- the OR-Set), so counts stay per-issue. `v.issueData` reads the once-built
  -- data hash (= `s.issueData`, `issueDataH_eq`) — the raw find was O(N) per
  -- issue, Θ(N²) over the label scan.
  let counted : List (String × Nat) := Id.run do
    let mut acc : List (String × Nat) := []
    for i in v.present do
      for l in (v.issueData i).labels.presentElements do
        acc := AssocList.insertWith (· + ·) l 1 acc
    return acc
  let rows := counted.map (fun (l, n) =>
    Json.mkObj [("label", Json.str (sanitizeSingle l)), ("count", jnum n)])
  return { data := Json.mkObj [("count", jnum counted.length), ("labels", Json.arr rows.toArray)]
           human := if counted.isEmpty then "no labels"
                    else String.intercalate "\n" (counted.map (fun (l, n) => s!"{sanitizeSingle l}  {n}"))
           notes }

/-! ## meta (the opaque per-key side-channel — drives nothing, ADR-0002) -/

/-- `tl meta set <id> <key> <value>`: write an opaque metadata value (per-key
    LWW). No theorem touches it (frame lemma); filter/cross-ref only. -/
def cmdMetaSet (dirOverride : Option String) (tok key value : String) (actor : String) : TlM CmdOut := do
  if key.trimAscii.isEmpty then
    throw (.mk' .usage "a meta key must be non-empty — `tl meta set <id> <key> <value>`")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, _) ← transact d (some actor) 1 (fun ctx _ => do
    let i ← resolveToken ctx.loaded.state tok
    .ok [.metaSet i key (some value)])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  return { data := Json.mkObj
            [("id", Json.str (displayId i)), ("key", Json.str (sanitizeSingle key)),
             ("value", Json.str (sanitizeSingle value)), ("status", Json.str "set")]
           human := s!"set {sanitizeSingle key} on {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl meta clear <id> <key>`: tombstone a metadata key. A disclosed noop when
    the key carries no current value. -/
def cmdMetaClear (dirOverride : Option String) (tok key : String) (actor : String) : TlM CmdOut := do
  if key.trimAscii.isEmpty then
    throw (.mk' .usage "a meta key must be non-empty — `tl meta clear <id> <key>`")
  let (d, replica, freshNotes) ← Tl.Sync.preWriteRefresh dirOverride
  let (ctx, parsed) ← transact d (some actor) 1 (fun ctx _ => do
    let s := ctx.loaded.state
    let i ← resolveToken s tok
    if (((s.issueData i).metadata.find key).bind (·.value)).join.isNone then .ok []
    else .ok [.metaSet i key none])
  let i ← MonadExcept.ofExcept (resolveToken ctx.loaded.state tok)
  let status := if parsed.isEmpty then "noop" else "cleared"
  return { data := Json.mkObj
            [("id", Json.str (displayId i)), ("key", Json.str (sanitizeSingle key)), ("status", Json.str status)]
           human := if parsed.isEmpty then s!"{displayId i} had no {sanitizeSingle key} — nothing to do"
                    else s!"cleared {sanitizeSingle key} on {displayId i}"
           notes := freshNotes ++ writeNotes ctx ++ (← Tl.Sync.autoSyncLocal d replica) }

/-- `tl meta get <id> [<key>]`: read one metadata value, or all of an issue's. -/
def cmdMetaGet (dirOverride : Option String) (tok : String) (key : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  let i ← MonadExcept.ofExcept (resolveToken v.state tok)
  let dta := v.issueData i
  match key with
  | some k =>
    let val := ((dta.metadata.find k).bind (·.value)).join
    return { data := Json.mkObj
              [("id", Json.str (displayId i)), ("key", Json.str (sanitizeSingle k)),
               ("value", val.elim Json.null (Json.str ∘ sanitizeSingle))]
             human := val.elim s!"(no {sanitizeSingle k})" sanitizeSingle, notes }
  | none =>
    let pairs := (AMap.keys dta.metadata).filterMap (fun k =>
      ((dta.metadata.find k).bind (·.value)).join.map (fun val => (k, val)))
    let rows := pairs.map (fun (k, val) =>
      Json.mkObj [("key", Json.str (sanitizeSingle k)), ("value", Json.str (sanitizeSingle val))])
    return { data := Json.mkObj
              [("id", Json.str (displayId i)), ("count", jnum pairs.length), ("meta", Json.arr rows.toArray)]
             human := if pairs.isEmpty then s!"{displayId i} has no meta"
                      else String.intercalate "\n" (pairs.map (fun (k, val) => s!"{sanitizeSingle k}: {sanitizeSingle val}")), notes }

/-- `tl meta list [<id>]`: the metadata keys in use — for one issue, or every key
    with how many issues carry it. -/
def cmdMetaList (dirOverride : Option String) (idTok : Option String) (skipBad : Bool) : TlM CmdOut := do
  let v ← loadView dirOverride skipBad
  let notes ← cleanReadNotes v
  match idTok with
  | some tok =>
    let i ← MonadExcept.ofExcept (resolveToken v.state tok)
    let keys := (AMap.keys (v.issueData i).metadata).filter (fun k =>
      (((v.issueData i).metadata.find k).bind (·.value)).join.isSome)
    return { data := Json.mkObj
              [("id", Json.str (displayId i)), ("count", jnum keys.length),
               ("keys", Json.arr (keys.map (Json.str ∘ sanitizeSingle)).toArray)]
             human := if keys.isEmpty then s!"{displayId i} has no meta"
                      else String.intercalate "\n" (keys.map sanitizeSingle), notes }
  | none =>
    let counted : List (String × Nat) := Id.run do
      let mut acc : List (String × Nat) := []
      for i in v.present do
        let dta := v.issueData i
        for k in (AMap.keys dta.metadata) do
          if (((dta.metadata.find k).bind (·.value)).join.isSome) then
            acc := AssocList.insertWith (· + ·) k 1 acc
      return acc
    let rows := counted.map (fun (k, n) =>
      Json.mkObj [("key", Json.str (sanitizeSingle k)), ("count", jnum n)])
    return { data := Json.mkObj [("count", jnum counted.length), ("keys", Json.arr rows.toArray)]
             human := if counted.isEmpty then "no meta in use"
                      else String.intercalate "\n" (counted.map (fun (k, n) => s!"{sanitizeSingle k}  {n}")), notes }

/-! ## doctor / init / version -/

/-- The `doctor` git-version check row from a parsed `git --version` (ADR-0006):
    `ok` at/above the floor (git ≥ 2.17), `warn` below it or when git is unreadable.
    Always a warn, never a failure (doctor reports, does not fail — ADR-0008). Pure,
    so the below-floor branch is unit-testable without an actually-old git. -/
def gitVersionRow (v : Option (Nat × Nat)) : Json × Bool :=
  match v with
  | none =>
    (Json.mkObj [("name", Json.str "gitVersion"), ("status", Json.str "warn"),
      ("message", Json.str "could not read `git --version` — git ≥ 2.17 is a runtime prerequisite for the refs/tl/log transport; ensure git is on PATH")], false)
  | some (mj, mn) =>
    let ok := Tl.Sync.gitMeetsFloor (mj, mn)
    (Json.mkObj <|
      [("name", Json.str "gitVersion"), ("status", Json.str (if ok then "ok" else "warn")),
       ("version", Json.str s!"{mj}.{mn}")]
      ++ (if ok then [] else
          [("message", Json.str s!"git {mj}.{mn} is below the required floor git ≥ 2.17 — tl's git plumbing may fail cryptically; upgrade git")]), false)

/-- A remote whose *effective* push URL (after `url.*.insteadOf` /
    `pushInsteadOf`) differs from its configured push target — one visible face
    of the ADR-0012 `HOME` residual: a URL rewrite in a git config `tl` cannot
    scrub without breaking credentials still redirects the push. -/
structure RemoteRewrite where
  remote : String
  configured : String
  effective : String

/-- A push-destination config key whose effective value is supplied by the
    global scope (`~/.gitconfig`) rather than repo-local config — the *other*
    face of the `HOME` residual: not a URL rewrite but the remote *selection*
    or its URL injected wholesale (`tl.remote`, `remote.<n>.url`,
    `remote.<n>.pushurl`). A hostile `HOME` redirects the push through these
    with no rewrite at all, so a rewrite-only check reports `ok` while the log
    goes elsewhere. `value` is the effective (global) value. -/
structure ExternalPushConfig where
  key : String
  value : String

/-- The doctor `gitRouting` row (pure core, branch-testable): the split-brain
    report comparing filesystem discovery with git's classification.
    `routingVars` are the scrubbed (ADR-0012) variables found inherited;
    `stateRoot` / `toplevel` arrive canonicalized (realpath) by the caller;
    `rewrite` is set when the resolved remote's effective push URL differs from
    its configured target; `external` lists push-destination keys sourced from
    the global scope. Every condition warns and teaches — none fails health.
    Routing-vars and the toplevel mismatch are informational (tl's own
    subprocesses scrub the routing environment, and a state directory below its
    repository's toplevel still shares through that repository's ref); the
    rewrite and the external-config list are the two faces of the carried
    residual — the push really does go elsewhere, and disclosure is the whole
    mitigation. -/
def gitRoutingRow (routingVars : List String) (stateRoot : String)
    (toplevel : Option String) (rewrite : Option RemoteRewrite)
    (external : List ExternalPushConfig) : Json × Bool :=
  let mismatch := toplevel.elim false (· != stateRoot)
  let msgs :=
    (if routingVars.isEmpty then [] else
      [s!"inherited git routing environment ({String.intercalate ", " routingVars}) — tl ignores it (ADR-0012) and operates on the repository found by filesystem discovery, but plain `git` in this shell binds elsewhere; unset the variable(s) to align them"])
    ++ (if mismatch then
      [s!"the state directory ({stateRoot}) is not at the repository toplevel ({toplevel.getD ""}) — sharing binds that repository's refs/tl/log; this is expected under an explicit --dir, otherwise move the state directory to the toplevel"]
    else [])
    ++ (match rewrite with
        | some r =>
          [s!"remote '{r.remote}' push URL is rewritten from {r.configured} to {r.effective} by a url.*.insteadOf/pushInsteadOf rule — `tl sync` pushes to the rewritten URL; this is expected if you force a transport for the same repository (e.g. https→ssh), so verify {r.effective} is the intended repository — a rewrite in a git config tl cannot scrub (a relocated or hostile HOME) could otherwise redirect your task log"]
        | none => [])
    ++ (if external.isEmpty then [] else
        [s!"your push destination is set by global git config (~/.gitconfig), not this repository: {String.intercalate ", " (external.map (fun e => s!"{e.key}={e.value}"))} — `tl sync` follows it; if you did not configure this, an inherited or hostile HOME is redirecting your task log (tl cannot scrub HOME without breaking credentials — set these keys in the repo, or run under a HOME you control)"])
  (Json.mkObj <|
    [("name", Json.str "gitRouting"),
     ("status", Json.str (if msgs.isEmpty then "ok" else "warn")),
     ("routingVars", Json.arr (routingVars.map Json.str).toArray),
     ("stateRoot", Json.str stateRoot),
     ("repoToplevel", toplevel.elim Json.null Json.str),
     ("remoteRewrite", match rewrite with
        | some r => Json.mkObj [("remote", Json.str r.remote),
                                ("configured", Json.str r.configured),
                                ("effective", Json.str r.effective)]
        | none => Json.null),
     ("externalPushConfig", Json.arr (external.map (fun e =>
        Json.mkObj [("key", Json.str e.key), ("value", Json.str e.value)])).toArray)]
    ++ (if msgs.isEmpty then [] else
        [("message", Json.str (String.intercalate "; " msgs))]), false)

def cmdDoctor (dirOverride : Option String) (sync : Bool) : TlM CmdOut := do
  let d ← discover dirOverride
  -- --sync reconciles first; best-effort (doctor never fails — ADR-0008): keep
  -- the remote leg's result to report what reconciling did, or the error to
  -- disclose if it failed.
  let (synced, syncErr, syncNotes) ← if sync then
      (try (do let (_, r, pn) ← performSync d; pure (some r, none, pn))
       catch e => pure (none, some e.message, ([] : List String)))
    else pure (none, none, [])
  -- doctor reports damage instead of failing on it (ADR-0008 exemption)
  let replicaRow ← try
      match ← loadReplica d with
      | some r => pure (Json.mkObj [("name", Json.str "replica"), ("status", Json.str "ok"),
                                    ("replica", Json.str r.id)], false)
      | none => pure (Json.mkObj [("name", Json.str "replica"), ("status", Json.str "warn"),
                                  ("message", Json.str "no replica id yet — one mints on the first write")], false)
    catch e =>
      pure (Json.mkObj [("name", Json.str "replica"), ("status", Json.str "fail"),
                        ("message", Json.str e.message)], true)
  let clockRow ← try
      let _ ← loadClock d
      pure (Json.mkObj [("name", Json.str "clock"), ("status", Json.str "ok")], false)
    catch e =>
      pure (Json.mkObj [("name", Json.str "clock"), ("status", Json.str "fail"),
                        ("message", Json.str e.message)], true)
  let own ← try loadReplica d catch _ => pure none
  let now ← liftSys (fun e => .mk' .internal s!"{e}") nowMs
  -- doctor reports store damage instead of dying on it (the exemption); the
  -- skew check runs here too, so deferred foreign ops surface as clockSkew.
  -- It reads through the fold cache but never persists it (persist := false):
  -- doctor stays a pure diagnostic, mutating nothing — not even a cache.
  let (loaded, loadFail) ← try
      pure (← readStateCached d false (some now) (own.map (·.id)) (persist := false), none)
    catch e =>
      pure (materialize [] false (some now) (own.map (·.id)), some e)
  let v : View := View.ofLoaded d loaded now own
  let logRows := loaded.refused.map (fun r =>
    let isOwn := own.any (·.id == r.replicaId)
    (Json.mkObj [("name", Json.str "log"),
                 ("status", Json.str (if isOwn then "fail" else "warn")),
                 ("message", Json.str s!"segment {r.replicaId}.jsonl refused: {r.error.message}"),
                 ("segment", Json.str r.replicaId)], isOwn))
  let logOk := match loadFail with
    | some e =>
      [(Json.mkObj [("name", Json.str "log"), ("status", Json.str "fail"),
                    ("message", Json.str e.message)], true)]
    | none =>
      if loaded.refused.isEmpty then
        [(Json.mkObj [("name", Json.str "log"), ("status", Json.str "ok")], false)]
      else logRows
  -- graph diagnostics (incl. duplicate-of hygiene, ADR-0008) — all over the
  -- view's pre-hoisted present/edges, so doctor scans the OR-Set views once,
  -- not once per check plus three more inside cycleCount
  let cyc := cycleCount v
  -- parents of a present `i` over the hoisted parent-edge view (`pedges` already
  -- filters child-present, and `i` is the child) — avoids re-deriving presentEdges
  -- per issue (the O(N·E) doctor scan)
  -- parents of `i` via the parent-by-child bucket (was an O(E) `v.pedges` filter
  -- per present issue — the O(N·E) doctor scan); the count is order-independent
  let multi := (v.present.filter (fun i => (v.parents i).length > 1)).length
  let dangling := (v.edges.filter (fun (f, t, k) =>
    (k == EdgeKind.Blocks || k == EdgeKind.Parent)
      && (!v.has f || !v.has t))).length
  let dupIssues := (v.present.filter (fun i =>
    match v.duplicateOf i with
    | some t => !v.has t || (v.duplicateOf t).isSome
    | none => false)).length
  let graphBad := decide (cyc > 0)
  let graphRow := (Json.mkObj
    [("name", Json.str "graph"),
     ("status", Json.str (if graphBad then "fail"
                          else if multi + dangling + dupIssues > 0 then "warn" else "ok")),
     ("cycles", jnum cyc), ("multiParent", jnum multi),
     ("danglingEdges", jnum dangling), ("duplicateOfIssues", jnum dupIssues)], graphBad)
  -- stale claims: the window is the `tl.staleAfter` git config (a compact
  -- duration like 1h / 45m / 24h) — there is no hardcoded default (ADR-0013,
  -- amended). Unset ⇒ no stale verdict at all, so the row is omitted; set but
  -- unparseable ⇒ a row that teaches the format. A claim is stale when its
  -- issue is still InProgress and the claim is older than the window.
  let staleCfg ← Tl.Sync.gitConfig d "tl.staleAfter"
  let staleRows : List (Json × Bool) := match staleCfg with
    | none => []
    | some raw =>
      match Time.parseDurationMs? raw with
      | none =>
        [(Json.mkObj
           [("name", Json.str "staleClaims"), ("status", Json.str "warn"),
            ("message", Json.str s!"git config tl.staleAfter='{sanitizeSingle raw}' is not a valid duration — set e.g. 1h, 45m, or 24h")], false)]
      | some w =>
        let stale := v.present.filter (fun i =>
          (v.issueData i).statusOf == .InProgress
            && match (v.provFor i).claimedAt with
               | some h => now > claimStaleDeadlineMs h w
               | none => false)
        [(Json.mkObj <|
           [("name", Json.str "staleClaims"),
            ("status", Json.str (if stale.isEmpty then "ok" else "warn")),
            ("window", Json.str raw),
            ("count", jnum stale.length)]
           ++ (if stale.isEmpty then [] else
               [("ids", Json.arr (stale.map (Lean.Json.str ∘ displayId)).toArray),
                -- the next-step the signal otherwise dead-ends on (ADR-0013)
                ("message", Json.str s!"{stale.length} claim(s) stale past {raw} — take one over with `tl claim <id> --steal`, or check with the holder")]), false)]
  -- clock skew (ADR-0007): foreign ops dated beyond the window are deferred
  -- (held back) until wall-clock catches up — never fatal (convergent and
  -- self-healing). The lead is over both accepted and deferred ops (a deferred
  -- op is absent from maxHlc, so reading maxHlc alone would understate a
  -- far-ahead peer). Warn when an op is deferred OR a clock leads `now` by more
  -- than the (much smaller) warn threshold — so a notably-ahead-but-folded
  -- clock (e.g. a 9h TZ misconfig, within the 24h window) is still flagged.
  let leadMs := (max loaded.maxHlc loaded.maxDeferredHlc) / 2 ^ 16 - now  -- Nat sub: 0 if behind now
  let notablyAhead := leadMs > skewWarnMs
  let skewSegs := (loaded.deferred.map (·.1)).eraseDups
  let skewRow := (Json.mkObj <|
    [("name", Json.str "clockSkew"),
     ("status", Json.str (if !loaded.deferred.isEmpty || notablyAhead then "warn" else "ok")),
     ("deferredOps", jnum loaded.deferred.length),
     ("clockLeadMs", jnum leadMs)]
    ++ (if skewSegs.isEmpty then [] else
        [("segments", Json.arr (skewSegs.map Json.str).toArray)]), false)
  -- sync posture (ADR-0011 §2): local only — no remote contact unless `--sync`
  -- just ran a `tl sync`. upstream/lastSync/ahead from git config + the marker;
  -- the live behind-count is `doctor --sync`'s job (sync then read).
  let posture ← syncPostureOf d
  -- No `behind` field: it cannot be observed without a fetch, and a --sync
  -- reconcile converges it to 0 — so it would only ever be null/0, never a real
  -- count. Report `ahead` (local unsynced ops) + lastSync always, and what a
  -- --sync reconcile did (reconciled/pushed/pulled) when it ran.
  let warnSync := posture.upstream.isSome &&
    (syncErr.isSome || (synced.isNone && (posture.lastSyncMs.isNone || posture.ahead > 0)))
  let syncMsg :=
    match posture.upstream with
    | none => "no remote configured — sharing is local/stealth only"
    | some name =>
      match syncErr with
      | some err => s!"tried to reconcile with '{name}' but it failed ({err}) — showing local posture; run `tl sync`"
      | none =>
        match synced with
        | some r =>
          if !r.ran then s!"reconciled locally; remote '{name}' not configured for this branch"
          else s!"reconciled with '{name}': " ++ (if r.pushed then "pushed" else "nothing to push")
                 ++ (if r.pulled then ", pulled remote changes" else "")
        | none =>
          match posture.lastSyncMs with
          | none => s!"remote '{name}' configured but never synced — run `tl sync`"
          | some ms =>
            if posture.ahead > 0 then s!"{posture.ahead} local op(s) not yet synced — run `tl sync`"
            else s!"up to date as of the last sync ({Time.isoOfEpochMs ms})"
  let syncRow := (Json.mkObj <|
    [("name", Json.str "sync"),
     ("status", Json.str (if warnSync then "warn" else "ok")),
     ("upstream", posture.upstream.elim Json.null Json.str),
     ("lastSync", posture.lastSyncMs.elim Json.null (fun ms => Json.str (Time.isoOfEpochMs ms))),
     ("ahead", jnum posture.ahead)]
    ++ (match synced with
        | some r => [("reconciled", Json.bool true), ("pushed", Json.bool r.pushed),
                     ("pulled", Json.bool r.pulled)]
        | none => [])
    ++ [("message", Json.str syncMsg)], false)
  -- read-refresh marker vs on-disk segments (ADR-0016 §3 boundary): the marker
  -- keys off the ref OID, so an externally deleted/truncated foreign cache file
  -- under .tl/log/ stays unfixed until the ref next moves. Warn on a mismatch (a
  -- `tl sync` re-materializes unconditionally). Low-pri: .tl/ is managed by tl.
  let refMarkRow ← try
      match ← loadRefMark d with
      | none => pure (Json.mkObj [("name", Json.str "refMark"), ("status", Json.str "ok")], false)
      | some mark =>
        let refSegs ← Tl.Sync.readRefAt d mark
        let (diskSegs, _) ← readSegments d
        let ownId := own.map (·.id)
        -- a foreign ref segment whose on-disk copy is missing or byte-differs
        let stale := refSegs.filter (fun rs =>
          ownId != some rs.replicaId &&
            (match diskSegs.find? (·.replicaId == rs.replicaId) with
             | some ds => ByteArray.hash ds.bytes != ByteArray.hash rs.bytes
             | none => true))
        pure (Json.mkObj
          [("name", Json.str "refMark"),
           ("status", Json.str (if stale.isEmpty then "ok" else "warn")),
           ("staleSegments", jnum stale.length),
           ("message", Json.str (if stale.isEmpty then "on-disk segments match the refresh marker"
             else s!"{stale.length} on-disk segment(s) differ from the marked ref — run `tl sync` to re-materialize"))], false)
    catch e =>
      pure (Json.mkObj [("name", Json.str "refMark"), ("status", Json.str "warn"),
                        ("message", Json.str s!"could not check the refresh marker: {e.message}")], false)
  -- git runtime floor (ADR-0006): a teaching warn below 2.17, so an older git
  -- surfaces here rather than failing the plumbing cryptically later. doctor
  -- reports, never fails (ADR-0008) — any read error folds to the warn row, like
  -- the sibling shell-touching rows.
  let gitVer ← (try liftSys (fun e => .mk' .internal s!"{e}") Tl.Sync.gitVersion
                catch _ => pure none)
  let gitVerRow := gitVersionRow gitVer
  -- split-brain report (ADR-0012/ADR-0014 T7): inherited routing variables and
  -- the filesystem-discovery vs git-classification comparison, canonicalized
  -- so a symlinked temp/state path doesn't read as a false mismatch. Like the
  -- sibling shell-touching rows, any read error folds into a warn row.
  let routingRow ← try
      -- only the repository-rerouting vars are worth surfacing here (see
      -- repoRoutingVars): a benign inherited XDG_CONFIG_HOME is not a
      -- split-repository condition and must not be nagged about
      let present ← liftSys (fun e => .mk' .internal s!"{e}")
        (Tl.Sync.repoRoutingVars.filterM (fun v => return (← IO.getEnv v).isSome))
      let canon := fun (p : String) => do
        match ← (IO.FS.realPath p).toBaseIO with
        | .ok r => pure r.toString
        | .error _ => pure p
      let stateRoot ← liftSys (fun e => .mk' .internal s!"{e}")
        (canon (if d.base.isEmpty then "." else d.base))
      let top ← Tl.Sync.gitToplevel d
      let top ← liftSys (fun e => .mk' .internal s!"{e}") (top.mapM canon)
      -- the carried residual, made visible: a url.*.insteadOf /
      -- url.*.pushInsteadOf rewrite living in a config tl cannot scrub (a
      -- relocated HOME) silently redirects the push. `remote get-url --push`
      -- resolves the actual push target (applying both rewrite forms) without
      -- touching the network, so this stays on doctor's local-only path
      -- (ADR-0011 §2). The baseline is the *raw* push target — a deliberate
      -- `remote.<n>.pushurl` (else `.url`), read without rewrites — so a
      -- legitimately configured distinct push URL is not a false positive;
      -- only an insteadOf-style rewrite moves the resolved URL off it.
      -- also disclose the other face of the residual: the remote *selection*
      -- or its URL injected wholesale from ~/.gitconfig (tl.remote /
      -- remote.<n>.url / .pushurl), which redirects the push with no URL
      -- rewrite at all — a rewrite-only check would report ok.
      let (rewrite, external) ← (do
        match ← Tl.Sync.resolveRemote d with
        | none => pure (none, [])
        | some remote =>
          -- rewrite: compare EVERY raw push target against what git resolves
          -- it to (both lists in config order; git pushes to every pushurl, so
          -- a rewrite of a non-first push URL is invisible to a single-URL
          -- read). The first raw target that resolves to a different URL is the
          -- disclosed redirect.
          let allPushurl ← Tl.Sync.gitConfigAll d s!"remote.{remote}.pushurl"
          let hasPushurl := !allPushurl.isEmpty
          let rawPush ← if hasPushurl then pure allPushurl
                        else Tl.Sync.gitConfigAll d s!"remote.{remote}.url"
          let effPush ← Tl.Sync.effectivePushUrls d remote
          let rewrite := (rawPush.zip effPush).find? (fun p => p.1 != p.2)
            |>.map (fun p => ({ remote, configured := p.1, effective := p.2 } : RemoteRewrite))
          -- external: push-destination keys sourced from the global scope,
          -- mirroring resolveRemote's chain — the winning selector (tl.remote,
          -- else branch.<current>.remote; a literal "origin" has no config to
          -- inject), then the selected remote's push targets (every global
          -- pushurl value is an extra push target regardless of a local one;
          -- else the url when no pushurl is set). Built from small pre-sized
          -- lists (no repeated `++ [x]`).
          let globalOf := fun (key : String) => do
            if ← Tl.Sync.configFromGlobal d key then
              pure [({ key, value := (← Tl.Sync.gitConfigScopedAll d "--global" key).head?.getD "" }
                      : ExternalPushConfig)]
            else pure ([] : List ExternalPushConfig)
          let selectorExt ← (do
            if (← Tl.Sync.gitConfig d "tl.remote").isSome then globalOf "tl.remote"
            else match ← Tl.Sync.currentBranch d with
              | some b => globalOf s!"branch.{b}.remote"
              | none => pure [])
          let pushurlExt := (← Tl.Sync.gitConfigScopedAll d "--global" s!"remote.{remote}.pushurl").map
            (fun v => ({ key := s!"remote.{remote}.pushurl", value := v } : ExternalPushConfig))
          let urlExt ← if hasPushurl then pure [] else globalOf s!"remote.{remote}.url"
          pure (rewrite, selectorExt ++ pushurlExt ++ urlExt))
      pure (gitRoutingRow present stateRoot top rewrite external)
    catch e =>
      pure (Json.mkObj [("name", Json.str "gitRouting"), ("status", Json.str "warn"),
                        ("message", Json.str s!"could not check git routing: {e.message}")], false)
  let rows := [replicaRow, clockRow] ++ logOk ++ [graphRow] ++ staleRows ++ [skewRow, syncRow, refMarkRow, routingRow, gitVerRow]
  let healthy := rows.all (fun (_, failed) => !failed)
  let data := Json.mkObj
    [("healthy", Json.bool healthy),
     ("checks", Json.arr (rows.map (·.1)).toArray)]
  let human := (if healthy then "healthy" else "PROBLEMS FOUND") ++
    s!" — {rows.length} checks ({(rows.filter (·.2)).length} failing)"
  return { data, human, notes := syncNotes }

/-- `tl sync`: reconcile through the shared `refs/tl/log` — the local-first leg
    (ADR-0016 §1: publish the own segment, absorb same-machine siblings), then
    the remote leg (ADR-0001 §5: fetch → union → push) when one is configured.
    The `--json` `data` carries one leg-result object per leg; `remote` is null
    only outside a git repo, and `{ran:false, reason:"no-upstream"}` when no
    remote is configured. -/
def cmdSync (dirOverride : Option String) : TlM CmdOut := do
  let d ← discover dirOverride
  -- stealth (ADR-0001 §7): fail closed rather than silently no-op, so a stealth
  -- repo never leaks and the user learns how to un-stealth (the `code` is stable).
  if ← isStealth d then
    throw { code := .stealthMode
            message := s!"this is a stealth repo (`tl init --stealth`): task state is local-only and never shared, so `tl sync` is disabled — to start sharing, remove the stealth marker `{d.stealthDisplayPath}` and run `tl sync` again; the conversion migrates nothing (ids and history are unchanged — see `{d.readmeDisplayPath}`)"
            context := [] }
  let (l, r, pnotes) ← performSync d
  let localLeg : Json :=
    if l.ran then
      Json.mkObj
        [("ran", Json.bool true), ("published", Json.bool l.published),
         ("absorbed", Json.arr (l.absorbed.map Json.str).toArray),
         ("tip", l.tip.elim Json.null Json.str)]
    else Json.mkObj [("ran", Json.bool false)]
  let remoteLeg : Json :=
    if !l.ran then Json.null  -- no git repo ⇒ no transport at all
    else if r.ran then
      Json.mkObj
        [("ran", Json.bool true), ("remote", Json.str r.remote),
         ("pushed", Json.bool r.pushed), ("pulled", Json.bool r.pulled),
         ("tip", r.tip.elim Json.null Json.str)]
    else Json.mkObj [("ran", Json.bool false), ("reason", Json.str "no-upstream")]
  let data := Json.mkObj [("local", localLeg), ("remote", remoteLeg)]
  let human :=
    if !l.ran then
      "not a git repository — tl shares through refs/tl/log; run inside a git repo"
    else
      let localPart :=
        (if l.published then "published your changes" else "already up to date")
        ++ (if l.absorbed.isEmpty then "" else s!"; absorbed {l.absorbed.length} sibling(s)")
      let remotePart :=
        if !r.ran then "; no remote configured (no-upstream) — shared locally only"
        else
          let pushed := if r.pushed then "pushed" else "nothing to push"
          let pulled := if r.pulled then ", pulled remote changes" else ""
          s!"; remote '{r.remote}': {pushed}{pulled}"
      s!"Synced: {localPart}{remotePart}"
  return { data, human, notes := pnotes }

/-- The committed discovery pointer (ADR-0011 §3): the one line an agent file
    carries so any harness surfaces `tl` with zero config. -/
def discoveryPointer : String :=
  "task state lives in `tl` (a git-native tracker) — run `tl ready --json` for what to work on and `tl doctor` for health; load the tl skill or `tl help --json` for how to drive it."

/-- The gitignored `.tl/README.md` primer (ADR-0011 §3) for anyone who opens
    `.tl/` directly. -/
def readmePrimer : String :=
  "# tl — task tracker\n\n" ++
  "This directory holds tl's task state for the project. It is gitignored and\n" ++
  "managed by tl — do not edit it by hand. State is an append-only op log under\n" ++
  "`log/`; every read is a fold over it.\n\n" ++
  "  tl ready                 what to work on now (ranked, unblocked)\n" ++
  "  tl claim <id>            take a ready item\n" ++
  "  tl close <id> --as done  finish it\n" ++
  "  tl why <id>              why something is blocked\n" ++
  "  tl sync                  share: publish + absorb via the refs/tl/log git ref\n" ++
  "  tl doctor                project health\n" ++
  "  tl help                  all commands (tl help --json for the grammar)\n\n" ++
  "Sharing modes: state initialized outside a git repository stays local-only\n" ++
  "and starts sharing on the first `tl sync` after the directory becomes a git\n" ++
  "repo with a remote. A stealth project (marker file `local/stealth` in this\n" ++
  "directory) never shares; to convert it, delete that marker and run `tl sync`\n" ++
  "— nothing migrates: log format, ids, and history are unchanged.\n"

/-- Where `init`/`import` place state (ADR-0001 §4, ADR-0012): the `--dir`/`TL_DIR`
    override wins; else the enclosing repo's toplevel; outside any repo, the cwd
    (with a local-only note). The placement walk honors the same boundaries as
    discovery: a `GIT_CEILING_DIRECTORIES` entry stops the search (repo-less
    placement, with a note), and a bare-gitdir layout refuses with a teaching
    usage error — a bare repository has no working tree to hold `.tl` state
    (`--dir` remains the deliberate escape hatch: an explicit target is never
    walked or refused). Shared by `cmdInit` and `cmdImport`'s implicit init. -/
def initTarget (dirOverride : Option String) : TlM (System.FilePath × List String) := do
  let override : Option String ← match dirOverride with
    | some p => pure (some p)
    | none => liftSys (fun e => .mk' .internal s!"environment read failed: {e}") (IO.getEnv "TL_DIR")
  match override with
  | some p => pure (System.FilePath.mk p, [])
  | none =>
    let cwd ← liftSys (fun e => .mk' .internal s!"{e}") IO.currentDir
    let ceilingList ← ceilingDirs
    -- `.ok` = repo toplevel found; `.error note` = no repo (the note explains
    -- why when a ceiling stopped the search early). Like discovery, ceilings
    -- bound the ascent only — the starting directory is always examined
    -- (git semantics, ADR-0012).
    let rec findRoot (dir : System.FilePath) (fuel : Nat) (atStart : Bool) :
        TlM (Except (List String) System.FilePath) := do
      match fuel with
      | 0 => return .error []
      | fuel + 1 =>
        if !atStart && ceilingList.contains dir.toString then
          return .error [s!"GIT_CEILING_DIRECTORIES stopped the repository search at {dir}"]
        if ← liftSys (fun e => .mk' .internal s!"{e}") (hasGitBoundary dir) then
          return .ok dir
        else if ← liftSys (fun e => .mk' .internal s!"{e}") (isGitDirLayout dir) then
          throw (.mk' .usage
            s!"cannot initialize tl in a git repository directory ({dir}): a bare repository has no working tree for .tl state — run `tl init` in a worktree or clone of it, or pass --dir to place state at an explicit directory; a bare repository still works as a sync remote")
        else
          match dir.parent with
          | some p => if p == dir then return .error [] else findRoot p fuel false
          | none => return .error []
    match ← findRoot cwd 256 true with
    | .ok root => pure (root / ".tl", [])
    | .error ceilingNote => pure (cwd / ".tl", ceilingNote ++
        ["not inside a git repository — state stays local-only until used under a git repo with a remote"])

def cmdInit (dirOverride : Option String) (stealth : Bool) : TlM CmdOut := do
  let (target, note) ← initTarget dirOverride
  let created ← initAt target
  let dirs := Dirs.ofStatePath target.toString
  let replica ← loadReplica dirs
  -- stealth (ADR-0001 §7): mark at *creation* so sharing stays disabled. The mode
  -- is fixed at creation — `--stealth` does not retroactively convert an existing
  -- repo, and a plain re-init never un-stealths. `stealthy` is the resulting state.
  if stealth && created.isSome then markStealth dirs
  let stealthy ← isStealth dirs
  let stealthNote : List String :=
    if stealthy then
      [s!"stealth: task state is local-only and never shared — `tl sync` is disabled and auto-sync stays off; to start sharing later, remove `{dirs.stealthDisplayPath}` and run `tl sync`"]
    else if stealth then
      ["--stealth ignored: already initialized and not stealth — the sharing mode is fixed at creation"]
    else []
  -- auto-sync default (ADR-0021 §5 / ADR-0016 §4): ON for a linked worktree,
  -- opt-in elsewhere, never overriding an existing knob. Stealth never auto-syncs.
  let autosyncNote ← if stealthy then pure [] else Tl.Sync.autoSyncInitDefault dirs
  -- write/refresh the gitignored primer (ADR-0011 §3), through the no-follow
  -- shim like every other .tl write
  writeLocalFile dirs (dirs.tlRel ++ "/README.md") readmePrimer
  -- the committed discovery pointer: suggest adding it to a root agent file;
  -- never auto-edit the user's committed files (no-surprise ethos — ADR-0011
  -- §3, decision: print, do not write; create no file when none exists). Stealth
  -- never offers it — a committed breadcrumb is the one thing stealth must avoid.
  let pointerNote : List String ← if stealthy then pure [] else do
    let rootDir := target.parent.getD (System.FilePath.mk ".")
    let mut existing : List String := []
    for f in ["AGENTS.md", "CLAUDE.md", "GEMINI.md"] do
      if ← liftSys (fun e => .mk' .internal s!"{e}") (rootDir / f).pathExists then
        existing := existing ++ [f]
    if existing.isEmpty then
      pure [s!"to make tl discoverable to agents, add this line to a root agent file (e.g. AGENTS.md):\n    {discoveryPointer}"]
    else
      pure [s!"to make tl discoverable, add this line to {String.intercalate " / " existing} if not already present:\n    {discoveryPointer}"]
  let data := Json.mkObj
    [("root", Json.str target.toString),
     ("replica", (replica.map (·.id)).elim Json.null Json.str),
     ("created", Json.bool created.isSome),
     ("stealth", Json.bool stealthy)]
  let human := match created with
    | some r => s!"Initialized tl in {target} (replica {r.id})" ++ (if stealthy then " — stealth (local-only)" else "")
    | none => s!"{target} already initialized — nothing to do (idempotent)"
  -- git runtime floor (ADR-0006): warn at setup if a present git is below 2.17, so
  -- the prerequisite is caught now rather than as a cryptic plumbing failure. git
  -- absent ⇒ no note: init can create local-only state outside any repo.
  -- a git read error must never fail init (it can create local-only state outside
  -- any repo) — fold to no note, like the git-absent case
  let gitFloorNote ← (try
      liftSys (fun e => .mk' .internal s!"{e}") (do
        match ← Tl.Sync.gitVersion with
        | some v => if Tl.Sync.gitMeetsFloor v then pure ([] : List String)
                    else pure [s!"git {v.1}.{v.2} is below the required floor git ≥ 2.17 — tl's git plumbing may fail cryptically; upgrade git"]
        | none => pure [])
    catch _ => pure ([] : List String))
  return { data, human, notes := note ++ stealthNote ++ pointerNote ++ autosyncNote ++ gitFloorNote }

/-- Read the import input: a single JSONL file, or a directory of `*.jsonl`
    (sorted by name, unioned). Returns the non-blank lines (ADR-0005). -/
def readImportLines (path : String) : TlM (List (String × String)) := do
  let fp := System.FilePath.mk path
  let md ← liftSys (fun e => .mk' .notFound s!"cannot read import path '{path}': {e}") fp.metadata
  let fileContents : List (String × String) ← match md.type with
    | .dir =>
      let entries ← liftSys (fun e => .mk' .internal s!"{e}") fp.readDir
      let files := (entries.toList.filter (·.fileName.endsWith ".jsonl")).map (·.path)
      let sorted := files.mergeSort (fun a b => decide (a.toString ≤ b.toString))
      sorted.mapM (fun f => do
        let c ← liftSys (fun e => .mk' .internal s!"reading {f}: {e}") (IO.FS.readFile f)
        -- the file's *name*, not its absolute path: re-importing the same-named
        -- file from any location stays byte-stable (ADR-0005 determinism)
        pure ((f.fileName).getD f.toString, c))
    | _ =>
      let c ← liftSys (fun e => .mk' .internal s!"reading {path}: {e}") (IO.FS.readFile fp)
      pure [((fp.fileName).getD path, c)]
  -- (source-file, line) for every non-blank line — file provenance feeds the
  -- deterministic (source-file, source-id) ordering + fingerprint (ADR-0005)
  return fileContents.flatMap (fun (f, c) =>
    (c.splitOn "\n").filterMap (fun l => if l.trimAscii.toString.isEmpty then none else some (f, l)))

/-- The import input's total byte size from file *metadata* — no content is read,
    so the resource bound (ADR-0005) is enforced before a huge/hostile input is
    loaded into memory. A directory sums its `*.jsonl` files. -/
def importInputBytes (path : String) : TlM Nat := do
  let fp := System.FilePath.mk path
  let md ← liftSys (fun e => .mk' .notFound s!"cannot read import path '{path}': {e}") fp.metadata
  match md.type with
  | .dir =>
    let entries ← liftSys (fun e => .mk' .internal s!"{e}") fp.readDir
    let files := (entries.toList.filter (·.fileName.endsWith ".jsonl")).map (·.path)
    files.foldlM (fun acc f => do
      let m ← liftSys (fun e => .mk' .internal s!"reading {f}: {e}") f.metadata
      pure (acc + m.byteSize.toNat)) 0
  | _ => pure md.byteSize.toNat

/-- Whether the repo already holds task state: any non-empty local segment, or a
    present `refs/tl/log` (the `--force` gate's "non-empty op-log", ADR-0005). The
    ref check is best-effort — outside a git repo it is simply absent. -/
def logIsNonEmpty (d : Dirs) : TlM Bool := do
  let (segs, _) ← readSegments d
  if segs.any (fun s => s.bytes.size > 0) then return true
  match ← ((Tl.Sync.refTip d).run.toBaseIO : IO _) with
  | .ok (.ok (some _)) => return true
  | _ => return false

/-- `tl import <path>` (ADR-0005): parse tl's bulk-import format into a
    deterministic seed op-log under an import replica. Implicit-inits a fresh
    repo; refuses a non-empty log without `--force`; bounds the input size unless
    `--allow-large`/`--max`. Both gates are separate — neither flag bypasses the
    other (ADR-0014 T6). Every clamp, skipped edge, and fallback time is disclosed. -/
def cmdImport (dirOverride : Option String) (path : String) (sourceTagArg : Option String)
    (force allowLarge : Bool) (maxArg : Option Nat) : TlM CmdOut := do
  let opts : Tl.Import.ImportOptions :=
    { sourceTag := sourceTagArg.getD "import", force, allowLarge, maxBytes := maxArg.getD 5000000 }
  -- resource-bounds gate from file metadata, BEFORE reading any content into
  -- memory (so a huge/hostile input is refused without loading it; ADR-0005)
  let inputBytes ← importInputBytes path
  if inputBytes > opts.maxBytes && !allowLarge then
    throw (.mk' .forceRequired s!"import input is {inputBytes} bytes, over the {opts.maxBytes}-byte bound — pass --allow-large, or raise --max <bytes>, for a trusted local migration")
  let fileLines ← readImportLines path
  -- parse every line; fail-closed on a malformed line or a duplicate source id.
  -- `seen` is a set (O(1)); buildSeed re-sorts, so the cons order is irrelevant.
  let mut records : List (String × Tl.Import.ImportRecord) := []
  let mut parseDisc : List String := []
  let mut seen : Std.HashSet String := ∅
  for (f, line) in fileLines do
    -- per-line size gate BEFORE parsing, so a pathological line cannot drive the
    -- JSON parser unbounded (ADR-0005 granular bounds); shares the --allow-large arm
    if line.utf8ByteSize > Tl.Import.Bounds.rawLineBytes && !allowLarge then
      throw (.mk' .forceRequired s!"import line in {f} is {line.utf8ByteSize} bytes, over the {Tl.Import.Bounds.rawLineBytes}-byte per-line bound — one record should not be this large; split the source, or pass --allow-large for a trusted migration")
    let (r, dsc) ← MonadExcept.ofExcept (Tl.Import.parseRecord line)
    if seen.contains r.sourceId then
      throw (.mk' .malformedLine s!"import has two records with id '{r.sourceId}' — source ids map 1:1 to a tl id, so they must be unique")
    seen := seen.insert r.sourceId
    records := (f, r) :: records
    parseDisc := parseDisc ++ dsc
  -- granular resource bounds + the derived-seed bound (ADR-0005): adjudicated on
  -- the pure records/seed BEFORE any `.tl/` is created, so a bounds refusal never
  -- leaves a freshly-initialized repo behind
  let boundsDisc ← MonadExcept.ofExcept (Tl.Import.checkBounds opts records)
  let result0 := Tl.Import.buildSeed opts records parseDisc
  let seedDisc ← MonadExcept.ofExcept (Tl.Import.checkSeedSize opts result0)
  let result := { result0 with disclosures := result0.disclosures ++ boundsDisc ++ seedDisc }
  -- resolve the target + implicit init (the documented exception to no-auto-init)
  let (target, initNotes) ← initTarget dirOverride
  let _ ← initAt target
  let d := Dirs.ofStatePath target.toString
  -- the --force gate (distinct from the bounds gate): refuse to double-seed
  if (← logIsNonEmpty d) && !force then
    throw (.mk' .forceRequired "this repo already holds task state (a local segment or refs/tl/log) — `import` refuses to double-seed; pass --force to append the import as a fresh seed")
  let bytes := String.join (result.lines.map (· ++ "\n"))
  Tl.Sync.writeForeignSegment d result.segmentReplica bytes.toUTF8
  let notes := result.disclosures ++ initNotes
  let data := Json.mkObj
    [("issues", jnum result.issueCount), ("ops", jnum result.opCount),
     ("replica", Json.str result.segmentReplica), ("source", Json.str opts.sourceTag),
     ("disclosures", Json.arr (result.disclosures.map (Json.str ∘ sanitizeSingle)).toArray)]
  return { data
           human := s!"Imported {result.issueCount} issue(s), {result.opCount} ops, under source '{sanitizeSingle opts.sourceTag}'"
                    ++ (if result.disclosures.isEmpty then "" else s!" ({result.disclosures.length} disclosure(s))")
           notes := notes.map sanitizeSingle }

/-- The product version (keep in lockstep with lakefile.lean's package
    version; `tl version` is the single user-facing source). -/
def productVersion : String := "0.1.0"

def cmdVersion : CmdOut :=
  { data := Json.mkObj [("version", Json.str productVersion), ("logFormat", jnum supportedVersion)]
    human := s!"tl {productVersion} (log format v{supportedVersion})" }

/-- `tl licenses` / `tl --licenses`: the third-party notice, embedded in the
    binary (ADR-0006 compliance deliverable). Human output is the notice
    itself; `--json` wraps the same text so the surface has human/json parity.
    The human string drops the notice's final newline because the stream layer
    prints it with `IO.println` — this keeps the process stdout byte-equal to
    the `THIRD-PARTY-LICENSES` file (spawned-binary test). -/
def cmdLicenses : CmdOut :=
  { data := Json.mkObj [("text", Json.str thirdPartyLicenses)]
    human := if thirdPartyLicenses.endsWith "\n"
             then (thirdPartyLicenses.dropEnd 1).toString else thirdPartyLicenses }

end Tl.Cli
