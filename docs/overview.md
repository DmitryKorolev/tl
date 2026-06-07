# Overview — what tl proves, tests, and trusts

> Implementation underway. This is the claim table: what the verified core
> proves, what tests cover, and what is trusted at the boundary. The kernel
> (`Tl/Crdt/`, `Tl/Kernel/`) is fully defined and total, and a first tranche of
> theorems is proved; the **Proof status** subsection below records, per row,
> what is *proved* versus what is a *tracked residual* (defined-and-total but
> with its soundness/completeness proof still outstanding — decomposed and
> recorded here per AGENTS.md Definition-of-Done #5, never downgraded to a test).
> The tested I/O shell (`Tl/Format`, `Tl/Clock`, `Tl/Cli`, …) is not yet built.

The discipline: prove inside the TCB, test outside it
([ADR-0004](adr/ADR-0004-verified-kernel-tcb-boundary.md)). A claim is
either a Lean theorem about the kernel, a test about the I/O shell, or a
carried assumption (the Trusted section below) — never a vibe.

## Proved (kernel theorems)

| Claim | Statement (shape) | ADR |
|---|---|---|
| CRDT convergence | the state join (issues/edges/labels OR-Sets, scalar LWW-registers, and the per-key-LWW `meta` map) is commutative, associative, idempotent ⇒ replicas with the same op-set materialize identical state | 0002, 0004 |
| Fold order/dup-insensitivity | `fold (π ops) = fold ops`; `fold (ops ++ ops) = fold ops` (the git-concat requirement) | 0001, 0004 |
| `ready` soundness + completeness | `i ∈ ready s now ↔ open ∧ ¬epic ∧ (deferUntil).all (·≤now) ∧ every blocker's effectiveStatus ∈ {done,cancelled}` (epic blockers discharge by rollup, not stored status) | 0004, 0003, 0010 |
| Totality on cyclic/dangling graphs | `ready` / `apply` / `effectiveStatus` / cycle detection total with no acyclicity precondition; dangling edges inert | 0003, 0004 |
| Honest liveness (deadlock-freedom) | one-directional: an open non-epic non-deferred issue with all blockers closed ⇒ `ready` non-empty; a stuck live working set ⇒ a cycle in the readiness-dependency relation `≺` (blocks edges + epic-rollup-on-open-children; pure or mixed-kind) — the only tool-pathological stall | 0003, 0004 |
| Cycle diagnostic correctness | `cycles s kind` = one canonical simple-cycle witness per cyclic SCC of that kind; `cycles s` also reports readiness-deadlock `≺`-cycles (mixed blocks+parent) so a stuck live set is never undiagnosed (exactly the cyclic SCCs + `≺`-cycles; polynomial, total) | 0003, 0004 |
| Epic rollup | unless manually cancelled, `effectiveStatus e = done ↔ all children closed`; cancel takes precedence; total incl. parent-cycles | 0003 |
| Invariant preservation | one `apply` preserves valid-status; inherited by every `Op` (endpoint-existence & acyclicity deliberately not invariants — tolerated at read time) | 0004 |
| Close-monotonicity | a single `close` op only unblocks: `ready (close s i) ⊇ ready s \ {i}`; `--cascade` is several such ops, each monotonic, so the composition is too | 0004 |
| Ready ordering is total | rank ends in the unique `id` ⇒ the `ready` order is unique and deterministic given the same state and `now` (a stable ranked queue to choose from; no atomic take-the-top); the critical-path-weight key is a total function on cyclic graphs | 0004 |
| frame lemma | `relate`/`unrelate`, any `meta` write, any `labels` write, and the per-op `actor` provenance field change neither `ready` nor rollup (the side-channels stay out of the verified core) | 0003, 0008, 0013 |
| CvRDT inflation / monotonicity | `s ≤ apply s o` (each op only moves up the lattice) ⇒ `ops ⊆ ops' → fold ops ≤ fold ops'` (a merge never loses information); with fold-dup-insensitivity, the full state-CvRDT pair. Op-granular: `apply (apply s o) o = apply s o` (at-least-once delivery safe) | 0002, 0004 |
| `ready` time-monotonicity | `now ≤ now' → ready s now ⊆ ready s now'` — time alone never un-readies an item (the defer-dual of close-monotonicity) | 0010, 0004 |
| `why` / `unblocks` correctness | `why s i` = exactly the transitive *unclosed* `blocks`-blockers of `i`; `unblocks s i` = exactly the set closing `i` newly readies; total on cyclic/dangling (same reach⁺ machinery as the weight key) | 0003, 0004 |

### Proof status (current)

What is **proved** in `Tl/Kernel/Theorems.lean` (and the layer files), checked
`#print axioms`-clean (only `propext` / `Classical.choice` / `Quot.sound`):

- **Thm 1 — join-semilattice.** `State.merge_comm/assoc/idem` over the whole
  product, composed from the per-layer laws (`AMap`, `FinSet`, `Reg`/`MetaMap`,
  `OrSet`, `IssueData`). `AMap.ext` is axiom-free.
- **Thm 2 — order/duplicate insensitivity.** `fold_eq_of_mem_iff` (same op-set ⇒
  identical state — strong eventual convergence), `fold_perm`, `fold_append_self`.
- **Thm 3 — invariant preservation.** `invariant_apply` (valid status is
  type-level; the enum/`Fin 5` make illegal values unrepresentable).
- **Thm 4 — `ready` soundness + completeness.** `mem_ready_iff`: membership in the
  ranked queue is exactly the readiness predicate (`rankSort_perm` shows the sort
  filters nothing). *Totality* is discharged by `ready`/`effectiveStatus`/`weight`/
  `cycles` being total Lean definitions (fuel / bounded `iterateN`), no `sorry`.
- **Thm 8 — CvRDT inflation + idempotent re-delivery.** `le_apply`,
  `fold_le_of_subset`, and `apply_idem`.
- **Thm 9 — `ready` time-monotonicity.** `ready_time_mono` (via `deferOk_mono`).

**Tracked residuals** — defined and total in the kernel, soundness/completeness
proof still outstanding (decomposed below; *not* downgraded to tests, per
Definition-of-Done #5):

- **Epic rollup correctness (ADR-0003).** `effectiveStatus` is defined and total
  (fuel-bounded over the parent graph, `Rollup.lean`); the residual is the
  *fuel-adequacy* lemma — on an acyclic parent graph the present-issue-count fuel
  is enough that the rollup equals the spec (Done iff all children closed,
  manual-cancel precedence), and a parent cycle provably falls back to not-done.
- **Thm 5 — honest liveness / deadlock-freedom.** The `≺` relation and its
  diagnostic are defined (`Cycles.precSucc`/`precCycles`); the residual is the
  one-directional theorem (acyclic `≺` over a live working set ⇒ a `≺`-minimal
  ready leaf).
- **Thm 6 — cycle-diagnostic correctness.** `cycles`/`precCycles` are defined and
  total; the residual is that `reachClosure` computes exact transitive
  reachability (the saturation-in-`|nodes|`-steps lemma) and hence that the
  reported SCCs are exactly the cyclic ones.
- **Thm 7 — close-monotonicity.** `close` is a `setFields` op; the residual is
  `ready (apply s close) ⊇ ready s \ {i}` and the ancestor-rollup-monotonicity
  lemma it carries.
- **Thm 10 — `why` / `unblocks` correctness.** Both are defined and total
  (`Ready.lean`); the residual is soundness/completeness, sharing the
  `reachClosure`-saturation lemma with thm 6.
- **Frame lemma.** The side-channel ops' deltas (`metaSet`/`labelAdd`/
  `labelRemove`/`relate`) leave the issue/edge OR-Sets and the status/defer
  registers untouched (mergewith-`none`/`empty` identities); the residual is the
  `effectiveStatus`/`ready` congruence over that preserved projection.

Reserved (proved when its feature is built). *Compaction preserves the
fold* — `fold ops = snapshot(F) ⊕ fold(ops above F)` for a causally-closed
frontier `F` — the obligation any future `tl compact` must discharge so a
snapshot can never change the materialized state (deferred with compaction,
ADR-0008).

## Tested (I/O shell, outside the TCB)

| Claim | How |
|---|---|
| Serialization round-trip | `parse (render m) = m` over the typed-`Op`+`unknown` model (canonical render); `render (parse l) = l` on canonical lines; preserve-unknown (0008) |
| beads import fidelity | differential test vs `.beads` fixtures (0005) |
| HLC clock implementation | clock-file parse/render, local-event and observe-remote update rules, backward-clock and overflow cases (0007); real durable monotonic persistence remains Trusted below |
| encoding order-preservation | the kernel proves the LWW/OR-Set order over the *decoded* `(hlc, replica, nonce)` integer triple (`Tl.Crdt.Stamp`) and delegates to the shell that the canonical wire strings (16-hex / 13 / 26 Crockford chars) compare bytewise/lexicographically in the *same* order — the linchpin that ties the proved kernel order to the on-disk bytes. Tested by cross-checking string compare against the `Stamp` order on sampled triples (0007/0008) |
| CLI contract | exit codes, JSON envelope (`schemaVersion`/`ok`/`data`\|`error`), command dispatch, the verb→delta mapping (0008) |
| ref sync transport | `refs/tl/log` plumbing (read/write), segment materialization, the complete-line union merge, push-rejection retry, no-upstream, and auto-sync error handling; the local-first leg + read-time ref-OID refresh for same-machine worktree sharing (0001/0016) |
| "superseded by …" signal | shell compares the converged winning `assignee` vs this replica's own latest `claim` op (0013); replica-relative, not a kernel property |

## Trusted (carried assumptions)

This section is the home for carried assumptions — properties relied on
but neither proved in-kernel nor fully testable (AGENTS.md tier 3). Any such
property must be listed here explicitly, never relied on silently. Current
entries: replica-id uniqueness (scoped: holds absent a sub-git byte-copy
of `.tl/local/` — `cp -r`, an image snapshot, a CI cache; the nonce keeps LWW
total even then, so this guards segment-ownership, not convergence, ADR-0007);
the deterministic import replica-id is explicitly scoped out of live
replica ownership and used only for one-shot seed logs (ADR-0005);
issue-id uniqueness (negligible ~4e-13 birthday collision at 80-bit
SHA-256, sibling to the above, ADR-0007); nonce uniqueness within a `(HLC, replica-id)` (128-bit CSPRNG, negligible collision in that tiny space, ADR-0007); HLC monotonic persistence;
git ref transport (`tl sync` moves the `refs/tl/log` bytes; the old
branch-tracked history-rewrite hazard — force-push/amend dropping log ops — is
moot now that the log lives in its own ref, not the user's commits,
ADR-0001); and
clocks/IDs/actor entering as data — each discharged by a test or trusted by
construction when implementation begins.

The trust boundary and threat model (who may read/write, and the threats
accepted or carried) are recorded in ADR-0014. Its tier-3 carried
assumptions: git access-control is `tl`'s only access control (a CRDT cannot
reject a write, so any party git lets push the ref is a trusted writer; any
reader sees all state and history); supply-chain integrity rests on the
release/signing identity and the Lean TCB (reproducibility binds binary→source,
not source→correctness); and agent-side prompt-injection resistance is the
consuming harness's job — `tl` labels content untrusted, sanitizes bytes, bounds
size, and discloses provenance, but cannot guarantee an LLM resists fenced data.

Local filesystem (ADR-0015). `O_APPEND` / `FILE_APPEND_DATA` write-atomicity
and working advisory locks are assumed on the local filesystem; a `.tl/`
shared over a network FS (NFS/SMB) is documented-unsupported — convergence still
holds via the per-op nonce, but ownership and HLC monotonicity do not. The Win32
bindings of these primitives (ADR-0015 §7) are best-effort on native Windows
(our Tier-2, ADR-0006); WSL is the Supported Windows path.

The TCB is: the Lean kernel (+ its checker), the file/JSONL I/O, git, and the
system clock. Nothing else.
