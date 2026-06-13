# ADR-0021 — Auto-sync: a synchronous, best-effort local-leg publish

- Status: Accepted
- Date: 2026-06-11

## Context

[ADR-0016](ADR-0016-worktree-sharing-local-first-sync.md) §4 decided that
auto-sync defaults on for linked worktrees (the local leg is free), and
[ADR-0001](ADR-0001-op-log-on-dedicated-ref.md) §5 sketched it as "publish the
ref after a mutation (best-effort, async)." But the *process model* was left
unpinned (the design-backlog "auto-sync process model" item): synchronous vs a
background process, whether to debounce, the failure surface, and exactly which
legs run. A daemon is out of scope by construction ([ADR-0001](ADR-0001-op-log-on-dedicated-ref.md)
— the server-less design). This ADR pins the model so the overview's "tested
auto-sync error handling" has a concrete target.

The key fact that shapes the decision: the **local leg is free and fast** (a
few git-plumbing subprocesses, ~tens of ms, zero network) and it is exactly
what makes a sibling worktree's read-time refresh ([ADR-0016](ADR-0016-worktree-sharing-local-first-sync.md)
§3) observe a write — the writer must publish its segment into the shared
`refs/tl/log` for the sibling's O(1) OID check to fire. The **remote leg is
networked** (and would push to a configured remote, e.g. GitHub, on every
mutation).

## Decision

### 1. Scope — the local leg only

Auto-sync runs **`syncLocal`** (publish this replica's segment into the shared
`refs/tl/log`, absorb siblings into `.tl/log/`), and **not** the remote leg.
The local leg is free and is precisely what cross-worktree visibility needs;
the remote leg is networked and auto-pushing to a remote on every `tl claim`
would be slow, surprising, and the wrong default. **Cross-clone propagation
stays explicit** (`tl sync`). (A future opt-in `tl.autosync.remote` could add a
best-effort async remote push for fully-sandboxed agents — deferred, not now.)

### 2. Synchronous, not a background process

Because the local leg is cheap, it runs **inline** after the mutation — after
the mutation lock is released (the local leg is lock-free,
[ADR-0016](ADR-0016-worktree-sharing-local-first-sync.md) §3). This avoids all
process-management complexity — no detached spawn, no orphan/zombie processes,
no parent-exits-before-child race, no invisible errors — and honors the daemon
exclusion. (ADR-0001's "async" was aimed at the *network* leg, which auto-sync
does not run; for the free local leg, synchronous is both simpler and
sufficient.)

### 3. No debounce

The local leg is idempotent-cheap: the union is canonicalized
([ADR-0001](ADR-0001-op-log-on-dedicated-ref.md) §5), so a burst of mutations
each publishes with near-no-op cost after the first. A scripted batch that
cares turns auto-sync off and syncs once at the end. Debounce would only matter
for an expensive/networked op, which this is not, and it would need
cross-process timing state for a negligible saving.

### 4. Best-effort — never fails the mutation

The mutation has **already succeeded** — its record is durably appended to the
own segment under the lock ([ADR-0015](ADR-0015-local-concurrency-fs-safety.md))
— *before* auto-sync runs, and the ref publish is a convenience a sibling would
re-derive on its own sync. So an auto-sync failure (ref contention surviving the
CAS-retry, a read-only filesystem, a hardened-path refusal) is **swallowed and
surfaced as a non-fatal note** (stderr, or a `--json` field), **never** a
non-zero exit. A write command's exit code is independent of auto-sync.

### 5. On/off — the `tl.autosync` git config

A boolean git config `tl.autosync`, read once per mutation (parity with
`tl.remote`, [ADR-0001](ADR-0001-op-log-on-dedicated-ref.md) §5). `tl init`
sets it: **on** for a linked worktree (free, and the point of
[ADR-0016](ADR-0016-worktree-sharing-local-first-sync.md) §4); opt-in (off,
offered) elsewhere; removable; and suppressed entirely under `--stealth`
([ADR-0001](ADR-0001-op-log-on-dedicated-ref.md) §7). A git config (not a
`.tl/local` marker) so it is inspectable with `git config` and consistent with
the other tl knobs.

### 6. Wiring — one hook after `transact`

Every write verb funnels through `Store.transact`; auto-sync is a single,
lock-free hook invoked **after** `transact` returns (never inside the lock — the
local leg must stay lock-free). So every mutation gets it uniformly, in one
place, and the hook reads `tl.autosync` and runs `syncLocal` best-effort.

**Built form.** Implemented in the CLI layer (`Store` cannot import `Sync`):
each write verb calls `autoSyncNotes` after `transact` returns (lock released),
which reads `tl.autosync` via `gitConfig` and, when `true`, runs `syncLocal`
through the same `.run.toBaseIO` best-effort catch `refreshFromRef` uses —
swallowing both `Tl.Error` and `IO.Error` into a non-fatal `notes` entry, never
a non-zero exit. `tl init` sets `tl.autosync=true` when it detects a linked
worktree (`isLinkedWorktree`: `--git-dir` ≠ `--git-common-dir`), opt-in
elsewhere, and never overrides an existing value. The write verbs *also* absorb
the ref *before* `transact` (the pre-transact local absorb, ADR-0016 §3
amendment) — auto-sync is the outbound mirror of that inbound refresh. Tested
(`Tests/CliTests.lean`): off-by-default (sibling blind), on (sibling sees the
write with no explicit sync), a publish failure disclosed while the write
survives, and the no-git no-op.

## Consequences

- Worktree siblings see a write near-instantly with zero network and zero
  process management: the writer publishes on every mutation, the sibling's
  read-refresh absorbs it. Together with read-refresh, sharing on one machine is
  transparent in both directions.
- The read path stays git-free in steady state (read-refresh is an O(1) OID
  check); auto-sync is the *write*-side half that actually moves the ref.
- A scripted bulk run pays a per-mutation local-sync cost (~tens of ms); it
  opts out (`tl.autosync=false`) and syncs once for batches.
- Cross-clone visibility remains sync-bounded and explicit. A fully-sandboxed
  agent (own clone, no worktree siblings) gains nothing from auto-sync and
  relies on explicit `tl sync` (or a session-boundary sync) to push — by design,
  not a defect.
- Tested (shell): the best-effort swallow + the non-fatal note, the
  config-driven on/off, and the lock-free-after-`transact` ordering.

## Alternatives considered

- **Async detached process** (spawn a background `tl sync`). Rejected: process
  lifecycle/zombie management, error invisibility, and an ordering race (the
  detached publish may not land before a sibling reads) — for no gain over a
  synchronous local leg that is already fast.
- **Full sync (local + remote) synchronously.** Rejected: it blocks the command
  on the network (and can hang on it), so a fast `tl claim` waits on a remote
  push — and it pushes to the remote on every write.
- **A daemon / filesystem watcher.** Excluded by ADR-0001's server-less design;
  auto-sync is per-command, not a long-running process.
- **Debounced** (sync only if >N ms since the last). Rejected: cross-process
  timing state for a negligible saving on an already-cheap op; batches opt out
  instead.
