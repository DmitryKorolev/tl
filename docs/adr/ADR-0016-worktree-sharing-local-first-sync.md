# ADR-0016 — Same-machine sharing: worktrees and local-first sync

- Status: Accepted
- Date: 2026-06-05

## Context

Agents increasingly run one per git worktree of the same repo on one
machine (e.g. an orchestrator that gives each agent an isolated worktree). `tl`
must let those agents coordinate — see each other's tasks and claims — smoothly.

The pieces are already correct:

- A linked worktree is its own repository boundary, so it gets its own
  gitignored `.tl/` (own replica-id, clock, segment) and never binds the
  parent's ([ADR-0012](ADR-0012-discovery-and-directory-override.md)).
- Each worktree is therefore a distinct replica with a distinct id, so the
  CRDT converges with no corruption ([ADR-0007](ADR-0007-identity-hlc-ids.md)).

But the transport was wrong for this case. Sync was remote-mediated
(`fetch → union → push`, reporting `no-upstream` when no remote is configured —
[ADR-0001](ADR-0001-op-log-on-dedicated-ref.md) §5), and reads fold only the
local `.tl/log/` segment files (§6). So two worktrees on one machine could
not see each other without a configured remote and network round-trips — absurd,
because git keeps `refs/tl/log` in the common `.git` directory, already
shared across every linked worktree of the repo. The shared substrate is sitting
right there; the design just wasn't using it.

This ADR pins how same-machine agents share, and what stays inherently
remote-bound.

## The substrate gradient

What agents physically share decides the transport — there is no single answer:

| Agents share… | Transport | Network? |
|---|---|---|
| Same checkout (one `.tl/`) | none — reads fold the shared local segments; the mutation lock serializes writes (ADR-0015) | none |
| Same repo, different worktrees | the common `.git` → one shared `refs/tl/log` | none (this ADR) |
| Separate clones, same machine | no shared ref; a local-path / `file://` remote (a peer or a shared bare repo) | none, but it is the remote leg |
| Fully sandboxed (own container, no shared FS/`.git`) | a network remote — the only common substrate | yes, mandatory |

The bottom row is inherent to a serverless design (the sync-bounded cost ADR-0001
already accepts), not a `tl` defect. "Remote" ≠ "network": only true
cross-host sandboxing forces a network endpoint.

## Decision

### 1. Local-first sync

`tl sync` (and auto-sync) run a local leg before the remote leg:

- Local leg (always runs): reconcile against the local `refs/tl/log` —
  update it from this replica's own segment, and materialize the *other*
  replicas' segments from it into `.tl/log/` (the §3 foreign-cache writeback of
  [ADR-0015](ADR-0015-local-concurrency-fs-safety.md): temp-file + atomic
  `rename`, never the own segment). For worktrees of one repo this ref is the
  shared common-`.git` ref, so the local leg is the same-machine transport.
- Remote leg (only if a remote exists): the existing `fetch → union → push`
  to the configured remote (ADR-0001 §5).

`no-upstream` now gates only the remote leg. The local leg still runs, so a
worktree with no remote configured still shares with its siblings — zero network.
A lone clone's local leg is a cheap no-op (no local peer) and the remote leg does
the work, exactly as today.

This is consistent with the segment-per-mutation / ref-at-sync rule: a mutation
still writes only its own segment, and the ref is (re)built from segments at sync
time (ADR-0001 §6) — the local leg just also *reads* the shared ref to absorb
siblings.

### 2. Worktree sharing uses the shared common-`.git` ref

Linked worktrees of a repo share `refs/tl/log` because git keeps it in
`$GIT_COMMON_DIR` (like `refs/heads`/`refs/tags`), not per-worktree like `HEAD`
and the index. Each worktree keeps its own gitignored `.tl/` (own replica-id,
clock, segment — ADR-0012/0007); only the ref is shared, and it is the
transport. No `.tl/` contents are shared on disk, so per-replica ownership is
preserved.

### 3. Read-time refresh (b-min with a ref-OID trigger)

Reads stay pure folds of the local `.tl/log/*.jsonl` segments — git is kept
off the steady-state read path. Smoothness comes from a cheap trigger, not from
folding the ref on every read:

- Before folding, a read does an O(1) compare of the shared `refs/tl/log`
  OID against the last-materialized OID recorded in `.tl/local/` (a new
  gitignored marker file; not part of the log format, no `v` bump).
- Unchanged (the common case) → fold the local files. Cost ≈ reading one
  small ref. Negligible.
- Moved (a sibling synced) → incrementally materialize the changed foreign
  segments (the §3 atomic rename), record the new OID, then fold.

So cross-worktree visibility is live without putting git/object-store inflate
on every read, and without the agent having to remember to `sync`.

A read may therefore perform a foreign-cache write (atomic rename, no
mutation lock — the same write `sync` already does). On a read-only filesystem a
read skips the refresh and folds what it has (a moment stale), never failing.
Concurrent readers racing to refresh are safe: the materialized content is a pure
function of the ref OID, and atomic rename makes last-writer-wins harmless.

### 4. Auto-sync defaults on for worktrees

Because the local leg is free (no network), `tl init` enables auto-sync by
default when it detects a linked worktree (still opt-in elsewhere, still
removable — ADR-0001 §4). Promptly publishing a write into the shared ref is what
makes a sibling's read-refresh see it.

### 5. Bounds (unchanged in spirit)

Visibility is still sync-bounded: worktree A sees B's op once B has published
it into the shared ref via B's (auto-)sync. The local-first leg makes both
"publish" and "absorb" free and near-instant on one machine, but it does not make
a mutation visible before the writer publishes it (segment-per-mutation,
ref-at-sync). Fully sandboxed agents reconcile only through the remote leg.

## Consequences

- Worktree agents coordinate with zero network and near-live visibility. The
  absurd "round-trip to a remote to talk to a sibling on the same disk" is gone;
  a no-remote worktree set shares correctly instead of silently getting nothing
  (the old `no-upstream` dead-end).
- The read path stays cheap and git-free in steady state — the hot
  `ready`/`show`/`list` path the agent loop hammers pays only an O(1) ref
  check until something actually changes.
- Reads can now write a foreign cache (atomic rename, no lock) — a deliberate
  softening of "reads never mutate," gated on filesystem writability.
- Staging: the local leg is part of the sync machinery
  ([Stage 3](../vision.md)); worktree-per-agent dogfooding therefore wants a
  minimal `tl sync` (at least its local leg) pulled forward, exactly as
  vision already allows for multi-clone sharing.
- Tested (shell, ADR-0001 sync set): the local leg with no remote (two
  worktrees share), the ref-OID trigger (unchanged-skip vs moved-materialize),
  the read-only-FS skip, and "a sibling's write is visible after its
  (auto-)sync." The remote leg's tests are unchanged.

## Alternatives considered

- b-max — fold the shared ref on every read. Rejected: it reintroduces
  git/object-store access + zlib-inflate into the hot read path, repeated on every
  fresh process and growing with log size — the wrong trade for a read-heavy agent
  workload. Its one upside (drop the foreign-cache files, since the ref is the
  foreign store) is not worth coupling reads to the object store. It also does
  not make sharing "instant" — both variants are bounded by the writer
  publishing to the ref; b-max only removes the reader's pull step.
- Shared `.tl/` via `TL_DIR` (one replica, many agents). Works today and is
  the documented interim workaround: point every worktree at one `.tl/`,
  collapsing to the single-checkout model serialized by the mutation lock. But
  `TL_DIR` is meant for test/CI isolation, it gives up per-worktree replica
  identity/ownership, and the `.tl/` must live somewhere all worktrees can reach.
  Fine as a stopgap, not the model.
- Remote-only (the prior behavior). Rejected: forces a configured remote and
  round-trips for worktrees that already share the ref locally, and dead-ends on
  `no-upstream` for the common no-remote worktree case.
- Put `.tl/log/` segments in the common `.git` dir (physically shared).
  Rejected: it abandons the gitignored-working-tree layout, muddies per-replica
  ownership and the discovery boundary, and the shared ref already provides
  the substrate without moving the segments.
