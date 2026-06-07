# ADR-0005 — One-shot import from beads

- Status: Accepted
- Date: 2026-05-31

## Context

Existing work already lives in a `.beads` repository (issues,
dependencies, and ancillary labels/comments). `tl` must be able to adopt
that history. The earlier question of *how compatible* `tl` should be with
beads resolved to: import once, then own the format. `tl` is not an
interoperating drop-in and owes beads no ongoing compatibility — which is
what frees the storage design (ADR-0001/0002).

A beads repo's portable data is its JSONL: `issues.jsonl`,
`dependencies.jsonl`, and `labels.jsonl` / `comments.jsonl` /
`events.jsonl`. The dolt server is an implementation detail `tl` ignores.

## Decision

Provide a one-shot `tl import <path-to-.beads>` that runs in the tested
I/O shell (not the kernel) and produces a seed op-log:

- Read `issues.jsonl` → a `create` op per issue, carrying a `tl` id
  derived deterministically from the source id (see "Init and deterministic
  IDs" below), the source id preserved in the metadata map under the reserved
  key `ext:beads` (the general `ext:<system>` convention, ADR-0002), plus
  `import:source = beads` so the JSON projection marks
  `provenance.source = "imported"` (ADR-0003), plus the initial scalar fields,
  stamped with the source's *created* timestamp as its HLC (so `createdAt`
  projects correctly and ordering is reproducible). For a source issue that is
  closed or in_progress, the importer additionally emits a `close` /
  `claim` op stamped with the source's `closed_at` / claim time — because the
  provenance projections `closedAt`/`claimedAt` read the HLC of the
  `close`/`claim` op, not the `create` (ADR-0008); a lone terminal-status
  `create` would leave them absent.
- Read `dependencies.jsonl` → one `depAdd` op per edge, carrying the tl edge
  `kind` mapped from the source dependency type (table below) — every
  `edgeAdd` is typed (ADR-0008).
- Read `labels.jsonl` → categorical tags become `labels` (an OR-Set, the
  natural home); non-categorical source labels and `comments.jsonl` are
  preserved as opaque `metaSet` writes (`import:comment:<source-comment-id>`
  keys; if the source comment has no id, use a deterministic hash of the full
  source comment record), on which no logic depends (vision non-goals).
- `events.jsonl` is not imported as logic — `tl`'s op-log is its own
  history. At most it informs import timestamps.

Import is idempotent and one-shot: importing the same source twice
into a fresh repo yields the same seed log (deterministic given the source
ids, record content, and timestamps when present — see below). After import, the source tracker is
retired for that repo; `tl` is the source of truth.

### Init and deterministic IDs

`import` is the one explicit bootstrap command, so it carries three rules
that reconcile it with the ID scheme (ADR-0007) and the no-auto-init rule
(ADR-0012):

- Implicit init. `tl import` on a repo with no `.tl/` performs an
  implicit `init` (creates `.tl/`, mints the replica-id, seeds the clock).
  This is the documented exception to ADR-0012's "commands never auto-init":
  the user explicitly asked to seed a repo. The refuse-unless-`--force` rule
  (below) still guards a *non-empty existing* log.
- Deterministic `tl` id from the source id. The seed id is
  `tl-<crockford32(SHA-256("import:" ++ source-tag ++ ":" ++ source-id))[0..80 bits]>` (`source-tag` = `beads`, the `:` delimiter and charset pinned in ADR-0007)
  — derived from the source id, not from `(replica-id, HLC, nonce)` (same
  function/width as ADR-0007). This keeps ids flat and stable across
  re-imports (genuine idempotence) while preserving the source id in the
  `ext:<system>` metadata key. It is the one documented exception to the
  random-triple id derivation.
- Deterministic replica/nonce. Seed ops carry a fixed, well-known import
  replica-id, not the random per-working-copy one:
  `crockford32(SHA-256("import-replica:" ++ source-tag ++ ":" ++ source-fingerprint))[0..64 bits]`
  rendered as the same fixed 13 lowercase chars as a live replica-id
  (ADR-0007). `source-fingerprint` is a SHA-256 digest of the canonical sorted
  source manifest `(source-file, source-record-id-or-hash, record-hash)`, so the
  same source imports with the same import replica and distinct sources do not
  intentionally share one. Seed ops also carry a deterministic per-op nonce
  derived from the source record + op role + target id — not the random per-op
  nonce of live writes. This keeps re-import byte-stable while still
  populating the `(replica, hlc, nonce)` envelope triple every op needs as
  its OR-Set add-tag and LWW tiebreak (ADR-0007/0008); the import HLC comes
  from source timestamps. Import is one-shot and single-writer, so this does
  not affect the LWW total-order argument (ADR-0007).
- Missing or invalid source timestamps are deterministic, never `now()`.
  The importer sorts source records by `(source-file, source-id, source-record-id
  or canonical-record-hash)` and assigns missing timestamps from the fixed
  fallback epoch `2000-01-01T00:00:00Z`, plus one millisecond per stable ordinal.
  This is disclosed in the import summary, keeps the log byte-stable, and avoids
  wall-clock dependence.

Importing into existing state is refused by default. If a non-empty op-log
already exists — local `.tl/log/` segments or a `refs/tl/log` ref (local or
remote), even when `.tl/` is freshly created or absent — `import` errors rather
than risk clobbering or
double-seeding live state; `--force` is required to proceed (it appends the
seed ops as a fresh import, the caller having taken responsibility). This is
the same explicit-over-silent stance as `init` (ADR-0012).

Status values that have no `tl` equivalent are mapped explicitly (the
mapping table lives in the importer and is part of what the differential
test checks), never silently dropped.

### Bounds and hostile-source handling

Import is local and explicit, but a `.beads` source can still be hostile or
accidentally enormous. The importer enforces fixed, tested bounds before
emitting seed ops: per-field byte size, label/key byte size, dotted-parent depth,
edge count, and total input/seed size. Exceeding a bound fails with
`force-required` and a summary naming the bound; an explicit override may proceed
for a trusted local migration, but every truncation/skip remains disclosed. The
render-layer protections from ADR-0014 T1 still apply after import: imported
free-form content is untrusted data.

### Field and status mapping

Grounded in the real `.beads` schema. Two rules cover the long tail:
skip orchestration-layer artifacts (they are not durable tasks) and
preserve real-issue fields opaquely when `tl` doesn't model them.

| beads | → tl |
|---|---|
| `status: open / in_progress / closed` | `create`, then for `in_progress`/`closed` a `claim`/`close` op (above); `closed` → `closeResolution` from `close_reason` (`done`→`status=done`; `cancelled`/`duplicate`→`status=cancelled`, since `duplicate` is a resolution, not a status); the source `closed_at` is the `close` op's HLC → projects as `closedAt` (ADR-0008) |
| `status: deferred` + `defer_until: T` | `open` + `deferUntil := T` ([ADR-0010](ADR-0010-defer-until.md)); the `deferred` view reproduces `❄` |
| `defer_until: T` (any status) | carry `deferUntil := T` |
| `blocked` (derived from deps) | derived — just import the dependency edges |
| `dependencies.jsonl` dependency type | → tl edge `kind`: blocking types → `blocks`; parent/epic/subtask types → `parent`; related/discovered/soft types → `related`; an unrecognized type → `blocks` (conservative — keeps the dependent not-ready rather than fabricating freedom), disclosed in the import summary (exact source vocabulary lives in the importer, differential-tested) |
| `priority` | → tl `priority` 0–4 (0 = highest) by the documented source scale; absent → default 2; `pinned` → 0 |
| `await_id` / `await_type` | by type: awaiting an existing imported issue → `blocks` edge; awaiting a skipped/tombstoned/missing issue → preserve opaque + disclose (no placeholder by default); an external/event → an `open` issue with a `waiting:*` label (or `defer` if a date is known); else preserve opaque |
| `due_at` (deadline) | not modeled as a field (deadlines out of scope, vision) → preserved opaquely as a `due_at` metadata key (ADR-0002); round-trips, drives nothing |
| `issue_type` ∈ {task, bug, feature, chore, decision} | → a reserved `type:<x>` label (categorical, filter-only; not a stored field — there is no `type` field, ADR-0003) |
| `issue_type: epic` | → `tl` epic (via `parent` edges, ADR-0003) |
| dotted hierarchical id (`2ds.1.10`) | → a flat `tl` id + a reconstructed `parent` edge to the immediate dotted prefix (`2ds.1` for `2ds.1.10`) when that parent exists; if the prefix is absent/skipped, no edge is emitted and the omission is disclosed. The original id is preserved in the `ext:beads` metadata key so existing references still resolve (a shell lookup over `ext:*`, like slug resolution) |
| ephemeral / wisp / template / molecule | skip — transient or orchestration definitions, not durable tasks |
| `status: tombstone` | skip — deleted |
| `pinned` / `hooked` and exotic types (convoy, gate, role, agent, message, …) | preserve opaque (or map `pinned` → high priority); not core |
| `compacted_*` metadata | ignore — `tl` rebuilds its own log (ADR-0008) |

beads' molecule / wisp / hook / polecat machinery is an agent-orchestration
sublayer that `tl` deliberately does not model (vision non-goals); the
importer skips those artifacts rather than translating them.

## Consequences

- No live interop. `tl` and `bd` are not expected to operate the same
  repo concurrently. Import is a migration, with a clear before/after.
- The importer is in the TCB, covered by a differential test: for a
  set of real `.beads` fixtures, the imported-then-materialized `tl` state
  matches the source repo's issues, statuses, and edges (and `ready`
  computed by `tl` matches the unblocked set implied by the source graph).
- Ancillary data survives without constraining the kernel. Source labels
  land in the `labels` OR-Set; the source reference, opaque `due_at`, and
  comments land in the per-key-LWW metadata map (ADR-0002). A frame lemma
  (ADR-0003) proves neither affects `ready`/rollup, so no theorem depends on
  them and they cannot complicate the proof.
- Determinism. Because seed timestamps derive from source data (not
  wall-clock at import time), a re-import reproduces the same log — testable
  and reviewable.

## Alternatives considered

- Coexist on the same repo (format-compatible drop-in). Rejected: it
  forces ongoing beads-format fidelity and reintroduces dolt concerns,
  contradicting "own the format" and "small."
- Output-equivalent drop-in (`tl` aliases `bd` byte-for-byte).
  Rejected: maximal compatibility burden for no benefit once we own the
  data.
- Import via the dolt database directly. Rejected: the JSONL is the
  documented, portable surface; reading dolt would couple us to a server
  and storage engine we are explicitly dropping.
