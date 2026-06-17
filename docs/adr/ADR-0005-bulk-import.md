# ADR-0005 — One-shot bulk import

- Status: Accepted
- Date: 2026-05-31

## Context

Existing work usually already lives in another tracker (issues, dependencies,
labels). `tl` must be able to adopt that history once, then own it. Rather than
couple to any one tool's storage engine or on-disk schema, `tl` defines its
**own portable bulk-import format** — a documented JSONL of issue records — and
the user transforms their source export (a tracker's JSON/CSV export, a script
over its API, etc.) into it. `tl` is not an interoperating drop-in and owes no
external tool ongoing compatibility — which is what frees the storage design
(ADR-0001/0002).

This keeps the importer small and stable: it parses one well-specified format,
not the schema of every tracker. Producing that format from a given source is a
transform the user owns (and scripts once).

## Decision

Provide a one-shot `tl import <path>` that runs in the tested I/O shell (not the
kernel) and turns tl's bulk-import format into a seed op-log.

### The import format

`<path>` is a JSONL file (or a directory of `*.jsonl`, unioned) — one **issue
record** per line. Each record is self-contained, carrying its fields and its
outgoing edges by source id:

```json
{ "id": "PROJ-42",
  "title": "Write the parser",
  "status": "open",                      // open | in_progress | done | cancelled (default open)
  "priority": 2,                         // 0–4, 0 = highest (default 2; clamped + disclosed)
  "assignee": "alice",                   // optional
  "description": "…", "notes": "…",      // optional free-form
  "labels": ["area:parser"],             // optional
  "deferUntil": "2026-07-01T00:00:00Z",  // optional ISO-8601 UTC; marks the open issue deferred
  "closeResolution": "done",             // done | cancelled | duplicate (only when closed)
  "duplicateOf": "PROJ-7",               // optional, with closeResolution = duplicate
  "blockedBy": ["PROJ-7"],               // outgoing blocks edges (this is blocked by …)
  "parent": "PROJ-1",                    // optional parent (epic) id
  "related": ["PROJ-9"],                 // optional symmetric links
  "meta": { "ext:jira": "PROJ-42", "due_at": "…" },     // optional opaque side-channel
  "createdAt": "…", "closedAt": "…", "claimedAt": "…" } // optional ISO-8601 provenance
```

Only `id` and `title` are required; everything else takes the documented
default. Edge endpoints reference other records' `id`s. Unknown keys are
preserved into `meta` under `import:<key>` rather than dropped, so a richer
source loses nothing.

The format deliberately mirrors tl's own model, so the mapping is direct —
there is no per-tracker translation table in the importer. Mapping a specific
tracker's vocabulary (status names, dependency types, hierarchical ids,
orchestration artifacts) onto this format is the user's transform step, done
once before import.

### Seed op-log

- Each record → a `create` op carrying the scalar fields, stamped with
  `createdAt` as its HLC (so `createdAt` projects correctly and ordering is
  reproducible). The source id is preserved in `meta` under `ext:<source>` (the
  general `ext:<system>` convention, ADR-0002), plus `import:source = <source>`
  so the JSON projection marks `provenance.source = "imported"` (ADR-0003).
- For a record that is `done`/`cancelled` or `in_progress`, the importer also
  emits a `close`/`claim` op stamped with `closedAt`/`claimedAt` — because
  `closedAt`/`claimedAt` read the HLC of the `close`/`claim` op, not the
  `create` (ADR-0008); a lone terminal-status `create` would leave them absent.
  `closeResolution` sets the resolution (`done`→`status=done`;
  `cancelled`/`duplicate`→`status=cancelled`, `duplicateOf` recorded via the
  `duplicate-of` meta key).
- `blockedBy`/`parent`/`related` → one typed `edgeAdd` op each
  (`blocks`/`parent`/`related`); every edge is typed (ADR-0008). An edge whose
  endpoint id is absent from the import is skipped and disclosed (no placeholder
  issue is fabricated).
- `labels` → `labels` OR-Set adds; `meta` → `metaSet` writes (on which no logic
  depends — vision non-goals).

### Determinism and idempotence

Importing the same source file twice into a fresh repo yields the same seed log.
The determinism rules reconcile `import` with the ID scheme (ADR-0007) and the
no-auto-init rule (ADR-0012):

- **Implicit init.** `tl import` on a repo with no `.tl/` performs an implicit
  `init` (creates `.tl/`, mints the replica-id, seeds the clock). The documented
  exception to ADR-0012's "commands never auto-init": the user explicitly asked
  to seed a repo. The refuse-unless-`--force` rule (below) still guards a
  non-empty existing log.
- **Deterministic `tl` id from the source id.** The seed id is
  `tl-<crockford32(SHA-256("import:" ++ source-tag ++ ":" ++ source-id))[0..80 bits]>`
  — the `:`-delimited preimage and charset pinned in ADR-0007, the leftmost-bits
  slice in ADR-0018. `source-tag` is the `--source <name>` (default `import`), so
  distinct sources do not collide and a re-import is byte-stable. The original id
  stays in the `ext:<source>` meta key, so existing references resolve (a shell
  lookup over `ext:*`, like slug resolution). This is the one documented
  exception to the random-triple id derivation.
- **Deterministic replica/nonce.** Seed ops carry a fixed import replica-id
  `crockford32(SHA-256("import-replica:" ++ source-tag ++ ":" ++ source-fingerprint))[0..64 bits]`
  (the same 13 lowercase chars as a live replica-id, ADR-0007), where
  `source-fingerprint` is the SHA-256 of the canonical sorted source manifest
  `(source-file, source-record-id, record-hash)`. Each op carries a deterministic
  per-op nonce
  `crockford32(SHA-256("import-nonce:" ++ source-tag ++ ":" ++ source-id ++ ":" ++ op-role ++ ":" ++ target-id))[0..128 bits]`
  (26 chars) — not the random per-op nonce of live writes — so the
  `(replica, hlc, nonce)` OR-Set add-tag / LWW triple is byte-stable across
  re-imports. Import is one-shot and single-writer, so this does not affect the
  LWW total-order argument (ADR-0007).
- **Deterministic timestamps, never `now()`.** Missing/invalid
  `createdAt`/`closedAt`/`claimedAt` are assigned from the fixed fallback epoch
  `2000-01-01T00:00:00Z` plus one millisecond per stable ordinal (records sorted
  by `(source-file, source-id)`), disclosed in the import summary, keeping the
  log byte-stable and wall-clock-independent.

### Two distinct safety gates

Two separate explicit gates, never conflated — one flag must not bypass both:

- **`--force` — clobber existing state.** Importing into a non-empty op-log
  (local `.tl/log/` segments or a `refs/tl/log` ref, local or remote, even when
  `.tl/` is freshly created or absent) is refused by default; `import` errors
  rather than double-seed live state. `--force` proceeds, appending the seed ops
  as a fresh import. Same explicit-over-silent stance as `init` (ADR-0012).
- **`--allow-large` / `--max <bytes>` — bounds override.** A hostile or
  accidentally-enormous source is bounded before any op is emitted: per-field
  byte size, label/key size, parent-chain depth, edge count, total input/seed
  size. Exceeding a bound fails `force-required` with a summary naming the bound;
  `--allow-large` (or a raised `--max`) proceeds for a trusted local migration,
  every truncation/skip disclosed. `--force` and the bounds override are
  separate gates, never conflated (ADR-0014 T6).

The render-layer protections from ADR-0014 T1 still apply after import: imported
free-form content is untrusted data.

### Priority and status

`status` maps to the stored enum; an out-of-range `priority` clamps to 0–4 with
disclosure (ADR-0002). A `status`/`closeResolution` value the format does not
define is a malformed line — fail-closed and disclosed, never silently dropped.

## Consequences

- **Source-agnostic.** The importer parses one tl-defined format; adapting any
  tracker is a user-side transform, scripted once. No per-tracker schema lives in
  tl.
- **No live interop.** Import is a migration with a clear before/after, not an
  ongoing integration.
- **In the TCB, differential-tested.** For a set of import-format fixtures, the
  imported-then-materialized `tl` state matches the records' fields, statuses,
  and edges (and tl's `ready` matches the unblocked set implied by the import
  graph).
- **Ancillary data survives without constraining the kernel.** Labels land in
  the `labels` OR-Set; source refs, opaque `due_at`, and unknown keys land in the
  per-key-LWW metadata map (ADR-0002). A frame lemma (ADR-0003) proves neither
  affects `ready`/rollup, so no theorem depends on them.
- **Determinism.** Seed timestamps derive from the source data (not wall-clock
  at import time), so a re-import reproduces the same log — testable and
  reviewable.

## Alternatives considered

- **Read a specific tracker's native storage directly** (a DB/SQL engine, or a
  tool-specific repo layout). Rejected: it couples the importer to that tool's
  storage and schema — the opposite of "own the format" and "small." A portable,
  tl-defined format keeps the importer to one parser and pushes per-tracker
  quirks into a user-side transform.
- **Coexist on the same repo (format-compatible drop-in).** Rejected: forces
  ongoing foreign-format fidelity and reintroduces the source's storage concerns,
  contradicting "own the format."
- **A built-in adapter per popular tracker.** Rejected for v1: an open-ended
  maintenance burden. The single documented format plus example transforms covers
  the need; per-tracker adapters can be community scripts.
