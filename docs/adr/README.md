# Architecture Decision Records

Each ADR records one decision: its context, the decision, consequences, and
the alternatives considered. ADRs are refinable, not frozen — when a new
need surfaces friction with an existing decision, supersede it with a new
ADR rather than treating the old one as non-negotiable.

Format: `ADR-NNNN-short-slug.md`, with a `Status` (Proposed / Accepted /
Superseded by ADR-MMMM) and a `Date`. Keep the substance human-readable; do
not reference task-tracker IDs.

## Index

| ADR | Title |
|---|---|
| 0001 | [Append-only op-log on a dedicated git ref](ADR-0001-op-log-on-dedicated-ref.md) |
| 0002 | [Minimal CRDT: OR-Set + LWW-register + metadata map](ADR-0002-minimal-crdt.md) |
| 0003 | [Relations, cycles, and rollup](ADR-0003-relations-cycles-rollup.md) |
| 0004 | [The verified kernel and the TCB boundary](ADR-0004-verified-kernel-tcb-boundary.md) |
| 0005 | [One-shot bulk import](ADR-0005-bulk-import.md) |
| 0006 | [Distribution and supported platforms](ADR-0006-distribution-and-platforms.md) |
| 0007 | [Identity, HLC, and ordering](ADR-0007-identity-hlc-ids.md) |
| 0008 | [Log format, JSON schema, and versioning](ADR-0008-log-format-versioning-compaction.md) |
| 0009 | [Proof dependencies: batteries over Mathlib](ADR-0009-proof-dependencies.md) |
| 0010 | [Defer (defer-until)](ADR-0010-defer-until.md) |
| 0011 | [Agent consumption: machine-readable reads and a skill](ADR-0011-agent-consumption.md) |
| 0012 | [Repo discovery and the directory override](ADR-0012-discovery-and-directory-override.md) |
| 0013 | [Actor identity, and the config-free stance](ADR-0013-actor-identity-and-config.md) |
| 0014 | [Threat model and trust boundary](ADR-0014-threat-model.md) |
| 0015 | [Local concurrency and filesystem safety](ADR-0015-local-concurrency-fs-safety.md) |
| 0016 | [Same-machine sharing: worktrees and local-first sync](ADR-0016-worktree-sharing-local-first-sync.md) |
| 0017 | [Human-facing CLI: output format and editing](ADR-0017-human-cli-output-and-editing.md) |
| 0018 | [Hand-rolled SHA-256 (pure Lean)](ADR-0018-hand-rolled-sha256.md) |
| 0019 | [Native primitives shim, and the FFI policy](ADR-0019-native-shim-ffi-policy.md) |
| 0020 | [`--json` data shapes (the stage-1 surface)](ADR-0020-json-data-shapes.md) |
| 0021 | [Auto-sync: a synchronous, best-effort local-leg publish](ADR-0021-auto-sync-process-model.md) |
| 0022 | [The materialization fold cache](ADR-0022-materialization-fold-cache.md) |
| 0023 | [Algorithmic efficiency: the proved/tested/assumed tiering and the prevention net](ADR-0023-efficiency-tiering-and-prevention.md) |
| 0024 | [Indexed views: accelerating proved collections behind an equality bridge](ADR-0024-indexed-views-bridge.md) |
| 0025 | [Incremental change feed: `tl log --since` and the version-vector cursor](ADR-0025-incremental-change-feed.md) |
| 0026 | [Continuous integration: platform, job graph, gates, and caches](ADR-0026-continuous-integration.md) |
