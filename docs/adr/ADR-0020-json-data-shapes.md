# ADR-0020 — `--json` data shapes (the stage-1 surface)

- Status: Accepted
- Date: 2026-06-10

## Context

The `--json` envelope, error-code enum, and exit codes are pinned in ADR-0008;
the canonical issue object (field names, derived projections, `provenance`,
`claim`) is pinned in ADR-0003. What is *not* yet pinned is the per-command
`data` payload — and under ADR-0008's additive-only rule each payload becomes
a permanent contract the day its command first ships (the design-backlog item
this ADR closes for the stage-1 commands). The additive-only promise binds
from 1.0 (ADR-0008 §Stability horizon), so during 0.x these shapes may still
be revised with a `schemaVersion` bump — they are pinned here as the intended
1.0 contract, deliberately chosen rather than emitted-by-accident.

## Decision

### Conventions (all commands)

- Every response is the ADR-0008 envelope; `data` shapes below. Field names
  are camelCase (ADR-0003/0008).
- **Omit-empty**: an optional field with no value is absent, not `null`.
  (Wire records distinguish null-vs-absent for *writes*, ADR-0002; the read
  projection has no clear-vs-unset distinction to preserve.) Two exceptions
  stay `|null` as ADR-0003 pins them: `provenance.createdBy` and
  `claim.currentAssignee`.
- **Ids render in display form** — `tl-` prefixed (ADR-0007: the prefix is
  added on render, and error messages already name the full `tl-…` form).
- **Timestamps** are ISO-8601 UTC with millisecond precision (the HLC's
  physical component, ADR-0008's provenance projections) — e.g.
  `2026-06-10T16:58:55.296Z`.
- **List-like payloads** are `{ "count": <total matches>, "items": [...] }`
  with `items` capped by `--limit` (vision: truncation is disclosed, never
  silent). Ranked order (`ready`) is the array order. When the rows are not
  issue objects the array key is the domain noun (`cycles`, `checks`) — same
  count-plus-capped-rows discipline.
- **Mutating verbs echo the issue**: the full post-mutation issue object
  (ADR-0003) is the `data`, so an agent never needs a follow-up `show`.
  A command that emits several records (ADR-0008 composites) echoes the
  primary issue with its relationships materialized.
- Free-form content fields in any payload are untrusted data — stated here
  and in the skill once, per ADR-0014 (no per-payload trust marker); per-issue
  `provenance` is the graded-trust signal. Content is byte-sanitized and
  bounded per ADR-0014 on every render path.

### Per-command payloads

**`tl create … --json`** — the created issue (echo convention). With inline
edge flags, `dependencies` reflects the edges just written:

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "id": "tl-9f3cq7rkv2m8e4ha", "title": "Write the parser",
  "status": "open", "effectiveStatus": "open", "priority": 2,
  "isEpic": false, "ready": false, "blocked": true, "deferred": false,
  "createdAt": "2026-06-10T16:58:55.296Z", "updatedAt": "2026-06-10T16:58:55.296Z",
  "dependencies": [
    { "type": "blocks", "from": "tl-kz8w2n4jp7e9h3vt", "to": "tl-9f3cq7rkv2m8e4ha" }
  ],
  "labels": [], "meta": {},
  "provenance": { "source": "native", "createdBy": "carol", "replica": "chp14mvsxr027" }
} }
```

**`tl list --json` / `tl ready --json`** — `{count, items}`; each row is the
trimmed issue object (the ADR-0003 scalars + derived booleans that drive
selection) plus two graph counts:

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "count": 23,
  "items": [
    { "id": "tl-kz8w2n4jp7e9h3vt", "title": "Design the AST",
      "status": "open", "effectiveStatus": "open", "priority": 0,
      "isEpic": false, "ready": true, "blocked": false, "deferred": false,
      "createdAt": "2026-06-10T16:58:55.296Z", "updatedAt": "2026-06-10T16:58:55.296Z",
      "dependencyCount": 0, "dependentCount": 1 }
  ]
} }
```

`dependencyCount`/`dependentCount` count the issue's live incoming/outgoing
`blocks` edges (the fold already has them; agents triage on fan-out without a
per-row `show`).

**`tl show <id> --json`** — the full ADR-0003 issue object (all scalar fields
present-if-valued, `labels`, `meta`, `dependencies` + `parent`, provenance
projections, derived booleans), plus `claim: { outcome, currentAssignee }`
when a recent local claim makes the contention signal meaningful (ADR-0013).

**`tl claim <id> --json`** — echo the updated issue plus the pinned outcome:

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "...": "full issue object — status in_progress, assignee, claimedAt set",
  "claim": { "outcome": "won", "currentAssignee": "carol" }
} }
```

A target that is not in `ready s now` is refused before writing with the
`not-claimable` error; its pinned context fields:

```json
{ "schemaVersion": 1, "ok": false, "error": {
  "code": "not-claimable",
  "message": "tl-9f3cq7rkv2m8e4ha is blocked by 1 open issue — run `tl why tl-9f3cq7rkv2m8e4ha`, or claim something from `tl ready`",
  "id": "tl-9f3cq7rkv2m8e4ha",
  "reasons": {
    "blockedBy": ["tl-kz8w2n4jp7e9h3vt"]
  }
} }
```

`reasons` carries only the clauses that apply, omit-empty: `status` (closed /
already `in_progress`), `assignee` (current holder), `isEpic: true`,
`deferUntil`, `blockedBy` (direct unclosed blockers; `why` gives the
transitive set).

**`tl close <id> --as … --json`** — echo, plus the proved freed set:

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "...": "full issue object — status done|cancelled, closeResolution, closedAt set",
  "unblocked": ["tl-9f3cq7rkv2m8e4ha"]
} }
```

`unblocked` is the kernel's `unblocks` set (ADR-0004 thm 10) — what an agent
wants in hand immediately after closing. `--cascade` echoes the root epic and
lists every closed id in an additional `closed: [ids]` array.

**`tl update <id> … --json`** — the updated issue (the mutating-verb echo
convention, exactly as `create`; no additional fields).

**`tl dep add / dep remove --json`** — a relationship ack in the pinned edge
orientation (`from` blocks `to`; for `parent`, `from` is the parent —
ADR-0003):

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "type": "blocks", "from": "tl-kz8w2n4jp7e9h3vt", "to": "tl-9f3cq7rkv2m8e4ha",
  "status": "added"
} }
```

(`"status": "removed"` for `dep remove`; a remove that observed no live tags
still succeeds — add-wins semantics — with `"status": "noop"`.)

**`tl why <id> --json`** — the not-ready reasons, flat and omit-empty;
`blockedBy` is the *transitive unclosed* blocker set (ADR-0004 thm 10) with
enough context to act on each:

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "id": "tl-9f3cq7rkv2m8e4ha", "ready": false,
  "status": "open", "isEpic": false,
  "blockedBy": [
    { "id": "tl-kz8w2n4jp7e9h3vt", "title": "Design the AST",
      "status": "open", "effectiveStatus": "open", "direct": true }
  ]
} }
```

(`deferUntil` appears when defer is a reason; a ready issue answers
`"ready": true` with no reason fields.)

**`tl dep cycles --json`** — the node-set witness per cyclic SCC (ADR-0004
thm 6), one entry per witness:

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "count": 1,
  "cycles": [
    { "kind": "blocks", "issues": ["tl-9f3cq7rkv2m8e4ha", "tl-kz8w2n4jp7e9h3vt"] }
  ]
} }
```

`kind` is `blocks` | `parent` | `readiness` (the `≺`-deadlock report, which
may mix kinds). `issues` is the SCC's members, sorted — the canonical witness.

**`tl doctor --json`** — checks are *data*: a doctor that finds problems
still exits `0` with `ok: true` (the command succeeded; the findings are its
answer — pinned here so agents and CI branch on content, not exit code):

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "healthy": false,
  "checks": [
    { "name": "replica", "status": "ok", "replica": "chp14mvsxr027" },
    { "name": "clock", "status": "ok" },
    { "name": "log", "status": "warn",
      "message": "segment c9k2mvq8rrt04 refused: malformed line 41 — its owning replica repairs or re-syncs it; other segments folded",
      "segment": "c9k2mvq8rrt04" },
    { "name": "graph", "status": "fail", "cycles": 1, "multiParent": 0, "danglingEdges": 2 }
  ]
} }
```

Check `status` is `ok` | `warn` | `fail`; `healthy` = no `fail`. The stage-1
check inventory is ADR-0011's (replica/clock/log integrity, graph
diagnostics, stale claims); checks are added additively.

**`tl init --json`** / **`tl version --json`**:

```json
{ "schemaVersion": 1, "ok": true, "data": { "root": ".tl", "replica": "chp14mvsxr027", "created": true } }
{ "schemaVersion": 1, "ok": true, "data": { "version": "0.1.0", "logFormat": 1 } }
```

(`"created": false` on an idempotent re-run. The ADR-0006 build-provenance
digest joins `version`'s payload as an additive field once the release
pipeline that produces it exists — deferred, not dropped.)

**`tl help --json`** / **`tl help <command> --json`** — the command grammar,
machine-readable (ADR-0011 §1), for agent introspection. The full dump and a
single-command/group filter share one shape (an agent parses
`commands`/`globalFlags` either way):

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "commands": [
    { "command": "close", "positionals": "<id>",
      "summary": "finish an issue; any closed status discharges its blockers",
      "flags": [
        { "name": "as", "value": true, "repeatable": false, "summary": "done | cancelled | duplicate (required)" }
      ] }
  ],
  "globalFlags": [
    { "name": "json", "value": false, "repeatable": false, "summary": "…" }
  ]
} }
```

`command` is the full verb (`"dep add"` for subcommands); `positionals` is a
human template; a flag's `value` marks whether it takes an argument and
`repeatable` whether a second occurrence is allowed. The schema is *generated
from the same grammar table that drives the parser and the human `tl help`*
(`Tl/Cli/Grammar.lean`), so it cannot describe a flag the parser rejects or
omit one it accepts — drift is structurally impossible, not merely tested.

**`tl stats --json`** — board counts (a pure projection):

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "total": 23, "open": 19, "inProgress": 1, "done": 3, "cancelled": 0,
  "ready": 10, "blocked": 8, "deferred": 0, "cycles": 0 } }
```

`open`/`inProgress`/`done`/`cancelled` count *stored* status; `ready`/
`blocked`/`deferred` are the derived views; `cycles` is the cycle-witness
count (structural per kind plus the non-duplicate readiness deadlocks, as
`doctor`'s graph check).

**`tl log [<id>] --json`** — the op history, newest first (an HLC-ordered
projection over the log, ADR-0008); `<id>` filters to ops touching that
issue. `--limit` caps `entries` (default 10, `0` = all); `count` is the total
matched. The `--since` cursor is deferred — it needs a version vector, not a
scalar HLC (backlog) — so this is the full-history (best-effort-capped) view.

```json
{ "schemaVersion": 1, "ok": true, "data": {
  "count": 41,
  "entries": [
    { "timestamp": "2026-06-11T01:27:49.277Z", "op": "close",
      "actor": "carol", "targets": ["tl-ppyg0ekgf91s56e0"] }
  ] } }
```

`op` is the wire verb (ADR-0008's closed enum); `actor` is `|null`;
`targets` is the issue id(s) the op touched (one for scalar/meta/label ops,
both endpoints for edge ops — the same set `tl log <id>` filters on).

**Error context fields** (extending ADR-0008's pinned codes with their named
context, same additive-only discipline): `not-claimable` → `id`, `reasons`
(above); `not-closeable` → `id`, `reasons` (omit-empty: `isEpic: true` with
`openChildren: [ids]` for the epic-`done` refusal; `selfDuplicate: true` for a
`--of` naming its own issue — ADR-0008 §write-time guards); `unsafe-path` →
`path`, `reason` (`"symlink"` | `"ownership"` — ADR-0015 §6);
`ambiguous-id` → `input`, `candidates: [ids]`; `not-found` → `input`;
`malformed-line` / `unknown-version` → `segment`, `line` (when known);
`lock-busy` → `path`, `timeoutMs`; `corrupt-clock` → `reason`
(`"unreadable"` | `"saturated"` — the two need different fixes, ADR-0007).
Every `message` teaches the fix (ADR-0008).

## Consequences

- The stage-1 freeze is deliberate: every shape above was chosen, not
  emitted-by-accident — the failure mode the backlog item warned about.
- Agents get a uniform read/act loop: mutations return the updated issue, so
  `create → claim → close` needs no interleaved `show`s; `close.unblocked`
  feeds the next `claim` directly.
- Later commands (`log`, `stats`, `dep tree/path`, `unblocks`, …) pin their
  shapes when built, following these conventions; the backlog keeps carrying
  them until then.
- `dependencies` stays the flat edge-triple array (ADR-0003). Inlining full
  issue snapshots inside it was rejected: it freezes a recursive shape and
  duplicates rows `--json` consumers can join by id; a richer view remains an
  additive future option.

## Alternatives considered

- **Bare arrays for list output.** Rejected: vision pins
  count-plus-capped-items so truncation is always disclosed (no silent caps),
  and the envelope needs a single `data` object anyway.
- **Minimal mutation acks** (id-only). Rejected: every consumer's next
  question is the updated state; echoing the issue object removes a
  round-trip and keeps one canonical shape.
- **A per-payload `contentTrust` marker.** Rejected in ADR-0014 (amended in
  this change): a constant field carries no information and freezes as
  permanent noise; `provenance` is the varying, useful signal.
- **Per-issue nested dependency snapshots in `show`.** Rejected above —
  additive later if a real consumer needs it.
- **`doctor` exits nonzero on findings.** Rejected: it conflates "the
  command failed" with "the project has findings" — agents and CI branch on
  the structured `checks`; a dedicated `--check` gate mode can be added
  additively if wanted.
