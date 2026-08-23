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
1.0 contract, deliberately chosen rather than emitted-by-accident. A
`schemaVersion` bump signals a break to an *installed base*, so it applies to a
revision *between releases*; iterating a shape **before the first release/tag**
(no consumer ever saw the prior shape) is not such a break and needs no bump —
e.g. `tl log`'s `cursor` settling from a bare string to the `{since, until}`
object (ADR-0025) happened entirely pre-release within `schemaVersion: 1`.
The first post-baseline bump was `schemaVersion: 2` — `show`'s `claim.outcome`
enum (ADR-0013/0008 §ledger); the second is `schemaVersion: 3` — the issue
object's `notes` field re-typed from a string to the journal-entry array
(ADR-0027/0008 §ledger). The examples below show the current envelope at `3`.

## Decision

### Conventions (all commands)

- Every response is the ADR-0008 envelope; `data` shapes below. Field names
  are camelCase (ADR-0003/0008). The success envelope may also carry an
  **omit-empty** top-level `"notes":[…]` array — the same loud-not-silent
  disclosures printed to stderr (foreign-refusal, skew-deferred, stale-read
  degrade, auto-sync skipped — ADR-0008), made machine-readable for the agent
  audience that consumes `--json` (ADR-0011). Additive over fields; absent when
  there are no notes, so the steady-state shape is byte-unchanged.
- **Omit-empty**: an optional field with no value is absent, not `null`.
  (Wire records distinguish null-vs-absent for *writes*, ADR-0002; the read
  projection has no clear-vs-unset distinction to preserve.) The pinned
  `|null` exceptions — each a field whose *value* is the answer, so the field
  stays present and `null` says "none": `provenance.createdBy` and
  `claim.currentAssignee` (as ADR-0003 pins them), `log`'s per-entry `actor`,
  `ready`'s top-level `staleness`, `doctor`'s sync-check `upstream`
  and `lastSync`, `init`'s `replica`, and the keyed `meta get` `value`.
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
{ "schemaVersion": 3, "ok": true, "data": {
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
{ "schemaVersion": 3, "ok": true, "data": {
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

`ready`'s `data` additionally carries a top-level `staleness` — always
present, the ADR-0011 sync-freshness advisory string, or `null` when there
is nothing to advise: the view is current, *or* no remote resolves to
compare against (the pinned `|null` convention above). `tl list` does not
emit it.

Both verbs take filter facets (`--label`/`--assignee` on `ready`, those plus
`--status`/`--priority`/`--blocked`/`--deferred`/`--stale` on `list`) — see
*filter facets* below; they narrow `items`/`count`, never the shape.

**`tl show <id> --json`** — the full ADR-0003 issue object (all scalar fields
present-if-valued, `labels`, `meta`, `dependencies` + `parent`, provenance
projections, derived booleans), plus `claim: { outcome, currentAssignee }`
when a recent local claim makes the contention signal meaningful (ADR-0013).

**`tl claim <id> --json`** — echo the updated issue plus the pinned outcome:

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "...": "full issue object — status in_progress, assignee, claimedAt set",
  "claim": { "outcome": "won", "currentAssignee": "carol" }
} }
```

A target that is not in `ready s now` is refused before writing with the
`not-claimable` error; its pinned context fields:

```json
{ "schemaVersion": 3, "ok": false, "error": {
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

**`tl close <id> --as … --json`** — echo, plus the proved freed set and the
close outcome:

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "...": "full issue object — status done|cancelled, closeResolution, closedAt set",
  "unblocked": ["tl-9f3cq7rkv2m8e4ha"],
  "close": { "outcome": "won", "resolution": "done" }
} }
```

`unblocked` is the kernel's `unblocks` set (ADR-0004 thm 10) — what an agent
wants in hand immediately after closing. The `close` block mirrors `claim`'s
`{outcome, currentAssignee}` (the close-side outcome
contract, ADR-0008 §close reporting): `outcome` is `won` when the issue is
terminal *as requested*, else `superseded` (a concurrent write took it to a
different terminal, reopened it, or — for `--as duplicate` — closed it against
a different canonical); `resolution` is the resolution that actually holds
(`done`\|`cancelled`\|`duplicate`, or `null` if not terminal), so an agent
branches on `outcome` and reads the winner without re-deriving it. This is an
additive field — a consumer reading `unblocked`/`closeResolution`/`status` is
unaffected — so it did not bump `schemaVersion`.

**`tl update <id> … --json`** — the updated issue (the mutating-verb echo
convention, exactly as `create`; no additional fields).

**`tl defer <id> --until <date> | --for <duration> --json`** /
**`tl undefer <id> --json`** — the deferred (or restored) issue, the
mutating-verb echo exactly as `create`; no additional fields. The observable
change is `deferUntil` (present while a deferral is set — even one already in
the past — absent after `undefer`) plus the recomputed `deferred`/`ready`
booleans. Deferring to an instant at or before now leaves the issue workable
and discloses it with a top-level note (`…already past — not deferred`);
re-deferring to the identical instant, or undeferring an undeferred issue,
appends nothing and still echoes the issue — the JSON carries no
applied-vs-noop marker (the human line words the difference).

**`tl reopen <id> --json`** — the reopened issue (echo, exactly as `create`):
`status` back to `open`, `closeResolution` and `closedAt` absent, any
holdover `assignee` cleared. The no-op is value equality, deliberately not
just `status == open`: only an issue that is already open with no
`closeResolution` and no assignee appends nothing (same echo either way) — a
merge-materialized open-but-assigned issue still gets a real reopen that
clears the assignee.

**`tl dep add / dep remove --json`** — a relationship ack in the pinned edge
orientation (`from` blocks `to`; for `parent`, `from` is the parent —
ADR-0003):

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "type": "blocks", "from": "tl-kz8w2n4jp7e9h3vt", "to": "tl-9f3cq7rkv2m8e4ha",
  "status": "added"
} }
```

(`"status": "removed"` for `dep remove`; a remove that observed no live tags
still succeeds — add-wins semantics — with `"status": "noop"`.)

**`tl dep relate / dep unrelate --json`** — the relationship ack with
`type: "related"`. `from`/`to` echo the *argument* order; the stored edge is
undirected (canonicalized to the sorted endpoint pair), so `relate A B` and
`relate B A` write the same edge:

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "type": "related", "from": "tl-kz8w2n4jp7e9h3vt", "to": "tl-9f3cq7rkv2m8e4ha",
  "status": "added"
} }
```

(`dep unrelate` answers `"status": "removed"`, or `"noop"` when the pair was
not related. `relate` has no noop: re-relating a related pair appends another
observed-add and still answers `"added"` — add-wins, same observable state. A
self-`relate` is a `usage` refusal; a self-`unrelate` is the `noop`.)

**`tl dep path <A> <B> --json`** — the blocks-chain witness between two
issues; all four fields always present, `path` the consecutive `blocks` chain
from `A` to `B` inclusive, empty exactly when `found` is `false`:

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "from": "tl-kz8w2n4jp7e9h3vt", "to": "tl-9f3cq7rkv2m8e4ha",
  "path": ["tl-kz8w2n4jp7e9h3vt", "tl-0dd3p1cqv2m8e4ha", "tl-9f3cq7rkv2m8e4ha"],
  "found": true
} }
```

**`tl dep critical --json`** — the open issues that block others, ranked;
`{count, items}` discipline:

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "count": 2,
  "items": [
    { "id": "tl-kz8w2n4jp7e9h3vt", "title": "Design the AST", "status": "open", "weight": 3 },
    { "id": "tl-9f3cq7rkv2m8e4ha", "title": "Write the parser", "status": "open", "weight": 1 }
  ]
} }
```

`weight` is the transitive dependent count over `blocks` (the proved reach⁺
cardinality — how much a close would help free); rows are the issues with
*effective* status `open` and `weight > 0`, ordered by `weight` descending,
ties by id ascending. In these rows `status` carries the effective status —
constant `"open"` by construction of the selection — and `title` is always
present, `""` when untitled.

**`tl parent set / parent remove --json`** — reparenting echoes the full issue
object (so the top-level `parent` field already shows the new canonical parent),
plus a `reparent` sub-object with the action metadata. `parent set` is a
courtesy *replace* (drop the child's other parent edges, add the target);
`replaced` lists the tombstoned parents (`status` ∈ `set` / `noop`):

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "id": "tl-9f3cq7rkv2m8e4ha", "parent": "tl-kz8w2n4jp7e9h3vt", "...": "…",
  "reparent": { "status": "set", "replaced": ["tl-0dd3p1cqv2m8e4ha"] }
} }
```

(`parent remove` carries `{ "status": "removed" | "noop", "removed": "<id>" }`;
removing a child's only parent drops the top-level `parent` field — it becomes a
root. A direct self-parent is a `usage` refusal; longer cycles stay *reported*
by `dep cycles`, never rejected — ADR-0003 §4.)

**`tl label add / label remove --json`** — a label ack in the same shape as the
relationship ack (`status` ∈ `added` / `removed` / `noop`; an add of a present
label or a remove of an absent one is the idempotent `noop`):

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "type": "label", "id": "tl-kz8w2n4jp7e9h3vt", "label": "feature", "status": "added"
} }
```

**`tl label list --json`** — the label vocabulary: every present label with how
many issues carry it, sorted by name; `count` is the number of distinct labels.

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "count": 2, "labels": [ { "label": "feature", "count": 3 }, { "label": "parser", "count": 1 } ]
} }
```

(`tl list --label <l>` is the issue-facet counterpart; its rows are the pinned
`list` item shape, unchanged — see *`tl list` filter facets* below.)

**`tl meta set / meta clear <id> <key> --json`** — a metadata ack: its own
`{id, key, value, status}` fields (no `type`/`from`/`to` — the ack names a
key, not an edge) with the relationship ack's `status` discipline:

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "id": "tl-9f3cq7rkv2m8e4ha", "key": "owner", "value": "carol", "status": "set"
} }
```

(`meta set` always answers `"set"` and echoes the written `value` — an LWW
register write is never a noop. `meta clear` answers `{id, key, status}` with
no `value` field: `"cleared"` when a value was present, `"noop"` when the key
was already clear.)

**`tl meta get <id> [<key>] --json`** — a read, two forms. Keyed:
`{id, key, value}` where `value` is the string value or `null` when the key
is absent (the pinned `|null` field — a missing key is an answer, not an
error). Keyless: every value-bearing key on the issue, key-ascending:

```json
{ "schemaVersion": 3, "ok": true, "data": { "id": "tl-9f3cq7rkv2m8e4ha", "key": "owner", "value": "carol" } }
{ "schemaVersion": 3, "ok": true, "data": { "id": "tl-9f3cq7rkv2m8e4ha", "count": 1, "meta": [ { "key": "owner", "value": "carol" } ] } }
```

**`tl meta list [<id>] --json`** — the key vocabulary. With an id: that
issue's value-bearing keys as an array of strings. Without: the project-wide
vocabulary in the `label list` shape — key-sorted rows, per-row `count` = how
many issues carry the key:

```json
{ "schemaVersion": 3, "ok": true, "data": { "id": "tl-9f3cq7rkv2m8e4ha", "count": 2, "keys": ["area", "owner"] } }
{ "schemaVersion": 3, "ok": true, "data": { "count": 2, "keys": [ { "key": "area", "count": 3 }, { "key": "owner", "count": 1 } ] } }
```

(The two forms share the `keys` name with different element shapes — a bare
string per key on one issue, a `{key, count}` row project-wide; the presence
of `id` discriminates.)

**`tl why <id> --json`** — the not-ready reasons, flat and omit-empty;
`blockedBy` is the *transitive unclosed* blocker set (ADR-0004 thm 10) with
enough context to act on each:

```json
{ "schemaVersion": 3, "ok": true, "data": {
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

**`tl unblocks <id> --json`** — the pre-close query dual to
`close.unblocked`: what closing `<id>` would make ready, computed without
writing anything. `freed` may be empty; `count` = its length:

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "id": "tl-9f3cq7rkv2m8e4ha",
  "count": 1,
  "freed": [
    { "id": "tl-kz8w2n4jp7e9h3vt", "title": "Design the AST",
      "status": "open", "effectiveStatus": "open" }
  ]
} }
```

Each `freed` row carries the stored `status` and the rollup-aware
`effectiveStatus`; `title` is omit-empty. The set and its order are the
kernel's `unblocks` (ADR-0004 thm 10) — the same set `close` then echoes as
`unblocked`.

**`tl dep cycles --json`** — the node-set witness per cyclic SCC (ADR-0004
thm 6), one entry per witness:

```json
{ "schemaVersion": 3, "ok": true, "data": {
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
{ "schemaVersion": 3, "ok": true, "data": {
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
{ "schemaVersion": 3, "ok": true, "data": { "root": ".tl", "replica": "chp14mvsxr027", "created": true } }
{ "schemaVersion": 3, "ok": true, "data": { "version": "0.1.0", "logFormat": 2,
  "build": { "kind": "clean", "commit": "<40-hex>", "dirty": false,
             "toolchain": "leanprover/lean4:v4.33.1", "manifestDigest": "<sha256 hex>" } } }
```

(`"created": false` on an idempotent re-run. `build` is the ADR-0006
build-provenance object, added here additively now that it has a pipeline to
produce it. `kind` is `development` | `dirty` | `clean` — see ADR-0006 "Tool
versioning" for what each asserts, and why there is no `release` value.
`commit` is `null` for a development build.)

**`tl help --json`** / **`tl help <command> --json`** — the command grammar,
machine-readable (ADR-0011 §1), for agent introspection. The full dump and a
single-command/group filter share one shape (an agent parses
`commands`/`globalFlags` either way):

```json
{ "schemaVersion": 3, "ok": true, "data": {
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
{ "schemaVersion": 3, "ok": true, "data": {
  "total": 23, "open": 16, "openEpics": 2, "openTasks": 14, "inProgress": 1,
  "done": 6, "cancelled": 0, "ready": 10, "blocked": 8, "deferred": 0,
  "cycles": 0 } }
```

`open`/`inProgress`/`done`/`cancelled` count *effective* status (rollup-aware —
a rolled-up epic counts as `done`, exactly as `list` and the glyphs render it),
so `stats` never disagrees with what `list` shows. `open` is split into
`openEpics` (open epics — children not all closed) and `openTasks` (open
non-epics), so an epic that is stored-`open` but effectively rolled-up is not
miscounted as workable. `ready`/`blocked`/`deferred` are the derived views;
`cycles` is the cycle-witness count (structural per kind plus the non-duplicate
readiness deadlocks, as `doctor`'s graph check).

**`tl log [<id>] [--since <cursor>] [--until <cursor>] --json`** — the op history
(an HLC-ordered projection over the log, ADR-0008); `<id>` filters to ops touching
that issue. With no bound it is newest-first, capped by `--limit` (default 10,
`0` = all). `--since` is a resumable forward change-feed — every op after the lower
cursor, oldest-first, exactly-once — and `--limit` defaults to `0` (all),
paginating the oldest first. `--until` browses backward — every op before the upper
cursor, newest-first — `--limit` defaults to 10 (a page, like plain log); it is
best-effort, not exactly-once (a still-merging log can gain an op below a page
already passed, ADR-0025). Given both, the bounds compose into a window.

Every response carries a top-level dual-edge `cursor` **object**
`{ "since": <resume-forward>, "until": <resume-back> }` (field names match the
flags), each a per-replica version vector serialized as comma-joined
`<replica>:<hlc>:<nonce>` triples sorted by replica: pass `cursor.since` to
`--since` to continue forward, `cursor.until` to `--until` to page older (full
semantics in ADR-0025). Forward emission is `(hlc, nonce) > since[replica]`
lexicographically (backward is `< until[replica]`), so a late foreign op below
another replica's maximum, and a same-replica op sharing an HLC (split by nonce),
are each delivered exactly once on the forward feed. A malformed cursor is a
`usage` error, never a silent full dump. `count` is the total matched (before
`--limit`); a cursor is scoped to the `<id>` filter it was produced under.

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "count": 41,
  "entries": [
    { "timestamp": "2026-06-11T01:27:49.277Z", "op": "close",
      "actor": "carol", "targets": ["tl-ppyg0ekgf91s56e0"] }
  ],
  "cursor": { "since": "93ac0kyg2gggt:116786845491855360:1",
              "until": "93ac0kyg2gggt:116786845491820032:1" } } }
```

`op` is the wire verb (ADR-0008's closed enum); `actor` is `|null`;
`targets` is the issue id(s) the op touched (one for scalar/meta/label ops,
both endpoints for edge ops — the same set `tl log <id>` filters on).

**`tl import <path> … --json`** — the import summary (ADR-0005): what one
fail-closed batch wrote. All five fields always present:

```json
{ "schemaVersion": 3, "ok": true, "data": {
  "issues": 3, "ops": 15,
  "replica": "chp14mvsxr027", "source": "github",
  "disclosures": []
} }
```

`issues` counts the imported records, `ops` the seed-log lines written,
`replica` the deterministic import replica id, `source` the `--source` tag
(default `import`). `disclosures` are ADR-0005's per-record disclosures
(clamped priority, skipped dangling edge, timestamp fallback, …); the same
strings are duplicated into the envelope's top-level `notes` (and stderr) —
in `data` they travel with the summary an agent stores. `<path>` is a JSONL
file or a directory of `*.jsonl`, unioned (ADR-0005); `/dev/stdin` works,
and a literal `-` is just a filename, so `not-found`.
A malformed line rejects the whole batch (`malformed-line`, nothing
written); re-seeding a repo that already holds task state requires
`--force`, and an input over the byte budget `--allow-large` (both refusals
are `force-required`).

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

### `tl list` / `tl ready` filter facets

`tl list` takes filter facets that narrow which issues appear. **Rows stay the
pinned `list` item shape above and `count` reports the post-filter total** — the
filters change the membership of `items`, never the JSON shape.

`tl ready` takes the `--label` and `--assignee` facets from the same table, with
the same semantics and the same shape rule: `count` is the post-filter total,
`items` the `--limit` head of it in ranked order (filtering preserves the rank),
and `staleness` is unaffected — it describes the *view*, not the result set. The
predicates and the human `[filtered by …]` echo are literally shared code
(`Tl.Cli.Commands.labelFacet` / `assigneeFacet` / `filterSuffix`), so the two
surfaces cannot drift. Neither `ready` facet can widen the result: `ready` is the
proved workable set (open, unblocked, non-epic, not deferred), so the
closed-gate bypass that `--status`/`--stale`/`--deferred` carry on `list` has no
counterpart there. Both halves of that shape rule are proved rather than
sampled, of the named expression `ready` evaluates (`Tl.Cli.readyRanked`):
filtering is a sublist of its input and a sublist of a ranked list is still
ranked, so `count` is the post-filter total of the same queue and the rank
survives it (`applyFacets_sublist`, `readyRanked_sorted`); `--limit` is the
named `readyPage`, with `readyPage_prefix` making `items` a *prefix* of that
filtered ranked list — covering the uncapped `--limit 0` branch as well as the
capped one — and `readyPage_length` pinning how long that prefix is, which is
what rules out the empty page the prefix law alone admits — and `readyPage_sorted` carrying the rank to the rendered page; and
membership is characterized rather than only bounded: a row is on the queue
exactly when the kernel calls it ready and every supplied facet accepts it
(`mem_readyRanked_iff`, over the `State.readyFast_eq` bridge — its
view-construction hypothesis discharged by `mem_readyRanked_ofLoaded_iff`),
which rules out under-reporting as well as widening; `readyRanked_cannot_widen`
is the forward half.

The other five `list` facets are deliberately **not** on `ready`:
`--status open` would be redundant because every ready issue is open, while its
other values, `--stale`, `--deferred`, and `--blocked` select for states that
`ready` excludes by definition and would therefore return nothing. `--priority`
is the one exclusion that is *not* forced — `ready` is
priority-ranked, so the ranking already answers "the important ones first", and a
priority *filter* would hide work rather than order it; it is left out until a
real need appears, and adding it later is additive.

`ready --assignee` is narrow by construction, and knowingly so: a claim writes
`assignee` together with `status := in_progress`, which `ready` excludes, and the
importer refuses to carry an assignee onto an open record — so there is no way to
pre-assign open work. What it matches is an open issue that still carries an
assignee, which only a merge can produce (a claim whose status write lost the LWW
to a concurrent `create`/`reopen` while its assignee write survived — ADR-0013).
That residue is exactly the state worth surfacing on a work queue: an item that
looks unclaimed but is spoken for. The facet is on `ready` because ADR-0013 and
the destination surface promised `ready --assignee me`, and it stays honest about
what it can match.

Neither verb echoes the active filters as a `data` field: the caller passed
them, and the human summary already names them. That is a deliberate omission,
additively fixable if a consumer ever needs it.

| Flag | Match |
|---|---|
| `--status <s>` | `open` / `in_progress` / `done` / `cancelled`; repeatable ⇒ **OR**; matches the row's `effectiveStatus` (rolled-up epics included). Naming a closed status (`done`/`cancelled`) includes closed issues without `--all` — it bypasses the default open-only gate, like `--stale`/`--deferred`. |
| `--assignee <name>` | the live-claim `assignee`; repeatable ⇒ **OR**; **exact**, case-sensitive (an identity is discrete, not free text). The reserved token `me` resolves to the **ambient** actor — the env/identity part of the ADR-0013 chain (`TL_ACTOR` → git config → `user@host`); a read filter has no `--actor` write-provenance override, and an actor literally named `me` is shadowed by the token. The raw `me` is echoed in the human summary, not the resolved identity. |
| `--priority <n>` | `0`–`4`; repeatable ⇒ **OR**; exact. There is deliberately no threshold form — a future `--min-priority` / `--max-priority` can be added additively without redefining `--priority N`. |
| `--blocked` | boolean; issues with ≥1 unclosed blocker (the derived `blocked` view). Stays within the open set — it does **not** bypass the closed-issue gate. Not the inverse of `tl ready` (which additionally excludes epics, in-progress, and deferred items) — just the blocked open set. |
| `--label <l>` | repeatable ⇒ **AND**; exact membership. |
| `--deferred` / `--stale <dur>` / `--all` / `--flat` / `--limit <n>` | the read facets and output controls carried elsewhere in the surface. |

Composition:

- **Different facets compose with AND** (each narrows). **Repeats within one
  facet are OR where an issue holds a single value (status / assignee /
  priority) and AND where it holds many (`--label`)** — an issue cannot be two
  statuses but can carry two labels. **Cross-facet composition is proved of the
  implementation; within one facet it is proved for the two facets `ready` and
  `list` share (`--label` AND, `--assignee` OR) and sampled for
  `--status`/`--priority`, whose facets are anonymous inline literals in
  `cmdList` with no name to state a theorem about.** Cross-facet: the fold is
  exactly a `List.filter` by the conjunction of every *active* facet's predicate
  (`Tl.Cli.applyFacets_eq_filter`) — one statement pinning which rows survive
  (`mem_applyFacets_iff`), in what order and with what multiplicity
  (`applyFacets_sublist`; a deduplicating fold satisfies the sublist law but not
  the characterization), and independently of the facet list's order
  (`applyFacets_of_perm`). It also settles the reading of an absent or empty
  flag — inactive facets contribute nothing rather than matching nothing, with
  `applyFacets_eq_self_of_inactive` at list-identity strength — and its dual,
  that a *supplied* flag is genuinely in play (`labelFacet_active_iff` /
  `assigneeFacet_active_iff`), which rules out a silently ignored facet. Within
  one facet: `labelFacet_pred_eq_true_iff` is the AND over exact label
  membership and `assigneeFacet_pred_eq_true_iff` the OR over the single held
  assignee (an unassigned issue matching neither —
  `assigneeFacet_pred_unassigned`); `mem_readyFacets_iff` composes the pair into
  the single statement `ready` instantiates — `list` shares the two facets but
  folds them inside a longer list with its own five, so what covers `list` is
  the general `mem_applyFacets_iff` over that list together with the two
  per-facet predicate laws. The two shared facets also provably leave the closed
  gate standing: `labelFacet_no_bypass` / `assigneeFacet_no_bypass` state it per
  facet, which with `facetsBypassGate_eq_true_iff` (a bypass has to come from
  *some* facet that asks for one — the gate `cmdList` consults) is what says
  sharing these facets with `ready` cannot introduce a bypass into `list`'s
  default view, whatever else `cmdList`'s list holds;
  `readyFacets_bypassGate_false` is the corollary at `ready`'s own pair.
- A flag value is the next token or `--flag=value`; repeat the flag to add (no
  comma-lists). The facets inherit the uniform `tl` parser and add no parsing
  rules of their own — including no new short aliases, though the global `-p` ⇒
  `--priority` alias reaches `list --priority` as it does every other command.
- The default open-only gate is bypassed by `--all`, `--stale`, `--deferred`,
  and a `--status` naming a closed status; the remaining facets refine whatever
  set those produce.
- The human summary names the active filters (`[filtered by …]`), with every
  echoed value sanitized so untrusted assignee/label text never reaches the
  terminal raw (the ADR-0017 render contract) and the assembled clause bounded
  like any other rendered field. The **zero-result** line names them too (`no
  issues [filtered by label nope]` / `nothing is ready [filtered by …]`): a
  typo'd value must not read as an empty backlog.
- Facet values use the complete stored string domain. Even an empty or
  control-only value remains exact-match queryable after a merge/import or an
  older write; when sanitization removes the whole value, the human echo uses
  `(empty after sanitization)` instead of a dangling clause. A *missing* value,
  an unknown facet, or a facet given to the wrong verb is still the uniform
  parser's `usage` error; the unknown-flag message names the command that *does*
  take the flag (`tl ready --status` → "`tl list` takes it"), derived from the
  grammar table so the hint cannot drift.

Deliberately **not** in this surface:

- **`--text <q>`** (free-text search) — **out of scope**, not merely deferred.
  The facets above are exact checks over materialized fields; a substring search
  without ranking or tokenization sets a find-everything expectation the tool
  would not meet, and doing it well is a project of its own. Full-text matching
  is also the one filter a consumer already has client-side (`tl list --json |
  jq` / grep). `tl`'s value is the structured facets; text search is not the
  tracker's job.
- **`--unassigned` / `--assignee none`** (issues with no live claim) — not built,
  but a clean additive extension if a real need appears.

## Consequences

- The stage-1 freeze is deliberate: every shape above was chosen, not
  emitted-by-accident — the failure mode the backlog item warned about.
- Agents get a uniform read/act loop: mutations return the updated issue, so
  `create → claim → close` needs no interleaved `show`s; `close.unblocked`
  feeds the next `claim` directly.
- A command built after the stage-1 set pins its shape here in the same
  change, following these conventions — as `log`, `stats`, `import`, and the
  `defer`/`reopen`/`meta`/`dep path`/`dep critical`/`dep relate`/`unblocks`
  families above now do; the backlog carries any not-yet-built verb until
  then. (`tl sync`'s payload is pinned where its semantics live, ADR-0016 —
  not duplicated here.)
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
