# tl — a dependency-aware task tracker for agents

`tl` ("task list") lets an agent track its work — tasks, epics, and the
dependencies between them — in the same git repo as the code, without a separate
service and without cluttering your code commits. Its job is to answer one
question:

> *"What can I work on right now, and is the dependency graph sane?"*

The answer survives an agent's context being cleared, and several agents can write
to it at once without merge conflicts.

That question is a pure function over state, so `tl` proves it correct in a small
verified kernel and confines everything that can't be proved (file I/O, the CLI,
git transport, the one-time import) to a tested shell.

This document is the front door: scope, architecture, and the
proved-vs-tested boundary. The decisions behind each choice live in the
ADRs (`docs/adr/`); when this document and an ADR conflict, the ADR is the
record and this document should be updated to match.

## Migrating existing data

`tl` owns its own native format. It can do a one-shot import from an
existing tracker's data (ADR-0005) and is the source of truth thereafter —
a migration, not an ongoing integration. `tl` owes no external tool any
format or output compatibility, which is what lets the storage format be
whatever the verified core wants.

## Task states

A small stored set, with the busy states *derived* from the graph rather
than stored (so they can never drift from the edges that define them):

| State | Stored? | Meaning |
|---|---|---|
| `open` | stored | not started |
| `in_progress` | stored | claimed / being worked |
| `done` | stored, terminal | completed |
| `cancelled` | stored, terminal | won't do / duplicate — closed but not done |
| `ready` | derived | `open` ∧ no unclosed blockers ∧ not an epic ∧ not deferred |
| `blocked` | derived | `open` ∧ ≥1 unclosed blocker (a blocker not yet `done`/`cancelled` — includes an `in_progress` one) |
| `deferred` | derived | `open` ∧ `deferUntil` in the future (ADR-0010) |

`done` and `cancelled` both count as *closed*, so both discharge a blocker
(abandoned work does not strand its dependents). An epic is never marked
*done* manually — it is `done` iff all its children are closed; the one
manual terminal it accepts is `cancelled` (via `close --as cancelled`), which takes precedence over the
derived rollup (ADR-0003).

No hard delete. There is no `tl delete`. To make an issue disappear, use
`tl close --as cancelled` — it stays closed-and-out-of-the-way while keeping
every reference to it valid and merge-clean. (OR-Set *removal* is reserved
for edges — `dep remove` / `unrelate`; an issue is never removed from the
set, only resolved. This avoids the dangling-reference and resurrection
hazards a concurrent delete-vs-edit would create; see ADR-0002.)

### Issue fields

An issue is a record of fields, each a last-writer-wins register (ADR-0002)
except where noted:

| Field | Type | Notes |
|---|---|---|
| `id` | Crockford-base32 hash | immutable identity / OR-Set key (ADR-0007) |
| `title` | text | one line |
| `status` | closed enum | `open / in_progress / done / cancelled`; a new issue defaults to `open` |
| `priority` | `0`–`4` (`Fin 5`) | 0 = highest; default 2; an out-of-range value clamps to `0..4` on parse/import, with disclosure (ADR-0002) |
| `assignee` | text? | optional free-form actor label; `claim` sets it to the current actor (ADR-0013) |
| `labels` | set of text | OR-Set; categorical tags, filter facets only, drive nothing |
| `description` | text? | optional freeform body — task *input* (whole-field, not threaded) |
| `notes` | text? | optional freeform body — task *output* / human notes (whole-field, not threaded) |
| `slug` | text? | optional display handle, not identity (ADR-0007) |
| `deferUntil` | ISO-8601 UTC instant? | timed postponement; stored as a normalized UTC instant string, distinct from the HLC (ADR-0010) |
| `createdAt` / `updatedAt` / `closedAt` / `claimedAt` | timestamp (derived) | provenance projected from the log at fold time, not stored (`claimedAt` backs `list --stale`); exact projection rules in ADR-0008 |
| `closeResolution` | `done\|cancelled\|duplicate` | the resolution, distinct from `status` (`duplicate` sets `status=cancelled`; `--of` records the canonical via the `duplicate-of` meta key) |
| `meta` | `key → text` map | per-key-LWW side-channel for opaque values (`ext:*` source refs, `due_at`, imported comments); drives nothing (ADR-0002/0005) |
| `provenance` | derived JSON object | output-only trust/provenance projection (`source`, `createdBy`, `replica`) for consumers; imported issues report `source:"imported"`; free-form content remains untrusted data (ADR-0003/0011/0014) |

Hierarchy (`parent`) and dependencies (`blocks` / `related`) are edges
(ADR-0003), not fields. `labels` and `meta` are side-channels — a categorical
filter facet and an opaque per-key map (for imports / cross-tracker refs) — that
no theorem touches; a frame lemma isolates them (ADR-0002/0003). Reserved
prefixes (`type:*`/`waiting:*` for labels, `ext:*`/`import:*` for meta) are
case-folded courtesy conventions, not merge-enforced (ADR-0002).

### Status transitions

The ergonomic verbs guide normal flow:

```
open ──claim──▶ in_progress ──close──▶ done | cancelled
  ▲                  │                        │
  └──────────────────┴────────── reopen ◀─────┘
```

Out of `ready` without changing status: an `open` issue can be deferred
(timed, auto-resumes — ADR-0010), or held back by an unclosed blocker (the
derived `blocked` view). There is no separate "on hold" state — an
indefinite external wait is modelled as `defer` with a check-back date, or as
an `open` issue carrying a `waiting:*` label.

Two honesty notes about what the kernel does and does not guarantee:

- The status field is a closed enum — the kernel guarantees the value is
  always one of the valid statuses (unrepresentable otherwise).
- Transition *legality* (e.g. forbidding `open → done` without passing
  through `in_progress`) is not a merge-enforced invariant. Status is an
  LWW register holding the latest value, not its path, so a transition rule
  can only be a local courtesy guard (warn/refuse on the local CLI),
  exactly like the local cycle check (ADR-0003). Lifecycle changes go through
  the explicit verbs (`claim`, `close --as`, `reopen`), because those verbs also
  own the coupled provenance projections (`claimedAt`, `closedAt`,
  `closeResolution`); generic `update --status` is not part of the intended CLI.

## What is in scope

The command surface, grouped by the agent's loop (decompose → find → claim
→ progress → finish/unblock). Every command supports `--json`. Global
options apply everywhere: `--dir <path>` / `TL_DIR=<path>` point `tl` at an
explicit state directory (skipping discovery — for isolated test/CI runs),
and color/encoding are separate surfaces — `--json` is always machine-stable
and uncolored, human output takes `--color=auto|always|never`
(`NO_COLOR`/non-TTY ⇒ `never`) and `--glyphs=auto|unicode|ascii`, with `--plain` =
`--color=never --glyphs=ascii` (a vision-level CLI contract; `NO_COLOR` per ADR-0013).

Work loop

| Command | Effect |
|---|---|
| `tl create "<title>" [--blocked-by …] [--blocks …] [--related …] [--parent …] [-p PRIO] [--description <text>] [-]` | add an issue, wiring deps/links inline (no round-trips); body via `--description`, or a trailing `-` to read it from stdin (ADR-0017 §8) |
| `tl ready [--assignee] [--label] [--limit] [--sync]` | ranked, filterable list of workable items — the core feature; flags a one-line staleness advisory when the local view may be behind upstream (`--sync` = reconcile first, then list — ADR-0011) |
| `tl init [--stealth]` | create the (gitignored) `.tl/`, mint the replica-id, and (in a git repo) wire up sharing; `--stealth` = local-only, zero repo-visible trace. Grows across stages (ADR-0001 §4 / ADR-0012) |
| `tl import <path> [--force]` | one-shot migration from an existing tracker's data; refuses existing task state (local `.tl/log/` segments or a local/remote `refs/tl/log`) without `--force` (ADR-0005) |
| `tl sync` | publish/receive task state: fetch + union-merge + push the `refs/tl/log` ref (ADR-0001) — the transport, since `tl` never commits to your branch |
| `tl claim <id> [--sync] [--verify]` / `tl update <id> --claim` | take a ready item only; non-ready targets are refused with `not-claimable` and actionable reasons (direct unclosed blockers — `tl why` for the transitive set — deferred until, epic, closed/in-progress; ADR-0020). `--sync` publishes around the take; `--verify` is an explicit preflight against the freshest reachable state (ADR-0001/0003/0013) |
| `tl update <id> [--assignee] [-p] [--slug] …` | scalar field edits via flags (lifecycle status uses `claim`/`close`/`reopen`; edges use `dep`/`parent`, never `update`) |
| `tl edit <id>` | open title/description/notes in `$EDITOR` |
| `tl close <id> --as done\|cancelled\|duplicate [--of <id>]` | finish; any closed status discharges blockers (`duplicate` sets `cancelled` + records the canonical via `--of`). An epic can't be closed `--as done` (it rolls up); cancelling an epic leaves its children open and reparentable — there is no `--cascade` (cut, ADR-0003 §3) |
| `tl reopen <id>` | terminal → `open` |
| `tl defer <id> --until <date>` / `--for <dur>` / `tl undefer <id>` | timed postponement; auto-resumes (ADR-0010) |

Dependencies (typed relations — `blocks` / `parent` / `related`, ADR-0003)

| Command | Effect |
|---|---|
| `tl dep add A B` / `tl dep remove A B` | add / retract a `blocks` edge — A is blocked by B (subject-first, blocker-second, like `create A --blocked-by B`); the CLI echoes "A is now blocked by B" to remove doubt (ADR-0003) |
| `tl parent set <child> <parent>` / `tl parent remove <child> <parent>` | reparent — `set` moves the child under a new parent (a courtesy replace; multi-parent from merges is reported, not enforced), `remove` detaches (ADR-0003 §4) |
| `tl dep relate A B` / `tl dep unrelate A B` | symmetric, informational link |
| `tl dep cycles` | report cycles per kind and readiness-deadlock (`≺`) cycles (mixed blocks+parent, ADR-0004 thm 5/6) — a key util |
| `tl why <id>` | the transitive set of *unclosed* issues blocking this one, rendered as the upward blocker tree |
| `tl unblocks <id>` | what closing this would free, rendered as the downward dependents tree |
| `tl dep path A B` | show a dependency path (the tool for breaking cycles) |
| `tl dep critical` | rank open issues by transitive dependent-count |

Read / visibility

| Command | Effect |
|---|---|
| `tl show <id>` | one issue, with blockers + dependents + parent/children inline |
| `tl log [<id>]` | chronological action history (HLC-ordered); per-issue when `<id>` given (ADR-0008) |
| `tl list [filters]` | many: status / assignee / label / priority / text / `--blocked` / `--deferred` / `--stale [<dur>]` (default 24h, ADR-0013); `--all` includes closed, `--flat` for rows (the rest are the destination surface — see §Staged implementation for what ships today) |
| `tl label add <id> <label>` / `label remove <id> <label>` / `label list [<id>]` | manage categorical label tags (filter-only; drive nothing) |
| `tl meta set <id> <key> <value>` / `meta get <id> [<key>]` / `meta clear <id> <key>` / `meta list [<id>]` | manage the opaque metadata side-channel — `ext:<system>` refs, imported fields (ADR-0002/0005); drives nothing |
| `tl stats` | counts by state, #ready, #blocked, #cycles |
| `tl doctor [--sync]` | health check: replica-id/clock/log integrity and graph conditions — cycles, multi-parent, dangling `blocks`/`parent` endpoints, `duplicate-of` hygiene (dangling/self/chained targets, ADR-0008); plus a local sync-posture row (upstream / lastSync / ahead, no remote contact; `--sync` = reconcile first — ADR-0011/0001) |
| `tl help [<cmd>]` / `tl <cmd> --help` | human help: top-level overview or per-command usage |
| `tl help [<cmd>] --json` | the same grammar machine-readably, for agent introspection (ADR-0011) |
| `tl version` | print the `tl` SemVer product version (`0.1.0` initially); `--json` also reports log/JSON schema versions, plus build provenance once the release pipeline exists (ADR-0006/0008/0020) |
| `tl --licenses` | print bundled third-party license notices and link-time dependency attribution (ADR-0006) |

`dep remove` / `unrelate` are first-class, not afterthoughts: they are the
reason the edge set needs a remove-capable CRDT (ADR-0002).

List-like commands use one limit convention: `ready` and `list`
default to `--limit 50` (`log` to `--limit 10`); `--limit 0` means all; any
truncation is disclosed in human output and represented as a full `count` plus
capped `items`/`ids` in JSON.

### Ready ordering

`ready` ranks by a total, deterministic order, so the ranked queue is
identical across replicas given the same state — a stable, most-important-first
list for an agent (or orchestrator) to choose from:

1. priority ascending (0 first);
2. then critical-path weight — the number of distinct issues reachable
   from this one over `blocks` edges (`dep critical`), descending — do the
   most-unblocking work first. This is a *total* kernel function even on a
   cyclic graph (a finite reachable set, ADR-0004 theorem 4);
3. then createdAt (HLC) ascending — older first;
4. then id — the absolute tie-break (unique, so the order is total).

Totality matters: because the final key is the unique `id`, the sort is a
total order — so the `ready` list is unambiguous and reproducible across
replicas given the same state and `now`, not just a presentation nicety. An
agent picks a ready item by its own judgment and `claim`s it; an orchestrator
partitions the ranked list across agents by id. There is no atomic "take the
top" primitive — concurrent `claim`s to the same item converge by LWW, the loser
told ("superseded by …", ADR-0013), not by a distributed lock.

### Human output format and editing

Every command has `--json` (ADR-0011); the default human-readable output and
the interactive `$EDITOR` editing flow are pinned in
[ADR-0017](adr/ADR-0017-human-cli-output-and-editing.md). In short: a
one-line-per-issue list — a color-coded status glyph (`○ ◐ ● ✓ ✗ ❄`), id,
priority, an `[epic]` marker (epics only), and a width-truncated title — plus a
summary footer + legend and `show`/`stats` layouts; hierarchy, including nested
epics, renders as a tree (`list` — the default view, `--flat` for rows —
`why`/`unblocks`, `show`); color and glyphs
are independent surfaces (`--color` / `--glyphs`; `--plain` = both off;
`NO_COLOR` honored); and long `description`/`notes` open `$EDITOR` only on
`create --edit`, a no-title `create`, or `edit`. The machine path is `--json` —
never colored, never an editor.

### Minimal by design (deferred, with defaults on record)

These are intentionally small or absent in v1, recorded so the omission is a
decision, not an oversight:

- Comments/threads — out (non-goal). The single freeform `description`
  field covers "write context on a task"; there is no threaded-message
  subsystem.
- Deadlines (`due_at`). Not modeled as a field (no behavior acts on a
  deadline); preserved opaquely on import in the `meta` map (ADR-0005), so the
  data round-trips without becoming a feature. Distinct from `defer` (a
  deadline pulls work forward, a defer pushes it back).
- Time/duration input formats (for `defer`): ISO-8601 dates/datetimes
  (`2026-06-15`, `2026-06-15T09:00Z`) and relative durations
  (`30m` `2h` `7d` `2w`). Parsed in the I/O shell and normalized to a single UTC
  instant on write, stored as an ISO-8601 UTC string — distinct from the
  16-hex HLC used for ordering/provenance; a tested contract (ADR-0010/0008).
- Scale target. Designed for thousands of issues/ops per repo, read
  by a fold-per-invocation (ADR-0001/0008). The fold-only premise outgrew
  itself at dogfooding scale, so the pre-pinned cache is now **built**
  (ADR-0022): an automatic, self-validating fold cache in gitignored
  `.tl/local/` (keyed to log content; rebuilt from scratch if stale/absent) —
  never a user-managed command, no log format impact. Reads and writes fold
  only appended suffixes; everything a command *discloses* is still
  recomputed live per invocation.
- Settings are config-free — environment + git config + flags, no config
  file (ADR-0013). A `tl config` is additive if a real need appears.
- Parallel work fan-out, and no `next` verb. There is deliberately no
  "take the top ready item" command — `ready` lists the ranked candidates and the
  agent (or orchestrator) picks one by its own judgment and `claim`s it. Fan-out
  is partitioning: take distinct items by id from `ready --limit N --json` +
  `claim <id>`, no central queue. If two pick the same item (e.g. across clones
  before a sync), LWW resolves it — the loser is told "superseded" and is free to
  take another (guaranteed progress, no herd).
- An incremental change feed is available alongside the full-state awareness
  model: `tl log --since <cursor>` returns the ops after a per-replica
  version-vector cursor, a resumable tail for an external supervisor or
  orchestrator. Agents may still re-fold full state per invocation (fine at the
  thousands-scale target); the feed is additive. The cursor is a version vector,
  not a scalar HLC, so a late-synced op from a lagging replica is not missed
  (ADR-0008, ADR-0020).

### Staged implementation (the MVP cutline)

The full surface above is the destination, not the first commit. A build order,
each stage shippable and testable on its own:

- Stage 0 — kernel + log. The verified core — `State`, the seven `Op`
  deltas, `apply`, `ready` (with its critical-path-weight key and
  `effectiveStatus`/`Rollup.lean`, which `ready`/`cycles` depend on), `cycles`
  (per-kind + readiness `≺`-cycles), the convergence + `ready` theorems — and
  the JSONL round-trip + HLC/replica + a minimal `tl init` (create `.tl/`, the
  `*` self-ignore, mint the replica-id, seed the clock — not the `refs/tl/log`
  refspec/auto-sync, which land in Stage 3, nor the `.tl/README.md` /
  discovery-pointer, which land in Stage 2). No work-loop verbs yet.
  Proves the thesis is *buildable*. (The kernel rollup/weight functions live
  here; only the epic/critical-path *ergonomics* are Stage 2.)
- Stage 1 — the MVP work loop. `create` (with inline `--blocked-by` /
  `--blocks` / `--parent` / `--related`), `ready`, ready-only `claim`,
  `close --as`, a minimal `update` (non-lifecycle scalars —
  title/priority/description/notes; the `--claim` alias is Stage 2, and
  reparenting landed as the dedicated `parent set/remove` verbs, not
  `update --parent`), `dep add/remove`, `why`, `dep cycles`, `show`,
  `list`, a minimal `doctor` (local clock/replica/log health + graph
  diagnostics; remote sync depth grows in Stage 3), and `--json` everywhere. This is the
  whole thesis — *"what can I work on, and is the graph sane"* — and is enough
  for an agent (or several on one machine, sharing the local log) to run
  autonomously. (That "one machine" case is a
  single checkout; agents in separate worktrees are separate replicas that
  share through the common-`.git` ref and the cheap local-first sync leg
  (ADR-0016), so worktree-per-agent sharing wants that leg pulled forward.) Cross-clone coordination — the
  sync-bounded claim/"superseded" story — needs `tl sync` (Stage 3); pull a
  minimal `tl sync` forward if multi-clone sharing is wanted in the MVP.
- Stage 2 — ergonomics + decomposition. epic display ergonomics
  (the `[epic]` glyph, child-rollup views, auto-rollup UX — the
  kernel rollup itself is Stage 0), `defer` / `undefer`, `labels`, `meta`,
  `relate`, `dep path` and the `dep critical` *command* (its weight
  function is Stage 0), `unblocks`, `reopen`, `edit`, slugs, `stats`, `log`,
  and the agent surface (the discovery pointer + local `.tl/README.md`, and the
  skill).
- Stage 3 — migration + sharing. `import`, the `refs/tl/log` sync/transport
  (fetch / union-merge / push, auto-sync, push-rejection + no-upstream handling —
  ADR-0001), the distribution matrix (ADR-0006). Compaction stays deferred
  (ADR-0008).

A reader who implements only Stage 1 has a useful, autonomous-agent-ready
tracker; later stages are additive and never change the Stage-0 format or
theorems.

## What is deliberately out of scope

This list is a contract against feature creep, not a backlog:

- Any database server / daemon. `tl`'s source of truth is plain files in
  git. No SQL engine, no server process, no lifecycle to manage.
- Collaborative text editing. Descriptions and notes are whole-field
  values, not character-level CRDTs (ADR-0002). No RGA / no sequence merge.
- Comments/labels as logic. `description` and `notes` are single
  freeform fields (no threaded comments); `labels` are a filterable
  side-channel. All round-trip and can be filtered on, but no behavior or
  theorem depends on them — they never affect `ready`, rollup, or any
  invariant.
- Agent memory / knowledge store. Persistent agent knowledge is a
  separate concern and a separate tool. `tl` tracks tasks, not knowledge.
- Workflow orchestration. Dispatching, supervising, or sequencing agents
  is the consumer's job; `tl` exposes state and stops there (ADR-0011).
- Rich query / reporting / web UI / sync service. Out.

If a feature is not on the in-scope list, the default answer is no, and
adding it requires a new ADR that argues why it belongs in a *small*,
*verified* tool.

## Architecture in one breath

> `tl` is a pure verified fold (CRDT convergence + tracker invariants +
> total, cycle-aware `ready`) wrapped in a thin tested shell that appends
> operations to a log and lets git move the bytes.

The pieces:

1. Append-only op-log, git as transport (ADR-0001). State is never
   stored directly; it is a *fold* over an append-only log of operations.
   Each replica appends only to its own log segment; `tl` keeps those segments
   on a dedicated git ref (`refs/tl/log`, ADR-0001) — not the working
   branch — so publishing task state never touches the user's commits, and
   `tl sync` reconciles divergent refs by unioning the append-only segments
   (the CRDT join). `tl` implements no conflict-resolution merge; git transports
   the ref's bytes and the order/duplicate-insensitive CRDT fold reconciles
   them.

2. A minimal CRDT (ADR-0002): an OR-Set for the collections (issues,
   dependency edges, per-issue labels) and a last-writer-wins register for
   every scalar field — plus a per-key-LWW metadata side-channel that reuses
   the register's join. Two textbook lattice constructions (the third is the
   second lifted over a key map). Convergence reduces to: the fold is
   insensitive to the order and duplication of operations.

3. A verified kernel (ADR-0004): the lattice convergence theorems plus
   the tracker theorems — invariant preservation, and a `ready` that is
   total, sound, and complete *even on a cyclic graph*.

4. A tested I/O shell (ADR-0004): data import, JSONL serialization,
   logical-clock generation, git invocation, CLI. Structurally unprovable;
   covered by round-trip property tests and a differential harness.

## The one subtlety: acyclicity is reported, not enforced

Under a single writer, "the dependency graph is a DAG" could be a hard
invariant — a cycle would be an illegal, unrepresentable state. Under a
CRDT it cannot be, because a merge is not allowed to reject anything:
two replicas can each add a locally-legal edge that together form a cycle
(ADR-0003).

So `tl` makes acyclicity a derived, reported property, not a stored
invariant. `ready` is total on a cyclic graph — an issue trapped in an
unresolved cycle is simply not ready, and `tl` reports the cycle. This is
the honest version of the design, and it yields a more useful liveness
theorem than the naive one:

> If an open, non-epic, non-deferred issue has all its blockers closed,
> `ready` is non-empty. So when a set of such issues is stuck (empty
> `ready`), the only *tool-pathological* cause is a cycle in the
> readiness-dependency relation — `blocks` edges, with an epic blocker
> expanded to its open children, so a pure-`blocks` or a mixed blocks+parent
> loop — every other empty-queue case has an actionable reason (an
> `in_progress` blocker to finish, a defer to wait out, an epic that rolls
> up). This is deadlock-freedom, not the (false) claim "empty queue ⟺
> everything is cycle-blocked." Full statement: ADR-0004 theorem 5.

Handling the cycle case totally — rather than excusing it with a
"well-formed input" hypothesis — is a deliberate discipline: cycles are
runtime-reachable via merge, so the proof must cover them.

This is one instance of a principle that governs the whole design:

> In a CRDT world, every cross-entity rule is derived (true by
> construction) or reported (flagged after the fact) — never
> enforced at write time.

Three instances: `blocked` is derived (from unclosed blockers), acyclicity is
reported (`dep cycles`), and an epic's `done` is derived (from its
children, ADR-0003). A merge cannot reject a write, so a rule it could
violate must not be a write-time guard — it must be a total function of the
materialized state, which is exactly what makes each one provable.

## Verification strategy: prove the core, test the boundary

Mirroring the discipline `tl` was born from:

- Inside the kernel (state, the op fold, `ready`, cycle detection):
  covered by Lean theorems, not tests. A test is not a substitute for a
  property that can be stated and proved.
- Outside the kernel (I/O, CLI, git, clocks, the data importer):
  covered by tests — round-trip properties for serialization, and a
  differential harness that checks the importer against real source-format
  fixtures (ADR-0005). These are structurally unprovable in-kernel.

A green build proves the stated theorems. The differential import test and
the round-trip tests validate that the compiled binary behaves as the
spec claims. Both are necessary.

## Distribution

`tl` ships the Lean-compiled binary itself — so the artifact users run is
the artifact proved. Because Lean (unlike Go) cross-compiles poorly, the
binary is built natively per target in a CI matrix, and the install
channels (Releases, `curl|sh`, npm, Homebrew) are thin veneers over those
prebuilt binaries. Supported targets are Linux x86-64/aarch64, macOS
aarch64, and Windows via WSL2 (the Linux binary, recommended Windows path);
native Windows x86-64 and macOS x86-64 are best-effort; FreeBSD is a community
port. `git` is a runtime prerequisite (ADR-0001).
See ADR-0006 for the full matrix, glibc floors, and the GMP/LGPL licensing
boundary.

## Artifacts are human-readable

Code, comments, and commit messages stand on their own. No task-tracker
IDs leak into the durable record. (`tl` is itself a task tracker; the
temptation to cross-reference its own issue IDs into its own source is
exactly the thing to resist.)

## ADR index

- ADR-0001 — Append-only op-log on a dedicated git ref
- ADR-0002 — Minimal CRDT: OR-Set + LWW-register + metadata map
- ADR-0003 — Relations, cycles, and rollup
- ADR-0004 — The verified kernel and the TCB boundary
- ADR-0005 — One-shot bulk import
- ADR-0006 — Distribution and supported platforms
- ADR-0007 — Identity, HLC, and ordering
- ADR-0008 — Log format, JSON schema, and versioning
- ADR-0009 — Proof dependencies: batteries over Mathlib
- ADR-0010 — Defer (defer-until)
- ADR-0011 — Agent consumption: machine-readable reads and a skill
- ADR-0012 — Repo discovery and the directory override
- ADR-0013 — Actor identity, and the config-free stance
- ADR-0014 — Threat model and trust boundary
- ADR-0015 — Local concurrency and filesystem safety
- ADR-0016 — Same-machine sharing: worktrees and local-first sync
- ADR-0017 — Human-facing CLI: output format and editing
- ADR-0018 — Hand-rolled SHA-256 (pure Lean)
- ADR-0019 — Native primitives shim, and the FFI policy
- ADR-0020 — `--json` data shapes (the stage-1 surface)
- ADR-0021 — Auto-sync: a synchronous, best-effort local-leg publish
- ADR-0022 — The materialization fold cache
- ADR-0023 — Algorithmic efficiency: the proved/tested/assumed tiering and the prevention net
- ADR-0024 — Indexed views: accelerating proved collections behind an equality bridge

## Open questions (for iteration)

The live list of open design questions is the [design backlog](design-backlog.md);
two worth calling out here, both fine to defer past first implementation:

- When to *implement* compaction — the mechanism is reserved (ADR-0008);
  the trigger/threshold and the version-vector frontier computation are
  unbuilt.
- Contention UX polish — beyond the basic "superseded" signal, whether
  to add an advisory lease/heartbeat is open.
