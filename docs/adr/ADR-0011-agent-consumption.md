# ADR-0011 — Agent consumption: machine-readable reads and a skill

- Status: Accepted
- Date: 2026-05-31 (amended 2026-06-06)

## Context

`tl`'s whole reason to exist is to be genuinely easy for agents to
consume. A verified core nobody reaches for is worthless. There are two
audiences, and this ADR is about the second:

- agents building `tl` → served by `AGENTS.md`;
- agents using `tl` as a tracker → the consumption surface this ADR
  designs.

The established pattern for agent-facing tools bundles four things: a
snapshot command the agent reads on waking, a SessionStart hook that
auto-emits that snapshot after compaction/clear, machine-readable (`--json`)
output everywhere, and a published skill with a session-close protocol. We
adopt a deliberately reduced form of it. Examining the actual consumption
workflows (below) showed that two of those four — the bundled snapshot command
and the auto-emitting hook — were *aggregation and auto-injection machinery*
whose costs (a third pinned JSON schema that merely re-packages existing reads,
and a surface that pushes untrusted task content into an agent's context
unbidden) outweighed their benefit: every workflow that needed live state could
get it from the same read commands a human uses, with one explicit call the
agent was already positioned to make. So `tl` ships `--json`-everywhere, a
committed discovery pointer, and the skill — and serves live state through the
existing reads, not a bespoke command. The dropped approaches are recorded
under *Alternatives considered* so the reasoning survives.

## Decision

Ship three things, smallest-surface-first.

### 1. Machine-readable everything

- `--json` on every command (already decided, vision). Output is a
  stable, documented envelope.
- Stable exit codes and a JSON envelope so an agent programs against
  results, not prose. The concrete envelope shape (`{ schemaVersion, ok,
  data | error: { code, message, … } }`) and the named, closed error-code
  enum are pinned in ADR-0008 (co-located with the `--json`
  schemaVersion contract). The catalog the enum covers includes at least: no
  `.tl` project found (ADR-0012); an ambiguous id/slug/prefix; a malformed
  log line; an unknown (newer) log format version — fail-closed at *segment*
  granularity: the offending segment is refused whole and loudly disclosed;
  a refused *foreign* segment is not a command error (the read succeeds and
  folds the rest), while the replica's *own* — or every — segment refused
  fails the read (ADR-0008); a corrupt/unreadable — or range-exhausted
  (saturated, ADR-0007) — `local/clock`, or a corrupt
  `local/replica`; `no-upstream`; and `not-claimable`. Each maps to a distinct
  stable `code` and exit code, not a generic failure — the boundary handles bad
  input totally rather than excusing it. Each error's `message` is
  actionable — it names the fix (the
  id, the path, the next command), not just what failed — so an agent can
  self-correct from it, not only branch on `code` (a message that merely restates
  its code is a defect).
- `tl help --json` / a command schema dump, so an agent can introspect
  the verb/flag grammar instead of scraping `--help` text.

### 2. Live state through the existing read commands

An agent reads live state through the same verbs a human uses — there is
deliberately no single bundled snapshot command (see *Alternatives
considered*: the rejected snapshot command). The two primary surfaces serve two
different consumers and are deliberately not merged:

- `tl ready` — the work-selection surface. Consumer: anyone (agent or
  human) choosing *what to do next*. A ranked, filterable list of workable
  items (excludes epics, blocked, deferred; ADR-0004 order). This is the
  dominant wake-up call for a self-dispatching agent.
- `tl doctor` — the health/triage surface. Consumer: anyone checking *is
  anything wrong*. In Stage 1 it covers local replica-id/clock/log integrity,
  graph diagnostics (cycles, multi-parent, dangling edges), and stale claims (the
  same conditions `tl dep cycles` and `tl list --stale` expose individually,
  ADR-0003). In Stage 3, once sharing lands, it also reports remote sync posture.

Different cadence, different consumer, different question — folding them into
one command would couple two things that evolve independently. The rest of the
read surface (`tl show <id>`, `tl list --deferred`, `tl list --stale`,
`tl dep cycles`, `tl why`/`tl unblocks`) covers the remaining queries on
demand.

Sync-freshness — the "is my view stale before I trust `ready`?" signal —
is rehomed onto these two commands rather than carried by a bundled snapshot:

- `tl doctor` owns the sync posture row: `{ upstream: <name>|null, lastSync,
  ahead }`, or a `no-upstream` / `stealth` marker (ADR-0001), so an agent can ask
  "is my view fresh?" directly. **By default it contacts no remote** — `upstream`
  is resolved from git config, `lastSync` from a local marker a sync writes, and
  `ahead` is the count of local *ops* written since that last sync (the own
  segment on disk vs the synced ref's own-segment — so it is correct in the main
  worktree, where writes don't move `refs/tl/log` until a sync). The live
  *behind*-count needs the remote, so it is gated behind `--sync` (below) — which
  also makes `doctor` report what reconciling did (pushed / pulled) — not done on
  every `doctor`.
- `tl ready` surfaces a one-line advisory when the local posture says the view
  may be stale ("view may be stale — never synced / N local change(s) since last
  sync / last synced N ago; run `tl sync`"), so an agent selecting work sees
  staleness *inline* without a second call. It is advisory, derived, local-only
  state — it never blocks, alters, or networks on the read.
- **Amendment (2026-06-16, built): `--sync`.** Detecting how far *behind the
  remote* you are requires the network, which `ready`/`doctor` must not do on
  every (hot-path) call. So neither contacts the remote unless run with `--sync`,
  which is exactly `tl sync` *then* the command (reconcile, then read the fresh
  state) — the single opt-in freshness lever, also on `claim` (ADR-0001 §5). This
  supersedes the original "doctor computes live ahead/behind every call": the
  default posture is local; `--sync` is how you get a remote-fresh one.

Untrusted content stays explicit. Any command that emits issue objects
(`ready`, `show`, `list`) carries per-issue `provenance`
(`{source, createdBy, replica}`, ADR-0003), and every free-form content field
(`title`/`description`/`notes`/`labels`/`assignee`/`slug`/`meta`) is replica- or
import-authored data, not instructions (ADR-0014 T1). Because nothing is
auto-injected, an agent only ever ingests this content by *explicitly running
a read* — there is no packaged payload pushed at it on waking, and so no
unbidden-content path into its context.

### 3. Discovery: a committed pointer (no hook)

The durable, cross-clone, product-independent discovery path is a committed
pointer, not a hook. Under ADR-0001 nothing in `.tl/` is committed, so
`tl init` *offers* to add a one-line pointer to the repo's root agent
file(s) — `AGENTS.md` / `CLAUDE.md` / `GEMINI.md` and equivalents — ("task
state lives in `tl`; use the tl skill / these docs for how to work, run
`tl ready --json` for what to work on and `tl doctor` for project health"), so
harnesses (Codex, Claude Code, Gemini, …) that read those files surface `tl`
with zero configuration, depending on no specific agent product. `tl init`
also generates a local `.tl/README.md` primer (what `tl` is, the core
verbs, "run `tl ready` / `tl doctor`") for anyone who opens `.tl/` directly —
but it is gitignored, so the committed pointer is the discovery path.

The "offer" is non-interactive (built for agents / non-TTY): `tl init`
*prints* the suggested pointer line and which root agent file to add it to,
and **never auto-edits the user's committed files** — `tl` writes only inside
the gitignored `.tl/` (no surprise edits to `AGENTS.md` etc.). When no root
agent file exists it suggests creating one and creates none itself (the
no-auto-init ethos, ADR-0012). Placing the line stays a one-step human/agent
action; the primer is written (and refreshed) under `.tl/` on every `init`.

No SessionStart hook. An auto-emitting hook would have to inject either
full task content (an unbidden untrusted-content path into the agent's
context — ADR-0014 T1) or a content-stripped summary (a second pinned schema
existing solely to feed the hook). Both costs buy only the saving of a single
explicit `tl ready` call that a directed or self-dispatching agent is already
positioned to make. The committed pointer already makes `tl` discoverable with
zero config; proactive re-grounding after compaction is a one-call self-serve,
not a thing the tool must push. The hook and its summary schema are recorded
under *Alternatives considered*.

### 4. A Claude skill (and optional plugin)

A published skill teaching the command vocabulary and *when* to use it: the
work loop (`ready` → `claim` → `close`), dependency introspection
(`why`/`unblocks`/`dep cycles`), project health (`doctor`), and a
session-close protocol (before declaring done: check status, file
deferrals as tasks, close finished items). A plugin can bundle the skill for
one-step adoption.

### Consumption workflows

Two shapes the skill teaches, named because they justify *which* read commands
the consumption surface must expose:

Directed work — an orchestrator or human hands the agent a specific item.
No board-wide snapshot is needed; the agent already has the id.

1. `tl show <id>` — read the item: blockers, dependents, parent/children.
2. `tl claim <id>` — take it only if it is currently ready (sets
   `in_progress` + assignee). If it is not ready, `not-claimable` explains why
   (blockers, deferred, epic, closed, or already claimed); use `tl why <id>` /
   `tl show <id>` to inspect. Use `--verify` to make that ready-set preflight
   explicit against the freshest reachable state, and `--sync` to publish the
   claim immediately in a shared repo (ADR-0001).
3. Do the work.
4. `tl close <id> --as done` (or `cancelled` / `duplicate`). Spin out any
   not-now scope as a new linked task (`tl create "…" --related <id>` /
   `--blocks`), never a note on a closed item — the deferral-as-task
   discipline below.

Autonomous self-dispatch — the agent picks its own work off the queue.

1. *(Optional)* `tl doctor` — confirm nothing is structurally wrong. Once
   sharing lands, also use its sync posture and run `tl sync` if behind.
2. `tl ready --json` — take the top workable item (ranked; excludes epics,
   blocked, deferred). `ready` flags staleness inline if the view is behind
   upstream.
3. `tl claim <id> --verify` — claim it, skipping to the next if it is no longer
   ready (`not-claimable` explains the reason, including if another replica
   already claimed it).
4. Work → `tl close`. Loop.
5. After compaction / `/clear` / a new session, the agent re-grounds by
   *re-running* `tl ready` (and `tl doctor` if it needs health) — it
   re-queries live state rather than relying on auto-injected memory. This is
   the workflow the dropped hook would have automated; it is one explicit call.

### The deferral-as-task discipline

A first-class rule of the consumption guidance, drawn from standing project
practice: when wrapping up, *"not doing this sub-scope now"* becomes a new
open task via `tl create "<title>" --related <id>` (or `--blocks`), never a
note on a closed item — so deferred work cannot evaporate. It is a
discipline, not a command — there is deliberately no dedicated verb for
it. Do not confuse it with `tl defer` ([ADR-0010](ADR-0010-defer-until.md)),
which is *timed postponement of this same task*; spinning out new scope is a
plain `create` + link.

## Consequences

- Adoption is one step (skill plugin) and introspection is
  programmatic (`--json`, `help --json`, stable exit codes) — the two
  things that decide whether agents actually use a tool.
- Live state is served by the same verbs humans use. No bespoke
  aggregation command to keep in sync with the individual reads, and no
  second "summary" schema. `tl ready` (what to work on) and `tl doctor`
  (is anything wrong) serve two different consumers and evolve independently.
- No auto-injection surface. An agent ingests untrusted task content only
  by explicitly running a read, which simplifies the trust boundary — there is
  no hook-pushed-content path. ADR-0014 (T1) is updated to match: its
  mitigation no longer leans on the SessionStart hook or a hook-safe summary
  schema (both removed); the surfaced-content vector is now just the explicit reads
  (`ready`/`show`/`list`), which fence and byte-sanitize content and disclose
  per-issue provenance; that content is untrusted is documented in the schema
  contract and the skill (ADR-0014), not stamped on each payload.
- No orchestration. This is consumption ergonomics, *not* a workflow
  engine — `tl` exposes its state cleanly and stops there; dispatching,
  supervising, and sequencing agents remain out of scope (vision non-goals).

## Alternatives considered

- A bundled live-state snapshot command. A single machine-readable
  fold aggregating `ready` + `cycles` + `diagnostics` (multi-parent, dangling)
  + `deferred` + `staleClaims` + sync posture + actor + a guidance pointer,
  JSON by default. Rejected: it was pure aggregation — every section is
  already a read command (`ready`, `dep cycles`, `doctor`,
  `list --deferred`/`--stale`) — so it bought one round-trip at the cost of a
  third pinned JSON schema (additive-only forever, ADR-0008) that overlaps
  two existing ones and carries a standing drift risk against them. Its one
  packaging customer was the SessionStart hook; with the hook gone, nothing
  consumed the bundle that could not make the individual calls. Its one
  genuinely-unique signal — sync-freshness — is rehomed onto `doctor`/`ready`.
- A SessionStart hook auto-emitting state. A hook that runs on
  compaction/`/clear`/new-session to re-ground the agent automatically.
  Rejected: it must inject either full content (an unbidden untrusted-content
  path into the agent's context, ADR-0014 T1) or a content-stripped summary;
  both exist only to save the agent a single explicit `tl ready` call. The
  committed discovery pointer already makes `tl` discoverable with zero
  config, and re-grounding after compaction is a one-call self-serve.
- A hook-safe summary (counts + ids, content-free). A hook-safe
  projection that replaced issue objects with ids and counts. Rejected: it
  existed *solely* to make the hook's auto-injection safe. No hook → no
  auto-injection → no injection surface → no need for a content-stripped
  projection. Cutting it also drops a permanently-pinned (additive-only,
  ADR-0008) second JSON shape.
- Docs only (README + man page). Rejected: agents need a primer they
  *load*, not prose they might read; the committed pointer + skill is the
  load path.
- Bake context injection into every command's output. Rejected: noisy
  and wasteful per-call; the reads already carry exactly the state their
  caller asked for.
- A richer orchestration/dispatch layer (agent hooks, work queues,
  supervisors). Rejected: that is the workflow-engine scope `tl`
  deliberately excludes.
