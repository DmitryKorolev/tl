# ADR-0013 — Actor identity, and the config-free stance

- Status: Accepted
- Date: 2026-06-04

## Context

Several commands need to know who is acting: `claim` sets
`assignee`, `ready --assignee me` filters on it, and the claim-contention
signal ("superseded by …", vision) compares the current assignee against a
recent local claim. Nothing yet says where that identity comes from.

Relatedly, settings-shaped things have accumulated — `$EDITOR`, `NO_COLOR`,
default priority, and now the actor — without a decision on whether `tl` has
a config file or stays env + flags only.

## Decision

### Actor identity

The current actor resolves in this order, first hit wins:

1. `--assignee <name>` flag, when the command takes one (explicit
   override, and what `claim --assignee=X` uses);
2. `TL_ACTOR` environment variable;
3. git `user.email` (via `git config user.email`);
4. `<os-user>@<hostname>` as a last-resort fallback.

This deliberately inherits the repository's existing git identity convention:
`git user.email` is already visible to collaborators through git history in a
normal shared repo. `tl` does not treat the actor as private. It may expose the
same identity through `refs/tl/log` before or more often than a code commit
would, so users or agents that want a non-PII handle should set `TL_ACTOR`
explicitly. If `--dir` / `TL_DIR` points at state outside any git repository, or
`git config user.email` is unset, resolution simply falls through to the
last-resort `<os-user>@<hostname>` label.

`me` (as in `ready --assignee me`) resolves to this same identity. The actor
is a free-form text label, carried as op data (the envelope `actor` field on
every op, ADR-0008; `claim` also writes it to the `assignee` field, ADR-0002) — it
is *not* the `replica-id` (ADR-0007). The two are
independent: replica-id identifies a *working copy* (for merge ordering and
segment ownership); the actor identifies a *person/agent* (for assignment and
the contention signal). One machine/replica may act as different actors over
time; one actor may write from many replicas.

Like clocks and IDs, the actor is resolved in the I/O shell and frozen into
every op as the envelope `actor` field (ADR-0008) — provenance the kernel
never reads (not part of the OR-Set/LWW key, so convergence is untouched). It
mirrors git's per-commit author, backs `provenance.createdBy` and per-op
authorship (ADR-0003), and is distinct from the `assignee` *field*, which only
`claim` / `update --claim` write. The kernel never reads the environment.

### The "superseded by …" signal is shell-only and replica-relative

The contention signal compares the materialized winning `assignee` (a
pure LWW value of the converged state) against this replica's own most
recent `claim` — read from its own segment `.tl/log/<replica-id>.jsonl`
(the same per-issue log scan `tl log <id>` uses, ADR-0008). It is therefore an
I/O-shell concern, not a kernel function: the converged state alone cannot
tell a replica that *its* actor claimed and lost, because that fact is
replica-relative, not a property of the merged state. `show` emits
"superseded by `<assignee>`" when the winner differs from that local claim and
the local claim is recent. Recent = within the same default stale-claim
threshold as `list --stale`, initially 24 hours, measured as
`now - claimedAt` against the query's injected `now` (ADR-0010); passing an
explicit stale duration to the relevant read command uses that duration for both
the stale marker and the superseded comparison. It is advisory output, never a
write-time guard. In `--json` it is structured, not prose: `show`
carries `claim: { outcome, currentAssignee }` (ADR-0003/0008) so an agent branches
on the outcome rather than parsing text.

### Config-free for now

`tl` has no bespoke config file. All settings come from environment
variables, git config, and command flags — `TL_ACTOR`, `TL_DIR`,
`$VISUAL`/`$EDITOR`, `NO_COLOR`, the `--color`/`--glyphs`/`--plain` output
surface (a CLI contract as stable as `--json` — additive-only from 1.0,
ADR-0008 §Stability horizon; `NO_COLOR` and a non-TTY
both force `--color=never`), and per-command flags. This matches the
"small, no daemon, no config server" ethos (ADR-0012 already rejected a
global store for *state*; this extends it to *settings*).

A `tl config` command and/or a config file is a clean additive extension
if real need appears (e.g. a persistent default priority or actor) — but it
is not built speculatively.

## Consequences

- `claim` / `--assignee me` are implementable against a defined
  identity, with sensible zero-config behavior (git email usually "just
  works") and explicit overrides for agents (`TL_ACTOR`).
- The PII exposure is accepted and documented. `tl` does not add a new
  authenticated identity system or hide git identity; `TL_ACTOR` is the escape
  hatch for shared repos and agents that want a stable non-PII handle.
- Actor vs. replica-id stay distinct, avoiding the bug of conflating
  "which working copy" with "which person/agent."
- No config parsing, no config-file format, no precedence-with-a-file
  matrix to design, test, or version yet — the surface stays minimal.
- Deterministic kernel preserved — the actor enters as op data, not an
  env read inside the fold.

## Alternatives considered

- Reuse `replica-id` as the actor. Rejected: a replica is a working copy,
  not a person; many tasks claimed from one checkout would all share an actor
  and one person across two machines would look like two actors.
- git `user.email` only. Rejected as the *sole* source: agents and CI
  often have no meaningful git identity; `TL_ACTOR` gives them an explicit
  one, and the fallback chain keeps it working with zero config.
- A config file from day one. Rejected: premature; env + git config +
  flags cover the current settings, and a file is additive later.
