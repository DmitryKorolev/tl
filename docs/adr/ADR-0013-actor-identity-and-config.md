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

1. `--actor <name>` flag, when the command takes one (the explicit
   provenance override; the env form is `TL_ACTOR`);
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
`claim` / `claim --steal` write and `reopen` clears (§ the actor/assignee split below).
The kernel never reads the environment.

### The "superseded by …" signal is shell-only and replica-relative

The contention signal checks whether this replica's own most recent
`claim` — read from its own segment `.tl/log/<replica-id>.jsonl` (the same
per-issue log scan `tl log <id>` uses, ADR-0008) — still *holds* in the
converged state. A claim writes `in_progress` + `assignee` at one stamp, so
holding is a property of **both** registers — the decidable form of the
kernel's proved `ClaimWon` predicate (`claimWonB`): both winning entries are
one claim's exact stamped writes, `(stamp, in_progress)` and
`(stamp, assignee)`. The assignee register alone would misreport a concurrent
close — which outstamps `status` but never writes `assignee` — as a win on a
closed issue. On `tl claim`'s own echo the outcome is binary: `won` when the
just-written claim holds, else `superseded` — including a partial survival
(assignee kept, status lost to a concurrent close or status-only write),
which the human line explains (the surviving assignee, the resulting status,
and what to do next — the truthful status/assignee ride the JSON payload)
rather than emitting a bare "superseded". `show`'s claim block adds two
refinements: it reads `won` whenever the *actor's current* claim holds —
`claimWonB` at the winning assignee stamp, at or after the surfaced claim —
so the same actor's re-claim after a reopen (from any replica) is not
misreported as a loss; and it reads `ended` (not `superseded`) when the claim
no longer holds but the winning status write is this replica's *own later*
close or reopen — the claim ended by its own successor write, history rather
than a lost race. Which claim is "this replica's latest" stays an I/O-shell
concern: the converged state alone cannot tell a replica that *its* actor
claimed and lost, because that fact is replica-relative, not a property of
the merged state. The block appears on **every** `tl show`, decoupled from
any age window (it is the replica's own provenance, so age never hides it).
The *stale-claim* window is a
separate concern, read by `doctor` and by `claim --steal` (§ takeover
below), with **no default**: it is the `tl.staleAfter`
git config (a compact relative duration — `45m`/`1h`/`24h`), measured as
`now - claimedAt` against the query's injected `now` (ADR-0010); unset ⇒
`doctor` reports no stale verdict. `tl list --stale <duration>` takes the
window as a mandatory argument (also no default). It is advisory output,
never a write-time guard. In `--json` it is structured, not prose: `show`
carries `claim: { outcome: won|superseded|ended, currentAssignee }`
(ADR-0003/0008) so an agent branches on the outcome rather than parsing text.

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

## The actor/assignee split, claim-only assignee, and takeover

Four freeze-sensitive decisions settle the actor/assignee surface before the
CLI ossifies:

- **Provenance flag `--actor`.** The acting-identity override (the resolution
  order above) is `--actor <name>`, matching the `TL_ACTOR` env form; the old
  `--assignee` spelling for provenance is dropped. `--assignee` is reserved for
  the assignee concept — the `--assignee me` read filter on `ready`/`list` (the
  facet grammar is settled separately). One flag no longer carries both
  provenance and assignment.
- **Claim-only `assignee`.** The `assignee` field is written only by `claim`
  and `claim --steal`, and cleared by `reopen`; neither `create` nor `update`
  may set it (a record carrying an `assignee` key preserves it in the unknown
  bag, never applied). So in the **steady state** an open issue carries no
  assignee — only a live claim sets one, and the claim moves the issue to
  `in_progress`. This is *not* an absolute invariant: `status` and `assignee`
  are independent LWW registers, so a CRDT merge can still produce a transient
  open-but-assigned state — a `claim` (which writes `in_progress` + `assignee`
  at one stamp) stamped *below* a later status write (a `create` or `reopen`
  under clock skew, or a crafted segment) loses the status LWW but keeps the
  assignee LWW. No write-time guard could forbid that merge (§core-principle-2);
  the superseded signal and a future `list --stale` are *derived* and tolerate
  it — such a split is exactly a *partial claim win*, which the both-register
  outcome above classifies as `superseded` (never `won`; the kernel's
  `ClaimPartial.not_won`). `tl reopen` is the CLI remedy: it is a value-equality idempotent (it fires
  unless the issue already equals open + no-resolution + no-assignee), so it
  clears any such smuggled-in assignee and restores the steady state.
- **`reopen` clears `assignee`.** Returning a closed issue to `open` clears the
  assignee alongside `closeResolution`; `claimedAt` is already absent after a
  reopen, so the issue becomes unassigned until re-claimed (the ADR-0008 reopen
  delta).
- **Takeover via `claim --steal`.** Taking over an already-claimed item is
  `claim <id> --steal`, allowed only when the existing claim is stale — by an
  inline `--stale <duration>` or the configured `tl.staleAfter` (no default). It
  writes an ordinary `claim` (status `in_progress`, the stealer as assignee, a
  fresh `claimedAt`), keeping lifecycle in `claim` and letting `doctor` name the
  exact fix. The staleness test is a local courtesy guard, never merge-enforced:
  two replicas can both steal, LWW keeps the later stamp, and the loser reads
  "superseded" — the existing claim-race contract. A separate `reassign` verb,
  and reassignment without a claim, are rejected.

First-class **routing** — earmarking an open task for an agent to pick up once
it is ready — is deferred, and stays available as an additive later step (relax
`assignee` to an earmark, or add a distinct `owner` field with `ready --owner
me`), with an `owner:*` label as the interim. Choosing claim-only now re-admits
an assignee writer later as a new allowed state, with no data migration.

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
