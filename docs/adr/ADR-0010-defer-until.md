# ADR-0010 — Defer (defer-until)

- Status: Accepted
- Date: 2026-05-31

## Context

Postponement has three genuinely distinct needs, and they must not collapse
into one another:

- `blocked` — waiting on another *tracked* task; resolves when the
  blocker closes. Derived from the graph.
- an indefinite external wait — waiting on something *outside* the
  tracker with no known resume time. `tl` does not model this as a
  distinct state; it is expressed as a `defer` with a check-back date, or as
  an `open` issue carrying a `waiting:*` label.
- defer — work that *could* proceed but is deliberately postponed
  until a time, reappearing automatically when the time passes.

The third — timed, auto-resuming postponement — is the one not yet covered.
Importing an existing tracker's "deferred-until-date" tasks losslessly
([ADR-0005](ADR-0005-import-from-beads.md)) also needs a timestamp field, so
the model and the import line up.

(An earlier draft split this into a `snooze` field *and* a separate
`defer`-creates-a-task command. That was a conflation: "spin leftover scope
into a new task" is a usage discipline, not a postponement primitive, and
giving it the `defer` name collided with timed defer. Corrected here — see
the closing note.)

## Decision

Defer is a field, not a state: a `deferUntil` timestamp (LWW register) on
an otherwise-`open` issue. `ready` excludes a deferred issue until the time
passes; `deferred` is a derived view, not a stored status.

- Kernel representation: an opaque, totally-ordered instant. `deferUntil` and
  the injected `now` (ADR-0004) are the *same* abstract ordered type — a
  monotonic instant (concretely `Nat` milliseconds since the Unix epoch) the
  kernel compares only by `≤`, deriving nothing else from it. Parsing a
  `--until <date>` / `--for <dur>` into that instant — time zone, bare-date
  anchor, relative-duration base — is a tested I/O-shell concern (one
  normalization to a UTC instant on write), not a kernel one. So `Ready.lean`
  depends only on the ordering and is unblocked independently of that parsing
  decision (input-parsing rules still open: [design backlog](../design-backlog.md)).
- Wire encoding, and the two time types. On disk `deferUntil` is an
  ISO-8601 UTC instant string (e.g. `2026-06-15T09:00:00Z`), or JSON `null`
  when cleared — the shell normalizes any `--until`/`--for` input to that single
  UTC instant on write (ADR-0008). It is deliberately not an HLC: the design
  carries two time types — HLC-valued provenance (`createdAt`/`claimedAt`/…,
  the 16-hex ordering clock, ADR-0007) and this plain wall-clock instant
  (`deferUntil`/`now`). They meet in exactly one place — the stale-claim compare
  `now − claimedAt` (ADR-0013) — which reads the physical-ms component of the
  `claimedAt` HLC against the `now` instant; the kernel's `Ready` defer check uses
  the instant alone.
- Field over state because it (a) auto-resumes — once `now ≥ deferUntil`
  the issue is ready again, no manual transition — and (b) composes: a
  deferred *and* blocked issue stays not-ready for both reasons. Same
  derived-exclusion pattern as `blocked` and epics (ADR-0003).
- Derived view: `deferred s now i := open i ∧ (deferUntil i).any (· > now)` —
  an absent `deferUntil` is treated as −∞ (not deferred), so the
  `ready`-conjunct `(deferUntil i).all (· ≤ now)` holds vacuously and
  `deferred` is its exact complement on open issues (the convention ADR-0004
  theorem 4 reads).
  Re-defer = an LWW write of a new time; `undefer` clears it.
- Commands: `tl defer <id> --until <date>` / `--for <duration>`,
  `tl undefer <id>`, `tl list --deferred`. `tl why` reports "deferred until
  T" as a reason an issue is not ready.

### Consequence for `ready` (signed-off tradeoff)

`ready` becomes a function of state and current time. This stays inside
the "clocks are data" rule ([ADR-0001](ADR-0001-op-log-on-dedicated-ref.md)):
`now` is an injected parameter, so the kernel stays deterministic.
Theorem 4 (ADR-0004) gains one conjunct and a parameter:

```
ready s now = { i | open i ∧ ¬isEpic s i
                      ∧ (∀ b ∈ blockers s i, closed (effectiveStatus s b))
                      ∧ (deferUntil i).all (· ≤ now) }
```

still total, still provable. Defer simply adds a fourth definitional
exclusion alongside not-open, epic, and unclosed-blocker. The honest
deadlock-freedom theorem (ADR-0003/0004 theorem 5) carries `non-deferred`
into its live-working-set hypothesis; it is not the (false) biconditional
"empty `ready` ⟺ every open issue is cycle-blocked or deferred" — an
`in_progress` blocker stalls `ready` with neither a cycle nor a defer.

## Consequences

- Lossless import of timed-deferral data. A source `deferUntil`-style
  timestamp (and any "deferred" status) maps to `open` + `deferUntil` with no
  translation gymnastics (ADR-0005).
- Time enters `ready` as an injected parameter only — no impurity in the
  kernel; replicas agree given the same `now`.
- One field, one conjunct, one derived view — minimal surface, no new
  command beyond `defer`/`undefer`.

## Alternatives considered

- Call it `snooze` / make it a status. Rejected: a status needs a manual
  transition back (no auto-resume) and collides with `blocked`; a field
  auto-resumes and composes.
- Two commands (a timed `snooze` *and* a task-spawning `defer`).
  Rejected — this was the original muddle. Timed postponement is one
  primitive (`defer`); spinning out scope is a discipline (below).
- A separate `hold` state for indefinite external waits. Rejected as
  feature creep: `defer` with a check-back date covers nearly the whole niche
  (and auto-resurfaces rather than waiting to be manually un-held), and a
  truly-indefinite park can be an `open` issue with a `waiting:*` label. One
  fewer status, transition, and field. Additive to introduce later if a real
  need for a never-auto-resurfacing park appears.

## Note: deferral-as-task is a discipline, not a command

*"I'm not doing this sub-scope now"* is handled by filing the leftover scope
as a new open task — `tl create "<title>" --related <id>` (or `--blocks`)
— never a note on a closed item, and never a dedicated verb. It is the
usage-side practice recorded in `AGENTS.md` and
[ADR-0011](ADR-0011-agent-consumption.md); it is unrelated to `defer`, which
is *timed postponement of this same task*.
