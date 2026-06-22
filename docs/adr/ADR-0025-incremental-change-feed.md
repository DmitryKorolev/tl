# ADR-0025 — Incremental change feed: `tl log --since` and the version-vector cursor

- Status: Accepted
- Date: 2026-06-21

## Context

[ADR-0011](ADR-0011-agent-consumption.md) serves agents that *use* `tl` with an
awareness model: read the snapshot, re-fold full state per invocation. That is
fine for "what should I do now," but an external supervisor, a wake-on-change
dispatch loop, or an orchestrator control plane needs the dual: a resumable tail
of *what changed since I last looked*. Without a first-class feed, every consumer
re-implements log diffing and dedup against `refs/tl/log`.

The log is an append-only set of per-replica op segments (ADR-0001), each op
carrying a `Stamp` `(hlc, replica, nonce)` (ADR-0007). A naive `--since <hlc>`
cursor — a single scalar high-water mark — is unsound on this substrate. The HLC
only advances the *local* clock, so a late-synced op from a lagging replica can
carry an HLC *below* another replica's watermark; a scalar filter silently drops
it. The fold is order-insensitive and the merge can introduce an op "below" where
a reader already was, so the feed must tolerate that without losing or
duplicating an op.

## Decision

Add `tl log [<id>] --since <cursor>` (`--json` and human alike): a read-only
projection over the op log returning the ops after the cursor, oldest-first, for
incremental tailing. No new `Op`, no kernel theorem — a derived read (ADR-0004
tier 2, tested shell code).

### The cursor is a per-replica version vector over `(HLC, nonce)`

The cursor records, for each replica (its decoded id), the highest `(hlc, nonce)`
already delivered. An op is emitted iff its `(hlc, nonce)` is strictly greater
than its replica's threshold (lexicographic). This is the log's true
intra-replica order: two ops can share an HLC and are separated by the nonce
(ADR-0007), so the cursor must track both, not the HLC alone.

This delivers each op exactly once across resumptions, including the two cases
that break simpler cursors:

- a late foreign op whose HLC is below another replica's maximum (a scalar
  high-water mark drops it — the per-replica thresholds keep it);
- two same-replica ops sharing an HLC, separated by nonce (an HLC-only
  per-replica frontier drops the second on resume — the `(hlc, nonce)` order
  keeps it).

`advancedCursor` is the input cursor raised by the ops actually delivered (the
`--limit`-capped page), so `--limit` paginates the feed without skipping. In
plain mode (no `--since`) the reported cursor is the full frontier of the visible
log — a start-from-now anchor, like a consumer beginning at "latest".

### Wire format and validation

The cursor serializes as comma-joined `<replica>:<hlc>:<nonce>` triples, the
replica in its canonical 13-char Crockford form, sorted by replica (so equal
frontiers render identically). A trimmed-empty token is the empty cursor (full
history, "earliest"). Every non-empty token is validated as strictly as the wire
decoder `decodeStamp` (ADR-0008): the replica must be a canonical 13-char
Crockford id below `2^64`, the hlc and nonce numeric; a malformed segment, an
empty `:`-field, a stray/trailing comma, or an out-of-range replica is a `usage`
error that names the expected shape — never a silent full dump.

### Scope of the cursor

A `--since` cursor is scoped to the `<id>` filter it was produced under (the
frontier is computed over the ops the feed delivered). Resume with the same
filter. Cross-filter resumption is undefined.

### Output shape

`data` carries `count` (total matched, before `--limit`), `entries` (the ops, in
the existing `{timestamp, op, actor, targets}` shape — unchanged, ADR-0020), and
`cursor`. The human view shows the same ops plus a `cursor:` line.

## Extensions

The cursor primitive above is the load-bearing part; these build on it additively.

- **Dual-edge cursor + cursor-valued `--until` (shipped).** The response `cursor`
  is an object `{ since: <resume-forward>, until: <resume-back> }` (field names
  match the flags): pass `cursor.since` to `--since` to continue forward,
  `cursor.until` to `--until` to read ops older than this page. Each edge always
  brackets the *delivered* page, so no op is unreachable — but the two edges are
  not interchangeable directions through one feed: a forward `--since` feed is
  continued with `cursor.since` (its `cursor.until` then points below the feed's
  oldest op, into pre-feed history, and on a one-op page coincides with
  `cursor.since`), and a backward `--until` browse is continued with `cursor.until`.
  `--until <cursor>` browses history backward — ops before the upper cursor,
  newest-first — and `--since C1 --until C2` composes into a bounded window. `--since` (forward) is exactly-once; `--until` (backward browsing of
  history) is best-effort — a still-merging CRDT log can gain an op below where a
  backward page already passed. The resume-back edge is the per-replica minimum of
  the delivered page accumulated onto the input upper bound (the dual of the
  forward edge's accumulation onto the lower bound), so paging back never
  re-delivers a replica bounded by an earlier page; at a boundary HLC shared by two
  replicas the per-replica thresholds differ by the `(hlc, replica, nonce)`
  tie-break. `--since` drains by default (`--limit 0`); `--until` and plain log
  page (`--limit 10`).
- **`--since` / `--until` as the universal temporal-bound pair (planned).** Beyond
  the cursor value (log only, shipped above), `--since`/`--until` will also accept
  a duration (`1h`, `7d`) or a date/timestamp (`2026-06-21`) — the same meaning in
  every command that takes a time, with `--last N` a count tail and `--since all`
  an explicit from-start. That duration/date grammar is decided once and shared
  with `defer` (`--until`/`--for`, ADR-0010) — not a second parser. Times are
  best-effort over physical wall-clock (skew-sensitive); the cursor is the exact,
  resumable form.
- **Title in the human view (planned).** The human `log` line shows each target's current
  title (sanitized, ADR-0014; truncated; via the indexed view, ADR-0024, not an
  O(N) find per op). The `--json` entry stays id-keyed: the feed is an immutable
  op stream and the title is mutable state derivable from the id, so this is a
  deliberate, recorded human/JSON divergence rather than a parity gap.

## Consequences

- **Exactly-once is forward-only.** `--since` over the retained log delivers every
  op once. Backward browsing (`--until`) is a best-effort view of currently-known
  history.
- **Compaction interaction.** Compaction is non-destructive (ADR-0008 rescoped,
  ADR-0022): the full op log is retained, so any cursor — however old — is always
  serviceable, and exactly-once holds indefinitely with no retention horizon. If
  a future opt-in destructive GC is ever built, a `--since` cursor below the GC
  horizon must report a gap and resync from a snapshot; that contract is reserved
  but dormant. The cursor and a snapshot frontier are the same version-vector
  primitive, which is why ADR-0008 reserved the shape — but they are distinct
  roles: the cursor is a *per-consumer position*, the snapshot frontier is a
  *global causal-stability frontier*.
- **Relationships.** Keys on the HLC/replica identity of ADR-0007; the byte shape
  is pinned in [ADR-0020](ADR-0020-json-data-shapes.md); the consumption context
  is [ADR-0011](ADR-0011-agent-consumption.md); the snapshot interaction is
  [ADR-0008](ADR-0008-log-format-versioning-compaction.md); the shared time
  grammar is [ADR-0010](ADR-0010-defer-until.md).

## Alternatives considered

- **Scalar HLC cursor** (`--since <hlc>`): rejected — silently drops a late
  foreign op below another replica's watermark. The original soundness reason the
  version vector was reserved (ADR-0008).
- **Per-replica HLC-only frontier** (`replica → max hlc`): rejected — drops the
  second of two same-replica ops sharing an HLC, since nonce is the real
  tiebreaker (ADR-0007).
- **Offset / page-number pagination**: rejected — unstable on an append-only,
  CRDT-merged log, where a sync can land an op "in the middle" and shift every
  offset. Cursors deliver each op once regardless of concurrent appends.
