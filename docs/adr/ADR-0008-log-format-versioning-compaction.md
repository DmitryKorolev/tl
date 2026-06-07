# ADR-0008 — Log format, versioning, and compaction

- Status: Accepted
- Date: 2026-05-31

## Context

ADR-0001 makes state a fold over an append-only op-log; this ADR pins the
concrete on-disk format, its version/evolution policy, and the
lifecycle of the log (it grows forever without compaction). The format
is a *permanent* compatibility surface: once a replica has written it,
every future reader must cope with it. Compaction, in turn, is harder than
it looks under a CRDT — dropping data safely is a distributed-GC problem —
so it is deferred, but the format must leave room for it now.

## Decision

### Record format

- Newline-delimited JSON (JSONL), one operation per line, UTF-8, LF
  line endings. (The branch-tracked `-text`/`merge=union` `.gitattributes`
  requirement is obviated under ADR-0001 — the log lives in `refs/tl/log`, not
  the working tree, so git never EOL-normalizes or merges it; `tl` writes the
  segments with LF and unions them itself.)
- Per-replica append-only segments at `.tl/log/<replica-id>.jsonl`
  (ADR-0001); `tl sync` unions them across replicas via `refs/tl/log` (ADR-0001).
- Every record shares a small envelope:
  - `v` — format version (integer; v1 = `1` is the baseline a first
    writer stamps — distinct from the product version (`tl version`) and the
    `--json` `schemaVersion` below);
  - `op` — operation kind, drawn from a closed enum (the readable wire
    verbs; see *Op kinds and payloads* below);
  - `hlc`, `replica`, `nonce` — the ordering/identity triple (ADR-0007);
    `hlc` is the 16-hex-char fixed-width string of ADR-0007 (a JSON string,
    never a bare number — 64-bit values exceed JSON's 2⁵³ safe range, where many
    parsers silently lose precision and corrupt LWW order); `replica` is 13 and
    `nonce` 26 Crockford chars;
  - `actor` — the resolved authoring actor (ADR-0013), free-form UTF-8 text (or
    `null`). It is provenance only: carried on every op and projected as
    `provenance.createdBy` / per-op authorship, but not part of the
    OR-Set/LWW identity key (the add-tag and LWW order use `(hlc, replica, nonce)`
    only), so it never affects convergence or the kernel. Part of the v1 baseline
    (an additive optional field — an old reader treats it as unknown); import seed
    ops carry `actor: null`, their provenance being the `source: "imported"`
    marker (ADR-0005). This mirrors git's per-commit author field;
  - op-specific payload fields.
- Records are destructured on read into a typed `Op` (no `.2.2.X`
  projection chains). Unknown fields are preserved on any rewrite
  (snapshotting), so additive evolution never loses data.

#### Canonical form and round-trip

The parsed model is a typed `Op` plus an `unknown` bag holding any
unrecognized JSON fields verbatim (so additive evolution never loses data). A
single canonical render is pinned: UTF-8, LF; envelope keys in the fixed
order `v, op, hlc, replica, nonce, actor`, then payload keys lexicographically, then the
`unknown` keys (lexicographically); no insignificant whitespace; an explicit
clear is JSON `null` (distinct from an absent key, ADR-0002); `hlc` / `id` /
add-tags in their pinned encodings (ADR-0007). The round-trip law is therefore
stated over the model, not raw text: `parse (render m) = m` for any model
value `m`, and `render (parse l) = l` for an already-canonical line `l`.
Minted values (`id`, `hlc`, `replica`, `nonce`) are read as data, never
re-derived on read.

#### OR-Set op payloads

The OR-Set (ADR-0002) needs add-tags and observed-tag sets; this pins their
concrete on-disk form so the type is implementable, without adding any new
identity machinery:

- The add-tag is the envelope's existing `(hlc, replica, nonce)` triple —
  *not* a new generated token and *not* a hash. Its canonical form is the
  string `"<hlc>.<replica>.<nonce>"` (the three fixed-width fields, dot-joined),
  so the tag is byte-identical across replicas and compared by string equality.
  Every `create` / `depAdd` / `relate` record is uniquely identified by that
  triple (the same triple that mints issue IDs, ADR-0007), so it serves directly
  as the observed-add token. Such an op carries its element key — the issue `id`,
  or the edge `(from, to, kind)` — plus its envelope identity.
- A `depRemove` / `unrelate` carries the element key AND an explicit
  `observed` field: a JSON array of the canonical add-tag strings it has seen
  for that element. It tombstones exactly those tags — add-wins, so a concurrent
  add the remover never saw survives (ADR-0002).
- These `observed` tag-sets and tombstones are exactly what accumulates and
  must survive until causally stable; the compaction snapshot digest
  subsumes them (compaction section below).

#### Record op kinds and payloads (the closed enum + verb→delta map)

The on-disk `op` kinds are readable user verbs, decoupled from the seven
kernel deltas they map onto (ADR-0004); the shell parser does the mapping
(tested, not proved). This is the closed enum of record ops — *each row is
exactly one JSONL record*. CLI commands that emit *several* records (e.g.
`update --parent`, `create` with inline edges, `close --of`) are a separate
layer, listed under "A CLI command may emit more than one record" below; they
are not record-op values. The enum and its payloads:

| wire `op` | kernel delta | payload (beyond the envelope) |
|---|---|---|
| `create` | create | `id`; optional initial scalars (`title`, `priority`, …); `status` defaults to `open` and `priority` to `2` — each seeded as an LWW write at the create HLC unless an initial value is carried (both are total fields, never absent) |
| `update` | setFields | `id`; one or more non-lifecycle scalar assignments (`title`/`priority`/`assignee`/`slug`/`description`/`notes`/…). Lifecycle status and time fields use the distinguished verbs below so their provenance projections stay well-defined |
| `claim` | setFields | `id`; sets `status=in_progress`, `assignee` |
| `close` | setFields | `id`; sets `status` (`done`\|`cancelled`), `closeResolution` (with `--of <id>` the *command* additionally emits a separate `metaSet` record — composites below) |
| `reopen` | setFields | `id`; sets `status=open`, clears `closeResolution` |
| `defer` / `undefer` | setFields | `id`; sets / clears `deferUntil` — an ISO-8601 UTC instant string (e.g. `2026-06-15T09:00:00Z`), or JSON `null` to clear; normalized on write, distinct from the 16-hex `hlc` (ADR-0010) |
| `metaSet` | metaSet | `id`, `key`, `value` (`null` = clear) — opaque metadata (ADR-0002) |
| `depAdd` / `relate` | edgeAdd | `from`, `to`, `kind` (`blocks`/`parent`/`related`); add-tag = the envelope triple in its canonical string form (`"<hlc>.<replica>.<nonce>"`, above), an opaque equality token for the OR-Set — distinct from LWW *comparison* of scalar writes, which is HLC-primary `(hlc, replica, nonce)` (ADR-0007). CLI `dep add A B` ⇒ `from=B, to=A` — A blocked-by B (ADR-0003) |
| `depRemove` / `unrelate` | edgeRemove | `from`, `to`, `kind`; `observed` add-tags (the OR-Set payload above) |
| `labelAdd` / `labelRemove` | labelAdd / labelRemove | `id`, `label`; (`labelRemove` also `observed`) |

Provenance timestamps are not op payload fields — `createdAt`,
`updatedAt`, `closedAt`, `claimedAt` are fold-time projections of op HLCs:
`createdAt` = the `create` op's HLC; `updatedAt` = the max HLC over the issue's
own scalar writes (`update`/`claim`/`close`/`reopen`/`defer`; edge/label/meta
ops do not bump it); `closedAt` = the HLC of the `close` that set the
current terminal status (absent once `reopen`ed); `claimedAt` = the HLC of the
latest `claim`-semantics op (`claim` or `update --claim`) that is later than
any `close`/`reopen` of the issue (absent if none) — backs `list --stale`.
`createdAt` (the ready-ordering key, ADR-0004) is read from the issue's
`create` op at fold time.

Stability rules follow from the verb/delta split:

- Pure field-writes that need no distinguished verb reuse `update`, so a
  future field-editing command adds no new `op` kind and needs no `v`
  bump (old readers fold it as an `update` with an additive optional field).
  A genuinely new *kind* of op (a new delta, or a new readable verb an old
  reader could mis-fold) does bump `v`, per the rules below.
- The kernel never sees the wire verb — only its delta — so the proof surface
  is the seven deltas, independent of how many verbs the CLI grows.
- A CLI command may emit more than one record — the layer *above* the
  record-op enum (each enum row is one record; these commands compose several):
  - `update --parent E` → `depRemove` of every currently-observed `parent` edge of `id` (each carrying its observed add-tags) + one `depAdd` (`kind=parent`, `from=E`, `to=id`), normalizing to a single local parent; a concurrent *unobserved* parent add can still re-create `multiParent` (add-wins, ADR-0003 §4), surfaced by the diagnostic;
  - `create … --blocked-by`/`--blocks`/`--related`/`--parent` → one `create` + one `depAdd` per wired edge;
  - `close --as duplicate --of <id>` → one `close` + one `metaSet` (`duplicate-of` → `<id>`);
  - `close --cascade` (epic cancel) → one `close` per affected issue.

  "Exactly one mutation path" (ADR-0004) is about the single kernel reducer,
  not one-record-per-command.

### Versioning and evolution

- `v` is a monotonic integer. The policy is fail-closed on newer:
  a reader that encounters `v` greater than it supports refuses the segment
  carrying it (not the whole log — see *Failure scope* below) and tells the
  user to upgrade, rather than silently mis-folding.
- Within a version, only additive changes are allowed: new *optional*
  envelope/payload fields (preserved by older readers via preserve-unknown).
- Any change an old reader could mis-fold — a new `op` kind, a new
  *record kind* (e.g. the `snapshot` below), a changed field meaning —
  requires a `v` bump. New readers always read old `v`. Preserve-unknown
  covers unknown *fields*, not unknown `op`/record kinds: a reader that
  meets an `op` or record kind it does not know fails closed on that segment
  (the same refuse-don't-misfold rule as a newer `v`), never silently
  under-folds.
- This keeps the forever-compat surface managed by exactly two rules:
  *monotonic `v` + preserve-unknown*.

### Corruption and partial-write policy (the parse layer)

The kernel fold is total over a *well-formed* op multiset; the parse
layer (I/O shell) must decide what a malformed byte stream does. Two cases,
both with a stated policy:

- A torn trailing line — a reader folds while another process is mid
  `O_APPEND` (ADR-0001). The parser tolerates an incomplete final line: it
  is ignored this read, and the next read sees it complete. This is normal
  concurrent operation, not corruption. Crash-then-append: if a writer
  *crashed* mid-append, the torn fragment has no trailing newline, and a later
  append would concatenate onto it and fuse two records. So every writer, on
  open, first ensures the segment ends in `\n` — if it does not, it appends a
  single `\n` to close the orphaned fragment before writing its own line. That
  turns the crash fragment into a self-contained line, which the mid-log
  malformed-line policy (below) then handles (fail-closed by default,
  `--skip-bad` to drop it with disclosure). A writer never appends onto a
  newline-less tail, so a crash can damage at most the one in-flight record.
- A malformed line mid-segment (a bad manual edit, a botched merge, or a
  hostile/garbage record another replica pushed) — the parser fails closed by
  default at *segment* granularity: it refuses only the offending segment,
  folds every other segment, and emits a loud diagnostic naming the bad segment
  and its owning replica/actor. An explicit `--skip-bad` (a.k.a. `--repair`)
  escape hatch instead skips individual unparseable lines, but loudly
  discloses how many and where (no silent caps). Default-refuse mirrors the
  fail-closed-on-newer-`v` rule: never silently produce a wrong fold.

  Why per-segment, not per-log: segments are independently authored and
  unioned (ADR-0001) and the fold is order/dup-insensitive (ADR-0004), so one bad
  record can only poison its own segment. Refusing the
  whole log would let any single writer — or an accidental `v` skew — deny
  service to *every* replica, an availability failure the integrity rule must
  not cause (ADR-0014 threat T2). A refused segment drops that one replica's ops
  from the view (loudly); its owner repairs/re-syncs it while everyone else
  converges normally. Reader-side handling of torn vs malformed lines is pinned
  in ADR-0015 §5.

### The `--json` output is a versioned stability contract

The on-disk log is not the only forever-compat surface — for an agent-facing
tool the `--json` output is one too (every consumer parses it). It is
governed by the same discipline as the log format:

- Every `--json` response carries a `schemaVersion` integer in its
  envelope. The initial baseline is `schemaVersion: 1`.
- Within a major schema version, changes are additive only — new fields,
  never renamed/removed/re-typed ones — so a consumer reading known fields is
  never broken by an upgrade.
- A breaking change bumps `schemaVersion`; the change and its version are
  documented.
- This makes the JSON a deliberate, versioned contract rather than whatever
  the serializer happens to emit.

Envelope shape and error codes (pinned here so CLI work cannot freeze an
ad-hoc shape under the additive-only rule; ADR-0011 §1 cross-references this):

- Envelope:
  `{ "schemaVersion": <int>, "ok": <bool>, "data": <command-specific> | "error": { "code": <enum>, "message": <human>, …context } }`.
  `ok` is the explicit discriminant; exactly one of `data` / `error` is
  present.
- Error `code` is a named, closed enum of stable lowercase-hyphen
  strings, seeded from the catalog ADR-0011 lists:
  `usage`, `internal`, `no-project`, `not-found`, `ambiguous-id`, `force-required`,
  `malformed-line`, `unknown-version`, `corrupt-clock`, `corrupt-replica`,
  `push-rejected`, `no-upstream`, `stealth-mode`, `lock-busy`,
  `not-claimable` (extend as new conditions arise). The enum
  obeys the same additive-only
  rule: codes may be *added* within a `schemaVersion`, never renamed or
  removed, so a consumer matching a known code is never broken. Each code
  maps to a stable nonzero process exit code, assigned once and never
  renumbered (additive like the enum; several codes may share one exit number):
  `0` success, `1` internal, `2` usage, then `3` no-project, `4` not-found,
  `5` ambiguous-id, `6` force-required, `7` malformed-line, `8` unknown-version,
  `9` corrupt-clock / corrupt-replica, `10` push-rejected, `11` no-upstream,
  `12` stealth-mode, `13` lock-busy, `14` not-claimable. `internal` is the
  catch-all for an otherwise-unclassified failure; known conditions must use
  their stable code instead of collapsing to `internal`.
- Streams and usage failures are part of the contract. With `--json`, the
  one JSON envelope (success or error) is written to stdout; incidental human
  diagnostics, progress, and repair disclosures go to stderr. Without
  `--json`, normal data goes to stdout and errors/diagnostics go to stderr.
  Argument-parse failures honor `--json` if the raw argv contains it anywhere:
  emit `{ ok:false, error:{ code:"usage", ... } }` with exit `2` instead of a
  prose usage block. Data outcomes such as `claim.outcome="superseded"` remain
  `ok:true` and exit `0`; an existing claim target that is not in the current
  `ready` set is an `ok:false` `not-claimable` error, with context fields
  explaining why the item is not ready (status/epic/deferred/blockers/current
  assignee as applicable). Agents branch on the structured outcome or error
  code, not on prose.

### Compaction — deferred, but reserved

- v1 ships without compaction. The log grows with usage; for the
  expected scale (thousands of issues/ops in a repo) this is fine. The cost
  is bounded by usage, not catastrophic. This deferral is logged here, not
  silent (AGENTS.md: no silent caps).
- Why it's hard (the reason it's deferred, not just unbuilt): under the
  CRDT, an op or OR-Set tombstone may only be discarded once every
  replica has observed it — otherwise a still-unmerged replica re-merges
  and *resurrects* a removed element. Safe compaction therefore needs a
  notion of causal stability: a frontier below which all replicas agree,
  computed from a version vector (per-replica high-water marks).
- What the format reserves now so compaction is a later change needing no
  format *restructuring*: a `snapshot` record kind carrying (a) a materialized
  state digest of all ops causally ≤ a stable frontier and (b) that frontier
  as a version vector. Reading then becomes `snapshot ⊕ fold(tails)` —
  fold the per-replica segment tails on top of the snapshot. The version
  vector also has uses beyond compaction (e.g. "have you seen my change?").
- The safety obligation (a reserved theorem, ADR-0004). Any compaction must
  preserve the fold: for a causally-closed frontier `F`,
  `fold ops = snapshot(stateAt F) ⊕ fold(ops above F)`. This is what guarantees a
  snapshot never changes the materialized state, and — with the union-merge
  interaction (design-backlog) — what guards against a strictly-growing line-union
  *resurrecting* ops a snapshot retired. Recorded now as the obligation; proved
  when compaction is built (deferred).
- When built, it is an explicit `tl compact` command — not automatic.
  Compaction is destructive of history (it discards ops `tl log` could
  otherwise show) and a wrong trigger could drop ops a slow replica hasn't
  observed, so the user stays in control of this one-way operation;
  auto-compact-when-provably-safe is a possible later opt-in. The name
  `compact` is honest that it collapses *settled history into a snapshot*
  (not "gc"-ing garbage — the data was real); `gc` may serve as an alias.
  The trigger/threshold and the causal-stability frontier computation remain
  deferred (to be designed with running code to test against).

## Consequences

- Debuggable, git-friendly, ethos-aligned. JSONL diffs cleanly, is
  human-readable (AGENTS.md), and makes preserve-unknown trivial.
- Reading model: materialization is fold-per-invocation —
  `snapshot ⊕ fold(tails)` on each command (ADR-0001). Caching/incremental
  materialization is a later optimization, not needed at expected scale.
- Compaction needs no format restructuring later. The `snapshot` kind and
  the version-vector frontier are reserved now. But because a `snapshot` is a
  new *record kind* an old reader cannot fold (and, once it discards ops below
  the frontier, an old reader that ignored it would under-fold), enabling
  compaction does bump `v` — fail-closed, so an old binary refuses a
  compacted log with an upgrade message rather than silently mis-folding.
  Whether the un-compacted v1 format stays `v=1` is unaffected.
- Fail-closed is honest. A user on an old binary gets a clear "upgrade"
  message, never a silently wrong fold.
- The log doubles as an action history (`tl log`). Because every
  mutation is an op, `tl log` is a read-only projection over the log — no
  separate events table. It merges the per-replica segments and orders by
  HLC (the established total order, ADR-0007); `tl log <id>` filters to ops
  touching that issue. Its visible horizon is bounded by compaction: ops
  below the snapshot frontier are gone, so `tl log` must disclose where
  history begins ("earlier ops compacted") rather than imply completeness
  (no silent caps).

## Alternatives considered

- Binary format. Rejected: opaque, not git-diffable, fights the
  human-readable-artifacts rule; preserve-unknown is harder. JSONL's slight
  size cost is irrelevant at this scale.
- Compaction in v1. Rejected: causal-stability GC is genuinely hard and
  premature; reserving the `snapshot`/version-vector shape lets us defer
  without painting ourselves into a corner.
- Best-effort compaction (drop old closed items without a frontier).
  Rejected: it can resurrect removed elements on a late merge — exactly the
  correctness failure the CRDT design exists to prevent.
