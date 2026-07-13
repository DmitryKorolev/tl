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
so its implementation is deferred, but the destructive design is pinned in
the compaction section and the format leaves room for it now.

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
order `v, op, hlc, replica, nonce, actor`, then **all** remaining keys — payload
and unknown alike — in one lexicographic order. (A payload-then-unknown grouping
would make the canonical bytes depend on which keys the *reader's* version
recognizes — an additively-added field is payload to a new reader but unknown to
an old one, both valid v1 readers — so the same record would canonicalize
differently across readers; the single order keeps rewrites byte-stable across
versions.) No insignificant whitespace; an explicit
clear is JSON `null` (distinct from an absent key, ADR-0002); `hlc` / `id` /
add-tags in their pinned encodings (ADR-0007).

String escaping is pinned, not toolchain-defined — "byte-stable across
versions" cannot rest on a serializer's unstated choices. Within a canonical
JSON string: `"` renders as `\"`, `\` as `\\`, U+000A as `\n`, U+000D as `\r`,
and every other code point below U+0020 as `\u00xx` — four hex digits,
lowercase (tab is `\u0009`, *not* `\t`). Every other code point — U+007F and
all non-ASCII included — is raw UTF-8, never `\uXXXX`-escaped; `/` is never
escaped. (This matches the pinned Lean toolchain's `Json.compress` today, but
the spec here is normative: the round-trip corpus carries an escape vector per
class above, so a toolchain change surfaces as a test failure to fix in `tl`'s
renderer — never a silent move of the canonical bytes.) The *parser* accepts
all standard JSON escapes; canonicality constrains only `render`.

The round-trip law is therefore
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
- A `depRemove` / `unrelate` carries the element key and an explicit
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
| `create` | create | `id`; optional initial scalars (`title`, `priority`, `description`, `notes`, `slug`, and the lifecycle `status`/`deferUntil` seed) — **not** `assignee`, which is `claim`-only (ADR-0013; a carried `assignee` key is preserved in the unknown bag, never seeded onto the open issue); `status` defaults to `open` and `priority` to `2` — each seeded as an LWW write at the create HLC unless an initial value is carried (both are total fields, never absent) |
| `update` | setFields | `id`; one or more non-lifecycle scalar assignments (`title`/`priority`/`slug`/`description`/`notes`/…). Lifecycle status/time fields and `assignee` use the distinguished verbs below so their provenance projections stay well-defined (`assignee` is `claim`/`claim --steal`-only, ADR-0013) |
| `claim` | setFields | `id`; sets `status=in_progress`, `assignee` |
| `close` | setFields | `id`; sets `status` (`done`\|`cancelled`), `closeResolution` (with `--of <id>` the *command* additionally emits a separate `metaSet` record — composites below) |
| `reopen` | setFields | `id`; sets `status=open`, clears `closeResolution` and `assignee` (ADR-0013) |
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
latest `claim`-semantics op (`claim` or `claim --steal`) that is later than
any `close`/`reopen` of the issue (absent if none) — backs `list --stale`.
`createdAt` (the ready-ordering key, ADR-0004) is read from the issue's
`create` op at fold time.

**`assignee` is claim-only.** Per ADR-0013, the `assignee` field is written
only by `claim`/`claim --steal` and cleared by `reopen`; neither `create` nor
`update` may set it (the delta rows above). The versioning status of this
shape, relative to an earlier design in which `create`/`update` could carry
`assignee` and `reopen` did not clear it, has two legs:

- `create`/`update` not setting `assignee` is genuinely **additive** — `tl`
  never emitted an `assignee` key on a `create`/`update` record (its CLI
  `--actor` flag is provenance, not a scalar write), so a carried key was
  always meant for, and is routed to, the unknown bag; the fold of every real
  `tl` record is unchanged.
- `reopen` clearing `assignee` is **not** additive: it is a changed-field
  meaning on an existing record kind, so a binary with the earlier semantics
  folds a reopened-not-reclaimed issue keeping its prior assignee while the
  current binary clears it — a same-`v1`-log fold divergence that, **had any
  release shipped**, would require a `v` bump. It does not, because the floor
  binds from 1.0 (§ Stability horizon) and **no release/tag has shipped**
  (product is pre-1.0): the prior fold was never a delivered contract, so
  changing it is unreleased iteration, not an inter-release break. The one
  live hazard pre-release — a stale *local* fold cache suffix-folding
  new-semantics ops onto an old-semantics cached state — is exactly the
  ADR-0022 cache-version obligation, handled by the `cacheVersion` 2→3 bump.
  No on-disk bytes or `v` change.

The first tagged release must still disclose the materialization change in its
notes (the Stability-horizon "never silently" duty).

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

#### Write-time guards, re-close, and `duplicate-of`

Derive-or-report (ADR-0003) bounds what a write may refuse; this pins the
**complete** stage-1 guard inventory, so no further guard creeps in silently
(adding one is an ADR amendment, not a local choice):

- `claim` refuses a target not in `ready s now` — `not-claimable`
  (ADR-0003/0020).
- `close --as done` on an epic is refused — `not-closeable` (ADR-0003 §3:
  done-ness rolls up; `--as cancelled` is allowed).
- `close <id> --as duplicate --of <id>` — a self-duplicate — is refused —
  `not-closeable`.
- Nothing else *refuses*. Every other lifecycle write is a plain LWW write:
  a merge can produce any of those states anyway, so a local guard would only
  misrepresent the model. (The corpus's courtesy *warnings* — the ADR-0003 §2
  own-`dep add`-closes-a-cycle warn, the §3 epic-transition surfacing — are
  not guards: they never refuse, so they are outside this inventory.)

Re-closing a closed issue is an **idempotent no-op**: with the same resolution
(and, for `duplicate`, the same canonical target) the command succeeds
(`ok: true`, exit `0`), echoes the issue, and appends **no** record — the
requested state already holds, and a duplicate write would only add log noise
and disturb the `closedAt`/`updatedAt` projections. With a *different*
resolution (or duplicate target) it is a normal resolution change: the
record(s) append as plain LWW writes (the epic-`done` refusal above still
applies).

The `duplicate-of` meta value (written by the `close --as duplicate --of`
composite above) is pinned: `--of` resolves exactly like any id argument —
full id, unambiguous prefix, or slug, per ADR-0007's resolution — erroring
`not-found` / `ambiguous-id` as usual, and the **resolved canonical bare id**
(16 chars, no `tl-`) is what is stored. On output the `--json` `meta`
projection renders a *well-formed* `duplicate-of` value in `tl-` display form
— ADR-0020's ids-render-display-form convention, without which an agent that
reads the bare value and passes it back positionally would have it resolve as
a *slug* (ADR-0007's grammar) — while a malformed value (a foreign writer's
garbage) renders as stored. At read time a `duplicate-of` whose
target is missing, is itself a duplicate (a chain), or names its own issue (a
self-reference some foreign writer appended — the local guard cannot bind
others) is tolerated in state, never repaired or flattened: these are the
value-level analogue of ADR-0003 §5's read-time tolerance (whose edge-inert
rule does not itself cover `meta` values), and they surface as `doctor`
graph-hygiene findings (additive checks, ADR-0020) rather than errors.

### Versioning and evolution

- `v` is a monotonic integer. The policy is fail-closed on newer:
  a reader that encounters `v` greater than it supports refuses the segment
  carrying it (not the whole log — see the corruption policy below) and tells
  the user to upgrade, rather than silently mis-folding.
- Within a version, only additive changes are allowed: new *optional*
  envelope/payload fields (preserved by older readers via preserve-unknown).
- Any change an old reader could mis-fold — a new `op` kind, a new
  *record kind* (e.g. the `compacted` marker below), a changed field meaning —
  requires a `v` bump. New readers always read old `v`. Preserve-unknown
  covers unknown *fields*, not unknown `op`/record kinds: a reader that
  meets an `op` or record kind it does not know fails closed on that segment
  (the same refuse-don't-misfold rule as a newer `v`), never silently
  under-folds.
- This keeps the forever-compat surface managed by exactly two rules:
  *monotonic `v` + preserve-unknown*.

#### Stability horizon: the forever promises bind from 1.0

The permanence language above — and the additive-only `--json` rule below —
binds from product **1.0** (SemVer 0.x conventionally permits breaks, ADR-0006,
and committing to a stable JSON this early would freeze shapes before real
usage has tested them). During 0.x both surfaces may still change
incompatibly, but never silently: a JSON break bumps `schemaVersion`, a log
break bumps `v` (the fail-closed rules above apply unchanged), and every break
is disclosed in release notes with a migration path for the log (at minimum
export → re-import). 1.0 then freezes whatever `v` / `schemaVersion` it ships;
from that point the forever rules hold unconditionally. Like any ADR this is
revisable — and note the asymmetry: moving the freeze *earlier* is always
cheap, while unfreezing after adoption would strand real replicas' logs.

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
  hostile/garbage record another replica pushed) — including a complete,
  well-formed record whose stamp `replica` does not encode to its segment's
  file name: segments are per-replica authored (ADR-0001), so a mis-assembled
  segment is damage of this same class. The parser fails closed by
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

  The command-level outcome follows the same availability logic: a read that
  refuses a *foreign* segment still succeeds (`ok: true`) — it folds the
  remaining segments, discloses the refusal on stderr, and surfaces it as a
  `doctor` finding. A read that refuses the replica's *own* segment — or
  every segment — fails (`ok: false`, `malformed-line` / `unknown-version`):
  answering from nothing would be a silently wrong fold (an empty board is an
  answer, not a disclosure). `tl doctor` is the one exemption — reporting
  refused segments is its job, so an own-segment refusal is a `fail` check
  inside an `ok: true` response (ADR-0020).

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
  `not-claimable`, `not-closeable` (the close refusals — epic-`done`,
  self-duplicate — see *Write-time guards* above), `unsafe-path` (the
  ADR-0015 §6 path-hardening refusals: a symlinked `.tl` component, an
  ownership mismatch, or a `--dir`/`TL_DIR` target failing the same
  validation; ADR-0014 T4), `verify-failed` (`claim --verify` could not confirm
  freshness because a configured remote was unreachable — the take is refused;
  distinct from a best-effort `--sync` failure, which only degrades) (extend as
  new conditions arise). The enum
  obeys the same additive-only
  rule: codes may be *added* within a `schemaVersion`, never renamed or
  removed, so a consumer matching a known code is never broken. Each code
  maps to a stable nonzero process exit code, assigned once and never
  renumbered (additive like the enum; several codes may share one exit number):
  `0` success, `1` internal, `2` usage, then `3` no-project, `4` not-found,
  `5` ambiguous-id, `6` force-required, `7` malformed-line, `8` unknown-version,
  `9` corrupt-clock / corrupt-replica, `10` push-rejected, `11` no-upstream,
  `12` stealth-mode, `13` lock-busy, `14` not-claimable, `15` not-closeable,
  `16` unsafe-path, `17` verify-failed. `internal` is the
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

### Compaction — a non-destructive snapshot; the destructive path pinned, deferred

Two separable concerns hide under "compaction." tl does the first; the second is
deferred.

- **Snapshot / checkpoint — a performance optimization, non-destructive.** The
  cost of a read is the fold. A snapshot is a materialized state plus the
  per-segment content keys it folded (the existing fold cache, ADR-0022): a read
  folds only each segment's appended byte-suffix onto the cached state, never from
  genesis, and the op log is retained in full. It is *content-keyed*, not a causal
  frontier — an append keeps it warm; any other divergence (a rewrite, or a
  reordering ref-absorb that lands a late op below a cached prefix) fails the
  per-segment key and rebuilds from the segments. So a late op never "folds below"
  anything: it is either an appended suffix (folded) or a prefix change (rebuild).
  Its correctness anchor is `fold_append`/`fold_perm` (ADR-0022) — no
  causal-stability proof. The local realization already ships per clone; a
  shared/durable snapshot generalizes the same content-keyed artifact so a cold
  clone or CI run need not fold from genesis. As a side cache, not a log record, it
  needs no format `v` bump and is forward-compatible: a reader that ignores it just
  folds the log.
- **Destructive GC — bounding log size; designed, deferred, opt-in, lossy.**
  Actually discarding ops below `F` to bound on-disk/transport size is the hard,
  CRDT-hostile part: an op or OR-Set tombstone may be dropped only once every
  replica has observed it, or a still-unmerged replica re-merges and *resurrects* a
  removed element. That needs a real causal-stability frontier (a version vector
  below which all replicas provably agree), and an offline clone can always sync an
  ancient op below any chosen `F` — so a safe automatic GC is genuinely hard. It is
  not needed at the expected scale (thousands of ops; small JSONL, git-packed on
  the ref; the fold cache bounds read cost regardless of length), so the
  *implementation* is deferred until a real size trigger — logged here, not
  silent (AGENTS.md). The *design* is pinned below, because two of its
  consequences are freeze-sensitive: the transport must start carrying unknown
  tree entries before the first release, and the `--json`/error surface it will
  need must stay additive. If built it is an explicit, user-driven `tl compact`
  (one-way, destructive of the `tl log` history a slow replica might still
  want), it carries a format `v` bump — the bumped `compacted` marker inside
  each trimmed segment is what an old reader actually meets, so it
  fail-closes on that segment with an upgrade message instead of silently
  under-folding — and it owes the change-feed a retention-horizon and
  gap/resync contract (ADR-0025).

The pinned destructive design (implementation deferred):

- **Transport preserve-unknown.** `tl sync` carries any `refs/tl/log` tree
  entry it does not recognize into the next commit's tree *verbatim* (blob
  bytes untouched) — the transport-level analogue of the record-level
  preserve-unknown rule above. Unknown entries are carried in the ref only:
  they are never materialized into `.tl/log/` (the read path's segment-name
  filter and the store's junk defense are unchanged, so a crafted tree entry
  still cannot become a local file). A *reserved* entry a new-format binary
  does recognize — the snapshot below — is line-unioned rather than carried
  one-sided. (Today's transport drops non-replica-named tree entries on
  every sync; fixing that is freeze-sensitive and ships pre-release as its
  own change — an old binary that strips the snapshot entry on every sync
  would otherwise fight the compactor.) This amends ADR-0001's "the tree
  *is* the `.tl/log/` contents": the tree is the per-replica segment blobs
  *plus* reserved and unknown non-replica entries.
- **Placement: the snapshot is a reserved non-replica-named tree entry** in
  `refs/tl/log`, line-unioned like any segment (two concurrent compactors'
  records both survive the union), and never enumerated as an on-disk segment
  (the store's junk filter is unchanged — a non-replica name never folds as a
  segment). Rejected placements: a synthetic-replica snapshot *segment* (a
  permanent violation of the replica-id-uniqueness carried assumption, and its
  owner stamps would be forgeries poisoning provenance); a non-replica entry
  *without* transport preserve-unknown (old binaries silently drop it); a
  separate ref (breaks the single-commit CAS atomicity of ADR-0001); a
  frontier-dropping union (silently loses never-observed ops — the same class
  as best-effort compaction below).
- **Trimmed segments carry `compacted` marker records** (with the `v` bump)
  through an explicit owner-check carve-out in materialization — never forged
  owner stamps. A marker byte-sorts into position after any union like every
  other line; nothing may assume it holds the first line of a segment.
- **Mixed-version reality, stated honestly.** After a compaction, an old
  binary's first refresh replaces its foreign caches with the trimmed
  segments, whose bumped `compacted` markers it then refuses *wholesale* —
  its board degrades to an own-segment-only view served with `ok: true` and
  refusal disclosures (a foreign-segment refusal never fails a command — the
  corruption policy above; an observer clone with no own ops instead fails
  the read under the every-segment-refused rule) until it upgrades. And
  every replica — old or new — *regrows* the ref with whatever untrimmed
  lines its local segments still hold when it syncs (the reconcile unions
  the pre-absorb local segments, and a line-union never re-shrinks): its own
  segment until it has itself compacted, plus any foreign cache holding
  untrimmed lines — including lines re-absorbed from a not-yet-compacted
  sibling. Every replica having compacted on the new format is therefore
  only the *necessary* floor: physical removal converges through **repeated
  compacts across the fleet** — each compact trims that replica's own
  segment and refreshes its caches, monotonically shrinking what can
  regrow, while a mere upgrade or sync advances nothing. **Pinned choice:
  regrowth-until-recompact is the accepted, disclosed cost.** The overlap tolerance theorem below makes resurrected
  lines state-harmless, and no workload needs hard size bounds yet. The
  alternative — a sync-side trim-at-marker in the new format — is rejected:
  it reintroduces a residual never-observed-op hazard that would have to
  ride the destructive confirmation.
- **Crash order.** A compact publishes the ref first (snapshot + trimmed
  blobs, one CAS commit), then absorbs, and trims its own segment *last* (an
  atomic rename under the mutation lock). A crash at any point degrades to
  harmless regrowth, never loss.
- **Preconditions and hygiene.** `tl compact` aborts on any refused segment;
  the frontier excludes skew-deferred lines; a re-trim cuts at a fresh
  frontier computed from the currently visible lines, never re-cuts at the
  old `F` (how its record seeds from and composes with surviving prior
  records is open point (a) below).
  `snapshot`/`compacted` records are exempt from skew deferral (the carve-out
  keeps the proved admission predicate intact for op records); the clock
  reseed floor takes `max(frontier)` into account; the fold-cache version
  bumps; `tl log --since` below the horizon answers the additive
  `compacted-gap` error code with a resync cursor (the ADR-0025 reserved
  contract), plain `tl log` discloses "earlier ops compacted"; and the feed,
  `stats`, and provenance projections exclude both record kinds.
- **The theorems (ADR-0004): reserved, proved when built.**
  *Fold-preservation* — `fold ops = snapshot(stateAt F) ⊕ fold(ops above F)`
  for a causally-stable frontier `F`; the discharge path is filter-partition
  plus the proved `fold_perm`/`fold_append`. *Overlap tolerance* —
  continuing the fold from `snapshot(stateAt F)` over **any** retained
  superset of the above-`F` ops still yields `fold allOps` (as line sets,
  below-`F` ∪ retained = the original set, so `fold_append` +
  `fold_eq_of_mem_iff` close it): the theorem that makes keep-everything
  unions and crash-regrowth provably state-harmless, and the reason the
  pinned choice above is safe. *Frontier join* — below-`F` of the pointwise-max of two
  frontiers is the union of their below-`F` sets (two compactors compose).
  Causal stability of `F` itself is not provable in-kernel: it becomes an
  explicit tier-3 carried assumption when built, held up operationally by
  `tl compact` requiring a successful preflight fetch and an explicit
  destructive confirmation. The non-destructive content cache above needs
  only `fold_append`/`fold_perm`, already proved (ADR-0022).
- **The version vector serves two roles of the same shape.** Per-replica
  high-water marks back both the snapshot frontier here and the change-feed cursor
  (ADR-0025) — distinct uses (global causal-stability vs per-consumer position),
  one primitive.
- **Two named open points, resolved before implementation.** The pin above
  deliberately leaves these undecided rather than guessing: (a) *reader
  selection and re-trim composition* — with both-survive union, several
  `snapshot` records can coexist; which one a reader seeds from, and what
  frontier a re-trim's record must carry (the join of every surviving
  frontier, including the incomparable-coordinate case where a fully-trimmed
  replica's coordinate resets), must be pinned so a stale surviving record
  can never seed an under-fold; (b) *snapshot-record supersession* — under
  both-survive union a superseded full-state record is never removed, so the
  reserved entry grows by one materialized state per compact; the
  supersession or accepted-growth story needs its own decision. Both gate
  the destructive implementation, not the transport rule above.

## Consequences

- Debuggable, git-friendly, ethos-aligned. JSONL diffs cleanly, is
  human-readable (AGENTS.md), and makes preserve-unknown trivial.
- Reading model: materialization is `snapshot ⊕ fold(tails)` on each
  command — the shipped content-keyed fold cache (ADR-0022) folds only each
  segment's appended suffix, rebuilding from the segments on any other
  divergence.
- A non-destructive snapshot needs no format change — it is a side cache
  (ADR-0022), so an old reader that ignores it simply folds the log, and the
  format stays `v=1`. Only a future destructive GC bumps `v`: once ops below the
  frontier are discarded, the bumped `compacted` marker inside each trimmed
  segment makes an old reader fail-close on that segment with an upgrade
  message rather than silently under-fold (the snapshot entry itself is
  invisible to old readers — it is not a segment).
- Fail-closed is honest. A user on an old binary gets a clear "upgrade"
  message, never a silently wrong fold.
- The log doubles as an action history (`tl log`, and the `--since` change-feed,
  ADR-0025). Because every mutation is an op, `tl log` is a read-only projection
  over the log — no separate events table. It merges the per-replica segments and
  orders by the `Stamp` total order (ADR-0007); `tl log <id>` filters to ops
  touching that issue. Under the non-destructive snapshot the full history is
  retained, so `tl log` is complete and any `--since` cursor stays serviceable.
  Only a future destructive GC would bound the horizon, and then `tl log` must
  disclose where history begins ("earlier ops compacted") rather than imply
  completeness (no silent caps).

## Alternatives considered

- Binary format. Rejected: opaque, not git-diffable, fights the
  human-readable-artifacts rule; preserve-unknown is harder. JSONL's slight
  size cost is irrelevant at this scale.
- Destructive GC in v1. Rejected: causal-stability GC is genuinely hard and
  premature. The non-destructive snapshot (a perf cache, ADR-0022) captures the
  read-cost win without it; reserving the `snapshot`/version-vector shape lets a
  future GC land without painting us into a corner.
- Best-effort compaction (drop old closed items without a frontier).
  Rejected: it can resurrect removed elements on a late merge — exactly the
  correctness failure the CRDT design exists to prevent.
