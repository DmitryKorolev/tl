# ADR-0007 — Identity, HLC, and ordering

- Status: Accepted
- Date: 2026-06-04

## Context

Three boundary values are load-bearing and tightly coupled, so they are pinned
together: the issue id (the OR-Set key and every edge endpoint), the
replica id (segment ownership + the LWW tie-break), and the HLC (the
LWW ordering clock). All are minted in the tested I/O shell and carried as
*data* in each op (ADR-0001: "clocks are data," so the kernel stays a
deterministic fold). The LWW-register merge (ADR-0002) keeps the write greatest
in the total order `(HLC, replica-id, nonce)` — get it wrong and LWW
silently loses updates or violates causality.

## Decision

### Issue IDs

Short, collision-resistant, flat hashes minted at creation, never reassigned;
an optional slug gives a memorable display handle without becoming identity.

- An id is `tl-<crockford-base32>` from a hash of `(replica-id, creation-HLC,
  nonce)` — effectively random, unique without coordination. (A sequential
  counter is rejected: it needs a global allocator and collides under concurrent
  creation, and renumbering on merge breaks every edge. Dotted hierarchical ids
  `2ds.1.10` are rejected too — `.N` needs a per-level counter, the same
  collision, and bakes the parent into the id so reparenting breaks references.
  Hierarchy is `parent` edges, ADR-0003, rendered at display time.)
- Hash function, preimage, and canonical length are pinned (they fix the
  OR-Set key and the round-trip target, ADR-0008): the id is the leftmost 80
  bits — the first 10 digest bytes, the NIST truncation convention; slice
  direction pinned in ADR-0018 — of SHA-256 of the preimage, read as a
  big-endian integer, Crockford-base32 = 16 characters after
  `tl-`. The native preimage is the three canonical fixed-width strings
  concatenated — `replica-id`(13) ++ `hlc`(16 hex) ++ `nonce`(26) — unambiguous by
  fixed width, no delimiter (the import preimage below is the one exception).
  SHA-256 is ubiquitous; minting is one hash per `create`, not a hot path. The
  canonical stored id is the bare 16-char hash — no `tl-` on disk, in the
  preimage, or in the merge/OR-Set key — read back as data, never re-derived on
  read (re-hashing happens only at mint time). The `tl-` is a display/reference
  affix only: added on render, stripped on parse, never a separate identity (see
  *Resolution* below).
- Collision policy. At 80 bits the birthday probability is ~4e-13 even at
  10⁶ issues, so issue-id uniqueness is a carried assumption (overview.md
  Trusted) rather than a code path — there is no cross-replica collision
  handling, because a local re-mint cannot see ids another replica minted
  concurrently (only width defends that, and 80 bits does). The one active check
  is on the deterministic `import` path (below).
- Display lengthens the shown prefix only as far as needed to disambiguate
  within the project (git-short-hash ergonomics); commands accept any unambiguous
  prefix, case-folded. Encoding: Crockford base32 (`0-9a-z` minus `i l o u`),
  lowercase, case-insensitive — typo-resistant (no `0/o`, `1/l`) and 5 bits/char.
- Resolution — the id↔slug discriminator. The `tl-` prefix is **reserved**: a
  positional token that begins with `tl-` is an id (strip it, then resolve as a
  full id or an unambiguous id-prefix, normalized on input exactly as the
  *Encoding* above dictates — ASCII-case-folded and Crockford symbol-aliased
  (`o`→`0`, `i`/`l`→`1`), so a typo'd id still resolves on the read path, not only
  at mint); a token that does **not** begin with `tl-` is a slug. The two languages are thus unconditionally
  disjoint and the resolver never guesses from content — the one cost is that a
  bare hash must carry its `tl-` to resolve as an id (a slug is never matched
  against the id space). `>1` match within a space → `ambiguous-id` (ADR-0008),
  whose message names the full `tl-…` form. The `ext:<system>` source id is a
  separate colon-keyed lookup (ADR-0005), not part of this positional grammar.
- Import-seed ids are the one exception to the random triple:
  `tl-<crockford32(SHA-256("import:" ++ source-tag ++ ":" ++ source-id))[0..80 bits]>` —
  hashed from the *source* id so re-import is byte-stable, keeping the source
  reference in the `ext:<system>` metadata key (ADR-0002/0005). The `source-tag`
  is a short lowercase `[a-z0-9]+` system name that excludes the `:` delimiter
  (so the preimage is unambiguous) — `beads` for the beads importer, matching
  the `ext:beads` key; `source-id` is the source's id as raw UTF-8 bytes. The
  importer checks the seeded set for the (astronomically unlikely) collision and
  lengthens deterministically rather than fusing two source issues.

### Optional slug

A human-chosen label (`--slug lexer-escapes`), an LWW field. Commands accept a
slug anywhere an id is, *if it resolves unambiguously*; it is mutable, may be
absent, may collide (then `tl` asks for the id). It is never the merge key —
the OR-Set key and every endpoint stay the flat hash id, so a slug change breaks
nothing.

The slug grammar is kebab-case `^[a-z0-9]+(-[a-z0-9]+)*$` — lowercase ASCII
letters and digits, single internal hyphens, no leading/trailing/double hyphen,
max 64 chars, ASCII-case-folded on input. **Digits are allowed** (`oauth2`,
`utf8`, `sha256` survive): the reserved `tl-` prefix — not the charset — is what
separates slugs from ids, so forbidding digits would protect nothing while
merging distinct terms (`sha256`/`sha3` → `sha`). Crockford symbol-aliasing is
**not** applied to slugs — they are author intent, not transcribed entropy, so
`s0` ≠ `so`. A slug may not begin with `tl-` (the reserved id prefix).

### The nonce

Freshly random per op (not per session/replica), carried on *every* op in
the record envelope (ADR-0008). Three load-bearing roles, pinned once here:
(a) issue-id uniqueness (above); (b) the final tie-break in the LWW total order
`(HLC, replica-id, nonce)` — writes sharing a `(HLC, replica-id)` can tie on the
first two; (c) the OR-Set add-tag (ADR-0002/0008). All depend on per-op randomness.
It is pinned like the issue id: 128 random bits from a CSPRNG, Crockford
base32 (26 chars — which hold 130 bits: the value is right-aligned with the two
spare high bits zero, the ULID layout, so a valid nonce's first char is
`0`–`7`). The only collision that matters is two ops sharing the *same*
`(HLC, replica-id)`. On the normal local path the mutation lock (ADR-0015)
serializes same-working-copy writes so the HLC strictly advances and they never
tie; a residual tie is confined to off-path cases — a duplicated replica-id (a
byte-copied working copy, below), a lock-less/network filesystem, or import's
deterministic nonce — a vanishing space, so at 128 bits the probability is
negligible: nonce
uniqueness within a `(HLC, replica-id)` is a carried assumption (overview.md
Trusted, sibling to replica-id and issue-id uniqueness), discharged by the
CSPRNG, not a code path.

### HLC

- An HLC value is (physical, logical): `physical` = ms since the Unix epoch
  (48 bits), `logical` = a counter (16 bits), packed as the 64-bit integer
  `(physical << 16) | logical`. On the wire (ADR-0008) it is exactly 16
  lowercase hex digits, zero-padded, no separator (a JSON string, never a bare
  number — a 64-bit integer exceeds JSON's 2⁵³ safe range, where many parsers
  silently lose precision and corrupt LWW order). Hex is chosen for this
  order-critical key because lowercase hex is ASCII-monotonic with no aliasing
  (`'0'<'9'<'a'<'f'`), so bytewise string order = integer order = LWW order, and
  16 chars cover the full 64 bits. (Same encoding for the `.tl/local/clock`
  value.)
- Local event: `physical = max(last.physical, now())`; if equal, `logical++`
  else `logical = 0`. Observe remote (folding ops from sync):
  `physical = max(last, remote, now())`, `logical` advanced to strictly exceed
  both on a tie — keeping causality across the transport.
- Persistence: the last HLC lives in `.tl/local/clock`, reloaded each
  invocation (each `tl` call is a fresh process; a reset would regress
  monotonicity). Wall-clock running backward → `logical` absorbs it (physical
  never decreases); `logical` overflow within one ms → bump `physical`.
- Range is fail-closed (no wrap). `physical` is bounded by 48 bits and the
  packed value by the 16-hex/64-bit field on which the LWW byte-order rests. A
  `logical`-overflow bump that would push `physical` past 2⁴⁸ saturates and
  errors rather than wrapping; and on observe-remote, an incoming HLC whose
  `physical` exceeds a sanity bound — `max(now(), last) +` a fixed skew window,
  capped at the 48-bit max — fails the parse-validity check, so that segment
  is refused at segment granularity (the fail-closed path of ADR-0008 §corruption
  / ADR-0015 §5), never silently folded into a wrong order. Natural
  (non-adversarial) overflow is ~8800 years out; this guards a hostile or broken
  remote clock (ADR-0014 T2).

### Replica identity

- A replica-id is minted once per working copy (on `init` or first
  write) — Crockford base32 of 8 random bytes (64 bits) from a CSPRNG (the same source as the nonce): a fixed 13 lowercase
  chars — the 64-bit value right-aligned with the single spare high bit zero
  (plain big-endian base-32: the same leading-zero convention as the 16-hex HLC
  and the ULID-style nonce, so a valid replica-id's first char is `0`–`f`;
  validation rejects a first char above `f` as out of range — the Stage-0
  `Replica.valid` checks width/charset only and is strengthened with the
  Stage-1 wiring).
  Stored in `.tl/local/replica`,
  gitignored (the whole `.tl/` is, ADR-0001): a shared replica-id collapses
  the LWW tie-break and per-segment ownership.
- It is used three ways: part of the LWW tie-break, the op `replica` field, and
  issue-id derivation.
- `(HLC, replica-id, nonce)` is a total order — the tuple-lexicographic
  order, computed as a bytewise compare of the fixed-width canonical strings
  (`hlc` 16-hex, then `replica-id` 13, then `nonce` 26 chars; each
  ASCII-monotonic), so keys compare without re-parsing to integers. Replica-id
  alone is not enough: two `tl` processes in the same working copy share a replica-id and
  (no lock) can mint identical `(HLC, replica-id)`; the per-op nonce is the
  final tie-break that keeps the LWW join a well-defined function. The blast
  radius is narrow — only two same-replica concurrent writes to the *same scalar
  field of the same issue*; `create`s and edge ops never arbitrate via LWW
  (their OR-Set keys differ).
- Replica-id uniqueness assumes a working copy is not byte-copied below git.
  A filesystem copy (`cp -r`, an image snapshot, a CI cache restoring
  `.tl/local/`) duplicates the id into two live replicas. Convergence still
  holds (the per-op nonce keeps LWW total, and `tl`'s segment-union on sync
  absorbs same-named-segment appends, ADR-0001), so this is not a
  correctness break; it violates the single-writer-append *ownership* model and
  weakens id-derivation entropy. Scoped explicitly in the carried assumption
  (overview.md); a future `doctor` check may detect a moved segment and re-mint,
  like a clone.

The kernel consumes the triple as an opaque, totally-ordered key; it mints no
component.

## Consequences

- Merge-clean. Concurrent creates on different replicas never collide and
  never need renumbering, so edges stay valid across merges — the property the
  whole design needs.
- Convergence rests on boundary facts outside the kernel: replica-id
  uniqueness and durable HLC monotonic persistence are recorded as carried
  assumptions (overview.md Trusted). The clock/ID implementation is still
  tested — clock-file parse/render, local/remote HLC update rules,
  backward-clock handling, and overflow — but those tests do not prove the
  real-world uniqueness/durability assumptions.
- LWW behaves sanely under skew: causally-ordered edits resolve correctly and
  the log reads in roughly real-time order; only *genuinely concurrent* same-field
  writes are arbitrated by the (skew-bounded) timestamp — the accepted LWW
  tradeoff (sets use OR-Sets instead).

## Alternatives considered

- Sequential counter / dotted hierarchical ids. Rejected: coordination,
  concurrent collision, renumbering-breaks-references.
- Colon id form `tl:<hash>`, or a configurable per-project prefix. Rejected:
  `:` is already a structural separator across the data model — metadata keys
  (`ext:beads`, `type:bug`, `waiting:*`, ADR-0002) and the import-id preimage
  `import:<tag>:<id>` (ADR-0005) — so `tl:q7rk`
  reads as a sibling of `ext:beads` and collides with the `ext:*` source-id
  resolution path; it also loses on git-native ergonomics (`<ref>:<path>`, scp
  `host:path`), URI-scheme/markdown parsing, and terminal word-selection. The
  hyphen `tl-` gives the same "prefix is separable" signal at no cost. A
  *configurable* prefix falls with it: it reintroduces content-based id↔slug
  ambiguity and fragments the single greppable, lint-anchorable id shape, for a
  customization of low value to an agent-first tracker.
- Full UUIDs. Merge cleanly but long; the short hash gives the same property
  with better ergonomics.
- Content hash of fields. Rejected: collides for identical content; the
  replica/clock/nonce avoids it.
- base36. Rejected for Crockford base32: same compactness, case-insensitive,
  no look-alikes.
- Wall-clock only / Lamport only. Rejected: skew loses updates / no real-time
  meaning. HLC gives both.
- Per-field vector clocks. Rejected for LWW: heavy metadata for no gain over
  scalar HLC; a version *vector* is reserved only for the compaction frontier
  (ADR-0008).
- Replica-id shared via git. Rejected: collisions destroy the LWW total order
  and segment ownership.
