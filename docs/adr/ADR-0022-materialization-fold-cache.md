# ADR-0022 — The materialization fold cache

- Status: Accepted
- Date: 2026-06-11
- Amended: 2026-06-13 — the cache integrity hash is now core's non-crypto
  `ByteArray.hash`, not the pure-Lean SHA-256: the cache is a discardable
  rot-check (tampering is the segments' trust domain, ADR-0014), so
  collision-resistance is not required and the cache carries no crypto
  assumption (ADR-0023/0024 measured SHA ≈25× slower at cache sizes).
  `cacheVersion` bumped 1→2.
- Amended: 2026-06-21 — `cacheVersion` bumped 2→3: the `WireOp.toOp` fold changed
  (ADR-0013's claim-only `assignee` — `update` no longer applies an
  `assignee`, `reopen` now clears it), so a v2 cache must rebuild.

## Context

[Vision §Scale target](../vision.md) pinned the design in advance: read-by-
fold-per-invocation until real repos outgrow the fold, then "an automatic,
self-validating cache in gitignored `.tl/local/` (keyed to log content;
rebuilt from scratch if stale/absent) — never a user-managed command," with
no log format impact. The trigger has fired an order of magnitude early:
dogfooding this repository (~169 ops) measured `tl ready` at 87s, `tl
doctor` 86s, `tl stats` 169s, and writes growing ×16 per ×4 ops — because
`transact` refolds the whole log under the mutation lock and every read
refolds it again, and the fold's per-op canonical-list insert makes it
quadratic in ops.

Two facts shape the design:

1. **Per-line classification is deterministic in segment bytes** — parse
   success, the segment-owner check, refusal, and `--skip-bad` skips are
   pure functions of the line. The *only* time-dependent input is the HLC
   skew deferral ([ADR-0007](ADR-0007-identity-hlc-ids.md)), which is proved
   monotone in `now` (a deferred line later becomes admissible, never the
   reverse on a healthy clock).
2. **The fold is order-insensitive and append-decomposable** — `fold (l ++
   ops) = ops.foldl apply (fold l)` (`Tl.Kernel.fold_append`, one line by
   `List.foldl_append`) and `fold_perm`/`fold_eq_of_mem_iff` (ADR-0004 thm
   2) make "cached prefix state + fold the rest on top" exactly equal to a
   fresh fold of the same op set. No new kernel theorem is needed.

## Decision

### 1. What is cached: the fold, nothing else

`.tl/local/cache` holds the folded kernel `State` plus, per segment, the
content key it folded: `(replicaId, byteLen, lineCount, checksum(prefix),
refused, deferredLines)` (the checksum is core's non-crypto `ByteArray.hash`). Every other `Loaded` field — the `ops` list
(provenance/`tl log` scan it), refusals, skips, deferrals, the HLC maxima,
decode warnings, `segmentCount` — is recomputed from a full live line decode
on every invocation. The cache can therefore only ever change *how the state
is computed*, never *what a command discloses*; reads stay O(log) in decode
with the quadratic refold gone (the dominant kernel-walk costs of
`ready`/`list` are separate work, tracked with the same performance epic).

### 2. Validity — self-validating against the live bytes

A cache is consulted only if **every** cached segment still passes, against
the live bytes and the live decode:

- the live segment exists and its first `byteLen` bytes hash to the recorded
  checksum (appends keep a cache warm; any rewrite — a repair, a reordering
  ref absorb — misses and rebuilds);
- the live refusal flag equals the recorded one. Classification is
  deterministic per line, but a bad line *appended* to a clean segment
  refuses the whole segment, dropping prefix ops a fresh fold never folds —
  the flag divergence forces the rebuild that keeps the two paths equal;
- every line deferred *now* within the prefix was deferred at snapshot time.
  The monotone direction (deferred then, admissible now) folds those lines
  on top; the reverse (a clock that went backwards) rebuilds.

A live segment the cache never saw contributes all its ops as suffix; a
cached segment missing live fails validity. Valid ⇒ `state = extras.foldl
apply cached.state` where `extras` = appended lines plus newly-admissible
snapshot-deferred lines; the partition argument (same bytes ⇒ same
classification; validity rules out every other drift) makes this the fresh
fold's op set exactly, and `fold_append` + `fold_perm` close the equality.
Anything invalid ⇒ full refold. Stale, absent, corrupt, wrong-version,
non-canonical — all the same answer: rebuild from the segments, never
repair. "Corrupt" includes *value* corruption, not just shape: the file is
a non-crypto checksum line (core's `ByteArray.hash`) over the payload line,
verified before any decoded value (the state, a line count, a deferral set)
is believed — a flipped digit that stays valid JSON must rebuild, not
silently drop an op. Decode then re-establishes the canonical sortedness
proofs via `AMap.ofAscList?` (`ascending_of_sorted` guarantees an encode is
never rejected), so a decoded state is canonical by construction. The
prefix-validity hash and the file checksum are rot/content checks, not
security digests: deliberate tampering inside `.tl/` is the segments' trust
domain (ADR-0014), so a fast 64-bit non-crypto hash suffices and the cache
needs no collision-resistance assumption (an accidental shape-preserving
collision is ~2⁻⁶⁴, negligible for the discardable cache). This *narrows*
the framing of the original design — the cache was briefly a pure-Lean
SHA-256 (ADR-0018), measured ≈25× slower at cache sizes (ADR-0023/0024), and
the crypto strength bought nothing here.

### 3. Who reads and writes it

- **Reads** (`loadView` → `readStateCached`): consult, then persist the
  refreshed cache best-effort whenever anything moved — the fold advanced,
  a content key changed (even with nothing new to fold, e.g. a torn
  fragment growing), or the cache was rebuilt (atomic temp+`rename` replace
  via `writeLocalFile`, the ADR-0015 §3 pattern; CSPRNG temp suffixes make
  concurrent lock-free readers collision-safe, and last-writer-wins is
  harmless because every written cache is valid for the bytes it folded).
  Only the exactly-fresh case writes nothing. A read-only filesystem or
  lost race never fails a read — the ADR-0015 §5 read discipline.
- **Writes** (`transact`): the guard-state materialize runs through the
  cache under the lock and persists the refreshed *pre-append* state (keyed
  to the pre-append bytes, it stays exactly valid; the next invocation folds
  the appended suffix). The write path stops paying the whole-log refold.
- **`doctor`**: reads through the cache, never persists (`persist :=
  false`) — the ADR-0016 §3 discipline extended: doctor mutates nothing, not
  even a cache.
- **`--skip-bad`** folds are *different* folds (skipped lines are absent
  from them): they neither consult nor produce the cache, so a skip-bad fold
  can never leak into a clean read or vice versa.

The file is gitignored via the `.tl/.gitignore` `*` self-ignore, local-only,
never synced, and has **no log format impact** (no `v` bump). It is opened
no-follow like every `.tl` file (ADR-0015 §6); a symlinked cache name is
refused on read and atomically *replaced* (not followed) on write. The cache
version is private to the working copy and moves freely — a mismatch is just
a rebuild — but it versions the *semantics*, not only the bytes: any change
to per-line classification (`decodeLine`, the segment-owner check), to
`WireOp.toOp`, or to kernel `apply`/`merge` must bump it, or two tl builds
sharing one working copy could suffix-fold new-semantics ops onto an
old-semantics cached state with no key divergence to force a rebuild.

### 4. The local realization of a non-destructive snapshot

This cache *is* the non-destructive snapshot of
[ADR-0008](ADR-0008-log-format-versioning-compaction.md), scoped to one working
copy: a materialized state at a frontier so a read folds only the tail, the op log
retained in full, a stale cache rebuilding from the segments. It changes no log
bytes, travels nowhere, and carries no `v` bump; its correctness is pinned by
tests against the fresh fold (the tested-shell tier, ADR-0004) over the proved
anchors (`fold_append`, `fold_perm`, `ascending_of_sorted`/`sorted_of_ascending`).

A **shared/durable snapshot** is the natural generalization, for when a cold clone
or a CI run must not fold from genesis: the same content-keyed, digest-validated,
fallback-to-fold artifact, published as a side object rather than kept in
`.tl/local/` — still no log-format change, since a reader that ignores it just
folds the log. Merging is trivial because a snapshot is a derived cache: keep any
valid one, or the highest-frontier one. Destructive GC — discarding the ops below
the frontier to bound size — stays a separate, deferred, opt-in concern
(ADR-0008); this cache never discards an op, so any `tl log --since` cursor stays
serviceable (ADR-0025).

## Consequences

- Reads and writes fold only appended suffixes in the steady state; the
  write-path quadratic under the lock is gone.
- **Accepted cost, recorded per the efficiency principle**: validity hashes
  every cached segment prefix with a fast non-crypto checksum (core's
  `ByteArray.hash`) on each consultation (once — the exactly-fresh check
  compares the cheap key fields instead of re-hashing, since under validity
  equal lengths imply equal bytes), and a refreshed cache re-serializes and
  re-hashes the whole state — linear in log bytes with small constants. This
  hash was originally the pure-Lean SHA-256 (ADR-0018); profiling
  (ADR-0023/0024) blamed it (≈25× slower than the extern), and since the
  cache is a rot-check not a security surface it was switched to
  `ByteArray.hash` rather than taking ADR-0018's optimized-SHA-with-a-proved-
  bridge path. Also accepted: the per-item
  `find?`/`contains` rescans in validity and the suffix partition — they
  are quadratic-shaped in *segment count* (= replica count, single digits)
  and *deferred-line count* (normally zero), not in ops, so an index would
  be machinery without a workload; revisit if either count grows real. The
  full per-read line decode also remains — the `ops` list is a disclosure
  surface (`provenance`, `tl log`), not a cache concern.
- A byte-copied `.tl/` clones the cache; the content key keeps the copy
  harmless (same bytes ⇒ same fold; diverged bytes ⇒ rebuild) — consistent
  with the replica-id uniqueness assumption's framing in
  [overview §Trusted](../overview.md).
- Tested-shell duty (`Tests/CacheTests.lean`): codec round-trip and
  fail-closed decode rows (every decoder arm, plus checksum-caught value
  flips), every validity branch with the *path taken* observed (a marker poisoned into a cache survives iff the cache was
  used), a seeded property pinning `materializeCached ≡ materialize` across
  random prefix splits and `now` advances, and the file lifecycle (healing,
  doctor non-persist, skip-bad bypass, symlink refusal).

## Alternatives considered

- **Cache the decoded `ops` too** (skip the per-read line decode). Rejected:
  the decode is linear and not the measured cost; persisting ops duplicates
  the log byte-for-byte and turns a cache into a second log.
- **Key on byte length alone** (skip hashing). Rejected: a same-length
  rewrite (a canonicalizing ref absorb can reorder lines) would silently
  fold a wrong prefix — "self-validating" is the pinned design, and the
  hash is what validates.
- **mtime-based invalidation.** Rejected: not a pure function of content;
  the vision pins content-keying.
- **A WAL/SQLite materialized store.** Rejected already by ADR-0015 ("the
  log *is* the WAL"); this cache adds no second source of truth — it is
  always discardable.
