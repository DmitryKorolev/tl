# Codebase map

> Stages 0 and 1 are built: the verified kernel (`Tl/Crdt/`, `Tl/Kernel/`)
> and the whole Stage-1 tested shell (`Tl/Error`, `Tl/Format/`, `Tl/Hash/`,
> `Tl/Store/` with the `ffi/tlsys.c` shim, `Tl/Clock/`, `Tl/Cli/`). Entries
> marked *(planned — Stage N)* do not exist yet; for those this map is the
> module-layout contract, not a description of code. The line that matters:
> the verified kernel has no I/O, and everything that touches the world is a
> separate, tested shell.

```
Tl.lean                 -- root module; imports everything below

Tl/Crdt/                -- generic CRDT pieces (verified; join laws — comm/
                        -- assoc/idem — are proved per structure in each file,
                        -- there is no separate Join.lean)
  Order.lean            --   TotalOrd + the Stamp triple (hlc, replica, nonce)
  Map.lean              --   sorted assoc map (AMap) + FinSet, with join laws
  MapFold.lean          --   batched canonical AMap join (mergeSort + adjacent
                        --   collapse, O(N log N)) = the iterated merge
                        --   (joinFast_eq) — the cold-fold core
  Lww.lean              --   LWW register; key is the TRIPLE (HLC, replica, nonce)
                        --   (ADR-0002/0007; wire encodings ADR-0007/0008 — 16-hex HLC, 13/26-char Crockford);
                        --   lifted pointwise over a key map = the `meta` CRDT
  OrSet.lean            --   observed-remove set + join laws

Tl/Kernel/              -- the verified core (NO I/O)
  State.lean            --   issues OR-Set, edges OR-Set, per-issue field maps,
                        --   labels OR-Set, and a per-key-LWW `meta` map (ADR-0002)
  Op.lean               --   the Op inductive; SEVEN deltas (create, setFields,
                        --   metaSet, edgeAdd, edgeRemove, labelAdd, labelRemove) —
                        --   readable CLI verbs map onto these in the shell (ADR-0008)
  Apply.lean            --   apply : State → Op → State  (total reducer + fold)
  Ready.lean            --   ready : State → Now → List Id  (total on cyclic AND
                        --   dangling graphs; blocker discharged iff its
                        --   effectiveStatus is done|cancelled — epics by rollup);
                        --   critical-path weight = |reach⁺ over blocks| (total);
                        --   why/unblocks = transitive unclosed blockers / freed-set
                        --   (same reach⁺ machinery; total, proved — ADR-0004 thm 10)
  ReadyFast.lean        --   the SHIPPED queue: hoisted present/edge views,
                        --   rollups through the batched map, one RankKey per
                        --   candidate, sort on cached keys, saturating closure
                        --   (reachFix + fixpoint stability); refinement bridge
                        --   readyFast_eq / unblocksFast_eq / whyFast_eq — the
                        --   fast forms EQUAL the spec, so thm 4/10 transfer
  Cycles.lean           --   per-kind cycle detection (bounded reachClosure
                        --   iteration — total, no well-founded obligation);
                        --   one canonical witness per cyclic SCC = the SCC's
                        --   sorted NODE SET (ADR-0004 thm 6; proved in SccProps);
                        --   ALSO readiness-deadlock ≺-cycles (mixed blocks+parent,
                        --   ADR-0004 thm 5/6) so no stuck live set is undiagnosed
  Rollup.lean           --   effectiveStatus (the SPEC: fuel form); reads epic's
                        --   STORED status first (manual-cancel precedence), else
                        --   derives from children
  RollupSpec.lean       --   rollup meets its ADR-0003 spec (unconditional
                        --   branches) + live-cycle conservatism (cycle members
                        --   are Open at every fuel — the path-cutoff exactness)
  RollupSat.lean        --   fuel saturation ⇒ the UNCONDITIONAL recurrence
                        --   (no acyclicity hypothesis; ascending-chain
                        --   pigeonhole, Mathlib zone like RollupAcyclic)
  RollupFast.lean       --   the SHIPPED rollup: memoized visiting+memo walk
                        --   over a hoisted parent-edge view (effStatusAll, one
                        --   pass per view) + the refinement bridge — pointwise
                        --   EQUAL to the spec (effStatusWith_eq/isReadyWith_eq),
                        --   so every spec theorem transfers; once-per-pass is
                        --   rollupVisit_find_hit (ADR-0003 §3 amendment)
  RollupAcyclic.lean    --   rollup fuel-adequacy on acyclic parent graphs
  Invariant.lean        --   Invariant = valid status enum ONLY; endpoint-existence
                        --   and acyclicity deliberately excluded (tolerated at read)
  Theorems.lean         --   convergence + tracker theorems (ADR-0004/0003);
                        --   liveness is one-directional deadlock-freedom, not a biconditional
  FoldFast.lean         --   the shipped cold fold: foldFast joins the deltas'
                        --   component maps by batched construction (O(N log N))
                        --   + the bridge foldFast_eq_fold — equal to fold, so
                        --   every fold theorem transfers (cold path, ADR-0022)
  Frame.lean            --   frame lemmas: meta/labels/relate move neither ready nor rollup
  CloseMono.lean        --   close-monotonicity (ADR-0004 thm 7)
  Reach.lean            --   reach⁺ closure; liveness/deadlock + why (thms 5/6/10;
                        --   the kernel's only Mathlib imports live here, ADR-0009)
  CyclesFast.lean       --   the SHIPPED diagnostics: hoisted views, rollups
                        --   through the batched map, saturating closures in
                        --   onCycle/sameSCC; bridge cyclesFast_eq /
                        --   precCyclesFast_eq — EQUAL to the spec, thm 6
                        --   transfers; commands compute each result once
  SccProps.lean         --   SCC-witness enumeration: exactly one witness per cyclic SCC
  Unblocks.lean         --   unblocks = the ready-set diff; exact and unconditional
  Ranking.lean          --   ready-queue ranking; the queue is proved sorted

Tl/Format/              -- I/O shell: wire encodings + on-disk record (tested)
  Crockford.lean        --   Crockford base32 codec (ids, replica, nonce; ADR-0007)
  Record.lean           --   JSONL record envelope: parse/render, preserve-unknown,
                        --   canonical key order + pinned string escaping
                        --   (ADR-0008 §canonical form)
  Codec.lean            --   the record↔Op codec: ParsedOp = the typed WireOp
                        --   (one constructor per ADR-0008 verb — a verb/payload
                        --   mismatch is unrepresentable) + Stamp + actor +
                        --   unknown bag; the kernel Op is the WireOp.toOp
                        --   projection (the verb→delta table, executable);
                        --   covers the FULL v1 enum, not just stage-1-emitted
                        --   verbs; strictly canonical decode, fail-closed
                        --   malformed-line/unknown-version (priority clamps,
                        --   disclosed)
  Time.lean             --   strict canonical ISO-8601 UTC ↔ epoch-ms codec
                        --   (deferUntil storage + the --json timestamps)
  Version.lean          --   v fail-closed-on-newer; v=0 is malformed, not older;
                        --   the snapshot record stays RESERVED (ships with
                        --   compaction behind a v bump, ADR-0008 — a v1 reader
                        --   refuses it as unknown-version)
  Ids.lean              --   issue-id mint (leftmost 80 SHA-256 bits over the
                        --   fixed-width preimage, ADR-0018) + the tl- display affix

Tl/Error.lean           -- the structured error contract: the closed code enum,
                        -- stable wire strings + exit codes, teaching messages,
                        -- ADR-0020 context fields (below Format/Store/Cli so
                        -- every shell layer fails through one type)

Tl/Hash/                -- pure hashing for identity minting (tested)
  Sha256.lean           --   FIPS 180-4 transcription returning the FULL 32-byte
                        --   digest; consumers slice (ids take the leftmost 80
                        --   bits, import widths differ — ADR-0007/0018); the
                        --   fixed-shape state is Vector-typed (Fin-indexed
                        --   constants/schedule/hash words, digestVec carries
                        --   its 32 bytes in the type); vector-tested (FIPS +
                        --   padding boundaries + the worked mint vector)

Tl/Store/               -- I/O shell: local persistence (tested)
  Paths.lean            --   the .tl/ layout + ADR-0012 discovery (walk-up bounded
                        --   by the .git dir-or-file boundary + ceiling dirs;
                        --   --dir/TL_DIR override; T4 validation → unsafe-path);
                        --   Dirs = (base, rel): the base follows symlinks, the
                        --   .tl components never do (ADR-0015 §6); TlM =
                        --   ExceptT Tl.Error IO is the shell failure channel
  Local.lean            --   .tl/local/ replica + clock files: load/persist,
                        --   auto-mint from OS entropy when absent (ADR-0012),
                        --   corrupt-replica/corrupt-clock fail-closed with the
                        --   remove-and-rerun fix; saturation = corrupt-clock
                        --   reason:"saturated" (ADR-0007)
  Lock.lean             --   the mutation lock (bounded lock-busy poll) and the
                        --   locked critical section `transact`: acquire → load
                        --   replica → materialize through the fold cache
                        --   (ADR-0022; a refused OWN segment fails the write) → read+advance the HLC (the absent-clock
                        --   arm reseeds from max(all-segments line max, now)
                        --   INSIDE the lock) → build (guards refuse before any
                        --   byte) → append → fsync → persist clock → release
                        --   (ADR-0015 §1)
  Segment.lean          --   segment append/enumerate/read; torn-tail skip;
                        --   crash-fragment closing; one O_APPEND write per
                        --   record + fsync (ADR-0008 §corruption, ADR-0015
                        --   §2/§5); enumeration validates log/ through the
                        --   shim walk before listing and only canonical
                        --   replica-id stems count as segments (junk .jsonl
                        --   disclosed, never silently folded or dropped)
  Materialize.lean      --   records → ops → fold into kernel State; segment-
                        --   scoped fail-closed with --skip-bad disclosures
                        --   (incl. the record/segment owner check — a record
                        --   stamped by another replica is a malformed line);
                        --   line-scoped max-HLC scan (the clock reseed); the
                        --   HLC skew window (ADR-0007) — a FOREIGN op dated
                        --   beyond now+W is deferred from the fold AND maxHlc
                        --   (own exempt), so a future HLC neither wins LWW nor
                        --   inflates the reseed (passes `now` only on the
                        --   read/write path; pure-fold default off)
                        --   (Tl/Sync composes Store primitives — own-segment
                        --   snapshot under lock, atomic foreign-cache replace —
                        --   rather than owning segment I/O)
  Cache.lean            --   the materialization fold cache (ADR-0022): the
                        --   folded State persisted in gitignored .tl/local/cache,
                        --   keyed per segment on (byteLen, sha256 prefix,
                        --   lineCount, refused, deferred lines); valid ⇒ reads
                        --   and transact fold only appended suffixes + newly-
                        --   admissible deferred lines on top (fold_append +
                        --   order-insensitivity); stale/corrupt/absent ⇒ rebuilt
                        --   from segments, never repaired; persists best-effort
                        --   via atomic replace (doctor reads, never persists;
                        --   --skip-bad bypasses). Only the fold is cached —
                        --   ops/refusals/deferrals/warnings recompute live
  Sys.lean              --   bindings to the native shim (ffi/tlsys.c): no-follow
                        --   + ownership-checked two-part open (the §6 checks
                        --   ride EVERY component of every open), read/write,
                        --   fsync (F_FULLFSYNC on Darwin), fd lock, OS entropy,
                        --   ownership check — mechanism only (ADR-0019); compiled
                        --   with the host cc (the bundled clang ships no macOS
                        --   system-header sysroot — a recorded ADR-0019 deviation)

Tl/Clock/               -- I/O shell: ordering/identity (tested)
  Hlc.lean              --   hybrid logical clock: pure update rules + hex codec
                        --   (file persistence + the recovery branches live in
                        --   Tl/Store/Local and Lock — ADR-0007 §HLC)
  Replica.lean          --   replica-id validation (canonical width/charset/
                        --   64-bit range); minting + persistence live in
                        --   Tl/Store/Local and draw from the shim's OS CSPRNG
                        --   (ADR-0019)
  Skew.lean             --   PROVED: the HLC skew-window admission predicate
                        --   (admittedB, the exact one the fold branches on) +
                        --   its monotonicity (admitted_mono_now ⇒ deferral is
                        --   eventual) and filter-identity-past-threshold; pure,
                        --   kernel-free (ADR-0007 amendment)
  SkewConverge.lean     --   PROVED: skew_converges — composes Skew's filter-
                        --   identity with the kernel fold (fold_eq_of_mem_iff)
                        --   ⇒ replicas converge regardless of clock skew

Tl/Sync/                -- I/O shell: refs/tl/log transport (tested)
  Ref.lean              --   read/write refs/tl/log via git plumbing (built): the
                        --   tree is root-level <replica-id>.jsonl blobs, commits
                        --   parent-chained, fixed neutral tl identity, CAS
                        --   update-ref (writeRefCas distinguishes a lost CAS
                        --   race from a real error); blob content is read/written
                        --   as raw bytes (gitBytes), never a lossy String round-
                        --   trip (ADR-0001 §2 in-ref encoding)
  Merge.lean            --   per-segment complete-line set union, canonical
                        --   (sorted/deduped) — the CRDT join (built, ADR-0001 §5)
  Local.lean            --   the local-first worktree leg + read-time refresh
                        --   (built, ADR-0016 §1/§3): syncLocal publishes the own
                        --   segment into the shared ref (CAS-retry) and absorbs
                        --   siblings into .tl/log/ via atomic rename, never the
                        --   own segment (`tl sync`); refreshFromRef is the read-
                        --   path O(1) ref-OID trigger (vs the .tl/local/ref-mark)
                        --   that absorbs siblings before a fold — best-effort,
                        --   lock-free, never fails a read
  Remote.lean           --   the remote fetch / union / push leg (built, ADR-0001
                        --   §5): resolveRemote (tl.remote > branch-upstream >
                        --   origin; detached-HEAD → origin); syncRemote unions
                        --   local+remote into a commit parented on BOTH tips (so
                        --   the push fast-forwards), retries once on a non-ff
                        --   rejection then push-rejected; no remote → no-upstream
                        --   (reported, not fatal). `tl sync` = local leg → remote
                        --   leg → absorb-pulled
  Sync.lean             --   auto-sync (planned — publish after a write, atop the
                        --   legs above)

Tl/Import/              -- I/O shell: one-shot beads import (planned — Stage 3)
  Beads.lean

Tl/Cli/                 -- I/O shell: command dispatch + JSON output (tested)
  Envelope.lean         --   the --json envelope (schemaVersion/ok/data|error) in
                        --   the deliberate member order (ADR-0008/0020)
  Project.lean          --   the read View + issue projections: the full object
                        --   and trimmed rows (omit-empty, display ids, forced-ms
                        --   timestamps), fold-time provenance (cross-op recency
                        --   compares the FULL Stamp — the LWW order — never the
                        --   bare HLC), dependencies +
                        --   canonical parent, the provenance trust block
                        --   (ADR-0003/0020)
  Sanitize.lean         --   the ADR-0014 render sanitizer (ANSI/control/zero-
                        --   width/bidi stripping; 1 KiB / 64 KiB bounds with
                        --   disclosed truncation) — applied on BOTH render paths
  Render.lean           --   human rendering (ADR-0017): the Style surfaces
                        --   (--color/--glyphs/--plain, NO_COLOR, TTY), the
                        --   one-line glyph/color format, the show detail view
                        --   + children tree (total on cyclic parent graphs),
                        --   footer/legend, stats block — never on the --json path
  Resolve.lean          --   id/slug resolution (tl- discriminator, case-fold +
                        --   symbol aliases, prefix/ambiguity — ADR-0007) and the
                        --   ADR-0013 actor chain
  Commands.lean         --   the stage-1 verbs + the agent-surface/ergonomics
                        --   verbs (reopen/stats/log, sync, label add/remove/list,
                        --   list --label facet); write guards run inside the
                        --   locked transact build (not-claimable, not-closeable,
                        --   the idempotent re-close); doctor's check rows
  Init.lean             --   tl init (idempotent on an existing replica;
                        --   completes a partial .tl; CSPRNG replica mint;
                        --   repo-toplevel placement lives in Commands.cmdInit)
  Main.lean             --   verb dispatch, arg parsing, streams + exit codes
                        --   (ADR-0008 §--json; the root Main.lean stays the
                        --   thin exe entry)

Tests/                  -- outside-TCB checks, run via `lake exe tltest`
  Harness.lean          --   assertion + seeded-generator harness
  CrockfordTests.lean   --   encode/decode round-trips
  HlcTests.lean         --   HLC update rules + hex codec branches
  RecordTests.lean      --   envelope round-trip + canonical order
  ErrorTests.lean       --   the (code, wire, exit) table + envelope bytes
  Sha256Tests.lean      --   FIPS/boundary vectors + the worked mint vector
  TimeTests.lean        --   instant-codec vectors + strictness rejections
  CodecTests.lean       --   a canonical line per verb, the escape classes,
                        --   fail-closed rows, the priority clamp, a fold smoke test
  SysTests.lean         --   per-branch shim tests (symlinks, locks, entropy, sync)
  StoreTests.lean       --   discovery, transact, crash/hostile adversity, clock
                        --   and replica recovery, lock contention
  CacheTests.lean       --   fold-cache codec round-trip + fail-closed rows,
                        --   every validity branch (path observed via a poisoned
                        --   marker), the cached≡fresh seeded property, file
                        --   lifecycle (healing, doctor non-persist, skip-bad
                        --   bypass, symlink refusal)
  CliTests.lean         --   per-verb contract rows + spawned-binary envelope/
                        --   exit/env tests (TL_DIR, ceiling dirs) + the tree
                        --   diamond/cycle/shared-root tree fixtures (shared
                        --   nodes render once and are marked on re-encounter;
                        --   parent cycles keep the distinct cycle marker)
  PerfTests.lean        --   scaling regression rows: ×4 synthetic ops must
                        --   grow ≤ ×12 on five ratio-asserted paths (cold
                        --   batched fold, warm cached materialize, rollup,
                        --   provenance, sync union); ready + diagnostics are
                        --   ceiling-only pending the tracked comparison-constant
                        --   and sublinear-find follow-ups
  CrossTests.lean       --   encoding order-preservation (all pairs) + the
                        --   compiled-kernel-vs-spec property cross-check
  SanitizeTests.lean    --   one row per ADR-0014 sanitizer class
  Main.lean             --   tltest entry point
```

Mapping to the boundary: `Tl/Crdt/` and `Tl/Kernel/` are proved
([ADR-0004](adr/ADR-0004-verified-kernel-tcb-boundary.md)); `Tl/Error`,
`Tl/Format`, `Tl/Hash`, `Tl/Store` (+ `ffi/tlsys.c`), `Tl/Clock`, `Tl/Sync`,
`Tl/Import`, `Tl/Cli` are the tested shell outside it.

## Cross-cutting invariants (load-bearing across modules & ADRs)

A handful of properties thread through many modules and ADRs at once — change one
and several proofs or tests move. A contributor should know these before touching
any single piece (it is also the bus-factor map: the correctness web in one
table).

| Invariant | Relied on by | Enforced / checked by |
|---|---|---|
| `(hlc, replica, nonce)` is a total order | every LWW/OR-Set join (the join is a *function*), issue-id derivation | kernel proof *given* the order; shell mints/validates the triple; nonce-uniqueness is a carried assumption (overview Trusted) — ADR-0002/0007 |
| Clocks / ids / actor are *data* (kernel reads no clock/RNG/env) | convergence being provable at all (the fold stays deterministic) | kernel has no I/O by type (`State → Op → State`); shell mints and freezes them into ops — ADR-0001 §1 / 0007 / 0013 |
| Order/duplicate-insensitivity of the fold | git-as-transport, the segment union, the worktree local-leg, at-least-once delivery | ADR-0004 thm 2 (+ thm 8 inflation/idempotent re-delivery) |
| Dangling `blocks`/`parent` edges are read-time inert | `ready` / `effectiveStatus` / cycle totality; no spurious not-ready | kernel: `Invariant` excludes endpoint-existence; reads treat a nonexistent endpoint as discharged — ADR-0002 / 0003 §5 / 0004 thm 3-4 |
| `actor` is provenance-only (not in the CRDT key) | convergence unaffected by provenance; `createdBy` projection | frame lemma — ADR-0003 / 0004 / 0008 / 0013 |
| `now` is injected; `deferUntil` is a plain instant distinct from the HLC | `ready` determinism + time-monotonicity; "clocks are data" | kernel signature (`Now` param); shell normalizes to an ISO-8601 UTC instant — ADR-0010 / 0004 thm 9 / 0008 |
| Fail-closed parse is *segment*-scoped, not log-scoped | availability under a bad/hostile/`v`-skewed line (one segment can't deny service to all) | shell parser — ADR-0008 §corruption / 0015 §5 / 0014 T2 |

Two reading rules these encode: derive-or-report, never enforce (any
cross-entity rule a merge could break is a total function of state, not a
write-time guard — ADR-0003), and prove the pure core, test the shell, name the
rest as a carried assumption (ADR-0004 / overview Trusted).
