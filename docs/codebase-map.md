# Codebase map

> Stage 0 is built: the verified kernel (`Tl/Crdt/`, `Tl/Kernel/`) and the
> first tested-shell pieces (`Tl/Format/`, `Tl/Clock/`, `Tl/Cli/Init`). Entries
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
  Cycles.lean           --   per-kind cycle detection (well-founded recursion);
                        --   one canonical witness per cyclic SCC = the SCC's
                        --   sorted NODE SET (ADR-0004 thm 6; proved in SccProps);
                        --   ALSO readiness-deadlock ≺-cycles (mixed blocks+parent,
                        --   ADR-0004 thm 5/6) so no stuck live set is undiagnosed
  Rollup.lean           --   effectiveStatus; reads epic's STORED status first
                        --   (manual-cancel precedence), else derives from children
  RollupSpec.lean       --   rollup meets its ADR-0003 spec (unconditional branches)
  RollupAcyclic.lean    --   rollup fuel-adequacy on acyclic parent graphs
  Invariant.lean        --   Invariant = valid status enum ONLY; endpoint-existence
                        --   and acyclicity deliberately excluded (tolerated at read)
  Theorems.lean         --   convergence + tracker theorems (ADR-0004/0003);
                        --   liveness is one-directional deadlock-freedom, not a biconditional
  Frame.lean            --   frame lemmas: meta/labels/relate move neither ready nor rollup
  CloseMono.lean        --   close-monotonicity (ADR-0004 thm 7)
  Reach.lean            --   reach⁺ closure; liveness/deadlock + why (thms 5/6/10;
                        --   the kernel's only Mathlib imports live here, ADR-0009)
  SccProps.lean         --   SCC-witness enumeration: exactly one witness per cyclic SCC
  Unblocks.lean         --   unblocks = the ready-set diff; exact and unconditional
  Ranking.lean          --   ready-queue ranking; the queue is proved sorted

Tl/Format/              -- I/O shell: wire encodings + on-disk record (tested)
  Crockford.lean        --   Crockford base32 codec (ids, replica, nonce; ADR-0007)
  Record.lean           --   JSONL record envelope: parse/render, preserve-unknown,
                        --   canonical key order (built); the record↔Op codec —
                        --   whose parsed model carries the wire verb, Stamp,
                        --   actor, and unknown bag ALONGSIDE the kernel Op (a
                        --   bare Op cannot round-trip) — lands with Stage 1
  Version.lean          --   format version policy; snapshot record (planned — Stage 1)

Tl/Hash/                -- pure hashing for identity minting (planned — Stage 1)
  Sha256.lean           --   FIPS 180-4 transcription returning the FULL 32-byte
                        --   digest; consumers slice (ids take the leftmost 80
                        --   bits, import widths differ — ADR-0007/0018); CAVP-tested

Tl/Store/               -- I/O shell: local persistence (planned — Stage 1)
  Paths.lean            --   the .tl/ layout + discovery glue (ADR-0001 §3, ADR-0012)
  Lock.lean             --   the mutation lock and the locked critical section:
                        --   acquire → mint-HLC → append → fsync → persist clock
                        --   → release (ADR-0015 §1)
  Segment.lean          --   segment append/enumerate/read; torn-tail skip and
                        --   segment-scoped fail-closed (ADR-0008 §corruption, ADR-0015 §5)
  Materialize.lean      --   records → ops → fold into kernel State
                        --   (Tl/Sync composes Store primitives — own-segment
                        --   snapshot under lock, atomic foreign-cache replace —
                        --   rather than owning segment I/O)
  Sys.lean              --   bindings to the native shim (ffi/tlsys.c): no-follow
                        --   open/read/write, fsync, fd lock, OS entropy, ownership
                        --   check — mechanism only; OS primitives the toolchain
                        --   lacks or does not guarantee, nothing else (ADR-0019)

Tl/Clock/               -- I/O shell: ordering/identity (tested)
  Hlc.lean              --   hybrid logical clock: pure update rules + hex codec
                        --   (built; file persistence wiring lands with the Store)
  Replica.lean          --   replica-id mint + validation (built; ditto persistence)

Tl/Sync/                -- I/O shell: refs/tl/log transport (planned — Stage 3)
  Ref.lean              --   read/write refs/tl/log via git plumbing (no branch/index)
  Merge.lean            --   per-segment complete-line set union (the CRDT join)
  Sync.lean             --   fetch / merge / push; push-rejection retry; no-upstream;
                        --   auto-sync; doctor's ref/segment health checks

Tl/Import/              -- I/O shell: one-shot beads import (planned — Stage 3)
  Beads.lean

Tl/Cli/                 -- I/O shell: command dispatch + JSON output
  Init.lean             --   tl init (built; its own IO test is pending — due
                        --   with the Stage-1 CLI test buildout)
  Main.lean             --   verb dispatch + the --json envelope (planned —
                        --   Stage 1; the root Main.lean stays the thin exe entry)

Tests/                  -- outside-TCB checks, run via `lake exe tltest`
  Harness.lean          --   assertion + seeded-generator harness (built)
  CrockfordTests.lean   --   encode/decode round-trips (built)
  HlcTests.lean         --   HLC update rules + hex codec branches (built)
  RecordTests.lean      --   envelope round-trip + canonical order (built)
  Main.lean             --   tltest entry point (built)
  --                    -- planned (Stage 1+): the record↔Op codec round-trip
  --                    -- corpus; store adversity tests (crash fragments,
  --                    -- hostile lines, lock contention); the encoding
  --                    -- order-preservation cross-check (wire-string order =
  --                    -- decoded Stamp order); the compiled-kernel-vs-spec
  --                    -- property cross-check; differential import (Stage 3)
```

Mapping to the boundary: `Tl/Crdt/` and `Tl/Kernel/` are proved
([ADR-0004](adr/ADR-0004-verified-kernel-tcb-boundary.md)); `Tl/Format`,
`Tl/Store`, `Tl/Clock`, `Tl/Sync`, `Tl/Import`, `Tl/Cli` are the tested shell
outside it.

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
