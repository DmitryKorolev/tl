# Codebase map (intended layout)

> Implementation has not started; this is the target structure, not a
> description of existing code. The line that matters: the verified
> kernel has no I/O, and everything that touches the world is a separate,
> tested shell.

```
Tl.lean                 -- root module; imports everything below

Tl/Crdt/                -- generic CRDT pieces (verified)
  OrSet.lean            --   observed-remove set + join laws
  Lww.lean              --   LWW register; key is the TRIPLE (HLC, replica, nonce)
                        --   (ADR-0002/0007; wire encodings ADR-0007/0008 — 16-hex HLC, 13/26-char Crockford);
                        --   lifted pointwise over a key map = the `meta` CRDT
  Join.lean             --   commutativity / associativity / idempotence

Tl/Kernel/              -- the verified core (NO I/O)
  State.lean            --   issues OR-Set, edges OR-Set, per-issue field maps,
                        --   labels OR-Set, and a per-key-LWW `meta` map (ADR-0002)
  Op.lean               --   the Op inductive; SEVEN deltas (create, setFields,
                        --   metaSet, edgeAdd, edgeRemove, labelAdd, labelRemove) —
                        --   readable CLI verbs map onto these in the shell (ADR-0008)
  Apply.lean            --   apply : State → Op → State  (total reducer)
  Ready.lean            --   ready : State → Now → List Id  (total on cyclic AND
                        --   dangling graphs; blocker discharged iff its
                        --   effectiveStatus is done|cancelled — epics by rollup);
                        --   critical-path weight = |reach⁺ over blocks| (total);
                        --   why/unblocks = transitive unclosed blockers / freed-set
                        --   (same reach⁺ machinery; total, proved — ADR-0004 thm 10)
  Cycles.lean           --   per-kind cycle detection (well-founded recursion);
                        --   one canonical simple-cycle witness per cyclic SCC;
                        --   ALSO readiness-deadlock ≺-cycles (mixed blocks+parent,
                        --   ADR-0004 thm 5/6) so no stuck live set is undiagnosed
  Rollup.lean           --   effectiveStatus; reads epic's STORED status first
                        --   (manual-cancel precedence), else derives from children
  Invariant.lean        --   Invariant = valid status enum ONLY; endpoint-existence
                        --   and acyclicity deliberately excluded (tolerated at read)
  Theorems.lean         --   convergence + tracker theorems (ADR-0004/0003);
                        --   liveness is one-directional deadlock-freedom, not a biconditional

Tl/Format/              -- I/O shell: on-disk log (tested)
  Record.lean           --   JSONL record <-> Op; preserve-unknown
  Version.lean          --   format version policy; snapshot record

Tl/Clock/               -- I/O shell: ordering/identity (tested)
  Hlc.lean              --   hybrid logical clock
  Replica.lean          --   replica-id minting + persistence

Tl/Sync/                -- I/O shell: refs/tl/log transport (tested)
  Ref.lean              --   read/write refs/tl/log via git plumbing (no branch/index)
  Merge.lean            --   per-segment complete-line set union (the CRDT join)
  Sync.lean             --   fetch / merge / push; push-rejection retry; no-upstream;
                        --   auto-sync; doctor's ref/segment health checks

Tl/Import/              -- I/O shell: one-shot beads import (tested)
  Beads.lean

Tl/Cli/                 -- I/O shell: command dispatch + JSON output (tested)
  Main.lean

Tests/                  -- outside-TCB checks
  Roundtrip.lean        --   parse ∘ render = id
  Differential.lean     --   import matches source-format fixtures
  Property.lean         --   sampled cross-check that the COMPILED kernel
                        --   matches its proved spec (regression net over the
                        --   executable; NOT a substitute for the Tl/Kernel +
                        --   Tl/Crdt theorems)
```

Mapping to the boundary: `Tl/Crdt/` and `Tl/Kernel/` are proved
([ADR-0004](adr/ADR-0004-verified-kernel-tcb-boundary.md)); `Tl/Format`,
`Tl/Clock`, `Tl/Sync`, `Tl/Import`, `Tl/Cli` are the tested TCB shell.

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
