# Design backlog

Open design questions for `tl` — decisions not yet made, or made but not yet
pinned in an ADR. Each item leaves the backlog by landing in an ADR (new or
amended) or by graduating into an implementation task when its stage starts.
Decisions already made are recorded in their ADRs (and git history); this lists
only what is still open.

Status: Stages 0 and 1 are built (the verified kernel and the MVP work
loop). Stages 2–3 are **partly built**: the agent surface (skill, `help --json`,
discovery pointer), the free verbs (`reopen`/`stats`/`log`), rich human output,
`list` open-by-default + `--tree`, and the **full `refs/tl/log` sync transport**
(local leg, read-time refresh, remote fetch/union/push, and the HLC skew window
— proved convergence-safe) have landed. Still open: the Stage-2 ergonomics verbs
(`labels`, `defer`/`undefer`, `dep tree/path/critical`, `edit`), auto-sync
(Stage 3, blocked on its process-model decision), and beads `import` (Stage 3).
The items Stage 1 touched have graduated: `duplicate-of`
semantics, the write-time guard inventory + idempotent re-close, the
`not-closeable` / `unsafe-path` error codes, the canonical string-escaping
spec (all ADR-0008, with ADR-0003/0015/0020 cross-refs), and clock-file
recovery + the HLC-saturation code (ADR-0007) landed 2026-06-10, joining the
stage-1 `--json` shapes and the 0.x stability horizon (ADR-0020 / ADR-0008).
Everything else
below remains stage-gated (decide when building that surface) or a
forever-contract surface that freezes on first implementation; the
*candidate-ADR* items are worth settling before/early.

## Candidate ADRs (settle before/early in implementation)

- `defer` input parsing [low] — the shell-side parsing of `--until` /
  `--for` (time-zone handling, bare-date anchor, relative-duration base) is
  unpinned; the kernel instant, the two-time-type model, and the stored ISO-8601
  UTC encoding are settled in ADR-0010/0008. Pin the parsing rules in ADR-0010, or
  split a small time-&-clocks ADR.

## Kernel & data model

- `reopen` and `assignee` [low] — ADR-0008's `reopen` sets `status=open` and
  clears `closeResolution` but does not touch `assignee`; with `claimedAt` going
  absent (reopen is later than the last `claim`), a reopened issue is `open`, not
  `in_progress`, yet still shows an `assignee`. Decide whether `reopen` also clears
  `assignee` (vision/ADR-0008/0013).

## Proof obligations (theorems to settle)

Kernel theorems still to decide whether to commit to:

- Cycle-breaking progress / termination [low] — prove that removing one
  kind-`k` edge between members of any SCC witness `cycles s k` reports
  strictly reduces the cyclic-SCC set, so the
  `dep cycles → dep remove` loop reaches an acyclic kind-`k` graph in ≤ (#SCCs)
  steps. Makes the diagnostic's advice provably *terminating*, not just correct
  (ADR-0004).
- Add-wins / re-add as explicit OR-Set theorems [low] — ADR-0002 states
  add-wins and re-addability in prose; elevate them to stated theorems (an
  unobserved add survives a concurrent remove; a removed element is re-addable with
  a fresh tag — not a 2P-set), so the `dep remove`/`unrelate` guarantee is a
  theorem rather than a consequence left implicit in the join laws (ADR-0002/0004).

## CLI surface (before CLI freeze)

- `tl list` input grammar [low] — the *output* rows are pinned (ADR-0020);
  the input surface so far: a bare `list` shows **open issues** oldest-first
  (effectively-closed hidden; `--all` includes closed), with `--limit`
  (default 10, `0` = all), `--tree` (ADR-0017 §2 forest), and `--label <l>`
  (repeatable ⇒ AND; built with labels). The open-by-default question is
  decided (this way) and built. Still open: the *other* facet flag spellings
  (status / assignee / priority / text) and text-match semantics (substring vs
  word, case folding, which fields) (vision / ADR-0020).
- `--json` `data` shapes for the later `dep` utilities
  (`tree`/`path`/`critical`) [low] — the stage-1 command shapes (incl. `doctor`,
  `dep cycles`, `why`), `tl help --json`, and now `tl stats` / `tl log` are
  pinned in ADR-0020 (`help`/`stats`/`log` built); the `dep` utilities pin
  when built, following its conventions. (`tl log`'s `--since` cursor stays
  deferred — it needs a version vector, below.)
- A future `tl log --since <hlc>` cursor needs a version vector, not a scalar
  HLC [low] — `observe-remote` advances only the local clock, so a late-synced op
  from a lagging replica keeps an HLC *below* another replica's watermark; a scalar
  `--since hlc` filter would silently miss it — a soundness hole for the promised
  incremental feed. Record that an incremental cursor must be a version-vector (the
  frontier compaction already reserves), and a scalar `--since` is best-effort/lossy;
  defer implementation but pin the contract (ADR-0008; relates to the read-command
  `--json` shapes above).

## Log format, versioning & compaction

- Compaction snapshot placement & union-merge interaction is unpinned [med] —
  ADR-0008 reserves a `snapshot` record and reads as `snapshot ⊕ fold(tails)`, and
  claims "no format restructuring later" — but it never says where the snapshot
  lives / which segment owns it, and the text reads two ways: *logical* compaction
  (ops stay; snapshot shadows them — but then the log never shrinks) vs *physical*
  removal (which the strictly-growing per-segment line-union, ADR-0001 §5, would
  re-add from any un-compacted replica, resurrecting the retired ops the
  snapshot tried to drop). Pin logical-vs-physical and, if physical, that
  compaction *does* require a sync/union change (ADR-0008 × ADR-0001 §5 ×
  ADR-0015 §3). A reserved kernel theorem records the safety obligation —
  *compaction preserves the fold*, `fold ops = snapshot(F) ⊕ fold(ops above F)` for
  a causally-closed frontier (ADR-0004/0008) — which whichever placement is chosen
  must discharge.

## Sync, discovery & local concurrency

- Discovery: bare repos, `.git`-file worktrees, `GIT_DIR`/`GIT_WORK_TREE` [low]
  — discovery for bare repos, `.git`-file worktrees, and
  `GIT_DIR`/`GIT_WORK_TREE` is undefined; delegate to `git rev-parse
  --show-toplevel`/`--git-dir` and state the bare-repo policy. (ADR-0012 handles
  linked worktrees/submodules — each its own boundary.)
- Network-FS behavior is undecided [low] — a `.tl/` on NFS/SMB is
  "documented-unsupported" (convergence holds via the nonce; ownership + HLC
  monotonicity do not), but no doc decides detect-and-warn vs silent-proceed.
  Decide; if detect, give `doctor` (and optionally `init`) a best-effort FS-type
  probe that *warns* (not a hard error, since convergence is unaffected) —
  ADR-0015 + ADR-0011/doctor.
- The committed discovery pointer has no home when no agent file exists [low] —
  ADR-0011's cross-clone discovery path is a one-line pointer `init` offers to add
  to a root agent file (`AGENTS.md`/`CLAUDE.md`/…); the local `.tl/README.md` is
  gitignored and does not travel. Decide what `init` does when none of those
  files exist (create a minimal one? which? skip — leaving no committed
  discovery?) — ADR-0011 / ADR-0001 §4.

## Import / beads

- Complete the beads field inventory [low] — every source field maps to a tl
  destination or an explicit, disclosed drop (ADR-0005).
- Differential-import fixtures, equality relation, and mapping matrix [low] —
  the differential-import test is mandated but these aren't pinned; commit `.beads`
  fixtures + an expected-state oracle under `Tests/fixtures/`, one row per mapping
  (ADR-0005 / overview).
- Import's deterministic per-op nonce derivation is informal [low] — the
  import-seed id and import replica-id are pinned to full precision (named SHA-256
  preimage, bit-slice, encoding), but the per-op nonce is only "derived from the
  source record + op role + target id" — no hash, preimage, or width — even though
  it is part of the OR-Set add-tag string and LWW triple that must be byte-identical
  for re-import idempotence (the differential-import oracle above). Pin it like its
  siblings (e.g. `crockford32(SHA-256("import-nonce:" ++ … ))[0..128]` → 26 chars) —
  ADR-0005.
- beads `priority` source scale and the `pinned` collision [low] — beads
  `priority` → 0–4 cites an undocumented source scale and `pinned` collides;
  document the exact table and resolve `pinned` (ADR-0005).
- Import `--force` is overloaded; the bounds-override flag is inconsistent [low]
  — ADR-0005 uses `--force` both to override import-into-existing state *and* (as
  `force-required`) to override the resource bounds; ADR-0014 T6 names the bounds
  override "`--force`/`--max`". Conflating two distinct safety gates means one
  `--force` bypasses both. Decide distinct flags (e.g. `--force` for clobber-existing,
  `--max`/`--allow-large` for bounds) and reconcile ADR-0005 × ADR-0014 T6.

## Build & proof infra

- Compiled-kernel-vs-spec property cross-check [low] — the mechanism now
  exists (`Tests/CrossTests.lean`: fixed-seed random op multisets; fold
  order/dup-insensitivity, join laws, ready soundness+sortedness,
  unblocks = ready-diff, rollup totality, all against the compiled
  functions); the residual is recording that shape — corpus, seeds, sampled
  theorems — in an ADR so the gate is contractual rather than incidental
  (ADR-0004 / a test ADR).
- "No task-ID leakage" lint pattern/scope [low] — pin the regex and excluded
  paths (`docs/`, `Tests/.../fixtures/`, the importer's `ext:beads`) — AGENTS.md /
  a lint spec.

## Distribution (before release)

- `git` minimum version floor [low] — `git` is a runtime prerequisite but no
  minimum version is pinned; pin a floor and have `doctor`/`init` check it
  (ADR-0006 / README).
- Native-Windows gating test pass [low] — the gating test pass for native
  Windows is open, spec'd only if it is promoted from Tier-2 (WSL is the Supported
  Windows path). The Win32 FS/git-shell-out *design* is in ADR-0015 §7 / ADR-0006.
- Signed-release verification is under-specified [med] — ADR-0006 says
  `curl|sh`/brew "verify and fail closed" via keyless Sigstore/cosign, but never
  pins the expected `--certificate-identity` + `--certificate-oidc-issuer` the
  verifier checks against — without which a fail-closed verifier accepts *any* valid
  Sigstore cert, hollowing out T3. Secondary (weaker): no Rekor/transparency-log
  disposition, offline-verification stance, or key/identity rotation/revocation
  path. Pin the expected identity/issuer and a rotation procedure (ADR-0006,
  cross-ref ADR-0014 T3).
