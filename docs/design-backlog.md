# Design backlog

Open design questions for `tl` — decisions not yet made, or made but not yet
pinned in an ADR. Each item leaves the backlog by landing in an ADR (new or
amended) or by graduating into an implementation task when its stage starts.
Decisions already made are recorded in their ADRs (and git history); this lists
only what is still open.

Status: Stages 0 and 1 are built (the verified kernel and the MVP work
loop). Stages 2–3 are **partly built**: the agent surface (skill, `help --json`,
discovery pointer), the free verbs (`reopen`/`stats`/`log`), rich human output,
`list` open-by-default + tree-by-default (`--flat` for rows), labels
(`label add/remove/list`,
`list --label`), the **full `refs/tl/log` sync transport**
(local leg, read-time refresh, remote fetch/union/push, and the HLC skew window
— proved convergence-safe), and **auto-sync** (ADR-0021: the best-effort
post-write local publish, plus the symmetric pre-transact absorb that refreshes
a write's view before its guards — ADR-0016 §3 amendment) have landed. Still
open: the Stage-2 ergonomics verbs (`defer`/`undefer`, `dep path`/`dep critical`
— the dependency trees render on `why`/`unblocks`, not a separate `dep tree`
verb — and `edit`), and bulk `import` (Stage 3).
Everything below remains stage-gated (decide when building that surface) or a
forever-contract surface that freezes on first implementation.

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

- `tl list` facet flags & text match [low] — open issues, `--limit`, the
  default forest (`--flat` for one-line rows), and `--label` are built and pinned
  (ADR-0020 / ADR-0017 §2). Still open: the *other* facet flag spellings
  (status / assignee / priority / text) and text-match semantics (substring vs
  word, case folding, which fields) (vision / ADR-0020).
- `--json` `data` shapes for the later `dep` utilities
  (`tree`/`path`/`critical`) [low] — the existing command shapes are pinned in
  ADR-0020; these `dep` utilities pin when built, following its conventions.

## Log format, versioning & compaction

- Destructive GC (physical op removal) is deferred and undesigned [low] — the
  non-destructive split is settled (ADR-0008, ADR-0022): the snapshot is the
  content-keyed fold cache, the ops stay, the log never shrinks, no `v` bump.
  Still open is *physical* removal — discarding ops below a causally-stable
  frontier — which needs a `snapshot` record + `v` bump, must answer the
  strictly-growing per-segment line-union so an un-compacted replica cannot
  re-add retired ops (ADR-0008 × ADR-0001 §5 × ADR-0015 §3), and carries the
  reserved *fold-preservation* theorem `fold ops = snapshot(F) ⊕ fold(ops above
  F)` for a causally-stable frontier (ADR-0004/0008).

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

## Import (bulk)

- Pin the bulk-import record schema [low] — finalize the import-format fields,
  each mapping to a tl field or an explicit, disclosed drop (ADR-0005).
- Differential-import fixtures, equality relation, and mapping matrix [low] —
  the differential-import test is mandated but these aren't pinned; commit
  import-format fixtures + an expected-state oracle under `Tests/fixtures/`, one row per mapping
  (ADR-0005 / overview).
- Import's deterministic per-op nonce derivation is informal [low] — the
  import-seed id and import replica-id are pinned to full precision (named SHA-256
  preimage, bit-slice, encoding), but the per-op nonce is only "derived from the
  source record + op role + target id" — no hash, preimage, or width — even though
  it is part of the OR-Set add-tag string and LWW triple that must be byte-identical
  for re-import idempotence (the differential-import oracle above). Pin it like its
  siblings (e.g. `crockford32(SHA-256("import-nonce:" ++ … ))[0..128]` → 26 chars) —
  ADR-0005.
- Priority on import [low] — the format's `priority` is 0–4 directly; an
  out-of-range value clamps with disclosure (ADR-0002/0005).
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
  paths (`docs/`, `Tests/.../fixtures/`, the importer's `ext:*` source refs) — AGENTS.md /
  a lint spec.

## Distribution (before release)

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
