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
a write's view before its guards — ADR-0016 write-path freshness), the Stage-2
ergonomics verbs (`defer`/`undefer`, `dep path`/`dep critical` — the
dependency trees render on `why`/`unblocks`, not a separate `dep tree` verb),
and bulk `import` (Stage 3) have landed. Still open: `edit`.
Everything below remains stage-gated (decide when building that surface) or a
forever-contract surface that freezes on first implementation.

## Sync, discovery & local concurrency

- Discovery: bare repos, `.git`-file worktrees, `GIT_DIR`/`GIT_WORK_TREE` [low]
  — discovery for bare repos, `.git`-file worktrees, and
  `GIT_DIR`/`GIT_WORK_TREE` is undefined; delegate to `git rev-parse
  --show-toplevel`/`--git-dir` and state the bare-repo policy. (ADR-0012 handles
  linked worktrees/submodules — each its own boundary.)

## Build & proof infra

- Compiled-kernel-vs-spec property cross-check [low] — the mechanism now
  exists (`Tests/CrossTests.lean`: fixed-seed random op multisets; fold
  order/dup-insensitivity, join laws, ready soundness+sortedness,
  unblocks = ready-diff, rollup totality, all against the compiled
  functions); the residual is recording that shape — corpus, seeds, sampled
  theorems — in an ADR so the gate is contractual rather than incidental
  (ADR-0004 / a test ADR).

## Distribution (before release)

- Known defects in the release shell, pending the Lean port [high] — seven
  confirmed findings are deliberately unfixed in shell, because the files that
  contain them are being replaced and patching-then-deleting would be wasted
  work. They are inert today: no release is possible until the repository is
  public, the npm packages exist and the tap and `release` environment are
  configured. Recorded here rather than left to the tracker, so a reader of
  this branch can see what is known-broken.

  In the manifest generator: a failing target-list read is swallowed by a shell
  assignment prefix, so the generator writes a manifest with an empty target
  list and exits 0, skipping every build-metadata check; and the build run id
  is compared only between legs, never against the run actually executing, so a
  self-consistent artifact set from a different run would pass.

  In the prerequisite audit: an API failure collapses into an empty policy and
  is reported as a *missing* prerequisite, which aborts a legitimate release
  with a remedy telling the operator to fix something already correct; and the
  tag-ruleset check accepts any include pattern beginning `refs/tags/v`, so a
  ruleset covering one specific tag reads as restricting every `v*` tag. That
  second one has been a proxy for the property in three consecutive reviews —
  first a count of rulesets, then a prefix — which is the argument for stating
  it as a typed predicate rather than guarding it once more.

  In the npm channel: package-content comparison is blind to symlinks and file
  modes, so a published package whose launcher lost its executable bit compares
  equal to a staged one that has it; nothing establishes that the `latest`
  dist-tag is not the bootstrap placeholder, which matters because a
  prerelease-first launch publishes under `next` and leaves `latest` where the
  bootstrap put it; and a bracket-class typo makes the selftest row guarding
  that unfireable.

  The fixes land with the port; the tasks that absorb each are named in the
  tracker. Deleting this entry without them would leave the defects recorded
  nowhere, which is what happened to reproducible builds once already.
- Reproducible builds [medium] — the one ADR-0006 release-integrity item still
  open, and the only bullet under ADR-0014 T3 not built. The inputs are already
  pinned and recorded per release (`build-metadata-<target>.json`, the SBOM,
  `tl version --json`), so a rebuilder can confirm *which* toolchain and
  dependency set a binary was built from; what is missing is a build that comes
  out bit-identical, which is what would let a third party re-derive the
  artifact rather than take the workflow's word for it. Until then the honest
  claim is "built by that workflow from that commit", and `REBUILDING.md` says
  exactly that rather than letting the signature imply more. Deleting this entry
  without building it would leave the ADR promising something nothing tracks.
- Consume the release manifest, rather than only verifying it [low] — every
  job downstream of signing verifies `release-manifest.json` against the
  directory it received, which is what catches a missing, modified or
  undescribed asset. They then still derive their own working lists: the
  Homebrew generator reads `SHA256SUMS`, npm staging reads which files are
  present, the dist-tag comes from the tag. Those derivations agree because
  they run against a vouched-for directory, so this is tidiness rather than a
  defect — but the manifest already records `targets`, `npm.distTag` and
  `homebrew.pinnedTargets`, and reading them would make one description
  authoritative instead of merely authoritative-looking. ADR-0006 says exactly
  this rather than claiming the stronger property.
- Native-Windows gating test pass [low] — the gating test pass for native
  Windows is open, spec'd only if it is promoted from Deferred (WSL is the
  Supported Windows path). The Win32 FS/git-shell-out *design* is in ADR-0015
  §7 / ADR-0006; no native package is published while the shim returns `ENOSYS`.
