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

- Release-shell defect migration record [high] — seven confirmed findings were
  recorded here so deleting their original scripts could not make the defects
  disappear from the architecture record.

  **The four GitHub-only blockers are retired.** The Lean ports replaced the
  affected scripts and close each defect at the decision layer:

  - `Targets.parse` plus manifest assembly refuse an unreadable or empty target
    set, replacing the generator path that swallowed a failed target-list read;
  - `RunContext` / `runContextOf` bind build records to the workflow run that is
    executing, rather than merely checking that the records agree with each
    other;
  - the prerequisite GitHub client keeps a 404 answer distinct from a response
    it could not read, so an operational API failure cannot become a false
    "missing prerequisite" verdict; and
  - `restrictsTagCreation` requires a ruleset to cover the whole release-tag
    namespace, not merely one pattern beginning with `refs/tags/v`.

  Their pure decisions and public-command refusal rows remain part of the
  release tests. The deleted shell generator and prerequisite checker are no
  longer first-release blockers; ADR-0028 requires these replacement checks to
  survive the remaining cutover.

  Two additional generator selftest defects were found by running it the way CI
  does rather than the way a developer does, and were **fixed in shell before
  the port**, because the rule against patching code that is about to be deleted
  is outranked by not leaving the branch unable to pass its own gates. Its
  fixture hardcoded a `workflowRef`, and the generator compared that field
  against `GITHUB_WORKFLOW_REF` whenever the variable is non-empty — which
  inside Actions it always is. So the selftest passed on every developer
  machine and failed in CI, and since both workflows run it through the release
  policy, the first push would have failed the gates job for a reason nothing
  local could show. Before deletion, the selftest was corrected to scrub the
  variable rather than adopt it: a fixture that copied the ambient value would
  compare a thing with itself, which is the check not running. The Lean port
  instead exercises the comparison with an injected run identity.

  The second is why that failure was hard to read: one invocation was not
  wrapped in the harness, so under `set -eu` a failure aborted the whole
  selftest with its diagnostic sent to `/dev/null` — no failing row, no count,
  no remedy line. A selftest that cannot report its own failure is the same
  defect class as a gate that cannot fail, one level up. That invocation was
  moved through the harness before the generator was retired.

  **Three npm findings remain as port obligations, but are no longer live
  defects in the current shell.** The publisher's normalized snapshot includes
  executable mode and refuses symbolic links it cannot compare to npm's served
  tree; an already-published version must resolve from the intended dist-tag;
  and the bootstrap latest-guard uses the corrected line-oriented pattern plus
  a planted command that proves the row can fire. Each has a discrete public
  selftest row.

  Retain these three findings until the npm port carries the same properties
  and replacement tests into `tlrelease`; deleting the record merely because
  the shell files disappear is what happened to reproducible builds once
  already.
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
