# ADR-0026 — Continuous integration: platform, job graph, gates, and caches

- Status: Accepted
- Date: 2026-07-01

## Context

The coverage mandate (ADR-0004) and the gate list in the contributor guide
(AGENTS.md, "CI gates") had no mechanized enforcement point: nothing ran the
proofs, the test suite, or the lints on every change. ADR-0006 additionally
requires a job pinned to the git ≥ 2.17 runtime floor — the floor's *runtime*
check (doctor/init) shipped, but no job proved the suite actually passes at
exactly the floor version. This ADR pins the CI platform, the job graph, the
mechanism behind each gate, and the cache strategy.

## Decision

### Platform

GitHub Actions on hosted runners. This matches where ADR-0006 already points:
the release build matrix presumes GitHub-hosted targets, and the provenance
plan (Sigstore signatures over GitHub OIDC) requires its workflow identity.
Every third-party action is pinned to a full commit SHA, consistent with the
ADR-0014 stance of pinning external inputs to immutable revisions.

### Job graph: `lint` → `build-and-test` (ubuntu, macos) → `git-floor`

The workflow lives at `.github/workflows/ci.yml`.

**`lint`** — source-level greps that run in seconds, before any toolchain
install, so a violation fails early:

- *Hard gate — Mathlib import scope.* Direct `import Mathlib` is allowed only
  in the ADR-0009 allowlist (`Tl/Kernel/Path.lean`, `Tl/Kernel/Reach.lean`,
  `Tl/Kernel/ReachBFS.lean`). Widening the scope means amending ADR-0009
  first.
- *Hard gate — no `sorry`/`admit` in the verified cone.* This duplicates the
  build gate (`sorry` emits a warning, so `--wfail` is the authority); the
  grep exists to fail the same defect before the build starts.
- *Hard gate — no `axiom`, `native_decide`, or `ofReduceBool` in the verified
  cone.* These compile **without warnings**, so the build gate cannot catch
  them; until a checked-in `#print axioms` probe closes the remaining
  false-negative holes (e.g. exotic same-line forms), this grep is the only
  CI net for the fixed trust boundary. Once the probe lands, the grep can
  demote to an advisory fast-fail.
- *Advisory — task-tracker-id leakage.* Warns on full display-form ids in
  tracked sources (excluding the two files that legitimately embed example
  ids). It stays advisory until the pattern and exclusion set are pinned by
  their own recorded decision — the realistic leakage vector is *truncated*
  ids in commit messages, which this pattern deliberately does not attempt
  yet.

**`build-and-test`** — a matrix over `ubuntu-latest` and `macos-latest`, the
two development platforms:

- `lake build --wfail` is the warning-free-build gate: it exits nonzero on
  any warning, **including warnings replayed from the build cache**
  (verified empirically on the pinned toolchain). A log-grep was considered
  and rejected — the assumed `./`-prefixed diagnostic format does not match
  real output, so a grep gate would silently pass everything.
- `lake exe tltest` then runs the full outside-TCB suite from the repo root
  (the harness expects the `tl` binary at `.lake/build/bin/tl` and the repo
  sources/fixtures at the working directory). The suite needs no network, no
  git identity, and no ambient environment variables.
- Both are driven through `leanprover/lean-action` (SHA-pinned), which
  installs elan and runs `lake exe cache get` before building. Two of its
  features are deliberately disabled: its bundled `.lake` GitHub cache (see
  Caches) and its `lake test` step (the package declares no Lake
  test_driver; the suite runs as an explicit step instead).
- The ubuntu leg uploads the built `tl` and `tltest` binaries as a
  short-lived artifact for the floor job.

**`git-floor`** — proves the suite passes at exactly the ADR-0006 floor:

- git 2.17.1 is built from a source tarball pinned by SHA-256
  (`79136e7aa83abae4d8a25c8111f113d3c5a63aeb5fd93cc72c26d49c6d5ba65e`, which
  matches the upstream-signed `sha256sums.asc`). kernel.org no longer serves
  historical release tarballs, so two independent mirrors are tried in
  order; the pinned hash keeps the download trustworthy regardless of which
  mirror answers.
- The build is minimal (`NO_CURL`, `NO_OPENSSL`, `NO_EXPAT`, `NO_GETTEXT`,
  `NO_PERL`, `NO_PYTHON`, `NO_TCLTK`) — the transport tl exercises is local
  plumbing only — and the installed prefix is cached across runs.
- The `PATH` override onto the floor git is scoped to the test steps only;
  checkout and the action steps keep the runner's modern git. Each test step
  first asserts `git --version` is exactly the floor version.
- The job runs the full suite against the uploaded artifact binaries (no
  toolchain install), then a floor smoke: `tl init` in a scratch repo must
  emit no below-floor note, and `tl doctor --json` must report the
  `gitVersion` check row with `status == "ok"` and `version == "2.17"`. The
  assertion targets the row itself because that row can only ever warn — it
  never flips doctor's `healthy` flag or exit code.

### Caches

Four caches, each keyed by exactly what invalidates it:

| path | key | note |
| --- | --- | --- |
| `~/.elan` | OS + arch + `lean-toolchain` hash | toolchain download |
| `~/.cache/mathlib` | `lake-manifest.json` + `lean-toolchain` hash | deliberately OS-agnostic — the `.ltar` archives are platform-independent, so one entry serves both runners |
| `.lake/packages` minus each package's `.lake` | `lake-manifest.json` hash | dependency *sources* only |
| `.lake/build` | OS + arch + manifest/toolchain hash + commit, with a restore-key falling back to the newest prior commit | tl's own incremental build |

Two prohibitions:

- **Never cache the unpacked dependency oleans** (`.lake/packages/*/.lake`).
  A cache entry that includes them is multi-gigabyte, re-uploaded per
  commit, and evicts everything else in the repository's shared cache
  budget — while `lake exe cache get` restores the identical content from
  the `~/.cache/mathlib` archives in seconds.
- **Never let any cache path include `.tl/local/`.** Restoring a byte-copied
  replica directory into a fresh environment is exactly the sub-git copy
  that the replica-id-uniqueness carried assumption excludes
  (docs/overview.md, Trusted).

The mathlib cache is a *full* hit only while every dependency rev in
`lake-manifest.json` byte-matches mathlib's own manifest at the pinned
mathlib rev; keeping that alignment on any pin bump is part of the ADR-0009
bump procedure.

### Operational points

- Concurrency: superseded runs are cancelled on PRs and feature refs, never
  on `main` — main runs populate the shared caches that PR runs restore.
- Branch protection requires all four checks: `lint`,
  `build-and-test (ubuntu-latest)`, `build-and-test (macos-latest)`,
  `git-floor`. No merge queue — a single-contributor repository does not
  need one.
- Warm-cache runs are dominated by the Lean build and the suite; the lint
  job keeps trivially-detectable defects from paying that cost.

## Consequences

- A green run now enforces, on every push to `main` and every PR: proofs
  compile warning-free on both platforms, the full suite passes on both
  platforms *and* at the git floor, the Mathlib scope is confined, and the
  trust boundary carries no new axiom or kernel bypass.
- The performance regression net (`Tests/PerfTests.lean`) genuinely runs in
  CI, as docs/overview.md already stated. Its assertions are growth ratios
  rather than absolute times, so runner noise is tolerated by design; a
  pathologically noisy runner can still flake a run, which re-running
  resolves.
- The axiom/native_decide grep carries known false-negative holes; the
  durable closure is a checked-in `#print axioms` probe, which is its own
  planned change.
- The floor job's git build recipe is exercised only in CI (macOS
  development machines cannot rehearse an Ubuntu gcc build); a recipe
  breakage therefore surfaces as a loud `git-floor` failure, never as a
  silently skipped gate.

## Alternatives considered

- **ubuntu:18.04 container for the floor job** — rejected: current
  node-based actions require glibc ≥ 2.28 (18.04 ships 2.27 and the node16
  fallback is sunset), its apt archive is end-of-life, and it would force a
  second toolchain install. Building the floor git on a supported runner
  keeps the job on maintained infrastructure.
- **Grep the build log for warnings instead of `--wfail`** — rejected as
  disproven: the assumed diagnostic format does not occur in real output,
  so the gate would pass vacuously.
- **lean-action's built-in `.lake` cache** — rejected: it keys the entire
  `.lake` tree per commit, which re-ships the unpacked mathlib oleans on
  every save (the first prohibition above).
- **Hand-rolling elan install and mathlib cache retrieval** — rejected:
  the SHA-pinned action performs both with maintained scripts; the pieces
  that did not fit (its cache, `lake test`) are disabled rather than
  re-implemented.
