# ADR-0006 — Distribution and supported platforms

- Status: Accepted
- Date: 2026-05-31

## Context

`tl` ships the Lean-compiled binary itself — kernel and I/O shell
compiled together (ADR-0004). Reimplementing the shipping binary in another
language for easier distribution would forfeit verification: the artifact
users run would no longer be the artifact proved. So distribution is
constrained by Lean's own toolchain, not ours.

Two facts shape everything:

1. Lean does not cross-compile cheaply. Unlike languages that produce a
   static, dependency-free binary for every OS from one host (Go being the
   canonical example), Lean cross-compiles poorly and its binaries link the
   Lean runtime + GMP. We must build natively per target in a CI matrix
   rather than cross-compiling from one machine.
2. Distribution channels are veneers over prebuilt binaries. npm, brew,
   and `curl|sh` do not solve the build problem — they only deliver a binary
   we have already produced per platform. The cost is the build; the
   channels are nearly free once binaries exist.

Lean's [supported-platform tiers](https://lean-lang.org/doc/reference/latest/platforms/):
Tier 1 (built + tested upstream, via elan) — Linux x86-64 (glibc 2.26+),
Linux aarch64 (glibc 2.27+), macOS aarch64, Windows. Tier 2 (cross-compiled,
untested) — macOS x86-64, WASM. FreeBSD is not a Lean tier; it exists only
as the downstream `math/lean4` port (build-from-source).

## Decision

### Support tiers (ours, mapped to Lean's)

- Supported — release-blocking, built *and fully tested* in our CI:
  - Linux x86-64, Linux aarch64, macOS aarch64 (Lean Tier 1).
  - Windows via WSL2 is Supported — it runs the Linux x86-64 binary, so it is
    fully covered at no extra cost, and is the recommended Windows path.
- Best-effort — built and smoke-tested, not release-blocking, no
  platform-specific debugging or perf work:
  - macOS x86-64 (Lean Tier 2). Our CI smoke-testing it partially
    compensates for the lack of upstream testing. A failure here does not
    block a release of the Supported binaries. No universal (`lipo`)
    binary — a separate artifact suffices.
- Deferred — designed but neither functional nor distributed:
  - Native (non-WSL) Windows x86-64. Lean supports the target, but tl's native
    filesystem shim deliberately returns `ENOSYS` on Win32 (ADR-0019), so a
    binary that starts but cannot safely create or mutate task state is not a
    release artifact. WSL2 is the Supported Windows path. Native Windows moves
    to Best-effort only after the Win32 primitives and their smoke-test pass
    exist; until then npm refuses `win32` rather than installing a broken CLI.
- Community — not in our CI:
  - FreeBSD, via the `math/lean4` Ports path (build-from-source,
    version tracking the port, CI only via a FreeBSD VM action or Cirrus if
    a maintainer wants it). Idiomatically distributed as a FreeBSD
    port/pkg that build-deps on `math/lean4`, not as a prebuilt binary.

### Build approach

- Native per-target CI matrix (Lean cross-compile is weak): GitHub hosted
  runners cover the four distributed targets (`ubuntu-*`,
  `ubuntu-*-arm`, Apple-Silicon macOS, and Intel macOS).
- Linux: build on an old-glibc base (manylinux-style container or an
  old Ubuntu) to honor Lean's glibc 2.26/2.27 floors, so the binaries run
  on any distro at or above that floor.
- GMP is statically linked, mirroring Lean. The Lean
  toolchain ships GMP as a static archive (`lib/libgmp.a`) and links it into
  `libleanshared`/the binary on every platform — verified on the shipped
  `arm64-apple-darwin` toolchain: `libgmp.a` is present, there is no
  `libgmp.dylib`, and `otool -L libleanshared.dylib` shows no GMP dependency.
  Since `tl` is compiled by that toolchain, its binary inherits static GMP
  automatically; we do not fight it. (*Full static* is impossible only for
  libc/libSystem on macOS, and finicky on glibc — old-glibc + dynamic
  libc stays the portable baseline for the C library. GMP being static is
  independent of, and unaffected by, that libc choice.)

### Channels

The four below are the channel *designs*. Which of them a given release
actually publishes is a separate, machine-readable answer in
`release/plan.json`, and that file is the only place it is written.

Before that file existed, "designed" and "published" had no distinguishing
mark, and the difference was not cosmetic: the prerequisite audit demanded five
npm packages and a Homebrew tap before anything could be signed, the release
policy ran their gates, and the workflow held jobs for them. A first release
through the GitHub channel alone was therefore blocked by external state that
nothing about it needed. A channel that is off is *absent* from the applicable
prerequisites, from the enabled jobs, and from the strict release policy —
never reported as missing or unchecked. "Missing" is a defect report, and a
channel nobody is publishing has no defect.

### v0.1.0 channel scope

**Enabled**: GitHub Releases and the `curl | sh` installer, with
`scripts/verify-release-artifacts.sh` as the standalone verification path for
the same assets. A v0.1.0 release publishes the signed binaries, `SHA256SUMS`,
a Sigstore bundle per asset, `release-manifest.json`, the SBOM, the compliance
set, and per-target build metadata and link audits.

**Deferred to v0.2.0**: npm and Homebrew. Neither is missing work in this
repository — both channels are implemented — and both are blocked on a manual
bootstrap that is unrelated to publishing a GitHub Release:

- npm's trusted publishing is configured per package, and npm only offers it
  for a package that already exists. The first release cannot authenticate, so
  enabling npm means publishing an immutable placeholder version of all five
  packages by hand and then registering the publisher. That is a decision about
  the npm namespace, not about whether the binaries are ready.
- Homebrew needs the tap repository to exist and a credential that can write to
  it. `Formula/tl.rb` stays here as the source of truth and stays inside the
  identity drift guard, so enabling the channel later is a tap plus a secret
  rather than new code.

Deferring them is what makes the first release reachable at all. It is recorded
here rather than left implicit because three separate mechanisms were treating
their absence as a fault.

### Dependency budget for the enabled channels

No path reachable from the GitHub-release workflow, `install.sh`,
`scripts/verify-release-artifacts.sh`, or the strict release policy may invoke
`python`, `python3`, `ruby`, `brew`, `node`, or `npm`. Lean owns JSON parsing,
typed decisions, manifest and metadata generation, prerequisite classification,
SBOM generation and identity-pin generation, through the separately built
`tlrelease` executable; POSIX shell remains thin orchestration and the user
bootstrap boundary.

This is a statement about *this project's* dependencies, not a ban on
channel-native runtimes. A Homebrew formula is necessarily a Ruby DSL and is
validated with real `brew` using Homebrew-managed Ruby; npm operations
necessarily use `node`/`npm`. Those runtimes belong to the channel that owns
them and become reachable only when that channel is enabled — the formula
rendering and the publish planning stay in Lean either way. What the budget
forbids is a *user* of the enabled channels needing an interpreter this project
chose for its own convenience, which is what a Python one-liner in the artifact
verifier was.

The boundary is enforced twice rather than documented: an inventory of the
enabled entry points rejects a forbidden invocation in the first-party scripts
they reach, and the policy, selftests and rehearsal run with failing
PATH-precedence shims for all six commands, having first proved each shim can
fire.

- GitHub Releases — the source of truth. CI uploads the prebuilt
  binaries here; everything else wraps them.
- `curl | sh` installer — universal baseline, no ecosystem dependency,
  platform-detecting; runs unmodified in WSL — the recommended Windows path
  (WSL is our Linux x86-64 target).
- npm — the priority veneer; the audience is agent/Node tooling and
  `npm i -g` is how such tools get adopted. Use
  the `optionalDependencies` pattern: the public `@taskloop/tl` package holds
  a POSIX `#!/bin/sh` launcher, and exact-version
  `@taskloop/tl-bin-darwin-arm64`, `@taskloop/tl-bin-darwin-x64`,
  `@taskloop/tl-bin-linux-arm64`, and `@taskloop/tl-bin-linux-x64` packages
  hold the same binaries as GitHub Releases. The `-bin-` infix is not
  decoration: it says the package carries a prebuilt binary rather than a
  library, and it keeps the names clear of the task-ID lint, whose Crockford
  class reads `tl-darwin` as a possible tracker id
  ([ADR-0026](ADR-0026-continuous-integration.md) records that limitation, and
  registering real package names in its exclusion set would erode what
  registering a token asserts).
  The launcher detects the installed target and `exec`s it, preserving signals
  and exit status; it uses no JavaScript process and no lifecycle hook. In
  particular, no `postinstall` download reaches an arbitrary URL. Native
  Windows npm installation is refused; npm under WSL selects Linux normally.
- Homebrew tap — `DmitryKorolev/homebrew-tap`; a formula that downloads the
  Release artifact per platform (not build-from-source, which would require
  users to have Lean). The formula's source of truth is `Formula/tl.rb` in this
  repository, beside `release/identity.json`, so the release-identity drift
  guard covers it; the release workflow fills in the version and the four
  digests from the *verified* `SHA256SUMS` and pushes the result to the tap.
  Two independent fail-closed checks and no bypass: Homebrew's own `sha256` on
  each url, and a cosign verification against the pinned identity in `install`,
  with `cosign` a hard dependency rather than an optional one. Homebrew has no
  equivalent of the installer's signature-only escape — on a machine that
  cannot run cosign, `brew` would simply install it first. A Best-effort target
  that did not build has its block dropped from the generated formula rather
  than pinning a digest that does not exist, so `brew` offers nothing on that
  platform for that release instead of the release failing.
- Prereleases reach each channel differently, and deliberately. GitHub marks
  them prerelease, so `install.sh`'s `/releases/latest` resolution skips them
  and a user must name one with `TL_VERSION`. npm publishes them under the
  `next` dist-tag, so `npm install @taskloop/tl` still resolves to the last
  stable version. Homebrew is not updated at all: a tap carries one formula,
  and overwriting it would make `brew install tl` resolve to a prerelease. The
  generated formula is still produced and attached to the run.
- Skip `go install` / `cargo` (wrong ecosystems). FreeBSD via Ports.

### Runtime prerequisites and signing

- `git` must be installed on the user's machine — `tl` shells out to it
  for transport (ADR-0001). Documented, not bundled.
- macOS Gatekeeper: an unsigned download is quarantined. Ad-hoc
  `codesign -s -` plus a documented `xattr -d com.apple.quarantine`
  workaround initially; full notarization (paid Apple account) deferred
  until justified.

### Tool versioning

The product version is SemVer (`tl version`, initially `0.1.0`) and is
distinct from the on-disk log `v` and the `--json` `schemaVersion` (ADR-0008).
A product minor/patch release may leave both schemas unchanged; a log or JSON
breaking change bumps its own schema even if the product version also changes.
`tl version --json` reports all three numbers plus the build provenance of the
running binary, as the additive `build` object ADR-0020 left room for:

```json
{ "version": "0.1.0", "logFormat": 2,
  "build": { "kind": "clean", "commit": "<40-hex>", "dirty": false,
             "toolchain": "leanprover/lean4:v4.32.2", "manifestDigest": "<sha256 hex>" } }
```

`commit` is `null` — not `""` — when no commit was stamped, so an agent reads
an absence rather than a value. `manifestDigest` is the SHA-256 of
`lake-manifest.json`, which fixes every dependency revision at once because the
ADR-0009 pins are immutable commits. Human output carries the same facts.

`kind` answers *which source does this binary correspond to*, and deliberately
stops there:

- `development` — no commit was stamped; a local `lake build`. A development
  build reports `dirty: false` whatever the tree looked like, because there is
  no commit for the tree to be dirty relative to.
- `dirty` — a commit was stamped over a tree with uncommitted changes, so the
  commit does not describe the binary.
- `clean` — stamped from a clean checkout; the binary corresponds to that commit.

There is deliberately no `release` kind. A binary cannot attest that it is an
official release — anyone can stamp a commit and build — so that claim is
carried by the Sigstore certificate identity pinned in `release/identity.json`
and verified per `VERIFYING.md`, never by the binary's own self-report.

The provenance is compiled in from the generated `Tl/Build/Stamp.lean`, whose
checked-in copy is the development stamp; `scripts/gen-build-provenance.sh
--stamp` rewrites it from git HEAD, which the release workflow runs on a clean
checkout of the tag before building and then smoke-tests against the compiled
binary. CI regenerates the file and diffs it, so a stamped copy cannot reach
`main` and be mistaken for the development stamp everything else assumes.

The generator's output is a pure function of `lean-toolchain`,
`lake-manifest.json`, and the git state, so an independent rebuilder gets the
same *stamp* from the same commit. That is a claim about the stamp only.
Whether the compiled binary comes out bit-identical rests on the Lean and
system toolchains, which the generator does not touch and nothing here checks —
reproducible builds remain the open item recorded below, and a stamp match is
not evidence of binary-to-source correspondence.

The generator fails closed throughout, because a stamp reading `clean` is taken
as an exact-correspondence claim: it refuses when `git status` cannot run
rather than reading the silence as a clean tree, counts untracked files even
when the repository's `status.showUntrackedFiles` config hides them, excludes
only its own output from that probe (so a second `--stamp` in one checkout does
not report the first run's stamp as a modification), and refuses to stamp a
source tree that merely sits inside an unrelated checkout, whose commit does
not contain that source at all. `--selftest` exercises each refusal in
throwaway directories and runs in CI, so a generator that quietly stopped
refusing cannot pass unnoticed.

### Runtime prerequisite: git ≥ 2.17

`git` is a runtime prerequisite — `tl` shells out to git plumbing for the
`refs/tl/log` transport and discovery. The floor is **git 2.17**, with a
`doctor`/`init` check that parses `git --version` (the stable `git version
X.Y.Z` line) and emits a teaching warning below it rather than letting an older
git fail cryptically.

The floor reflects the support matrix rather than a plumbing need. The only feature `tl`
uses above the ~1.8 era is `git rev-parse --git-common-dir` (2.5, for
linked-worktree detection); `-C` (1.8.5), `config`, `ls-tree`, `cat-file`,
`hash-object --stdin`, `mktree`, `commit-tree`, the positional `update-ref`
compare-and-set, `fetch`, `push --porcelain`, and `symbolic-ref` are all older,
and there is no `git worktree` shell-out. 2.17 sits above that 2.5 feature floor
with margin and matches the oldest Supported-tier glibc baseline (glibc 2.27,
Ubuntu 18.04, which ships git 2.17); a higher round number such as 2.20 would
drop 18.04 despite its in-tier glibc. CI pins and tests the floor version so a
future plumbing dependency above it cannot slip in unnoticed (decided
2026-06-21).

The runtime check shipped 2026-06-21: `Tl.Sync.parseGitVersion` /
`gitMeetsFloor` / `gitVersion` (a bounded `git --version`), surfaced as a
`doctor` `gitVersion` check row (`ok` at/above the floor, a teaching `warn`
below it or when git is unreadable — a warn, never a doctor failure) and an
`init` below-floor note. The CI leg is the `git-floor` job
([ADR-0026](ADR-0026-continuous-integration.md)): it builds git 2.17.1 from a
hash-pinned tarball, runs the full test suite under it, and smoke-asserts that
`doctor` reports the floor git's `gitVersion` row as `ok` — so a future
plumbing dependency above the floor cannot slip in unnoticed.

### Release integrity and provenance

Binary distribution is gated on a verifiable release pipeline:

- The permanent release repository is `DmitryKorolev/tl`; the public npm
  package is `@taskloop/tl`. `release/identity.json` is the machine-readable
  current pin, and `VERIFYING.md` is the user procedure and identity-history
  table.
- Keyless signing runs directly in `.github/workflows/release.yml`, triggered
  by a SemVer tag. It is not delegated to a reusable workflow: GitHub OIDC
  records the workflow ref, so indirection would change the certificate
  identity being pinned. The exact issuer and anchored cosign expression are:

  ```text
  https://token.actions.githubusercontent.com
  ^https://github\.com/DmitryKorolev/tl/\.github/workflows/release\.yml@refs/tags/v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?$
  ```

  The expression permits SemVer release and pre-release tags, but is anchored
  to this repository and workflow. A valid certificate from any other GitHub
  repository, workflow path, branch, or non-SemVer tag fails verification.
- Each asset has a Sigstore bundle containing its signature, Fulcio
  certificate, and Rekor inclusion proof. Verification requires the proof in
  the bundle; it never repairs a missing proof by trusting an unbound live-log
  lookup. The installer's sole escape is
  `TL_INSTALL_SKIP_SIGNATURE=1`, which skips Sigstore only — the selected
  SHA-256 digest remains mandatory. Homebrew has no signature-skip mode.
- A repository owner/name or release-workflow-path change is an identity
  rotation, not an editorial rename. Before the new identity signs anything,
  a protected change updates `release/identity.json`, `VERIFYING.md`, this ADR,
  the installer, and the Homebrew formula together. The history table retains
  the old identity for old releases; artifacts are never re-signed to rewrite
  history. A compromise records and withdraws the affected release interval
  before rotating. `Tests/ReleaseTests.lean` compares every operative copy as
  text — `release/identity.json`, VERIFYING.md, this ADR, ADR-0014,
  `install.sh` and `Formula/tl.rb` — and
  `scripts/check-release-identity.sh` checks what the expression *means*
  against adversarial candidates, which a text-equality guard cannot.

  One limitation, stated rather than implied: every shipped verifier reads the
  *current* pin only. The history table in VERIFYING.md is how a reader
  verifies an artifact signed under a superseded identity — by hand, with that
  row's issuer and expression — because `install.sh`, `Formula/tl.rb` and
  `scripts/verify-release-artifacts.sh` each carry exactly one. Rotating
  therefore makes older artifacts unverifiable *by the shipped tooling*, not
  unverifiable as such; a rotation that needed the tooling to accept both
  would have to add that deliberately.

- Every GitHub Release publishes per-asset SHA-256 digests, a signed
  `SHA256SUMS`, and per-asset signatures. The `curl | sh` installer and
  Homebrew formula verify these and fail closed by default.
- Release artifacts carry a Sigstore/cosign signature and SLSA provenance
  attestation from GitHub OIDC, binding the artifact to the source commit,
  workflow, pinned Lean toolchain, and checked-in `lake-manifest.json`.
- npm uses trusted publishing / OIDC, 2FA, `npm --provenance`, no long-lived
  publish tokens, and the registered `@taskloop` organization scope. The
  launcher pins each platform package by exact version, and npm verifies the
  registry-supplied tarball integrity. The package has no lifecycle script and
  never downloads arbitrary URLs during installation.
- Reproducible builds are the **open** item, and this bullet is the goal rather
  than a description of what ships. Present tense here contradicted the honest
  answer three other documents already gave, so it is written as the target it
  is: pinned Lean + lake dependencies, deterministic timestamps/paths, and a
  documented independent rebuilder that can verify binary-to-source
  correspondence. Reproducibility would prove "this binary came from this
  source"; the Lean proofs prove the source-level correctness claims either way.

  What exists today is the first half. Every release records the inputs —
  `build-metadata-<target>.json`, the SBOM, `tl version --json` — so a
  rebuilder can confirm *which* toolchain and dependency set produced a binary.
  What does not exist is a rebuild that comes out bit-identical, so nobody
  outside this workflow can re-derive the artifact. `REBUILDING.md`, shipped
  with each release, states that boundary to users; the remaining work is
  tracked in docs/design-backlog.md.
- Every binary release includes an SBOM and the full link-time dependency audit
  required by the licensing section below. **Built**: `scripts/gen-sbom.sh`
  emits SPDX 2.3 derived from `lean-toolchain` and `lake-manifest.json` (no
  generation timestamp, so two runs for one release agree byte for byte), and
  each build leg writes `link-audit-<target>.txt` from `ldd`/`otool -L` plus a
  symbol scan of the actual candidate — the one drift the license generator
  cannot see, since a newly bundled library appears in the binary without
  appearing in any manifest.

  These, `LICENSE`, `THIRD-PARTY-LICENSES` and `REBUILDING.md` ship as
  *companion assets* rather than by wrapping each binary in a per-platform
  archive. The archive would buy one artifact identity across channels at the
  cost of changing every asset name and every consumer of them; the companion
  set keeps the download a single unpacked file, and the identity comes instead
  from `release-manifest.json` — the canonical description of the release,
  listed in `SHA256SUMS` and signed with everything else, and verified by each
  downstream job before it does anything with the directory. Being precise
  about what that buys today: the manifest is the single *authoritative*
  description and the point at which a mismatched, missing or undescribed asset
  is caught, and generating it is where each binary is checked against the
  digest its own build leg recorded. The jobs downstream of it still derive
  their own working lists — the Homebrew generator from `SHA256SUMS`, the npm
  staging from the files present, the dist-tag from the tag — rather than
  reading the manifest's `targets` and `npm` blocks. Those derivations now all
  run against a directory the manifest has vouched for, which is what removes
  the disagreement; consuming the manifest's own decisions directly is the
  remaining step, tracked in docs/design-backlog.md.
  The installer places the notice beside the binary and the formula installs it
  to `doc`; both skip it with a message on a release that publishes none, since
  refusing a good binary over a missing sidecar is the wrong trade.
- Each build leg records what it built — `build-metadata-<target>.json`: the
  candidate's digest, the source commit, the runner and container image, the
  toolchain and the manifest digest — and the signing job refuses a binary that
  does not match its own leg's record. That is the build→sign boundary, which
  otherwise had no re-verification: the signing job downloads from the artifact
  store and would sign whatever arrived. Provenance evidence travels this way
  rather than by attesting per leg, because attesting per leg means granting
  `id-token: write` to four more jobs, and every job defined inline in the
  release workflow shares one `job_workflow_ref` — each could then mint a
  certificate every verifier accepts.
- The external state this pipeline rests on is neither created nor implied by
  declaring it in the workflow, and *which* state applies is derived from
  `release/plan.json` rather than fixed. For the channels v0.1.0 enables that
  is: the repository being public, the `release` environment and its protection
  rules, the `v*` tag ruleset, and the signing identity. npm's per-package
  trusted publishers and the tap credential belong to their channels and
  produce no rows at all while those channels are off — a disabled channel is
  neither missing nor unchecked, because there is nothing it is supposed to
  have. `docs/release-prerequisites.md` is the procedure, the audit runs before
  anything is signed, and what it cannot read is carried in docs/overview.md.
  An operational failure to *reach* the API is reported as exactly that and
  never as an absent prerequisite: the two demand opposite responses, and
  conflating them aborts a legitimate release with a remedy telling the
  operator to fix something already correct.

## Consequences

- The marginal cost of each channel is small; the cost is the per-target
  build. Releases + curl already cover Linux and macOS, with WSL2 as the
  Supported Windows path, which is why v0.1.0 ships those two and defers the
  rest: npm and brew add reach, not coverage, and each carries a manual
  bootstrap that has nothing to do with whether the binaries are ready.
- Native Windows is a toolchain problem the project has not paid for, not an
  app-level one. Lean itself is Tier 1 there, but `ffi/tlsys.c` returns
  `ENOSYS` for every Win32 primitive, so the residual lift is the ADR-0015 §7
  primitives plus a smoke-test pass — not path handling, and not free via npm,
  which refuses `win32` outright. (The `.gitattributes` log-integrity
  requirement is obviated under ADR-0001 — the log lives in `refs/tl/log`, not
  EOL-normalizable working-tree files.)
- macOS x86-64 stays cheap and bounded by the best-effort policy.
- Licensing boundary. The runtime links GMP under LGPLv3; this
  is a stated, bounded exception to the project's no-copyleft rule. Binary
  distribution mirrors Lean (static GMP + a bundled LGPLv3 notice +
  open-source relink) — a packaging checklist, detailed below.
- Supply-chain trust is explicit. Users trust the Lean compiler/checker,
  GitHub release infrastructure, the signing identity, and the pinned build
  workflow; signatures make that trust auditable rather than implicit today,
  and reproducibility would extend the audit below the signature to the bytes
  themselves once it exists (ADR-0014).

## Licensing boundary (GMP / LGPL)

This intersects the project's no-copyleft discipline directly, so it is
stated explicitly here before we rely on it. (Engineering reading, not legal
advice; confirm with counsel before any commercial/closed distribution.)

### Why GMP is present and unavoidable

Lean's runtime uses GMP for arbitrary-precision `Nat`/`Int` (small ints
are unboxed; large ones spill to GMP bignums). It is linked into
`libleanshared`, so *every* Lean-compiled binary pulls it in. We do not vendor
it — Lean does: its binary releases bundle `libgmp.a` and a single `LICENSES`
notices file (headed *"the binary releases of Lean bundle libraries and files
under the following licenses"*) carrying the full LGPLv3 text + GMP notice
(alongside LLVM/Apache, glibc/LGPL, CaDiCaL/MIT). GMP cannot be reimplemented away
without forking the Lean runtime (verification-affecting, out of scope). The
boundary is therefore *managed*, not eliminable — and `tl`'s job is to
propagate Lean's existing handling, not invent its own.

### We elect LGPLv3, and that election matters

Modern GMP (≥ 6.0) is dual-licensed: LGPLv3+ *or* GPLv2+ — the user of
the library chooses. `tl` elects LGPLv3. Choosing the GPLv2 option would
make the combined work GPL and infect `tl`'s own code; LGPLv3 does not:

> LGPL is not viral across the linking boundary. `tl`'s own source stays
> under its own permissive license (Apache-2.0, matching Lean); only GMP
> itself remains LGPL. This is the whole difference from GPL, and it is why
> linking GMP does not entangle `tl`'s license the way vendoring GPL
> code would.

### What LGPLv3 obligates on distribution

1. Notice & attribution — convey that GMP is used; include the LGPL text
   and GMP's copyright notice.
2. Library source — provide or point to GMP's source (plus any
   modifications). We use unmodified toolchain GMP → a pointer to upstream
   suffices.
3. Relinking provision (LGPLv3 §4) — the user must be able to swap GMP
   for their own build and relink. Satisfied either by *dynamic linking* (a
   replaceable shared library) or, for *static linking*, by providing the
   application in relinkable form — object files or source.

### Binary distribution strategy: mirror Lean

Adopt Lean's own posture verbatim —

- Static GMP (inherited from the toolchain, above);
- Bundled notice: ship a third-party `LICENSES`/`THIRD-PARTY-LICENSES` notice
  — propagating Lean's GMP/LGPLv3 entry plus `tl`'s own deps — in every
  artifact;
- §4 relink via open source: because `tl` stays Apache open-source and
  buildable from a pinned toolchain and manifest (release-integrity section —
  buildable, which §4 requires; not yet *reproducible*, which it does not), the
  LGPLv3 §4 "swap GMP and relink" obligation is met the same way Lean meets it — the full source + pinned
  build system + the GMP upstream pointer are public, so any recipient can rebuild
  and relink. No separate object-file drop is required while `tl` is open.

The residual was a packaging checklist — confirm the notices file actually
travels into every channel a release publishes, and that the rebuild/relink
path is documented — and it is discharged **per channel**, which is the only
form the obligation takes: compliance attaches to distribution, so a channel
that distributes nothing owes nothing.

For the channels v0.1.0 enables, it is discharged now. The notice is a signed
companion asset of the GitHub Release and `install.sh` places it beside the
binary, and `REBUILDING.md` ships with every release documenting both the
rebuild and the LGPLv3 §4 relink.

For the deferred channels the mechanism exists and is gated with them: the
formula installs the notice to `doc`, and it is bundled in all five npm
packages (`scripts/npm-pack.sh` refuses a manifest that stops listing it, and
its selftest inspects every platform tarball rather than only the host's).
Those are covered by CI today and become live obligations on the release that
turns each channel on. (A *closed-source* fork
would instead owe §4 object files — out of scope here; confirm with counsel before
any such distribution.)

### Why this is an acceptable exception to the no-copyleft rule

The project rule targets *GPL/copyleft code that would constrain the
license*. GMP-via-Lean is a different category and acceptable because it is
(1) LGPL, not GPL — no infection; (2) an unavoidable transitive
dependency of the trusted toolchain, not vendored or reimplementable away;
and (3) handled identically to Lean's own binary releases (static GMP + a bundled
LGPLv3 notice + open-source relink), so binary distribution is a packaging
checklist, not an unresolved licensing risk.

### Compliance deliverables

- A `THIRD-PARTY-LICENSES` file and a `tl licenses` / `tl --licenses` command
  listing the real link-time set — Lean's bundled `LICENSES` notices ⊕ `tl`'s
  own deps: Lean runtime (Apache-2.0), GMP (LGPLv3 + notice + upstream source
  URL), LLVM (Apache-2.0-with-exceptions), libuv (MIT — statically linked into
  every Lean binary but **omitted from Lean's own `LICENSES` file**, so `tl`'s
  notice adds the entry itself), the Lake package deps compiled into the binary
  (mathlib and its cone, all Apache-2.0 except lean4-cli/MIT), and anything
  else the linker pulls in. **Built**: `scripts/GenLicenses.lean` (run as
  `lake env lean --run scripts/GenLicenses.lean`) regenerates the repo-root
  `THIRD-PARTY-LICENSES` and the embedded copy `Tl/Cli/Licenses.lean` in one
  pass from the live inputs — `lean-toolchain`, `lake-manifest.json`,
  per-package `LICENSE` files on disk (classified fail-closed), and the
  toolchain's bundled `LICENSES` file. `Tests/CliTests.lean` pins the embedded
  copy byte-equal to the file and drift-tests the notice against the current
  toolchain version and every manifest rev, so a pin bump fails the suite
  until the notice is regenerated. The same test file gates license
  *compatibility*: every manifest package's LICENSE must classify to the
  permissive allowlist (Apache-2.0/MIT) — a dep under a copyleft, unknown, or
  missing license fails the suite, and widening the allowlist is a deliberate
  edit to this ADR. The link-set check (`nm`/`otool -L`, or
  `ldd` on Linux, over the built binary — how the static GMP/libuv set was
  established) stays a manual step on toolchain bumps: a *new* bundled library
  is the one drift the generator cannot see. Worked example: the v4.32.0
  toolchain started bundling OpenSSL (`libssl.a`/`libcrypto.a`, on the
  default `leanc` link line, omitted from Lean's `LICENSES` like libuv) —
  but the symbol check shows the linker dead-strips every OpenSSL object out
  of `tl` (the only trace is Lean's three-instruction `lean_openssl_version`
  shim returning a header constant), so no OpenSSL code ships and no notice
  is owed. If tl ever starts using Lean's networking, this flips: the check
  will show real `SSL_`/`EVP_`/`CRYPTO_` symbols and the notice must then
  add OpenSSL (Apache-2.0 for 3.x) the same way it carries libuv.
- That file travels in every distribution artifact of every channel a release
  publishes — Release asset, npm package, Homebrew bottle — since compliance
  attaches to distribution, and a channel that is off distributes nothing.
- `tl` published under Apache-2.0.
- Do not patch GMP → nothing to publish beyond the upstream pointer.
- **Done for the enabled channels.** The bundled notices file is a signed
  companion asset that `install.sh` places beside the binary, and the
  open-source rebuild/relink path is documented in `REBUILDING.md`, which
  travels with every release: `tl`'s source + pinned toolchain + the GMP
  upstream pointer, which together let a recipient rebuild and relink. The
  npm and Homebrew carriers are built and CI-covered, and become live
  obligations on the release that enables each channel.
- **Done.** The full link-time dependency set is audited per target on each
  actual candidate (`link-audit-<target>.txt`), rather than assuming GMP is the
  only copyleft component.

## Alternatives considered

- Reimplement the shipping binary in Go/Rust for free cross-compilation.
  Rejected: it forfeits verification — the run artifact would not be the
  proved artifact (ADR-0004). The whole premise dies here.
- Truly-static musl Linux build. Deferred: finicky against the
  glibc-based toolchain; old-glibc + dynamic libc meets Lean's stated floor
  with less risk.
- Universal macOS binary (`lipo`). Rejected for now: effort
  disproportionate to a declining platform under the best-effort policy.
