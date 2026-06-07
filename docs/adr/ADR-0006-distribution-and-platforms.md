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
  - Native (non-WSL) Windows x86-64 — Lean Tier 1, but *our* Tier 2: we ship
    a `win32-x64` binary (npm/Release), smoke-tested only. The Win32 filesystem
    abstraction (ADR-0015 §7) and git-shell-out specifics are the *design* but are
    not in the gating matrix — a native-Windows-only bug is best-effort, not
    release-blocking. Demoted because the agent/dev surface is Linux+macOS and
    serious Windows use is WSL (above); promote back to Supported on real
    native-Windows demand or a maintainer for the Windows test pass.
- Community — not in our CI:
  - FreeBSD, via the `math/lean4` Ports path (build-from-source,
    version tracking the port, CI only via a FreeBSD VM action or Cirrus if
    a maintainer wants it). Idiomatically distributed as a FreeBSD
    port/pkg that build-deps on `math/lean4`, not as a prebuilt binary.

### Build approach

- Native per-target CI matrix (Lean cross-compile is weak): GitHub
  hosted runners cover all five Supported/Best-effort targets
  (`ubuntu-*`, `ubuntu-*-arm`, `macos-14`, `macos-13`, `windows-latest`).
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

- GitHub Releases — the source of truth. CI uploads the prebuilt
  binaries here; everything else wraps them.
- `curl | sh` installer — universal baseline, no ecosystem dependency,
  platform-detecting; runs unmodified in WSL — the recommended Windows path
  (WSL is our Linux x86-64 target).
- npm — the priority veneer; the audience is agent/Node tooling and
  `npm i -g` is how such tools get adopted. Use
  the `optionalDependencies` pattern (a launcher package + one
  prebuilt-binary package per platform, e.g. `@tl/cli-darwin-arm64`), not a
  `postinstall` download — hermetic and CI-safe. This pattern also delivers a
  native Windows `win32-x64` binary for `npm i -g`, shipped best-effort
  (our Tier 2 — smoke-tested, not gating; WSL is the Supported Windows path).
- Homebrew tap — fast-follow; a formula that downloads the Release
  artifact per platform (not build-from-source, which would require users to
  have Lean).
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
`tl version --json` reports all three numbers plus the git commit / build
provenance digest for the running binary.

### Release integrity and provenance

Binary distribution is gated on a verifiable release pipeline:

- Every GitHub Release publishes per-asset SHA-256 digests, a signed
  `SHA256SUMS`, and per-asset signatures. The `curl | sh` installer and
  Homebrew formula verify these and fail closed by default.
- Release artifacts carry a Sigstore/cosign signature and SLSA provenance
  attestation from GitHub OIDC, binding the artifact to the source commit,
  workflow, pinned Lean toolchain, and checked-in `lake-manifest.json`.
- npm uses trusted publishing / OIDC, 2FA, `npm --provenance`, no long-lived
  publish tokens, and a defensively-registered `@tl` package scope. The
  launcher pins each platform package by exact version and integrity hash; it
  never downloads arbitrary URLs in `postinstall`.
- Builds are made reproducible where the platform toolchain allows: pinned
  Lean + lake dependencies, deterministic timestamps/paths, and a documented
  independent rebuilder that can verify binary-to-source correspondence.
  Reproducibility proves "this binary came from this source"; the Lean proofs
  still prove the source-level correctness claims.
- Every binary release includes an SBOM and the full link-time dependency audit
  required by the licensing section below.

## Consequences

- The marginal cost of each channel is small; the cost is the per-target
  build. Releases + curl + npm covers ~everyone (incl. Windows via npm);
  brew is cheap to add.
- Windows is more tractable than its app-level reputation. The toolchain
  is Lean Tier 1 (built + tested upstream) and npm reaches it for free; the
  residual lift is git-shell-out path handling and a Windows test pass. (The
  `.gitattributes` log-integrity requirement is obviated under ADR-0001 — the
  log lives in `refs/tl/log`, not EOL-normalizable working-tree files.)
- macOS x86-64 stays cheap and bounded by the best-effort policy.
- Licensing boundary. The runtime links GMP under LGPLv3; this
  is a stated, bounded exception to the project's no-copyleft rule. Binary
  distribution mirrors Lean (static GMP + a bundled LGPLv3 notice +
  open-source relink) — a packaging checklist, detailed below.
- Supply-chain trust is explicit. Users trust the Lean compiler/checker,
  GitHub release infrastructure, the signing identity, and the pinned build
  workflow; signatures and reproducibility make that trust auditable rather
  than implicit (ADR-0014).

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
  reproducibly buildable (release-integrity section), the LGPLv3 §4 "swap GMP and
  relink" obligation is met the same way Lean meets it — the full source + pinned
  build system + the GMP upstream pointer are public, so any recipient can rebuild
  and relink. No separate object-file drop is required while `tl` is open.

The residual is therefore a packaging checklist:
confirm the notices file actually travels into the Release tarball, the npm
package, and the brew bottle, and that the rebuild/relink path is documented.
This is a release gate, not an MVP implementation blocker. (A *closed-source* fork
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

- A `THIRD-PARTY-LICENSES` file and a `tl --licenses` command listing the
  real link-time set — in practice Lean's bundled `LICENSES` notices ⊕ `tl`'s
  own deps: Lean runtime (Apache-2.0), GMP (LGPLv3 + notice + upstream source
  URL), LLVM (Apache-2.0-with-exceptions), and anything else the linker pulls in.
- That file travels in every distribution artifact — Release tarball,
  npm package, Homebrew bottle — since compliance attaches to distribution.
- `tl` published under Apache-2.0.
- Do not patch GMP → nothing to publish beyond the upstream pointer.
- Before the first binary release, confirm the bundled notices file ships in all
  three channels and document the open-source rebuild/relink path (GMP is
  static — see *Binary distribution strategy*): point to `tl`'s source + pinned
  toolchain + GMP upstream, which together let a recipient rebuild and relink.
- Audit the full link-time dependency set once the build exists, rather
  than assuming GMP is the only copyleft component.

## Alternatives considered

- Reimplement the shipping binary in Go/Rust for free cross-compilation.
  Rejected: it forfeits verification — the run artifact would not be the
  proved artifact (ADR-0004). The whole premise dies here.
- Truly-static musl Linux build. Deferred: finicky against the
  glibc-based toolchain; old-glibc + dynamic libc meets Lean's stated floor
  with less risk.
- Universal macOS binary (`lipo`). Rejected for now: effort
  disproportionate to a declining platform under the best-effort policy.
