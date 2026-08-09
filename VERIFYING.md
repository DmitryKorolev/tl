# Verifying tl releases

GitHub Releases from `DmitryKorolev/tl` are the source of truth for native
artifacts. The npm package is `@taskloop/tl`; its platform packages contain the
same binaries rather than independent builds.

No release has shipped yet. The commands below pin the identity the first
release will use.

Each release publishes, besides the per-target binaries: `SHA256SUMS` and its
Sigstore bundle, a bundle per asset, `release-manifest.json` (the canonical
description of the release — its assets and their digests, which targets were
published and at which tier, the npm packages and dist-tag, the toolchain and
`lake-manifest.json` digest), `LICENSE`, `THIRD-PARTY-LICENSES`, an SPDX SBOM,
`REBUILDING.md`, and per target a `link-audit-<target>.txt` and a
`build-metadata-<target>.json`. Every one of them is listed in `SHA256SUMS`, so
the procedure below covers the whole release and not only the binaries.

## Required checks

For an asset named `$asset`, download the asset, `SHA256SUMS`,
`SHA256SUMS.sigstore.json`, and the matching `$asset.sigstore.json` bundle from
the same GitHub Release. Pin the verifier inputs once:

```sh
issuer='https://token.actions.githubusercontent.com'
identity='^https://github\.com/DmitryKorolev/tl/\.github/workflows/release\.yml@refs/tags/v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?$'
```

Verify the sums file itself before using it:

```sh
cosign verify-blob SHA256SUMS \
  --bundle SHA256SUMS.sigstore.json \
  --certificate-oidc-issuer "$issuer" \
  --certificate-identity-regexp "$identity"
```

Select the asset's exact filename, verify its digest, and then verify its own
Sigstore bundle:

```sh
awk -v name="$asset" '$2 == name { print }' SHA256SUMS | shasum -a 256 -c -
cosign verify-blob "$asset" \
  --bundle "$asset.sigstore.json" \
  --certificate-oidc-issuer "$issuer" \
  --certificate-identity-regexp "$identity"
```

The expression is deliberately anchored. It accepts SemVer release and
pre-release tags, but only when GitHub's OIDC certificate names the direct
`.github/workflows/release.yml` workflow in this repository. The bundle must
contain the artifact signature, certificate, and Rekor transparency-log
inclusion proof; a missing or invalid proof is a verification failure, not a
reason to query the log and continue.

The normal installer verifies both checks. Its explicit
`TL_INSTALL_SKIP_SIGNATURE=1` escape skips only the Sigstore check: SHA-256
verification remains mandatory. This is for an environment where cosign cannot
run, not a weaker default.

## The same checks, scripted

`scripts/verify-release-artifacts.sh` in this repository performs exactly the
steps above, reading the issuer and identity from `release/identity.json` so
there is no second copy of the pin to drift:

```sh
scripts/verify-release-artifacts.sh <download-dir> tl-linux-x64
```

It is the code the release workflow itself runs, over the candidate artifacts
before creating the GitHub Release, so nothing is published that this procedure
would reject; `--selftest` runs it
against fabricated missing, malformed, mismatched, and rejected-signature
inputs on every commit. A procedure that is documented but never executed is a
procedure nobody has tested.

It honours the same `TL_INSTALL_SKIP_SIGNATURE=1` escape as the installer —
one hatch, one name, so a reader who sets the documented variable cannot end up
running the check they meant to skip. Without cosign on `PATH` and without that
variable, it refuses rather than quietly degrading to a digest-only check.

`install.sh` performs the same checks but does not call this script: it is
piped straight into a shell with no checkout to read, so it embeds its own copy
of the issuer and the certificate expression. `Tests/ReleaseTests.lean` fails if
that copy drifts from `release/identity.json`.

## Identity history and rotation

| Releases | Repository and workflow | OIDC issuer | Status |
|---|---|---|---|
| `v0.1.0` onward | `DmitryKorolev/tl/.github/workflows/release.yml` | `https://token.actions.githubusercontent.com` | current |

A repository transfer or rename, or a release-workflow path change, creates a
new signing identity. Before signing under it, a protected change must update
`release/identity.json`, this table, ADR-0006, the installer, and the Homebrew
formula together. Old releases are not re-signed under a new identity.

Historical rows stay here because they are what you verify an old artifact
*with* — by hand. Every shipped verifier carries exactly one pin, the current
one: `install.sh` embeds it, `Formula/tl.rb` embeds it, and
`scripts/verify-release-artifacts.sh` reads `release/identity.json`. After a
rotation, an artifact signed under a superseded identity is still verifiable,
but not by those: take its row's issuer and expression from this table and run
the two `cosign verify-blob` commands above with them. Saying so is the point —
the alternative is a reader running the scripted procedure against an old
release, watching it fail, and concluding the artifact is bad.

A compromise records the affected release interval, withdraws those artifacts,
and rotates the repository/workflow identity before another release.

`release/identity.json` is the machine-readable current pin.
`Tests/ReleaseTests.lean` keeps its values synchronized with this document,
ADR-0006, ADR-0014, `install.sh` and `Formula/tl.rb` — every operative copy —
and `scripts/check-release-identity.sh` checks that the expression still
discriminates, which a text-equality guard cannot.

## Before a release is tagged

`docs/release-prerequisites.md` records the state this pipeline depends on that
lives outside the repository: the npm packages must exist before trusted
publishing can be configured for them, the `release` environment must carry its
protection rules, the `v*` tag ruleset must be active, and the tap credential
must be present. `scripts/check-release-prereqs.sh` audits what can be audited
and runs in the signing job before anything is signed; what it cannot read is
carried in [docs/overview.md](docs/overview.md) as an explicit assumption.
