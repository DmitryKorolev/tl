# Verifying tl releases

GitHub Releases from `DmitryKorolev/tl` are the source of truth for native
artifacts. The npm package is `@taskloop/tl`; its platform packages contain the
same binaries rather than independent builds.

No release has shipped yet. The commands below pin the identity the first
release will use; the release workflow will fill in the final asset names.

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

## Identity history and rotation

| Releases | Repository and workflow | OIDC issuer | Status |
|---|---|---|---|
| `v0.1.0` onward | `DmitryKorolev/tl/.github/workflows/release.yml` | `https://token.actions.githubusercontent.com` | current |

A repository transfer or rename, or a release-workflow path change, creates a
new signing identity. Before signing under it, a protected change must update
`release/identity.json`, this table, ADR-0006, the installer, and the Homebrew
formula together. Historical rows stay here so old artifacts are verified
against the identity that signed them; old releases are not re-signed under a
new identity. A compromise records the affected release interval, withdraws
those artifacts, and rotates the repository/workflow identity before another
release.

`release/identity.json` is the machine-readable current pin. The test suite
keeps its values synchronized with this document and the ADR; when the installer
and formula land, the same guard expands to cover their operative copies.
