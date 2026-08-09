#!/bin/sh
# Verify downloaded tl release artifacts exactly as VERIFYING.md tells a user
# to, against the identity pinned in release/identity.json.
#
#   scripts/verify-release-artifacts.sh <dir> <asset>...
#   scripts/verify-release-artifacts.sh --selftest
#
# <dir> must contain, for each <asset>: the asset itself, `SHA256SUMS`,
# `SHA256SUMS.sigstore.json`, and `<asset>.sigstore.json`.
#
# One implementation, three callers: the release workflow runs it over the
# candidates before publishing them, so nothing is released that the published
# procedure would reject; the installer runs the same checks on what it
# downloads; and `--selftest` runs it against fabricated failures. A procedure
# documented but never executed is a procedure nobody has tested.
#
# Order matters and is not an accident. The signature on `SHA256SUMS` is
# checked *first*, because every digest comparison afterwards trusts that file;
# checking a digest against an unverified sums file proves only that the
# attacker was consistent.
#
# TL_VERIFY_SKIP_SIGNATURE=1 skips the Sigstore checks and keeps the SHA-256
# checks mandatory. It exists for an environment where cosign cannot run. It is
# not a weaker default and there is no flag for it: an environment variable
# someone had to set on purpose leaves a trace in shell history and CI logs.
set -eu

usage() {
  echo "usage: $0 <dir> <asset>... | $0 --selftest" >&2
  exit 2
}

# Locate release/identity.json relative to this script, so the installer can
# run from anywhere.
script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
identity_file="$script_dir/../release/identity.json"

fail() {
  echo "verify-release-artifacts: $1" >&2
  exit 1
}

# Read a string field from release/identity.json without assuming jq: the
# installer runs on machines that have curl and a shell and little else.
identity_field() {
  sed -n 's/.*"'"$1"'"[[:space:]]*:[[:space:]]*"\(.*\)".*/\1/p' "$identity_file" | head -1
}

sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | cut -d' ' -f1
  else
    fail "no sha256sum or shasum on PATH — the digest check is mandatory and cannot be skipped. Install coreutils (Linux) or use the system shasum (macOS)."
  fi
}

verify_dir() {
  dir=$1
  shift
  [ -d "$dir" ] || fail "'$dir' is not a directory"
  [ "$#" -gt 0 ] || usage

  [ -f "$identity_file" ] || fail "release/identity.json not found next to this script (looked at $identity_file) — without the pinned issuer and certificate identity a signature check would accept any valid Sigstore certificate, which is no check at all."

  issuer=$(identity_field certificateOidcIssuer)
  identity=$(identity_field certificateIdentityRegexp)
  [ -n "$issuer" ] || fail "release/identity.json has no certificateOidcIssuer — repair the pin before verifying anything against it."
  [ -n "$identity" ] || fail "release/identity.json has no certificateIdentityRegexp — repair the pin before verifying anything against it."

  sums="$dir/SHA256SUMS"
  [ -f "$sums" ] || fail "$sums not found — download SHA256SUMS from the same GitHub Release as the assets."

  skip_signature=0
  if [ "${TL_VERIFY_SKIP_SIGNATURE-}" = "1" ]; then
    skip_signature=1
    echo "verify-release-artifacts: TL_VERIFY_SKIP_SIGNATURE=1 — skipping Sigstore checks. SHA-256 verification still applies; you are trusting that SHA256SUMS is authentic by some other means."
  elif ! command -v cosign >/dev/null 2>&1; then
    fail "cosign not found on PATH — install it from https://github.com/sigstore/cosign/releases to verify the signatures. If cosign genuinely cannot run here, re-run with TL_VERIFY_SKIP_SIGNATURE=1, which keeps the SHA-256 checks and drops only the signature checks."
  fi

  # The sums file first: everything below trusts it.
  if [ "$skip_signature" -eq 0 ]; then
    bundle="$sums.sigstore.json"
    [ -f "$bundle" ] || fail "$bundle not found — download SHA256SUMS.sigstore.json from the same GitHub Release. Without it the sums file is unauthenticated, and every digest below would only prove internal consistency."
    cosign verify-blob "$sums" \
      --bundle "$bundle" \
      --certificate-oidc-issuer "$issuer" \
      --certificate-identity-regexp "$identity" \
      || fail "the signature on SHA256SUMS did not verify against the pinned identity. Do not use these files. Re-download from the official release; if it still fails, the artifacts are not the ones this repository signed — report it rather than working around it."
    echo "verify-release-artifacts: SHA256SUMS signature ok"
  fi

  for asset in "$@"; do
    path="$dir/$asset"
    [ -f "$path" ] || fail "$path not found — the asset name must match the one in SHA256SUMS exactly."

    # Pull this asset's line out of the sums file by exact name. Not `sha256sum
    # -c`, which would check every line and fail on assets for other platforms
    # that were never downloaded.
    expected=$(awk -v want="$asset" '$2 == want || $2 == "*" want { print $1; found = 1 } END { exit !found }' "$sums") \
      || fail "SHA256SUMS has no entry named '$asset'. Either the asset was renamed after signing, or you are checking it against a different release's sums file."
    case "$expected" in
      *[!0-9a-fA-F]* | '')
        fail "the SHA256SUMS entry for '$asset' is not a hex digest ('$expected') — the file is malformed or truncated; re-download it."
        ;;
    esac
    if [ "${#expected}" -ne 64 ]; then
      fail "the SHA256SUMS entry for '$asset' is ${#expected} characters, not the 64 of a SHA-256 digest — the file is malformed or truncated; re-download it."
    fi

    actual=$(sha256_of "$path")
    if [ "$actual" != "$expected" ]; then
      fail "digest mismatch for '$asset': the file hashes to $actual but SHA256SUMS says $expected. Delete the download and fetch it again; if it still differs, do not run it."
    fi
    echo "verify-release-artifacts: $asset digest ok"

    if [ "$skip_signature" -eq 0 ]; then
      asset_bundle="$path.sigstore.json"
      [ -f "$asset_bundle" ] || fail "$asset_bundle not found — download the per-asset Sigstore bundle from the same GitHub Release. The bundle must carry the artifact signature, the certificate, and the Rekor inclusion proof; a missing bundle is a verification failure, not a reason to continue."
      cosign verify-blob "$path" \
        --bundle "$asset_bundle" \
        --certificate-oidc-issuer "$issuer" \
        --certificate-identity-regexp "$identity" \
        || fail "the signature on '$asset' did not verify against the pinned identity. Do not run this binary. Re-download from the official release; if it still fails, report it rather than working around it."
      echo "verify-release-artifacts: $asset signature ok"
    fi
  done

  echo "verify-release-artifacts: verified $# asset(s) in $dir"
}

# ---------------------------------------------------------------------------
# Selftest. Every refusal path above, in throwaway directories.
#
# The Sigstore arms are exercised against a stub `cosign` placed first on PATH.
# That is deliberate: the stub covers *this script's* branching on a verifier
# verdict, which is what could regress here. Whether real cosign checks a Rekor
# inclusion proof correctly is cosign's own business, and the release workflow
# runs the real thing over real artifacts before publishing.
# ---------------------------------------------------------------------------
selftest() {
  command -v git >/dev/null 2>&1 || true
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  failures=0
  self=$script_dir/$(basename -- "$0")

  # A stub cosign whose verdict is read from COSIGN_STUB_VERDICT.
  mkdir -p "$work/bin"
  cat > "$work/bin/cosign" <<'STUB'
#!/bin/sh
if [ "${COSIGN_STUB_VERDICT:-ok}" = "ok" ]; then
  echo "Verified OK"
  exit 0
fi
echo "stub cosign: refusing" >&2
exit 1
STUB
  chmod +x "$work/bin/cosign"

  # A release directory that verifies cleanly.
  fixture() {
    d="$work/$1"
    mkdir -p "$d"
    printf 'binary contents\n' > "$d/tl-linux-x64"
    digest=$(sha256_of "$d/tl-linux-x64")
    printf '%s  tl-linux-x64\n' "$digest" > "$d/SHA256SUMS"
    printf '{}\n' > "$d/SHA256SUMS.sigstore.json"
    printf '{}\n' > "$d/tl-linux-x64.sigstore.json"
    echo "$d"
  }

  expect_status() {
    dir=$1; want=$2; name=$3
    got=0
    ( PATH="$work/bin:$PATH" "$self" "$dir" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
    if [ "$got" -ne "$want" ]; then
      echo "  FAIL $name: expected exit $want, got $got" >&2
      sed 's/^/    /' "$work/err" >&2
      failures=$((failures + 1))
      return 0
    fi
    echo "  ok   $name (exit $got)"
  }

  echo "verify-release-artifacts --selftest:"

  d=$(fixture happy); expect_status "$d" 0 "a complete, consistent release verifies"

  d=$(fixture no-sums); rm "$d/SHA256SUMS"
  expect_status "$d" 1 "a missing SHA256SUMS is refused"
  d=$(fixture no-sums-bundle); rm "$d/SHA256SUMS.sigstore.json"
  expect_status "$d" 1 "a missing SHA256SUMS bundle is refused"
  d=$(fixture no-asset-bundle); rm "$d/tl-linux-x64.sigstore.json"
  expect_status "$d" 1 "a missing per-asset bundle is refused"
  d=$(fixture no-asset); rm "$d/tl-linux-x64"
  expect_status "$d" 1 "a missing asset is refused"

  d=$(fixture unlisted); printf 'deadbeef  some-other-asset\n' > "$d/SHA256SUMS"
  expect_status "$d" 1 "an asset absent from SHA256SUMS is refused"
  d=$(fixture malformed); printf 'not-a-digest  tl-linux-x64\n' > "$d/SHA256SUMS"
  expect_status "$d" 1 "a non-hex digest line is refused"
  d=$(fixture truncated); printf 'abcdef  tl-linux-x64\n' > "$d/SHA256SUMS"
  expect_status "$d" 1 "a short digest line is refused"
  d=$(fixture mismatch); printf 'tampered\n' >> "$d/tl-linux-x64"
  expect_status "$d" 1 "a digest mismatch is refused"

  # Signature verdicts, via the stub.
  d=$(fixture bad-signature)
  got=0
  ( PATH="$work/bin:$PATH" COSIGN_STUB_VERDICT=bad "$self" "$d" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 1 ]; then
    echo "  ok   a rejected signature is refused (exit 1)"
  else
    echo "  FAIL a rejected signature is refused: expected exit 1, got $got" >&2
    failures=$((failures + 1))
  fi

  # The escape hatch drops signatures and keeps digests.
  d=$(fixture skip-ok); rm "$d/SHA256SUMS.sigstore.json" "$d/tl-linux-x64.sigstore.json"
  got=0
  ( PATH="/usr/bin:/bin" TL_VERIFY_SKIP_SIGNATURE=1 "$self" "$d" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 0 ]; then
    echo "  ok   TL_VERIFY_SKIP_SIGNATURE=1 verifies without bundles (exit 0)"
  else
    echo "  FAIL TL_VERIFY_SKIP_SIGNATURE=1 verifies without bundles: expected exit 0, got $got" >&2
    sed 's/^/    /' "$work/err" >&2
    failures=$((failures + 1))
  fi
  d=$(fixture skip-mismatch); rm "$d/SHA256SUMS.sigstore.json" "$d/tl-linux-x64.sigstore.json"
  printf 'tampered\n' >> "$d/tl-linux-x64"
  got=0
  ( PATH="/usr/bin:/bin" TL_VERIFY_SKIP_SIGNATURE=1 "$self" "$d" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 1 ]; then
    echo "  ok   TL_VERIFY_SKIP_SIGNATURE=1 still refuses a digest mismatch (exit 1)"
  else
    echo "  FAIL TL_VERIFY_SKIP_SIGNATURE=1 still refuses a digest mismatch: expected exit 1, got $got" >&2
    failures=$((failures + 1))
  fi

  # Without cosign and without the explicit opt-out, refuse rather than
  # silently degrade to a digest-only check.
  d=$(fixture no-cosign)
  got=0
  ( PATH="/usr/bin:/bin" "$self" "$d" tl-linux-x64 >"$work/out" 2>"$work/err" ) || got=$?
  if [ "$got" -eq 1 ] && grep -q "cosign not found" "$work/err"; then
    echo "  ok   a missing cosign is refused rather than skipped (exit 1)"
  else
    echo "  FAIL a missing cosign is refused rather than skipped: expected exit 1 naming cosign, got $got" >&2
    sed 's/^/    /' "$work/err" >&2
    failures=$((failures + 1))
  fi

  if [ "$failures" -ne 0 ]; then
    echo "verify-release-artifacts: --selftest found $failures broken case(s). This verifier no longer refuses what it claims to refuse — repair it before trusting anything it accepts." >&2
    exit 1
  fi
  echo "verify-release-artifacts: --selftest passed"
  exit 0
}

case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  -*) usage ;;
  *) verify_dir "$@" ;;
esac
