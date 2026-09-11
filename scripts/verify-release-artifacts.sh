#!/bin/sh
# Verify downloaded tl release artifacts exactly as VERIFYING.md tells a user
# to, against the identity pinned in release/identity.json.
#
#   scripts/verify-release-artifacts.sh [--require-signature] <dir> <asset>...
#
# <dir> must contain, for each <asset>: the asset itself, `SHA256SUMS`,
# `SHA256SUMS.sigstore.json`, and `<asset>.sigstore.json`.
#
# Two callers: the release workflow runs it over the candidate artifacts before
# publishing them, so nothing is released that the published procedure would
# reject; and the native public-process corpus drives fabricated failures on every commit.
# A procedure documented but never executed is a procedure nobody has tested.
#
# `install.sh` performs the same checks but does not call this script — it is
# piped into a shell with no checkout to read, so it carries its own copy of
# the pinned issuer and expression. `Tests/ReleaseTests.lean` fails if that
# copy drifts from `release/identity.json`. The digest and reporting helpers it
# uses are defined here and tested through its public process interface.
#
# Order matters and is not an accident. The signature on `SHA256SUMS` is
# checked *first*, because every digest comparison afterwards trusts that file;
# checking a digest against an unverified sums file proves only that the
# attacker was consistent.
#
# TL_INSTALL_SKIP_SIGNATURE=1 skips the Sigstore checks and keeps the SHA-256
# checks mandatory. It exists for an environment where cosign cannot run. It is
# not a weaker default and there is no flag for it: an environment variable
# someone had to set on purpose leaves a trace in shell history and CI logs.
#
# `--require-signature` refuses that escape outright. The release workflow
# passes it, because there the escape would be a silent downgrade of the one
# gate standing between a candidate and the public: without it, a
# `TL_INSTALL_SKIP_SIGNATURE=1` inherited from anywhere in the job environment
# turns "nothing is published that this procedure would reject" into comparing
# SHA256SUMS against itself. A user's escape hatch and a release gate's are not
# the same thing, and the difference has to be expressible.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
# Complete local digest helpers: the standalone verification procedure must
# not source tracked release administration code. The public native corpus
# tests these through this script's ordinary argv.
verifier_lower() {
  printf '%s' "$1" | tr 'ABCDEF' 'abcdef'
}

# SHA-256 of a file, lowercase hex. coreutils ships sha256sum; macOS ships
# shasum. Both print "<hex>  <name>", so the first field is the digest.
#
# Deliberately not `sha256sum "$1" | cut -d' ' -f1`. A pipeline's status is its
# *last* command's, so `cut` returning 0 masked a digest tool that was present
# on PATH but broken — the caller got an empty string and a success status, and
# reported it downstream as "the file hashes to  but SHA256SUMS says …", which
# is a tampering verdict for a broken toolchain. Substitution first, status
# checked, field taken afterwards.
verifier_sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    verifier__digest_out=$(sha256sum "$1") || verifier__digest_out=''
  elif command -v shasum >/dev/null 2>&1; then
    verifier__digest_out=$(shasum -a 256 "$1") || verifier__digest_out=''
  else
    echo "no sha256sum or shasum on PATH — the digest check is mandatory and cannot be skipped. Install coreutils (Linux) or use the system shasum (macOS)." >&2
    return 1
  fi
  if [ -z "$verifier__digest_out" ]; then
    echo "the digest tool on PATH produced no output for '$1' — it is present but not working. The digest check is mandatory and cannot be skipped; repair the installation of coreutils or shasum." >&2
    return 1
  fi
  printf '%s' "${verifier__digest_out%% *}"
}

# Pull one asset's digest out of a sums file by exact name, and prove it is a
# digest before anybody compares against it.
#
# Not `sha256sum -c`, which checks every line and so fails on assets for other
# platforms that were never downloaded. The `*name` form is accepted because
# that is what `sha256sum` writes in binary mode.
#
# Prints the lowercase digest on success. On failure prints a teaching message
# to stderr and returns non-zero; the caller decides whether that is fatal.
verifier_sums_digest() {
  verifier__sums=$1
  verifier__name=$2
  if ! verifier__digest=$(awk -v want="$verifier__name" \
      '$2 == want || $2 == "*" want { print $1; found = 1 } END { exit !found }' "$verifier__sums"); then
    echo "$verifier__sums has no entry named '$verifier__name'. Either the asset was renamed after signing, or this is a different release's sums file." >&2
    return 1
  fi
  case $verifier__digest in
    *[!0-9a-fA-F]* | '')
      echo "the $verifier__sums entry for '$verifier__name' is not a hex digest ('$verifier__digest') — the file is malformed or truncated; re-download it." >&2
      return 1
      ;;
  esac
  if [ "${#verifier__digest}" -ne 64 ]; then
    echo "the $verifier__sums entry for '$verifier__name' is ${#verifier__digest} characters, not the 64 of a SHA-256 digest — the file is malformed or truncated; re-download it." >&2
    return 1
  fi
  verifier_lower "$verifier__digest"
}


usage() {
  echo "usage: $0 [--require-signature] <dir> <asset>..." >&2
  exit 2
}

# Locate release/identity.pin relative to this script, so it can run from
# anywhere.
#
# The pin, not release/identity.json. This script is what VERIFYING.md tells a
# reader to run, and it used to need `python3` for exactly one thing: reading
# two strings out of JSON. It could not scrape them — the certificate
# expression contains `\.`, which JSON stores as `\\.`, so a text scrape hands
# cosign a pattern meaning "a literal backslash followed by any character".
# That matches no real certificate, and the failure is silent in the worst
# direction: it rejects every genuine signature while looking exactly like
# tampering rather than like a broken verifier.
#
# So the pin is published in a form that needs no parser: two inert lines, the
# issuer then the expression, generated from release/identity.json by
# `tlrelease write-pin` and drift-guarded against it. Requiring an interpreter
# to check a signature was a dependency this project chose for its own
# convenience and charged to the user.
pin_file="$script_dir/../release/identity.pin"

fail() {
  echo "verify-release-artifacts: $1" >&2
  exit 1
}

# Run cosign and distinguish two very different outcomes. A verification
# failure means these bytes are not what this repository signed. Anything else
# — cosign missing a dependency, a broken pin file, no network for a trust-root
# refresh — is a problem with the checking apparatus, and reporting that as
# tampering sends the reader hunting for an attacker that is not there.
cosign_verify() {
  target=$1
  bundle_path=$2
  label=$3
  out=$(cosign verify-blob "$target" \
          --bundle "$bundle_path" \
          --certificate-oidc-issuer "$issuer" \
          --certificate-identity-regexp "$identity" 2>&1) && return 0
  case $out in
    *"no matching signatures"* | *"none of the expected identities matched"* | \
    *"certificate identity"* | *"invalid signature"* | *"inclusion proof"* | \
    *"transparency log"* | *"tlog"*)
      printf '%s\n' "$out" >&2
      fail "the signature on '$label' did not verify against the pinned identity. Do not use it. Re-download from the official release; if it still fails, these are not the artifacts this repository signed — report it rather than working around it."
      ;;
    *)
      printf '%s\n' "$out" >&2
      fail "cosign could not complete the check on '$label', so whether it is authentic is unknown — this is not evidence of tampering. The usual causes are a cosign version mismatch, no network for the trust-root refresh, or a damaged bundle file. Re-run once; if it persists, verify by hand with the commands in VERIFYING.md."
      ;;
  esac
}

verify_dir() {
  require_signature=$1
  dir=$2
  shift 2
  [ -d "$dir" ] || fail "'$dir' is not a directory. Pass the directory the release assets were downloaded into, then the asset names within it — for example 'scripts/verify-release-artifacts.sh ~/Downloads tl-linux-x64'."
  [ "$#" -gt 0 ] || usage

  [ -f "$pin_file" ] || fail "release/identity.pin not found next to this script (looked at $pin_file) — without the pinned issuer and certificate identity a signature check would accept any valid Sigstore certificate, which is no check at all. Regenerate it with 'tlrelease write-pin --identity release/identity.json --output identity.pin --output-dir release'."
  [ -r "$pin_file" ] || fail "release/identity.pin is not readable (looked at $pin_file). A pin that cannot be read is not a weaker check, it is no check; fix the permissions rather than verifying without it."

  # One opened descriptor for the whole file, so both lines come from a single
  # read of a single file: two separate reads could be handed one line each
  # from two different pins.
  #
  # `IFS= read -r` is what makes the expression survive. Without `-r`, `read`
  # interprets the backslashes in `\.` and hands cosign an expression matching
  # nothing; without the empty `IFS`, leading and trailing whitespace is
  # stripped from a value that is passed verbatim to a matcher.
  #
  # The file is *data*. It is never sourced and never evaluated — the values
  # only ever become arguments — so nothing in it can execute.
  #
  # `read` returns non-zero at end of file *after* assigning what it managed to
  # read, so a file whose last line has no terminating newline yields the value
  # and a failure status. That is a truncated write, and it is refused rather
  # than accepted: the two-line shape is what makes the file unambiguous, and a
  # reader that tolerated a missing terminator would disagree with
  # `release/Identity.lean`, which refuses it. One pin, two readers, one answer.
  # The raw bytes first, before any of them reaches a shell variable.
  #
  # A shell variable cannot hold a NUL: `read` drops it silently, and so does
  # command substitution, so a pin carrying one arrived here already repaired
  # and every check below passed. `release/Identity.lean` refuses it — it
  # refuses everything outside printable ASCII — so the two readers of one pin
  # disagreed about that byte, which is exactly what this pair exists to
  # prevent. Counting the bytes rather than capturing them is what survives the
  # round trip: `wc -c` reports a number, and a number is text.
  #
  # Deleting the printable range and the newline leaves exactly the bytes that
  # do not belong, so a non-zero count is the refusal. Under the C locale, so
  # the class means ASCII rather than whatever the caller's locale considers
  # printable.
  pin_stray_count=$(LC_ALL=C tr -d '\040-\176\n' < "$pin_file" | LC_ALL=C wc -c) \
    || fail "could not read release/identity.pin to check its bytes (looked at $pin_file). A pin that cannot be read is not a weaker check, it is no check."
  pin_stray_count=$(printf '%s' "$pin_stray_count" | tr -d ' ')
  if [ "$pin_stray_count" -ne 0 ]; then
    fail "release/identity.pin contains $pin_stray_count byte(s) outside printable ASCII — a carriage return from Windows line endings, or a NUL, are the usual causes. A NUL in particular vanishes on its way into a shell variable, so this check reads the file's bytes directly: it would otherwise be accepted here and refused by 'tlrelease check-pin', one pin with two answers. Regenerate it with 'tlrelease write-pin --identity release/identity.json --output identity.pin --output-dir release'."
  fi
  pin_issuer=''
  pin_identity=''
  pin_extra=''
  pin_terminated=0
  pin_extra_present=0
  {
    IFS= read -r pin_issuer || true
    if IFS= read -r pin_identity; then pin_terminated=1; fi
    if IFS= read -r pin_extra; then pin_extra_present=1; fi
  } < "$pin_file"

  issuer=$pin_issuer
  identity=$pin_identity

  [ -n "$issuer" ] || fail "release/identity.pin has no issuer on its first line — an empty issuer would not constrain the certificate at all. Regenerate it with 'tlrelease write-pin --identity release/identity.json --output identity.pin --output-dir release'."
  [ -n "$identity" ] || fail "release/identity.pin has no certificate identity expression on its second line — an empty expression matches every certificate, which is no check at all. Regenerate it with 'tlrelease write-pin --identity release/identity.json --output identity.pin --output-dir release'."
  # A third line is refused rather than ignored: a reader that skipped it could
  # be handed a second, different pin below the one it used. Both an empty
  # third line and trailing data without a newline are caught, because the two
  # look the same to a reader that only counts non-empty lines.
  if [ "$pin_extra_present" -eq 1 ] || [ -n "$pin_extra" ]; then
    fail "release/identity.pin has more than two lines. The pin is exactly two — the issuer, then the certificate identity expression — and extra content is refused rather than ignored, because a reader that skipped it could be handed a second, different pin below the one it used."
  fi
  # Anything outside printable ASCII, which in practice means a carriage
  # return from a file with Windows line endings. A CR rides into the value
  # cosign is given and makes the expression match nothing — the same silent
  # rejection of genuine signatures that the JSON scrape would have caused.
  # Under the C locale, so the class means "ASCII printable" rather than
  # whatever the caller's locale considers printable. On a UTF-8 locale this
  # host accepted a non-ASCII byte, which would then ride into the expression
  # cosign is handed while `release/Identity.lean` refuses the same value —
  # two readers of one pin disagreeing is the thing this pair exists to avoid.
  # `tr` rather than a `case` glob, and with the locale pinned on the command
  # itself: a bracket expression's idea of "printable" follows the caller's
  # locale, and on a UTF-8 one this host accepted a non-ASCII byte. Deleting
  # the printable-ASCII range leaves exactly the bytes that do not belong, so
  # a non-empty remainder is the refusal. Emptiness is what is tested, not a
  # status, so nothing here can be masked by a pipeline's last stage.
  pin_stray_bytes=$(printf '%s' "$issuer$identity" | LC_ALL=C tr -d '\040-\176')
  if [ -n "$pin_stray_bytes" ]; then
    fail "release/identity.pin contains a byte outside printable ASCII — a carriage return from Windows line endings is the usual cause. The pin is passed to cosign verbatim, so it would silently match nothing; rewrite it with Unix line endings and ASCII only."
  fi
  if [ "$pin_terminated" -ne 1 ]; then
    fail "release/identity.pin does not end with a newline, so its second line is truncated. Regenerate it with 'tlrelease write-pin --identity release/identity.json --output identity.pin --output-dir release' rather than repairing it by hand: a partially written pin is not a weaker check, it is a check against an unknown expression."
  fi
  # Both anchors, not just the head. cosign matches unanchored, so a missing
  # `^` accepts a certificate whose identity merely *contains* the pinned one —
  # and a missing `$` accepts one that merely *begins* with it, which is not
  # hypothetical: a git tag name may contain `/`, so
  # `…/release.yml@refs/tags/v1.0.0/anything` would satisfy a head-only pin.
  # Tests/ReleaseTests.lean already required both of release/identity.json;
  # this verifier checked only the first half.
  case $identity in
    '^'*) ;;
    *) fail "the pinned certificateIdentityRegexp is not anchored at ^ ('${identity}'). cosign matches unanchored, so an unanchored expression would accept a certificate whose identity merely *contains* this repository's — repair release/identity.pin by regenerating it from release/identity.json." ;;
  esac
  case $identity in
    *'$') ;;
    *) fail "the pinned certificateIdentityRegexp is not anchored at \$ ('${identity}'). cosign matches unanchored, so an expression without a tail anchor accepts any certificate identity that merely *begins* with this one — a tag name may contain '/', so trailing content is reachable. Repair release/identity.json." ;;
  esac

  scratch=$(mktemp -d) || fail "could not create a temporary directory for this run's scratch files. Set TMPDIR to a writable directory and retry."
  trap 'rm -rf "$scratch"' EXIT INT TERM

  sums="$dir/SHA256SUMS"
  [ -f "$sums" ] || fail "$sums not found — download SHA256SUMS from the same GitHub Release as the assets."

  skip_signature=0
  if [ "${TL_INSTALL_SKIP_SIGNATURE-}" = "1" ]; then
    if [ "$require_signature" -eq 1 ]; then
      fail "TL_INSTALL_SKIP_SIGNATURE=1 is set, but this run was invoked with --require-signature. That combination is refused rather than resolved: the caller is a release gate whose entire purpose is to reject anything the published verification procedure would reject, and honouring the escape here would reduce it to comparing SHA256SUMS against itself. Unset the variable in this environment."
    fi
    skip_signature=1
    echo "verify-release-artifacts: TL_INSTALL_SKIP_SIGNATURE=1 — skipping Sigstore checks. SHA-256 verification still applies; you are trusting that SHA256SUMS is authentic by some other means."
  elif ! command -v cosign >/dev/null 2>&1; then
    if [ "$require_signature" -eq 1 ]; then
      fail "cosign not found on PATH, and this run was invoked with --require-signature. A release gate cannot fall back to a digest-only check: install cosign in this job (sigstore/cosign-installer) before verifying candidates."
    fi
    fail "cosign not found on PATH — install it from https://github.com/sigstore/cosign/releases to verify the signatures. If cosign genuinely cannot run here, re-run with TL_INSTALL_SKIP_SIGNATURE=1, which keeps the SHA-256 checks and drops only the signature checks."
  fi

  # The sums file first: everything below trusts it.
  if [ "$skip_signature" -eq 0 ]; then
    bundle="$sums.sigstore.json"
    [ -f "$bundle" ] || fail "$bundle not found — download SHA256SUMS.sigstore.json from the same GitHub Release. Without it the sums file is unauthenticated, and every digest below would only prove internal consistency."
    cosign_verify "$sums" "$bundle" SHA256SUMS
    echo "verify-release-artifacts: SHA256SUMS signature ok"
  fi

  for asset in "$@"; do
    path="$dir/$asset"
    [ -f "$path" ] || fail "$path not found — the asset name must match the one in SHA256SUMS exactly."

    # Pull this asset's line out of the sums file by exact name, and prove it
    # is a digest. Both adapters have independent local helpers, exercised
    # through the native public-process corpora.
    # The scratch file goes in a temp directory, not beside the assets. Written
    # into $dir it fails on read-only media — an immutable artifact mount, a
    # root-owned download directory — and the refusal that followed was a bare
    # "verify-release-artifacts: " with no message at all, for a release that
    # was perfectly good. This file exists to keep a broken checker from
    # reading as a bad artifact; that applies to its own scratch space too.
    expected=$(verifier_sums_digest "$sums" "$asset" 2>"$scratch/sums-err") || {
      fail "$(cat "$scratch/sums-err")"
    }

    # Two statements, not one. Nested, `$(verifier_lower "$(verifier_sha256_of …)")`
    # captures verifier_lower's status — which succeeds on empty input — so a host
    # with neither sha256sum nor shasum produced an empty digest, skipped the
    # "digest check is mandatory" refusal entirely, and reported a missing tool
    # as "digest mismatch … hashes to  but SHA256SUMS says …". That is the one
    # verdict this file must never get wrong, and the nesting hid it.
    actual=$(verifier_sha256_of "$path") \
      || fail "no sha256sum or shasum on PATH — the digest check is mandatory and cannot be skipped. Install coreutils (Linux) or use the system shasum (macOS)."
    actual=$(verifier_lower "$actual")
    if [ "$actual" != "$expected" ]; then
      fail "digest mismatch for '$asset': the file hashes to $actual but SHA256SUMS says $expected. Delete the download and fetch it again; if it still differs, do not run it."
    fi
    echo "verify-release-artifacts: $asset digest ok"

    if [ "$skip_signature" -eq 0 ]; then
      asset_bundle="$path.sigstore.json"
      [ -f "$asset_bundle" ] || fail "$asset_bundle not found — download the per-asset Sigstore bundle from the same GitHub Release. The bundle must carry the artifact signature, the certificate, and the Rekor inclusion proof; a missing bundle is a verification failure, not a reason to continue."
      cosign_verify "$path" "$asset_bundle" "$asset"
      echo "verify-release-artifacts: $asset signature ok"
    fi
  done

  echo "verify-release-artifacts: verified $# asset(s) in $dir"
}


require_signature=0
case "${1-}" in
  '') usage ;;
  --require-signature)
    require_signature=1
    shift
    [ "$#" -gt 0 ] || usage
    case "${1-}" in
      -*) usage ;;
    esac
    verify_dir "$require_signature" "$@"
    ;;
  -*) usage ;;
  *) verify_dir "$require_signature" "$@" ;;
esac
