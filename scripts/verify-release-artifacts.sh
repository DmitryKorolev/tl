#!/bin/sh
# Verify downloaded tl release artifacts exactly as VERIFYING.md tells a user
# to, against the identity pinned in release/identity.json.
#
#   scripts/verify-release-artifacts.sh [--require-signature] <dir> <asset>...
#   scripts/verify-release-artifacts.sh --selftest
#
# <dir> must contain, for each <asset>: the asset itself, `SHA256SUMS`,
# `SHA256SUMS.sigstore.json`, and `<asset>.sigstore.json`.
#
# Two callers: the release workflow runs it over the candidate artifacts before
# publishing them, so nothing is released that the published procedure would
# reject; and `--selftest` runs it against fabricated failures on every commit.
# A procedure documented but never executed is a procedure nobody has tested.
#
# `install.sh` performs the same checks but does not call this script — it is
# piped into a shell with no checkout to read, so it carries its own copy of
# the pinned issuer and expression. `Tests/ReleaseTests.lean` fails if that
# copy drifts from `release/identity.json`, and
# `scripts/check-embedded-copies.sh` fails if its copies of the shared helpers
# drift from `scripts/lib/release-common.sh`.
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
RC_LIB_SELF="$script_dir/lib/release-common.sh"
if [ ! -f "$RC_LIB_SELF" ]; then
  echo "verify-release-artifacts: scripts/lib/release-common.sh not found next to this script (looked at $RC_LIB_SELF) — it holds the digest and reporting helpers this verifier shares with the rest of the release machinery. Run it from a checkout." >&2
  exit 2
fi
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

usage() {
  echo "usage: $0 [--require-signature] <dir> <asset>... | $0 --selftest" >&2
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

  [ -f "$pin_file" ] || fail "release/identity.pin not found next to this script (looked at $pin_file) — without the pinned issuer and certificate identity a signature check would accept any valid Sigstore certificate, which is no check at all. Regenerate it with 'tlrelease write-pin release/identity.json release/identity.pin'."
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
    fail "release/identity.pin contains $pin_stray_count byte(s) outside printable ASCII — a carriage return from Windows line endings, or a NUL, are the usual causes. A NUL in particular vanishes on its way into a shell variable, so this check reads the file's bytes directly: it would otherwise be accepted here and refused by 'tlrelease check-pin', one pin with two answers. Regenerate it with 'tlrelease write-pin release/identity.json release/identity.pin'."
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

  [ -n "$issuer" ] || fail "release/identity.pin has no issuer on its first line — an empty issuer would not constrain the certificate at all. Regenerate it with 'tlrelease write-pin release/identity.json release/identity.pin'."
  [ -n "$identity" ] || fail "release/identity.pin has no certificate identity expression on its second line — an empty expression matches every certificate, which is no check at all. Regenerate it with 'tlrelease write-pin release/identity.json release/identity.pin'."
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
    fail "release/identity.pin does not end with a newline, so its second line is truncated. Regenerate it with 'tlrelease write-pin release/identity.json release/identity.pin' rather than repairing it by hand: a partially written pin is not a weaker check, it is a check against an unknown expression."
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

  scratch=$(mktemp -d) || fail "could not create a temporary directory for this run's scratch files."
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
    # is a digest. Shared with the installer through the library, because the
    # two copies of this had already diverged on what they accepted.
    # The scratch file goes in a temp directory, not beside the assets. Written
    # into $dir it fails on read-only media — an immutable artifact mount, a
    # root-owned download directory — and the refusal that followed was a bare
    # "verify-release-artifacts: " with no message at all, for a release that
    # was perfectly good. This file exists to keep a broken checker from
    # reading as a bad artifact; that applies to its own scratch space too.
    expected=$(rc_sums_digest "$sums" "$asset" 2>"$scratch/sums-err") || {
      fail "$(cat "$scratch/sums-err")"
    }

    # Two statements, not one. Nested, `$(rc_lower "$(rc_sha256_of …)")`
    # captures rc_lower's status — which succeeds on empty input — so a host
    # with neither sha256sum nor shasum produced an empty digest, skipped the
    # "digest check is mandatory" refusal entirely, and reported a missing tool
    # as "digest mismatch … hashes to  but SHA256SUMS says …". That is the one
    # verdict this file must never get wrong, and the nesting hid it.
    actual=$(rc_sha256_of "$path") \
      || fail "no sha256sum or shasum on PATH — the digest check is mandatory and cannot be skipped. Install coreutils (Linux) or use the system shasum (macOS)."
    actual=$(rc_lower "$actual")
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

# ---------------------------------------------------------------------------
# Selftest. Every refusal path above, in throwaway directories.
#
# The Sigstore arms are exercised against the shared stub `cosign` placed first
# on PATH. That is deliberate: the stub covers *this script's* branching on a
# verifier verdict, which is what could regress here. Whether real cosign
# checks a Rekor inclusion proof correctly is cosign's own business, and the
# release workflow runs the real thing over real artifacts before publishing.
# ---------------------------------------------------------------------------
selftest() {
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  self=$script_dir/$(basename -- "$0")

  rc_selftest_begin "verify-release-artifacts" "$work"

  rc_write_stub_cosign "$work/bin" "$pin_file" "$work"

  # A release directory that verifies cleanly.
  fixture() {
    d="$work/$1"
    mkdir -p "$d"
    printf 'binary contents\n' > "$d/tl-linux-x64"
    digest=$(rc_sha256_of "$d/tl-linux-x64")
    printf '%s  tl-linux-x64\n' "$digest" > "$d/SHA256SUMS"
    printf '{}\n' > "$d/SHA256SUMS.sigstore.json"
    printf '{}\n' > "$d/tl-linux-x64.sigstore.json"
    echo "$d"
  }

  # Run the verifier with the stub first on PATH.
  verify() {
    PATH="$work/bin:$PATH" "$self" "$@"
  }
  # A PATH with cosign genuinely absent, built by dropping every directory that
  # holds one rather than by naming two that usually do not. `PATH=/usr/bin:/bin`
  # is only cosign-free where cosign is not packaged there: on Fedora, Arch and
  # Alpine it is, so the two rows that model "cosign is absent" instead drove
  # the *real* cosign against fixture bundles containing `{}` — failing there
  # and nowhere else, inside a gate documented as hermetic.
  path_without_cosign() {
    pwc__out=''
    pwc__rest=$PATH
    while [ -n "$pwc__rest" ]; do
      case $pwc__rest in
        *:*) pwc__dir=${pwc__rest%%:*}; pwc__rest=${pwc__rest#*:} ;;
        *) pwc__dir=$pwc__rest; pwc__rest='' ;;
      esac
      [ -n "$pwc__dir" ] || continue
      [ -x "$pwc__dir/cosign" ] && continue
      if [ -z "$pwc__out" ]; then pwc__out=$pwc__dir; else pwc__out="$pwc__out:$pwc__dir"; fi
    done
    printf '%s' "$pwc__out"
  }
  bare_path=$(path_without_cosign)
  # …and without it, for the cases that must not find cosign at all.
  verify_bare() {
    PATH="$bare_path" "$self" "$@"
  }
  # The premise those rows rest on, checked rather than assumed. Without this
  # they pass on a host where cosign is absent for an unrelated reason and stop
  # meaning anything on one where it is not.
  rc_run env PATH="$bare_path" sh -c 'command -v cosign'
  rc_note "$([ "$RC_STATUS" -ne 0 ] && echo 0 || echo 1)" \
    "the cosign-absent rows below really run without cosign on PATH"

  d=$(fixture happy)
  rc_expect_status 0 "a complete, consistent release verifies" verify "$d" tl-linux-x64

  d=$(fixture no-sums); rm "$d/SHA256SUMS"
  rc_expect_status 1 "a missing SHA256SUMS is refused" verify "$d" tl-linux-x64
  d=$(fixture no-sums-bundle); rm "$d/SHA256SUMS.sigstore.json"
  rc_expect_status 1 "a missing SHA256SUMS bundle is refused" verify "$d" tl-linux-x64
  d=$(fixture no-asset-bundle); rm "$d/tl-linux-x64.sigstore.json"
  rc_expect_status 1 "a missing per-asset bundle is refused" verify "$d" tl-linux-x64
  d=$(fixture no-asset); rm "$d/tl-linux-x64"
  rc_expect_status 1 "a missing asset is refused" verify "$d" tl-linux-x64

  d=$(fixture unlisted); printf 'deadbeef  some-other-asset\n' > "$d/SHA256SUMS"
  rc_expect_status 1 "an asset absent from SHA256SUMS is refused" verify "$d" tl-linux-x64
  d=$(fixture malformed); printf 'not-a-digest  tl-linux-x64\n' > "$d/SHA256SUMS"
  rc_expect_status 1 "a non-hex digest line is refused" verify "$d" tl-linux-x64
  d=$(fixture truncated); printf 'abcdef  tl-linux-x64\n' > "$d/SHA256SUMS"
  rc_expect_output 1 "not the 64" "a short digest line is refused as truncated, not as tampering" \
    verify "$d" tl-linux-x64
  d=$(fixture mismatch); printf 'tampered\n' >> "$d/tl-linux-x64"
  rc_expect_output 1 "digest mismatch" "a digest mismatch is refused" verify "$d" tl-linux-x64

  # An uppercase sums file is valid and must verify. The hex check accepts A-F
  # deliberately, so comparing case-sensitively against lowercase output would
  # report correct bytes as tampering — the worst possible false positive.
  d=$(fixture uppercase)
  awk '{ print toupper($1) "  " $2 }' "$d/SHA256SUMS" > "$d/SHA256SUMS.up"
  mv "$d/SHA256SUMS.up" "$d/SHA256SUMS"
  rc_expect_status 0 "an uppercase SHA256SUMS verifies rather than reading as tampering" \
    verify "$d" tl-linux-x64

  # Signature verdicts, via the stub.
  d=$(fixture bad-signature)
  rc_expect_output 1 "did not verify against the pinned identity" "a rejected signature is refused" \
    env COSIGN_STUB_VERDICT=bad PATH="$work/bin:$PATH" "$self" "$d" tl-linux-x64

  # The escape hatch drops signatures and keeps digests.
  d=$(fixture skip-ok); rm "$d/SHA256SUMS.sigstore.json" "$d/tl-linux-x64.sigstore.json"
  rc_expect_status 0 "TL_INSTALL_SKIP_SIGNATURE=1 verifies without bundles" \
    env TL_INSTALL_SKIP_SIGNATURE=1 PATH="$bare_path" "$self" "$d" tl-linux-x64
  d=$(fixture skip-mismatch); rm "$d/SHA256SUMS.sigstore.json" "$d/tl-linux-x64.sigstore.json"
  printf 'tampered\n' >> "$d/tl-linux-x64"
  rc_expect_status 1 "TL_INSTALL_SKIP_SIGNATURE=1 still refuses a digest mismatch" \
    env TL_INSTALL_SKIP_SIGNATURE=1 PATH="$bare_path" "$self" "$d" tl-linux-x64

  # --require-signature is the release gate's mode: the escape is refused, not
  # honoured, because a gate that can be switched off by an inherited
  # environment variable is not a gate. Both arms — the variable set, and
  # cosign simply absent — must refuse.
  d=$(fixture require-vs-skip)
  rc_expect_output 1 "invoked with --require-signature" \
    "--require-signature refuses an inherited TL_INSTALL_SKIP_SIGNATURE" \
    env TL_INSTALL_SKIP_SIGNATURE=1 PATH="$work/bin:$PATH" "$self" --require-signature "$d" tl-linux-x64
  d=$(fixture require-no-cosign)
  rc_expect_output 1 "cannot fall back to a digest-only check" \
    "--require-signature refuses when cosign is absent" \
    env PATH="$bare_path" "$self" --require-signature "$d" tl-linux-x64
  d=$(fixture require-happy)
  rc_expect_status 0 "--require-signature still verifies a good release" \
    verify --require-signature "$d" tl-linux-x64

  # Without cosign and without the explicit opt-out, refuse rather than
  # silently degrade to a digest-only check.
  d=$(fixture no-cosign)
  rc_expect_output 1 "cosign not found" "a missing cosign is refused rather than skipped" \
    verify_bare "$d" tl-linux-x64

  # A host with no digest tool must say so, not report the artifact as
  # tampered. The two are the opposite diagnosis and send a reader to
  # completely different places; a nested command substitution used to hide
  # the difference by capturing the wrong status.
  # An empty PATH is not the scenario — the script needs dirname and pwd to
  # start at all. What is being modelled is a host where the digest tools
  # specifically are absent, so they are shadowed by stubs that fail the way
  # a missing command does.
  d=$(fixture no-digest-tool)
  nodigest="$work/nodigest"
  mkdir -p "$nodigest"
  for tool in sha256sum shasum; do
    printf '#!/bin/sh\nexit 127\n' > "$nodigest/$tool"
    chmod +x "$nodigest/$tool"
  done
  rc_expect_output 1 "digest check is mandatory" \
    "a broken digest tool refuses rather than producing an empty digest" \
    env PATH="$nodigest:$PATH" TL_INSTALL_SKIP_SIGNATURE=1 "$self" "$d" tl-linux-x64
  rc_note "$(! grep -q 'digest mismatch' "$RC_ERR" && echo 0 || echo 1)" \
    "the missing-tool refusal is not phrased as tampering"

  # A read-only asset directory is a legitimate place to verify from: immutable
  # media, a root-owned download. The verifier must not need to write there,
  # and must not lose its own message when it cannot.
  d=$(fixture read-only)
  chmod a-w "$d"
  rc_expect_output 0 "digest ok" "a read-only asset directory verifies" \
    verify "$d" tl-linux-x64
  printf 'not-a-digest  tl-linux-x64\n' > "$work/ro-sums" 2>/dev/null || true
  chmod u+w "$d"
  printf 'not-a-digest  tl-linux-x64\n' > "$d/SHA256SUMS"
  chmod a-w "$d"
  rc_expect_output 1 "not a hex digest" \
    "a refusal from a read-only directory still carries its message" \
    verify "$d" tl-linux-x64
  chmod u+w "$d"

  # The pin itself. These run the script against a substituted identity file,
  # so they check what happens when the *pin* is broken rather than when an
  # artifact is.
  # `pin_bytes` is written with `printf '%s'` and no trailing newline of its
  # own, so each case controls the file's bytes exactly — including whether it
  # ends in a newline, which is one of the malformations under test.
  pin_case() {
    # pin_case <name> <expected-status> <needle> <pin-bytes>
    name=$1; want=$2; needle=$3; content=$4
    d=$(fixture "pin-$(echo "$name" | tr ' /$^' '____')")
    alt_root="$work/alt-$(echo "$name" | tr ' /$^' '____')"
    mkdir -p "$alt_root/scripts/lib" "$alt_root/release"
    cp "$self" "$alt_root/scripts/"
    cp "$RC_LIB_SELF" "$alt_root/scripts/lib/"
    printf '%s' "$content" > "$alt_root/release/identity.pin"
    rc_expect_output "$want" "$needle" "$name" \
      env PATH="$work/bin:$PATH" "$alt_root/scripts/$(basename -- "$self")" "$d" tl-linux-x64
  }
  valid_expr='^https://github.com/x$'
  pin_case "an empty pin is refused" 1 "no issuer on its first line" ''
  pin_case "a pin with only an issuer is refused" 1 "no certificate identity expression" \
    'https://example.invalid
'
  pin_case "a pin with an empty issuer line is refused" 1 "no issuer on its first line" \
    "
$valid_expr
"
  pin_case "a pin with an empty expression line is refused" 1 "no certificate identity expression" \
    'https://example.invalid

'
  # A third line is refused rather than ignored: a reader that skipped it could
  # be handed a second, different pin below the one it used.
  pin_case "a pin with a third line is refused" 1 "more than two lines" \
    "https://example.invalid
$valid_expr
https://evil.invalid
"
  pin_case "a pin with an empty third line is refused" 1 "more than two lines" \
    "https://example.invalid
$valid_expr

"
  pin_case "a pin with trailing data and no newline is refused" 1 "more than two lines" \
    "https://example.invalid
$valid_expr
trailing"
  # A truncated write: two lines, but the second has no terminator. `read`
  # assigns what it got and then reports end-of-file, so a reader that ignored
  # its status would accept this — and disagree with release/Identity.lean,
  # which refuses it.
  pin_case "a pin whose last line is unterminated is refused" 1 "does not end with a newline" \
    "https://example.invalid
$valid_expr"
  # A carriage return rides into the value cosign is given and makes the
  # expression match nothing — a silent rejection of every genuine signature,
  # which looks exactly like tampering.
  pin_case "a pin with Windows line endings is refused" 1 "outside printable ASCII" \
    "$(printf 'https://example.invalid\r\n%s\r\n' "$valid_expr")"
  # Non-ASCII. release/Identity.lean refuses anything above U+007E, and under a
  # UTF-8 locale the shell's [[:print:]] does not — so this row is what shows
  # the two readers of one pin actually agreeing.
  pin_case "a pin carrying a non-ASCII byte is refused" 1 "outside printable ASCII" \
    "$(printf 'https://ex\303\251mple.invalid\n%s\n' "$valid_expr")"
  # A NUL, written straight into the file. It cannot travel through `pin_case`
  # at all: its content arrives as a shell argument, and an argument is a
  # NUL-terminated string — which is the same reason this verifier now counts
  # the file's own bytes instead of inspecting what `read` managed to store.
  # Before that it accepted a pin `tlrelease check-pin` refuses, so one pin had
  # two answers and only the stricter reader was ever going to say so.
  d=$(fixture pin-nul)
  alt_root="$work/alt-pin-nul"
  mkdir -p "$alt_root/scripts/lib" "$alt_root/release"
  cp "$self" "$alt_root/scripts/"
  cp "$RC_LIB_SELF" "$alt_root/scripts/lib/"
  printf 'https://example.invalid\000\n%s\n' "$valid_expr" > "$alt_root/release/identity.pin"
  rc_expect_output 1 "outside printable ASCII" "a NUL byte in the pin is refused" \
    env PATH="$work/bin:$PATH" "$alt_root/scripts/$(basename -- "$self")" "$d" tl-linux-x64
  rc_expect_output 1 "vanishes on its way into a shell variable" \
    "the NUL refusal says why the bytes are counted rather than read" \
    env PATH="$work/bin:$PATH" "$alt_root/scripts/$(basename -- "$self")" "$d" tl-linux-x64
  # An unanchored expression is the failure a text-equality drift guard cannot
  # see: it is well-formed, it verifies real artifacts, and it also accepts a
  # certificate whose identity merely contains this repository's.
  pin_case "an expression unanchored at the head is refused" 1 "not anchored at ^" \
    'https://example.invalid
https://github.com/x$
'
  # The tail anchor is the half this verifier used to drop. A tag name may
  # contain a slash, so trailing content past the pinned identity is reachable.
  pin_case "an expression unanchored at the tail is refused" 1 "not anchored at" \
    'https://example.invalid
^https://github.com/x
'
  # The pin is data, never sourced. A line that would be a command
  # substitution if it were ever evaluated must reach cosign as literal text —
  # so it is refused for its shape, not executed.
  pin_case "a pin whose expression is not anchored cannot execute either" 1 "not anchored at" \
    'https://example.invalid
$(touch '"$work"'/pin-was-evaluated)
'
  rc_expect_status 1 "no pin file was evaluated while being read" \
    test -e "$work/pin-was-evaluated"

  # The missing and unreadable pin, which is the difference between a check
  # that is weaker and a check that is absent.
  d=$(fixture pin-missing)
  alt_root="$work/alt-pin-missing"
  mkdir -p "$alt_root/scripts/lib" "$alt_root/release"
  cp "$self" "$alt_root/scripts/"
  cp "$RC_LIB_SELF" "$alt_root/scripts/lib/"
  rc_expect_output 1 "identity.pin not found" "a missing pin is refused" \
    env PATH="$work/bin:$PATH" "$alt_root/scripts/$(basename -- "$self")" "$d" tl-linux-x64
  printf '%s\n' 'https://example.invalid' "$valid_expr" > "$alt_root/release/identity.pin"
  chmod a-r "$alt_root/release/identity.pin"
  # root ignores the mode bit, so this row only means something unprivileged.
  if [ -r "$alt_root/release/identity.pin" ]; then
    echo "  ok   an unreadable pin is refused (skipped: this user can read a mode-000 file)"
  else
    rc_expect_output 1 "is not readable" "an unreadable pin is refused" \
      env PATH="$work/bin:$PATH" "$alt_root/scripts/$(basename -- "$self")" "$d" tl-linux-x64
  fi
  chmod u+r "$alt_root/release/identity.pin"

  # A verifier that cannot run must not be reported as tampering: the two
  # outcomes send a reader to entirely different places.
  d=$(fixture broken-verifier)
  rc_expect_output 1 "not evidence of tampering" \
    "a verifier that cannot run is not reported as tampering" \
    env COSIGN_STUB_VERDICT=broken PATH="$work/bin:$PATH" "$self" "$d" tl-linux-x64

  # Usage and argument handling: exit 2, distinct from a verification refusal.
  d=$(fixture usage)
  rc_expect_status 2 "no arguments is a usage error" verify
  rc_expect_status 2 "an unknown flag is a usage error" verify --bogus
  rc_expect_status 2 "--selftest with extra arguments is a usage error" verify --selftest extra
  rc_expect_status 2 "a directory with no assets named is a usage error" verify "$d"
  rc_expect_status 2 "--require-signature with no assets named is a usage error" \
    verify --require-signature "$d"
  rc_expect_output 1 "is not a directory" "a nonexistent directory refuses with a naming message" \
    verify "$work/no-such-dir" tl-linux-x64
  rc_expect_output 1 "for example" "the not-a-directory message shows the expected invocation" \
    verify "$work/no-such-dir" tl-linux-x64

  # What was actually passed to cosign, from the stub's own log of the happy
  # path. The transparency-log check is not ours to skip, and the bundle the
  # proof lives in has to be named on every call.
  if [ -s "$work/cosign-argv" ]; then
    if grep -q 'insecure-ignore-tlog' "$work/cosign-argv"; then
      rc_note 1 "cosign is never invoked with a transparency-log bypass"
    else
      rc_note 0 "cosign is never invoked with a transparency-log bypass"
    fi
    calls=$(grep -c 'verify-blob' "$work/cosign-argv" || true)
    bundles=$(grep -c -- '--bundle' "$work/cosign-argv" || true)
    if [ "$calls" -ge 2 ] && [ "$calls" = "$bundles" ]; then
      rc_note 0 "every cosign call names a bundle ($calls calls)"
    else
      rc_note 1 "every cosign call names a bundle ($calls verify-blob calls, $bundles with --bundle)"
    fi
    # Which blobs, not just how many calls. An aggregate count is satisfied by
    # the sums-file call alone, so deleting the per-asset check would pass it.
    : > "$work/cosign-blobs"
    d=$(fixture blob-coverage)
    rc_run verify "$d" tl-linux-x64
    if grep -qx SHA256SUMS "$work/cosign-blobs" && grep -qx tl-linux-x64 "$work/cosign-blobs"; then
      rc_note 0 "cosign is handed both the sums file and each asset"
    else
      rc_note 1 "cosign is handed both the sums file and each asset (saw: $(tr '\n' ' ' < "$work/cosign-blobs"))"
    fi
  else
    rc_note 1 "cosign was never invoked, so the signature checks did not run"
  fi

  rc_selftest_end "This verifier no longer refuses what it claims to refuse — repair it before trusting anything it accepts."
}

require_signature=0
case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
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
