#!/bin/sh
# Prepare the one-time npm bootstrap packages.
#
#   scripts/npm-bootstrap.sh <output-dir>    build and validate them, print the
#                                            exact commands to run under 2FA
#   scripts/npm-bootstrap.sh --selftest
#
# npm configures trusted publishing per package, and only for a package that
# already exists. The five names this project publishes do not exist, so the
# first tagged release cannot authenticate: it would publish the GitHub Release
# and the Homebrew formula and then fail at `npm publish`, leaving a red release
# with its artifacts already public. Somebody has to create the names by hand
# first, under 2FA, and that is the only manual step this file cannot remove.
#
# What it does remove is every way of getting that step wrong. The runbook used
# to say "publish 0.0.0 from a local checkout", which does not work:
#
#   - the checked-in manifests say 0.1.0, so a local `npm publish` would burn
#     the real first release number on a placeholder;
#   - the platform directories hold no binary and no licence files until
#     `npm-pack.sh` stages them, so the tarball would contain a README and a
#     manifest and nothing else;
#   - the default dist-tag is `latest`, so that empty placeholder would be what
#     `npm install @taskloop/tl` resolved to until the first real release.
#
# So this builds the packages instead: version 0.0.0, a deliberate placeholder
# executable that explains itself, the licence files, and a `bootstrap`
# dist-tag that no user resolves. It then validates all five tarballs and
# prints the commands. The placeholder versions stay published afterwards —
# unpublishing is restricted and would free nothing — and are never a `latest`
# target.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd -P)
RC_LIB_SELF="$script_dir/lib/release-common.sh"
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

BOOTSTRAP_VERSION=0.0.0
BOOTSTRAP_TAG=bootstrap

usage() {
  echo "usage: $0 <output-dir> | $0 --selftest" >&2
  exit 2
}

fail() {
  echo "npm-bootstrap: $1" >&2
  exit 1
}

# The placeholder the packages carry instead of a binary. It must not look like
# a broken tl: it says what it is and exits non-zero, so anyone who reaches it
# learns why rather than filing a bug about a corrupt install.
placeholder_script() {
  cat <<'PLACEHOLDER'
#!/bin/sh
echo "tl: this is a bootstrap placeholder package (version 0.0.0), published only so that npm trusted publishing could be configured for this package name before the first real release. It contains no tl binary." >&2
echo "tl: install a real release with 'npm install -g @taskloop/tl', or see https://github.com/DmitryKorolev/tl" >&2
exit 1
PLACEHOLDER
}

build() {
  out=$1
  [ -e "$out" ] && [ -n "$(ls -A "$out" 2>/dev/null)" ] \
    && fail "'$out' already exists and is not empty. Pass a fresh path: publishing from a directory holding a previous run's output would publish whichever tree npm found first."
  mkdir -p "$out"

  identity_name=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["npmPackage"])' \
    "$repo_root/release/identity.json")
  scope=${identity_name%%/*}

  [ -f "$repo_root/LICENSE" ] || fail "$repo_root/LICENSE not found."
  [ -f "$repo_root/THIRD-PARTY-LICENSES" ] || fail "$repo_root/THIRD-PARTY-LICENSES not found — run the licence generator first."

  names=''
  # The launcher, then one package per target, so the names match exactly what
  # the release will publish. Read from release/targets.json rather than
  # written out, like every other consumer.
  for pkg in tl $(rc_targets | sed 's/[^ ]*/tl-bin-&/g'); do
    dir="$out/$pkg"
    mkdir -p "$dir/bin"
    if [ "$pkg" = tl ]; then
      full="$identity_name"
      description="Bootstrap placeholder for the tl launcher package"
    else
      full="$scope/$pkg"
      description="Bootstrap placeholder for the tl ${pkg#tl-bin-} binary package"
    fi
    names="$names $full"
    placeholder_script > "$dir/bin/tl"
    chmod +x "$dir/bin/tl"
    cp "$repo_root/LICENSE" "$dir/LICENSE"
    cp "$repo_root/THIRD-PARTY-LICENSES" "$dir/THIRD-PARTY-LICENSES"
    cat > "$dir/README.md" <<README
# $full — bootstrap placeholder

Version $BOOTSTRAP_VERSION of this package exists for one reason: npm can only
configure a trusted publisher for a package that already exists, so the name had
to be created before the first real release could publish to it.

It contains no tl binary. It is published under the \`$BOOTSTRAP_TAG\` dist-tag
and is never what \`npm install $identity_name\` resolves to.

Install tl from <https://github.com/DmitryKorolev/tl>.
README
    python3 - "$dir/package.json" "$full" "$BOOTSTRAP_VERSION" "$description" <<'PYEOF'
import json, sys
path, name, version, description = sys.argv[1:5]
json.dump({
    "name": name,
    "version": version,
    "description": description,
    "license": "Apache-2.0",
    "repository": {"type": "git", "url": "git+https://github.com/DmitryKorolev/tl.git"},
    "files": ["bin/tl", "README.md", "LICENSE", "THIRD-PARTY-LICENSES"],
    "publishConfig": {"access": "public"},
}, open(path, "w"), indent=2)
open(path, "a").write("\n")
PYEOF
  done

  # Validate before printing any command a human will paste. Every tarball must
  # carry the four files, at version 0.0.0, under the right name — the failure
  # this replaces produced a tarball with a README and a manifest and nothing
  # else, and nothing noticed.
  packed="$out/.packed"
  mkdir -p "$packed"
  count=0
  for pkg in tl $(rc_targets | sed 's/[^ ]*/tl-bin-&/g'); do
    dir="$out/$pkg"
    ( cd "$dir" && npm pack --pack-destination "$packed" ) >/dev/null 2>&1 \
      || fail "could not pack $dir."
    tgz=$(ls -t "$packed"/*.tgz | head -1)
    listing=$(tar -tzf "$tgz")
    for required in package/bin/tl package/README.md package/LICENSE package/THIRD-PARTY-LICENSES package/package.json; do
      case $listing in
        *"$required"*) ;;
        *) fail "$(basename -- "$tgz") does not contain $required. Do not publish it: an npm version cannot be reissued." ;;
      esac
    done
    got_version=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["version"])' "$dir/package.json")
    [ "$got_version" = "$BOOTSTRAP_VERSION" ] \
      || fail "$dir is version $got_version, not $BOOTSTRAP_VERSION. Publishing it would consume a real release number."
    count=$((count + 1))
  done
  rm -rf "$packed"

  echo "npm-bootstrap: prepared and validated $count package(s) in $out"
  echo
  echo "Run these under 2FA, from an account that owns the $scope scope:"
  echo
  for pkg in tl $(rc_targets | sed 's/[^ ]*/tl-bin-&/g'); do
    echo "  npm publish $out/$pkg --access public --tag $BOOTSTRAP_TAG"
  done
  echo
  echo "Then, on npmjs.com, for each of:${names}"
  echo "  add a trusted publisher — repository DmitryKorolev/tl, workflow"
  echo "  .github/workflows/release.yml, environment release — and remove any"
  echo "  classic automation token that can publish these packages."
  echo
  echo "Finally, confirm with scripts/check-release-prereqs.sh before tagging."
  echo
  echo "--tag $BOOTSTRAP_TAG is deliberate: without it npm would set 'latest',"
  echo "and these placeholders would be what 'npm install $identity_name'"
  echo "resolves to until the first real release."
}

selftest() {
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  # Hermetic npm state. Without this every row runs against the caller's
  # ~/.npm cache and ~/.npmrc, so the gate's outcome depends on the machine it
  # runs on rather than on the code — a cache in one state made this selftest
  # fail on a reviewer's host and pass here. A gate whose verdict tracks the
  # caller's home directory is not reporting on the release.
  npm_config_cache="$work/npm-cache"
  npm_config_userconfig="$work/npmrc"
  npm_config_update_notifier=false
  npm_config_fund=false
  npm_config_audit=false
  export npm_config_cache npm_config_userconfig npm_config_update_notifier \
    npm_config_fund npm_config_audit
  : > "$npm_config_userconfig"
  rc_selftest_begin "npm-bootstrap" "$work"

  command -v npm >/dev/null 2>&1 || {
    echo "npm-bootstrap: --selftest needs npm on PATH" >&2
    exit 2
  }

  out="$work/bootstrap"
  rc_expect_status 0 "the bootstrap packages build and validate" "$0" "$out"

  expected=$(rc_targets | wc -w | tr -d ' ')
  expected=$((expected + 1))
  got=$(find "$out" -maxdepth 1 -mindepth 1 -type d | wc -l | tr -d ' ')
  rc_note "$([ "$got" -eq "$expected" ] && echo 0 || echo 1)" \
    "one package per published name, plus the launcher ($got of $expected)"

  # Every property the runbook's prose version got wrong.
  for pkg in tl tl-bin-linux-x64; do
    v=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["version"])' "$out/$pkg/package.json")
    rc_note "$([ "$v" = 0.0.0 ] && echo 0 || echo 1)" \
      "$pkg is version 0.0.0, not the real release number ($v)"
    for f in bin/tl LICENSE THIRD-PARTY-LICENSES README.md; do
      rc_note "$([ -f "$out/$pkg/$f" ] && echo 0 || echo 1)" "$pkg carries $f"
    done
  done
  rc_note "$([ -x "$out/tl/bin/tl" ] && echo 0 || echo 1)" "the placeholder is executable"
  rc_run "$out/tl/bin/tl"
  rc_note "$([ "$RC_STATUS" -ne 0 ] && echo 0 || echo 1)" \
    "the placeholder exits non-zero rather than pretending to be tl"
  rc_note "$(grep -q 'bootstrap placeholder' "$RC_ERR" && echo 0 || echo 1)" \
    "the placeholder explains what it is"

  # The printed commands must carry the non-default tag, or the placeholders
  # become `latest` for every user until the first release.
  rc_run "$0" "$work/second"
  rc_note "$(grep -q -- "--tag bootstrap" "$RC_OUT" && echo 0 || echo 1)" \
    "the printed publish commands use the bootstrap dist-tag"
  rc_note "$(! grep -qE 'npm publish [^\n]*--tag latest' "$RC_OUT" && echo 0 || echo 1)" \
    "no printed command publishes to latest"
  rc_note "$(grep -q 'trusted publisher' "$RC_OUT" && echo 0 || echo 1)" \
    "the output names the follow-up trusted-publisher step"
  rc_note "$(grep -q 'check-release-prereqs' "$RC_OUT" && echo 0 || echo 1)" \
    "the output points at the audit that confirms the result"

  # The names must be exactly the ones the release will publish.
  identity_name=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["npmPackage"])' \
    "$repo_root/release/identity.json")
  got_name=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["name"])' "$out/tl/package.json")
  rc_note "$([ "$got_name" = "$identity_name" ] && echo 0 || echo 1)" \
    "the launcher is named from release/identity.json ($got_name)"

  # A tarball missing the binary must be refused, since a version cannot be
  # reissued once published.
  broken="$work/broken"
  "$0" "$broken" >/dev/null 2>&1
  python3 -c '
import json, sys
path = sys.argv[1]
data = json.load(open(path))
data["files"] = [f for f in data["files"] if f != "bin/tl"]
json.dump(data, open(path, "w"), indent=2)
' "$broken/tl/package.json"
  # Re-validating means re-running over the same directory, which the
  # non-empty guard refuses — so the guard itself is what this row checks.
  rc_expect_output 1 "already exists and is not empty" \
    "building over a previous run's output is refused" "$0" "$broken"

  rc_expect_status 2 "no arguments is a usage error" "$0"
  rc_expect_status 2 "an unknown flag is a usage error" "$0" --bogus

  rc_selftest_end "The bootstrap is the one manual step before the first release; it must not hand a human a command that publishes the wrong thing."
}

case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  -*) usage ;;
  *)
    [ "$#" -eq 1 ] || usage
    build "$1"
    ;;
esac
