#!/bin/sh
# Publish the staged npm packages, idempotently.
#
#   scripts/npm-publish.sh <staging-dir> <dist-tag>
#   scripts/npm-publish.sh --plan <staging-dir> <dist-tag>   decide, publish nothing
#   scripts/npm-publish.sh --selftest
#
# npm versions are immutable: a version cannot be republished, and unpublishing
# does not free it. The previous shape — a `for` loop of `npm publish` under
# `set -e` — therefore had no recovery. Two platform packages publish, the
# third fails on a network blip, the launcher (published last, so that it never
# resolves to packages that do not exist yet) never goes out at all, and a
# re-run dies immediately on E403 for the first package. What is left is a
# permanently half-published version whose only remedy is to burn the number
# and re-tag.
#
# Cross-registry publication cannot be transactional — GitHub, npm and the
# Homebrew tap have no shared commit — so the property to aim for is not
# all-or-nothing. It is: **every step is safe to retry, and repeated execution
# converges the registry to the staged tree.** That is what this script does.
# For each package:
#
#   1. Ask the registry what is there.
#   2. Absent            → publish it.
#   3. Present, and its contents match what we staged → nothing to do.
#   4. Present, and different → stop, as an immutable conflict. Publishing
#      cannot fix it and neither can this script; a human has to decide.
#
# "Matches" is compared over the *contents*, not the tarball bytes: gzip output
# is not stable across npm versions or platforms, so a byte comparison would
# report a spurious conflict on a re-run from a different runner image. Each
# tarball is unpacked and every member compared by path and SHA-256, which is
# the property actually at stake — does the published package contain the
# binary this release signed.
#
# First release: trusted publishing is configured per package on npmjs.com, and
# npm only allows that for a package that already exists. The five packages
# must therefore be bootstrapped by hand before the first tag; see
# docs/release-prerequisites.md. This script reports that case specifically
# rather than letting npm's authentication error stand as the explanation.
set -eu

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
RC_LIB_SELF="$script_dir/lib/release-common.sh"
# shellcheck source=lib/release-common.sh
. "$RC_LIB_SELF"

usage() {
  echo "usage: $0 [--plan] <staging-dir> <dist-tag> | $0 --selftest" >&2
  exit 2
}

fail() {
  echo "npm-publish: $1" >&2
  exit 1
}

# The manifest field <2> of the package staged at <1>.
manifest_field() {
  python3 -c 'import json,sys; print(json.load(open(sys.argv[1] + "/package.json"))[sys.argv[2]])' \
    "$1" "$2"
}

# content_digest <dir> <out> — write <dir>'s contents to <out> as sorted
# "<sha256>  <relative path>" lines. The comparison unit: a published package
# matches the staged one when these agree.
#
# Written to a file and reported by exit status rather than printed into a
# command substitution. `$( … )` discards the digest tool's status, and a
# `sha256sum` that is on PATH but cannot run — a broken coreutils, a wrapper,
# a permission denial — then produced an *empty* digest for every file while
# this function still exited 0. The comparison degenerated to comparing path
# lists, so a published package holding entirely different bytes at the same
# paths was reported as "already published and matches this staging tree", and
# the release converged on the wrong artifact.
content_digest() {
  cd__dir=$1
  cd__out=$2
  ( cd "$cd__dir" || exit 1
    # The `while` is the last stage of the pipeline and so runs in a subshell;
    # `exit 1` there ends that subshell, which is the pipeline's status, which
    # is this subshell's status, which is what the caller checks.
    find . -type f | LC_ALL=C sort | while IFS= read -r cd__file; do
      cd__digest=$(rc_sha256_of "$cd__file") || exit 1
      printf '%s  %s\n' "$cd__digest" "${cd__file#./}"
    done ) > "$cd__out"
}

# Ask the registry whether <name>@<version> exists. Sets RS_STATE to `absent`
# or `present`; returns non-zero when the answer is neither, so a network or
# authentication problem is never read as "absent" and turned into a publish
# attempt against a version that may already exist.
#
# Sets a variable rather than printing one, and the caller must not wrap it in
# `$( … )`: a command substitution runs in a subshell, so an `exit` inside it
# ends only that subshell. Written the other way, this function reported the
# problem and the loop carried on regardless.
registry_state() {
  rs_name=$1
  rs_version=$2
  RS_STATE=''
  if npm view "${rs_name}@${rs_version}" version >"$RC_OUT" 2>"$RC_ERR"; then
    RS_STATE=present
    return 0
  fi
  # npm reports a missing package *or* a missing version as E404.
  if grep -q 'E404\|404 Not Found\|is not in this registry\|No match found' "$RC_ERR"; then
    RS_STATE=absent
    return 0
  fi
  sed 's/^/    /' "$RC_ERR" >&2
  return 1
}

publish_one() {
  po_dir=$1
  po_tag=$2
  po_plan=$3
  po_name=$(manifest_field "$po_dir" name)
  po_version=$(manifest_field "$po_dir" version)

  registry_state "$po_name" "$po_version" \
    || fail "could not determine whether ${po_name}@${po_version} already exists, and publishing without knowing that risks either a spurious E403 or a silent gap. The usual causes are a network failure or an expired token. Re-run once; if it persists, check the registry status and the workflow's OIDC configuration."
  case $RS_STATE in
    absent)
      if [ "$po_plan" -eq 1 ]; then
        echo "  would publish ${po_name}@${po_version} (--tag ${po_tag})"
        planned_publish=$((planned_publish + 1))
        return 0
      fi
      echo "  publishing ${po_name}@${po_version} (--tag ${po_tag})"
      if npm publish "$po_dir" --provenance --access public --tag "$po_tag" \
           >"$RC_OUT" 2>"$RC_ERR"; then
        sed 's/^/    /' "$RC_OUT"
        published=$((published + 1))
        return 0
      fi
      sed 's/^/    /' "$RC_ERR" >&2
      # The first-release case, called out because npm's own message is an
      # authentication error and the actual cause is a missing prerequisite.
      if grep -q 'ENEEDAUTH\|E401\|401 Unauthorized\|Unable to authenticate\|trusted publish' "$RC_ERR"; then
        fail "publishing ${po_name}@${po_version} failed to authenticate. If this is the first release, that is expected and not a workflow bug: npm configures trusted publishing per package and only for a package that already exists, so all five packages must be bootstrapped by hand before the first tag. Follow docs/release-prerequisites.md, then re-run this job — it is idempotent, so anything already published is left alone."
      fi
      fail "publishing ${po_name}@${po_version} failed. Nothing about this run is lost: re-run the job and it will skip whatever already published and continue from here."
      ;;
    present)
      # Immutable, so the only question is whether what is there is what we
      # meant to put there.
      staged_unpacked="$work/staged/$po_name"
      remote_unpacked="$work/remote/$po_name"
      mkdir -p "$staged_unpacked" "$remote_unpacked"

      ( cd "$po_dir" && npm pack --pack-destination "$work/packed" ) >"$RC_OUT" 2>"$RC_ERR" \
        || { sed 's/^/    /' "$RC_ERR" >&2; fail "could not pack the staged ${po_name} to compare it with the published version."; }
      staged_tgz=$(ls -t "$work/packed"/*.tgz | head -1)
      tar -xzf "$staged_tgz" -C "$staged_unpacked"

      ( cd "$remote_unpacked" && npm pack "${po_name}@${po_version}" ) >"$RC_OUT" 2>"$RC_ERR" \
        || { sed 's/^/    /' "$RC_ERR" >&2; fail "${po_name}@${po_version} exists on the registry but could not be downloaded for comparison. Re-run; if it persists, compare it by hand before publishing anything else."; }
      remote_tgz=$(ls "$remote_unpacked"/*.tgz | head -1)
      tar -xzf "$remote_tgz" -C "$remote_unpacked"
      rm -f "$remote_tgz"

      # Digested before either is compared, and a digest that could not be
      # taken stops the publication rather than answering the question with
      # whatever it managed to produce.
      content_digest "$staged_unpacked/package" "$work/staged.list" \
        || fail "could not digest the staged ${po_name} to compare it with the published version. The digest tool on PATH is present but not working, and a comparison it cannot make must not be answered either way — an npm version is immutable, so publishing over a mismatch is not recoverable. Repair coreutils or shasum and re-run."
      content_digest "$remote_unpacked/package" "$work/remote.list" \
        || fail "could not digest the published ${po_name} to compare it with the staging tree. Same cause and same remedy as above; nothing has been published by this run."
      if cmp -s "$work/staged.list" "$work/remote.list"; then
        echo "  ${po_name}@${po_version} is already published and matches this staging tree"
        # The dist-tag is separate state and can lag behind a partial run, so
        # it is checked rather than assumed. **Read, not written**: OIDC
        # trusted publishing authorizes `npm publish` and nothing else, so
        # `npm dist-tag add` has no credential in this job and would fail on
        # every resumed run — turning the one path that exists to recover a
        # partial publish into a guaranteed failure. On the first publish the
        # tag is set by `npm publish --tag`, which is why this case only ever
        # arises on a retry.
        #
        # Reading it is a public registry GET and needs no credential. If it
        # already points where it should, the channel has converged and there
        # is nothing to do. If it does not, this script cannot fix it and says
        # so with the exact command a human can run under 2FA.
        current=''
        if npm view "$po_name" "dist-tags.${po_tag}" >"$RC_OUT" 2>"$RC_ERR"; then
          current=$(tr -d ' \t\r\n' < "$RC_OUT")
        fi
        if [ "$current" = "$po_version" ]; then
          echo "    '${po_tag}' already points at ${po_version}"
        elif [ "$po_plan" -eq 1 ]; then
          echo "    '${po_tag}' points at '${current:-<unset>}', not ${po_version} — would need a manual dist-tag repair"
        else
          fail "${po_name}@${po_version} is published, but the '${po_tag}' dist-tag points at '${current:-<unset>}'. Users resolving that tag get the wrong version. This job publishes over OIDC trusted publishing, which authorizes 'npm publish' and no other registry mutation, so it cannot move the tag: run it by hand under 2FA — 'npm dist-tag add ${po_name}@${po_version} ${po_tag}' — and re-run this job to confirm."
        fi
        skipped=$((skipped + 1))
        return 0
      fi

      diff -u "$work/staged.list" "$work/remote.list" >&2 || true
      fail "${po_name}@${po_version} is already on the registry and its contents differ from what this release staged (the listing above is staged vs published, by SHA-256). npm versions are immutable — this cannot be resolved by publishing, and unpublishing does not free the number. Either this version was published from a different build, or the staging tree is not the one that produced it. Decide deliberately: bump the version everywhere and re-tag, or confirm the published package is correct and skip it."
      ;;
  esac
}

run() {
  staging=$1
  dist_tag=$2
  plan=$3

  [ -d "$staging" ] || fail "'$staging' is not a directory — stage the packages first with scripts/npm-pack.sh."
  case $dist_tag in
    latest | next) ;;
    *) fail "'$dist_tag' is not a dist-tag this pipeline uses. Stable releases publish under 'latest' and prereleases under 'next' (ADR-0006); anything else would make 'npm install @taskloop/tl' resolve somewhere unintended." ;;
  esac
  command -v npm >/dev/null 2>&1 || fail "npm is not on PATH."

  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
  mkdir -p "$work/packed" "$work/staged" "$work/remote"
  rc_capture_into "$work"

  published=0
  skipped=0
  planned_publish=0

  # Platform packages first, launcher last. The launcher declares them as
  # exact-version optional dependencies, so publishing it first would leave a
  # window in which installing it resolves nothing to run. On a resumed run the
  # order matters more, not less: it is what makes a partial state always a
  # prefix of a good one.
  for dir in "$staging"/tl-bin-*; do
    [ -d "$dir" ] || continue
    publish_one "$dir" "$dist_tag" "$plan"
  done
  [ -d "$staging/tl" ] || fail "$staging/tl is missing — the launcher package is what users install."
  publish_one "$staging/tl" "$dist_tag" "$plan"

  if [ "$plan" -eq 1 ]; then
    echo "npm-publish: --plan only. $planned_publish package(s) would be published, $skipped already match."
    return 0
  fi
  echo "npm-publish: $published published, $skipped already present and matching, under the '$dist_tag' dist-tag"
}

selftest() {
  work_outer=$(mktemp -d)
  trap 'rm -rf "$work_outer"' EXIT
  # Hermetic npm state. Without this every row runs against the caller's
  # ~/.npm cache and ~/.npmrc, so the gate's outcome depends on the machine it
  # runs on rather than on the code — a cache in one state made this selftest
  # fail on a reviewer's host and pass here. A gate whose verdict tracks the
  # caller's home directory is not reporting on the release.
  npm_config_cache="$work_outer/npm-cache"
  npm_config_userconfig="$work_outer/npmrc"
  npm_config_update_notifier=false
  npm_config_fund=false
  npm_config_audit=false
  export npm_config_cache npm_config_userconfig npm_config_update_notifier \
    npm_config_fund npm_config_audit
  : > "$npm_config_userconfig"
  rc_selftest_begin "npm-publish" "$work_outer"

  # A stub npm. It records what it was asked to do and answers from a fixture
  # registry laid out as <registry>/<escaped name>/<version>/package/…, so the
  # comparison path runs over real files rather than a mocked verdict.
  bin="$work_outer/bin"
  mkdir -p "$bin"
  cat > "$bin/npm" <<STUB
#!/bin/sh
log="$work_outer/npm-log"
registry="$work_outer/registry"
printf '%s\n' "\$*" >> "\$log"
esc() { printf '%s' "\$1" | tr '/@' '__'; }
case "\$1" in
  view)
    spec=\$2
    field=\${3:-version}
    case "\$field" in
      dist-tags.*)
        tag=\${field#dist-tags.}
        if [ -f "\$registry/\$(esc "\$spec")/tag-\$tag" ]; then
          cat "\$registry/\$(esc "\$spec")/tag-\$tag"
          exit 0
        fi
        exit 1
        ;;
    esac
    name=\${spec%@*}
    version=\${spec##*@}
    if [ -d "\$registry/\$(esc "\$name")/\$version" ]; then
      echo "\$version"
      exit 0
    fi
    echo "npm error code E404" >&2
    echo "npm error 404 Not Found - GET https://registry.npmjs.org/\$name - Not found" >&2
    exit 1
    ;;
  publish)
    dir=\$2
    [ -n "\${NPM_STUB_PUBLISH_FAILS:-}" ] && { echo "\${NPM_STUB_PUBLISH_ERROR:-npm error code E500}" >&2; exit 1; }
    name=\$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1] + "/package.json"))["name"])' "\$dir")
    version=\$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1] + "/package.json"))["version"])' "\$dir")
    dest="\$registry/\$(esc "\$name")/\$version/package"
    mkdir -p "\$dest"
    ( cd "\$dir" && tar -cf - . ) | ( cd "\$dest" && tar -xf - )
    # publish --tag X sets the dist-tag as part of publishing, which is the
    # only way this job can set one at all.
    want_tag=latest
    prev=''
    for a in "\$@"; do
      [ "\$prev" = "--tag" ] && want_tag=\$a
      prev=\$a
    done
    mkdir -p "\$registry/\$(esc "\$name")"
    printf '%s\n' "\$version" > "\$registry/\$(esc "\$name")/tag-\$want_tag"
    echo "+ \$name@\$version"
    exit 0
    ;;
  pack)
    # \`npm pack <spec>\` downloads; \`npm pack --pack-destination D\` packs cwd.
    dest=.
    spec=''
    shift
    while [ \$# -gt 0 ]; do
      case \$1 in
        --pack-destination) dest=\$2; shift 2 ;;
        -*) shift ;;
        *) spec=\$1; shift ;;
      esac
    done
    if [ -n "\$spec" ]; then
      name=\${spec%@*}
      version=\${spec##*@}
      src="\$registry/\$(esc "\$name")/\$version"
      [ -d "\$src" ] || { echo "npm error code E404" >&2; exit 1; }
      ( cd "\$src" && tar -czf - package ) > "\$(esc "\$name")-\$version.tgz"
    else
      name=\$(python3 -c 'import json,sys; print(json.load(open("package.json"))["name"])')
      version=\$(python3 -c 'import json,sys; print(json.load(open("package.json"))["version"])')
      tmp=\$(mktemp -d)
      mkdir -p "\$tmp/package"
      tar -cf - . | ( cd "\$tmp/package" && tar -xf - )
      ( cd "\$tmp" && tar -czf - package ) > "\$dest/\$(esc "\$name")-\$version.tgz"
      rm -rf "\$tmp"
    fi
    exit 0
    ;;
  dist-tag)
    # Modelled on what OIDC trusted publishing actually authorizes: the
    # publish verb, and no other registry mutation. The previous stub answered
    # success here, which is why a script that ran dist-tag add on every
    # resumed run looked correct in the selftest and would have failed on the
    # first real retry. A mock must not be able to do something production
    # cannot. (No backticks anywhere in this heredoc: it is unquoted, so a
    # backtick in a comment is command substitution and runs.)
    echo "npm error code ENEEDAUTH" >&2
    echo "npm error need auth This command requires you to be logged in to https://registry.npmjs.org/" >&2
    exit 1
    ;;
esac
exit 0
STUB
  chmod +x "$bin/npm"

  # Staging trees built by the real stager, over stub "binaries" — the layout
  # this script publishes is the one npm-pack.sh produces, not a hand-made
  # approximation of it.
  assets="$work_outer/assets"
  mkdir -p "$assets"
  for target in $(rc_targets); do
    printf '#!/bin/sh\necho "stub %s"\n' "$target" > "$assets/tl-$target"
    chmod +x "$assets/tl-$target"
  done
  stage_at() {
    "$script_dir/npm-pack.sh" "$1" "$assets" >/dev/null 2>&1 \
      || { echo "npm-publish: --selftest could not stage the packages into $1" >&2; exit 1; }
  }

  staging="$work_outer/staging"
  stage_at "$staging"

  pub() { PATH="$bin:$PATH" "$0" "$@"; }

  rc_expect_status 0 "a first publish, with an empty registry, publishes everything" \
    pub "$staging" latest
  count=$(grep -c '^publish ' "$work_outer/npm-log" || true)
  rc_note "$([ "$count" -eq 5 ] && echo 0 || echo 1)" \
    "all five packages were published ($count)"
  # The launcher must go last: it pins the platform packages by exact version,
  # so publishing it first leaves a window where it resolves nothing to run.
  last=$(grep '^publish ' "$work_outer/npm-log" | tail -1)
  rc_note "$(printf '%s' "$last" | grep -q 'staging/tl --' && echo 0 || echo 1)" \
    "the launcher is published last, after the platform packages it pins"

  # The whole point: running it again must converge, not fail.
  : > "$work_outer/npm-log"
  rc_expect_status 0 "a re-run over an already-published version succeeds" pub "$staging" latest
  rc_note "$(! grep -q '^publish ' "$work_outer/npm-log" && echo 0 || echo 1)" \
    "a re-run publishes nothing a second time"
  rc_note "$(! grep -q '^dist-tag' "$work_outer/npm-log" && echo 0 || echo 1)" \
    "a re-run never calls dist-tag, which OIDC cannot authorize"
  rc_note "$(grep -q 'dist-tags.latest' "$work_outer/npm-log" && echo 0 || echo 1)" \
    "a re-run reads the dist-tag instead, which needs no credential"

  # A partial failure, then a resume. This is the scenario that used to strand
  # the version permanently.
  rm -rf "$work_outer/registry"
  : > "$work_outer/npm-log"
  partial="$work_outer/partial"
  stage_at "$partial"
  first_pkg=$(ls -d "$partial"/tl-bin-* | head -1)
  PATH="$bin:$PATH" "$0" --plan "$partial" latest >/dev/null 2>&1 || true
  # Publish exactly one package by hand, simulating a run that died after it.
  ( cd "$first_pkg" && PATH="$bin:$PATH" npm publish "$first_pkg" >/dev/null 2>&1 )
  : > "$work_outer/npm-log"
  rc_expect_status 0 "a resumed run after a partial publish succeeds" pub "$partial" latest
  again=$(grep -c '^publish ' "$work_outer/npm-log" || true)
  rc_note "$([ "$again" -eq 4 ] && echo 0 || echo 1)" \
    "the resumed run publishes only the four that were missing (published $again)"

  # A published version whose contents differ is an immutable conflict: it must
  # stop, because neither publishing nor unpublishing can resolve it.
  conflict="$work_outer/conflict"
  stage_at "$conflict"
  target_dir=$(ls -d "$conflict"/tl-bin-* | head -1)
  printf '#!/bin/sh\necho "a different binary"\n' > "$target_dir/bin/tl"
  rc_expect_output 1 "immutable" "a published version with different contents is a conflict" \
    pub "$conflict" latest
  rc_expect_output 1 "cannot be resolved by publishing" \
    "the conflict message says publishing cannot fix it" pub "$conflict" latest

  # A digest tool that is on PATH but cannot run. The comparison it answers
  # decides whether an immutable version is published over, so a digest nobody
  # could take must stop the run rather than settle it. Before this the tool's
  # status was discarded by `$( … )` and every file digested to the empty
  # string, which reduced the comparison to comparing path *names*: a published
  # package holding entirely different bytes reported as matching.
  broken_digest="$work_outer/broken-digest"
  mkdir -p "$broken_digest"
  cp "$bin/npm" "$broken_digest/npm"
  for tool in sha256sum shasum; do
    printf '#!/bin/sh\necho "%s: cannot read that file" >&2\nexit 1\n' "$tool" \
      > "$broken_digest/$tool"
    chmod +x "$broken_digest/$tool"
  done
  rc_expect_output 1 "could not digest the staged" \
    "a digest tool that cannot run stops the comparison instead of answering it" \
    env PATH="$broken_digest:$PATH" "$0" "$conflict" latest
  rc_expect_output 1 "not recoverable" \
    "the broken-digest refusal says why the comparison cannot be skipped" \
    env PATH="$broken_digest:$PATH" "$0" "$conflict" latest

  # A publish that fails for an authentication reason names the bootstrap.
  rm -rf "$work_outer/registry"
  fresh="$work_outer/fresh"
  stage_at "$fresh"
  rc_expect_output 1 "bootstrapped by hand before the first tag" \
    "an authentication failure names the first-release bootstrap" \
    env NPM_STUB_PUBLISH_FAILS=1 NPM_STUB_PUBLISH_ERROR="npm error code ENEEDAUTH" \
        PATH="$bin:$PATH" "$0" "$fresh" latest
  # …and any other publish failure says the run is resumable, because it is.
  rm -rf "$work_outer/registry"
  rc_expect_output 1 "re-run the job" "another publish failure says the run can be resumed" \
    env NPM_STUB_PUBLISH_FAILS=1 NPM_STUB_PUBLISH_ERROR="npm error code E500" \
        PATH="$bin:$PATH" "$0" "$fresh" latest

  # A published version whose dist-tag points elsewhere is not a silent partial
  # success: users resolving that tag keep getting the previous version. It is
  # also not something this job can repair — OIDC authorizes `npm publish` and
  # no other registry mutation — so it must stop and hand over the exact
  # command a human can run under 2FA.
  rm -rf "$work_outer/registry"
  PATH="$bin:$PATH" "$0" "$fresh" latest >/dev/null 2>&1
  a_pkg=$(ls -d "$fresh"/tl-bin-* | head -1)
  a_name=$(manifest_field "$a_pkg" name)
  printf '9.9.9\n' > "$work_outer/registry/$(printf '%s' "$a_name" | tr '/@' '__')/tag-latest"
  rc_expect_output 1 "dist-tag points at '9.9.9'" \
    "a published version whose dist-tag points elsewhere stops the run" \
    pub "$fresh" latest
  rc_expect_output 1 "npm dist-tag add" \
    "the dist-tag message hands over the exact manual command" \
    pub "$fresh" latest
  rc_expect_output 1 "no other registry mutation" \
    "the message says why this job cannot fix it itself" \
    pub "$fresh" latest

  # And the capability model is load-bearing: if the script ever calls
  # `dist-tag` again, the stub refuses it the way OIDC does, so the row above
  # cannot quietly start passing for the wrong reason.
  rc_run env PATH="$bin:$PATH" npm dist-tag add "x@1.0.0" latest
  rc_note "$([ "$RC_STATUS" -ne 0 ] && echo 0 || echo 1)" \
    "the stub refuses dist-tag, as OIDC trusted publishing does"

  # An unreadable registry answer must not be read as "absent" and turned into
  # a publish attempt against a version that may already exist.
  cat > "$bin/npm-broken" <<'BROKEN'
#!/bin/sh
echo "npm error network request to https://registry.npmjs.org failed" >&2
exit 1
BROKEN
  chmod +x "$bin/npm-broken"
  broken_bin="$work_outer/broken-bin"
  mkdir -p "$broken_bin"
  cp "$bin/npm-broken" "$broken_bin/npm"
  rc_expect_output 1 "could not determine whether" \
    "a registry error is not read as 'this version does not exist'" \
    env PATH="$broken_bin:$PATH" "$0" "$fresh" latest

  # --plan decides without publishing.
  rm -rf "$work_outer/registry"
  : > "$work_outer/npm-log"
  rc_expect_status 0 "--plan reports what it would do" pub --plan "$fresh" latest
  rc_note "$(! grep -q '^publish ' "$work_outer/npm-log" && echo 0 || echo 1)" \
    "--plan publishes nothing"

  # Argument handling.
  rc_expect_status 2 "no arguments is a usage error" pub
  rc_expect_status 2 "one argument is a usage error" pub "$fresh"
  rc_expect_status 2 "an unknown flag is a usage error" pub --bogus "$fresh" latest
  rc_expect_output 1 "not a dist-tag this pipeline uses" "an unexpected dist-tag is refused" \
    pub "$fresh" beta
  rc_expect_status 1 "a missing staging directory is refused" pub "$work_outer/nope" latest

  rc_selftest_end "Do not publish with this script until it is repaired: an npm version cannot be reissued."
}

plan=0
case "${1-}" in
  '') usage ;;
  --selftest)
    [ "$#" -eq 1 ] || usage
    selftest
    ;;
  --plan)
    plan=1
    shift
    [ "$#" -eq 2 ] || usage
    run "$1" "$2" "$plan"
    ;;
  -*) usage ;;
  *)
    [ "$#" -eq 2 ] || usage
    run "$1" "$2" "$plan"
    ;;
esac
