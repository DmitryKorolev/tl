# Release prerequisites

Everything the release pipeline depends on that does not live in this
repository. Writing `environment: release` in a workflow does not create a
protected environment; declaring trusted publishing in a comment does not
register it with npm. Each item below is state configured somewhere else, and
the pipeline is only as strong as the weakest of them.

`scripts/check-release-prereqs.sh` checks what can be checked from a shell with
`gh` authenticated. What it cannot check is listed here with an owner and a
procedure, and carried in the Trusted section of
[overview.md](overview.md) — a dependency that is neither verified nor
recorded is the one that fails at the worst moment.

## Before the first release, once

### 0. The repository must be public

Everything below assumes it. GitHub Releases are the source of truth for
artifacts (ADR-0006), and a private repository serves its release assets only
to authenticated clients with access: an anonymous `GET` of
`https://github.com/DmitryKorolev/tl/releases/latest` answers **404**. That is
not a configuration detail, it is the whole distribution story —

- `install.sh` resolves the latest tag from that redirect and downloads every
  asset from `/releases/download/<tag>/`. Both 404 for a user.
- `Formula/tl.rb` downloads its binary, its Sigstore bundle and the notice from
  the same place, so `brew install tl` cannot work.
- `VERIFYING.md` tells a user to download the asset, `SHA256SUMS` and the
  bundles. They cannot.
- The npm packages would still install — npm does not care where the binaries
  came from — but the release they are meant to be checkable against would be
  unreachable, which removes the property the npm job exists to preserve.

Deployment protection rules are also a paid feature on private repositories
(free on public ones), so the `release` environment's required reviewers and
`v*` deployment-tag rule — the whole of section 2 — may not be configurable at
all while the repository is private. Confirm that before relying on them.

So: make the repository public, or decide deliberately that this release is
npm-only and record that decision in ADR-0006 — it would retire the installer,
the Homebrew tap and the published verification procedure, which is a change to
what tl distributes rather than a deferral.

### 1. Bootstrap the five npm packages

npm configures trusted publishing **per package**, and only for a package that
already exists. None of `@taskloop/tl`, `@taskloop/tl-bin-darwin-arm64`,
`@taskloop/tl-bin-darwin-x64`, `@taskloop/tl-bin-linux-arm64` or
`@taskloop/tl-bin-linux-x64` exists yet, so the first tagged release cannot
authenticate: it would publish the GitHub Release and the Homebrew formula and
then fail at `npm publish`, leaving the release red with its artifacts already
public.

There is no way to pre-register trust for a name that does not exist, so the
2FA publish is manual. Everything around it is not:

```sh
scripts/npm-bootstrap.sh /tmp/tl-bootstrap
```

That builds the five placeholder packages at version `0.0.0`, each carrying
`LICENSE`, `THIRD-PARTY-LICENSES`, a README explaining what it is, and an
executable that exits non-zero saying so; validates all five tarballs actually
contain those files; and prints the exact `npm publish` commands. Do not
hand-roll this. The obvious reading of "publish 0.0.0 from a local checkout"
does not work: the checked-in manifests say `0.1.0`, so it would consume the
real first release number; the platform directories hold no binary and no
licence files until `npm-pack.sh` stages them, so the tarballs would contain a
README and a manifest and nothing else; and the default dist-tag is `latest`,
so those empty placeholders would be what `npm install @taskloop/tl` resolved
to until the first real release.

Then:

1. Run the printed `npm publish … --tag bootstrap` commands under 2FA, from an
   account that owns the `@taskloop` scope. The `bootstrap` tag is deliberate —
   no user resolves it.
2. On npmjs.com, for each package, add a trusted publisher: this repository,
   the workflow `.github/workflows/release.yml`, and the `release` environment.
   The environment must match: both `sign` and `publish-npm` declare
   `environment: release`, and npm treats the environment as part of the
   trusted-publisher configuration, so a publisher registered without one — or
   with a different one — will not authenticate.
3. Remove any classic automation token that could publish these packages, so
   the OIDC path is the only one.
4. Run `scripts/check-release-prereqs.sh` and confirm the npm rows pass.
5. Only then create the first release tag.

The placeholder `0.0.0` versions stay published: unpublishing is restricted and
would in any case free nothing. They are never a `latest` dist-tag target.

One consequence of publishing over OIDC, worth knowing before a retry: trusted
publishing authorizes `npm publish` and no other registry mutation, so the
release job cannot move a dist-tag. It sets the tag as part of publishing, and
on a resumed run it *reads* the tag and stops with the exact `npm dist-tag add`
command if it points somewhere else. That command is a manual, 2FA step by
necessity, not by choice.

### 2. Create and protect the `release` environment

The `sign` and `publish-npm` jobs both declare `environment: release`. That
declaration is inert until the environment exists and carries protection rules.
Without them, anyone who can create a tag can cause this workflow to sign —
with an identity every verifier accepts — whatever commit that tag points at.

`publish-npm` names it for a second reason as well: npm treats the environment
as part of a trusted publisher's configuration, and GitHub only puts one into
the OIDC subject for a job that references it, so the name here and the name
registered on npmjs.com must agree.

In repository settings → Environments → `release`:

- **Required reviewers**: at least one, and not the person who pushed the tag
  where the platform allows that distinction.
- **Deployment branches and tags**: restrict to the tag pattern `v*`, so a
  branch push can never enter this environment.

### 3. Protect the `v*` tags with a ruleset

Independently of the environment, a repository ruleset targeting tags matching
`v*` should restrict who may create, update and delete them. The workflow's
ancestry check — that the tagged commit is on `origin/main` — is a backstop and
not a substitute: it sees what the tag points at, never who pushed it.

### 4. Create the Homebrew tap and its credential

`DmitryKorolev/homebrew-tap` must exist with a `Formula/` directory, and the
`HOMEBREW_TAP_TOKEN` secret must hold a token with write access to it.
`GITHUB_TOKEN` cannot write to another repository. A stable release now fails
if this secret is missing, rather than warning and exiting zero — a green
release that quietly did not update a promised channel is worse than a red one.

## Before every release

- The tag is a SemVer `v` tag whose version matches every copy
  (`scripts/check-release-version.sh --tag <tag>` — also run by the release
  policy on the tagged commit).
- The tagged commit is on `main`. The `sign` job enforces this.
- `scripts/check-release-prereqs.sh` passes.

## What the checker cannot see

Recorded here and in [overview.md](overview.md) as carried assumptions, because
a check that cannot run must not be silently absent:

`scripts/check-release-prereqs.sh` reads more than this table once claimed. It
inspects the actual rule *types* on the `release` environment (a
required-reviewers rule with at least one reviewer, and a deployment policy
whose tag patterns cover `v*`), and each tag ruleset's target, enforcement
state, ref conditions and whether it carries a creation restriction — because a
count of protection rules is satisfied by a wait timer and a count of rulesets
by an unrelated branch rule. It also distinguishes "not found" from "could not
read", so an API failure is reported as unchecked rather than as absent.

What remains genuinely out of reach:

| Assumption | Why it cannot be checked here | Owner |
|---|---|---|
| The required reviewer is not the same person who pushes the tag | The API exposes who may approve, not who will push; on a single-maintainer repository the two coincide by definition | repository admin |
| Each npm package's trusted publisher names *this* workflow and environment | npm exposes no public API for a package's trusted-publisher configuration | npm org owner |
| No classic automation token can still publish the packages | Same | npm org owner |
| `HOMEBREW_TAP_TOKEN` grants write access to the tap and nothing else | A secret's scope is not readable from a workflow | repository admin |
| GitHub Actions, npm and Sigstore behave as documented | Third-party infrastructure (ADR-0014) | — |

Each is a *live* assumption, not a one-time one: an environment's protection
rules can be removed, and a trusted publisher can be reconfigured, without
anything in this repository changing. Re-run the audit in section 1–4 whenever
repository or npm-organization permissions change.
