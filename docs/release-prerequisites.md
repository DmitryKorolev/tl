# Release prerequisites

Everything the release pipeline depends on that does not live in this
repository. Writing `environment: release` in a workflow does not create a
protected environment; declaring trusted publishing in a comment does not
register it with npm. Each item below is state configured somewhere else, and
the pipeline is only as strong as the weakest of them.

The audit checks what can be checked from a shell with `gh` authenticated. What
it cannot check is listed here with an owner and a procedure, and carried in the
Trusted section of [overview.md](overview.md) — a dependency that is neither
verified nor recorded is the one that fails at the worst moment.

## Which of these apply

Not all of them, and not always the same ones. A prerequisite belongs to a
distribution channel, and `release/plan.json` says which channels a release
publishes. A section below whose channel is disabled produces **no prerequisite** — no row
reading *missing*, and none reading *unchecked*. "Missing" is a defect report,
and a channel nobody is publishing has no defect. It does produce one visible
row, in a class of its own, so that a reader can see the plan was consulted
rather than the section forgotten.

`scripts/check-release-prereqs.sh` reads `release/plan.json` and applies that
rule. A deferred channel's rows are reported as **deferred**, counted in their
own class, and never contribute to the verdict — so the signing job's audit
passes on a release that publishes through neither npm nor Homebrew. Enabling a
channel in the plan is what turns its rows back into prerequisites, which is
also the moment its bootstrap has to be done.

A plan the audit cannot *read* is a third answer again: those rows come back
*unchecked*, never *deferred*. "Off" is a decision somebody made, and a file
nobody could parse is not evidence of one.

For **v0.1.0** — the GitHub Release and the installer (ADR-0006) — that means
sections 0, 2 and 3 apply. Section 1 (npm) and section 4 (the Homebrew tap)
belong to channels deferred to v0.2.0 and are not prerequisites of the first
release. They are written up now because enabling a channel is exactly the
moment its bootstrap has to be done, and a procedure discovered then is a
procedure improvised.

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
- Once npm is enabled, its packages would still install — npm does not care
  where the binaries came from — but the release they are meant to be checkable
  against would be unreachable, which removes the property the npm job exists
  to preserve.

Deployment protection rules are also a paid feature on private repositories
(free on public ones), so the `release` environment's required reviewers and
`v*` deployment-tag rule — the whole of section 2 — may not be configurable at
all while the repository is private. Confirm that before relying on them.

So: make the repository public. This one has no alternative under the v0.1.0
plan, because both enabled channels serve from the release assets — there is no
release without it. It is the single prerequisite the audit cannot work around
and the first thing to do.

### 1. Bootstrap the five npm packages — *only when the npm channel is enabled*

Not a prerequisite of v0.1.0: `release/plan.json` has npm disabled, so the
release workflow runs no npm job and the audit reports a single `deferred` row
for this whole section rather than five missing packages. This section
is the procedure for the release that turns the channel on.

npm configures trusted publishing **per package**, and only for a package that
already exists. None of `@taskloop/tl`, `@taskloop/tl-bin-darwin-arm64`,
`@taskloop/tl-bin-darwin-x64`, `@taskloop/tl-bin-linux-arm64` or
`@taskloop/tl-bin-linux-x64` exists yet, so the first tagged release with this
channel enabled cannot authenticate: it would publish the GitHub Release and
then fail at `npm publish`, leaving the release red with its artifacts already
public. Deferring the channel rather than racing that bootstrap is what keeps
the first release from carrying an unrelated way to fail.

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

### 4. Create the Homebrew tap and its credential — *only when the Homebrew channel is enabled*

Not a prerequisite of v0.1.0, for the same reason as section 1: with the
channel disabled there is no `publish-homebrew` job, and the audit reports a
single `deferred` row for this section rather than auditing the tap.

`DmitryKorolev/homebrew-tap` must exist with a `Formula/` directory, and the
`HOMEBREW_TAP_TOKEN` secret must hold a token with write access to it.
`GITHUB_TOKEN` cannot write to another repository. A stable release now fails
if this secret is missing, rather than warning and exiting zero — a green
release that quietly did not update a promised channel is worse than a red one.

Store it as a **repository** secret, not an environment one. `release` is the
only environment this document names, so an environment secret is the natural
reading — but `publish-homebrew` declares no `environment:`, so
`secrets.HOMEBREW_TAP_TOKEN` would resolve there to the empty string and the
job would refuse for a secret that exists. Putting that job behind the `release`
environment instead would gate it with the same approval as signing, at the
cost of a third manual approval per release; that is a deliberate trade to make
when the channel is enabled, not a detail to discover mid-release.

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
whose tag patterns cover `v*` and which admits no branch deployments at all),
and each tag ruleset's target, enforcement state, ref conditions and whether it
carries a creation restriction. "Ref conditions" means the include set covers
*every* `v*` tag — `~ALL`, `refs/tags/*` or `refs/tags/v*`, with no exclude
list — rather than merely containing a pattern that begins `refs/tags/v`: a
ruleset naming the single tag `v1.0.0`, or the one line `v1.*`, restricts that
tag or that line and leaves the rest of the namespace open. This matters
because a
count of protection rules is satisfied by a wait timer and a count of rulesets
by an unrelated branch rule. It also distinguishes "not found" from "could not
read" on the rows where the two have different remedies — each npm package, the
Homebrew tap, and the `release` environment separate a 404 from any other
status, and a tag ruleset the API could not read is reported as unchecked
rather than counted as absent. The repository-visibility and deployment-policy
rows report any failure as unchecked without separating the 404, which is the
same fail-closed direction. An unreachable registry or a 5xx is never reported
as a prerequisite nobody created. Collapsing those two would abort a
correct release on a transient 5xx, with a remedy telling the operator to
create something that already exists.

What remains genuinely out of reach:

The `Applies` column follows the same rule as the sections: an assumption
belonging to a disabled channel is not being carried, because nothing is
relying on it.

| Assumption | Why it cannot be checked here | Owner | Applies |
|---|---|---|---|
| The required reviewer is not the same person who pushes the tag | The API exposes who may approve, not who will push; on a single-maintainer repository the two coincide by definition | repository admin | always |
| Each npm package's trusted publisher names *this* workflow and environment | npm exposes no public API for a package's trusted-publisher configuration | npm org owner | npm enabled |
| No classic automation token can still publish the packages | Same | npm org owner | npm enabled |
| `HOMEBREW_TAP_TOKEN` grants write access to the tap and nothing else | A secret's scope is not readable from a workflow | repository admin | Homebrew enabled |
| GitHub Actions and Sigstore behave as documented | Third-party infrastructure (ADR-0014) | — | always |
| npm behaves as documented | Third-party infrastructure (ADR-0014) | — | npm enabled |

Each is a *live* assumption, not a one-time one: an environment's protection
rules can be removed, and a trusted publisher can be reconfigured, without
anything in this repository changing. Re-run the audit whenever repository or
npm-organization permissions change — and on the release that enables a
channel, because that is when its rows start being carried.
