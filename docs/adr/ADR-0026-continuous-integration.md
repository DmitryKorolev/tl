# ADR-0026 — Continuous integration: platform, gates, and caches

- Status: Accepted (trust gate revised 2026-08-01)
- Date: 2026-07-01

## Context

The coverage mandate in ADR-0004 needs a mechanized enforcement point. A
warning-free Lean build checks every elaborated proof, but it does not reject a
new `axiom`, and stored `.olean` files are trusted when imported. ADR-0006 also
requires the test suite to run at the git 2.17 runtime floor.

The first implementation of the trust gate grew into a source-text scanner, a
custom probe command, a verdict parser, a cache-deletion wrapper, and a
checkout-mutating test script. Repeated review found lexical holes and stale
cache/wiring hazards. The implementation duplicated parts of Lean's grammar
and used count floors as approximations for facts Lean and the filesystem can
report exactly.

## Decision

### Platform and job graph

CI uses GitHub Actions hosted Ubuntu and macOS runners. Third-party actions are
pinned to full commit hashes.
Pushes to every branch run CI, so a candidate commit can receive required
checks before it reaches protected `main` when pull requests are disabled. The
branch filter excludes tag pushes; release tags use the separate release
workflow. Only `main` pushes save the shared toolchain and dependency caches;
protecting `main` is a repository-setting prerequisite, not something those
save guards enforce. The git-floor job separately uses branch-scoped caching
for its hash-pinned Git build.

The graph is:

1. `release-policy`, building the separately scoped `tlrelease` executable;
2. `hermetic-release`, running the GitHub-only policy and retained adapters in
   a runtime-stripped inner container;
3. `homebrew-formula`, needing Homebrew rather than a Lean toolchain;
4. `build-and-test` on Ubuntu and macOS;
5. `git-floor`, after the build matrix, using the Ubuntu artifacts.

Only `git-floor` carries a `needs:`. The policy jobs run independently
of the product build so a policy failure and a build failure are both visible
from one run. The lexical task-ID
gate was a fifth job on the same reasoning until it became `tlrelease
task-id-lint`; a Lean binary cannot run in a job with no Lean, so it is a step
of `build-and-test` now, beside the dependency boundary that moved for the same
reason.

That move costs what the separate job bought: a leak is no longer reported in
seconds, it is reported after the matrix builds, and a build that fails does not
report it at all. The trade is deliberate. The alternative is a second,
toolchain-free implementation of the same lexical rule, which is the copy the
gate spent a change removing — and a rule stated twice is the failure this
project keeps finding, where a rule reported late is a delay.

ADR-0028 changes one edge during the typed release-machinery cutover. Once the
build stamp is produced by `tlrelease`, the release workflow first builds and
tests that separately scoped executable in `gates`, hands it off with a
same-run file-set-hash comparison, and only then runs `stamp`; product build
jobs remain downstream of the resulting stamp. The bootstrap comparison cannot
be delegated to the binary being compared. The gated binary is staged as
`release-tool/tlrelease`, and an unprivileged runner step binds
`hashFiles('release-tool/tlrelease')` in its `env:`, writes the distinctly
named `releaseToolFileSetHash` step output through `$GITHUB_OUTPUT`, and the job
output maps that value; `hashFiles` is deliberately not used directly in a job
output expression. The upload action names that same non-hidden staged path;
the stage, upload, and hash source are pinned together. Each side's pinned
pattern must match exactly one file, and the consumer compares its post-download
`hashFiles('tool/tlrelease')` result
with the producer value before running `/bin/chmod 0755 tool/tlrelease`. This
proves only same-run transport equality and is never compared with a raw
SHA-256 digest. This is now the active graph. The typed workflow-stamp command
owns the clean-source/version checks, stamp write and framed output batch.

`release-policy` runs `tlrelease policy --profile ci --strict`; the release
workflow runs the release profile. `release/Policy.lean` owns the ordered
registry and both execution and listing use its plan-aware selection function.
`--strict` makes a missing tool a failure, and a skipped gate is never counted
as passing. The historical shell runner, single-gate adapters and parity
snapshot are deleted. The registry requires the exact shell inventory, invokes
ShellCheck directly, and checks formula syntax through the native Homebrew
command.

`hermetic-release` is the dynamic half of ADR-0028's dependency budget. One
outer job builds the native runner and invokes `tlrelease hermetic --root .`,
the same public command used locally on Linux and macOS. Lean prepares the
inputs and runs `lake -KreleaseOnly=true build tlreleaseStatic --wfail` in a
digest-pinned Ubuntu builder, using the checkout's actual Lake configuration.
The explicit release-only mode omits unrelated proof-library downloads; normal
product builds and the trust verifier keep both pinned dependencies.
That preparation container may fetch the toolchain and dependencies; it has
no publication credentials. The runner downloads hash-pinned static tools,
constructs the declared adapter fixtures, records their digests, and launches
one digest-pinned `alpine/git` evidence container. The complete Podman argv is
pinned in `Tests/HermeticTests.lean`: no network, read-only image and checkout,
capabilities dropped, no privilege gain, no container-engine socket, and separate
writable scratch and libc-observation mounts. Rootless Podman maps the runner
to container uid/gid 0 with `--userns host --user 0:0`;
the inner run checks that this is the scratch owner. This permits reading the
image inventory, including root-owned directories, without host root or a
recursive ownership change to the checkout. `--read-only-tmpfs=false` disables
Podman's otherwise implicit writable temporary mounts. Nothing
from the outer job's environment or credentials is passed implicitly.
Per-command arguments, output and failures remain under `.lake/hermetic/`.
Temporary containers are removed on success and failure. A zero status without
the worker's final completion verdict refuses. The native completion predicate
has a characterization theorem; preparation, evidence collection and cleanup
are tested I/O. `Tests/ReleaseDriftTests.lean` pins CI's invocation of this
shared runner, rather than reconstructing its process policy from shell text.

The inner run checks both PATH lookup and the image filesystem for `python`,
`python3`, `ruby`, `brew`, `node`, and `npm`; checks the declared positive tool
inventory and the handoff manifest; then runs the strict release profile. That
profile executes the installer and standalone-verifier public suites. The same
outer step packs the npm package with scripts disabled and extracts its launcher;
the inner run drives those exact post-pack bytes through supported and
refused OS, architecture, libc, package-layout, mode, symlink, stream, exit,
process-identity and signal cases. Its curl, cosign, uname, sysctl and shasum
fixtures all record reachability. The real npm and Homebrew acceptance jobs stay
outside this container because their channel-native runtimes are the thing
those jobs are meant to exercise.

The gates it holds are the release-machinery checks the Lean suite cannot
express:

- `tlrelease identity-check` checks what the pinned cosign
  certificate expression *means* — that it accepts this repository's release
  workflow on a SemVer tag and rejects adversarial neighbours (a repository
  whose name contains ours, a different workflow in this repository, an
  unescaped-dot match, a non-SemVer tag). `Tests/ReleaseTests.lean` guards that
  every operative copy carries the same text, which is drift; meaning needs a
  regular-expression engine the Lean suite does not have, and an expression
  that is anchored and well-formed while matching the wrong repository would
  pass a text-equality guard and hollow out the fail-closed verifier
  (ADR-0014 T3).
- The stamp generator's refusal paths are exercised in `lake exe tltest`,
  against real git checkouts on disk: the three that matter are all git's — a
  repository setting that hides untracked files, a source tree sitting inside an
  unrelated checkout, and a git that cannot report at all — and a stub could be
  made to say anything about any of them. The gate here is the drift check:
  `tlrelease stamp --root .` regenerated and diffed, because three documents
  state as fact that the checked-in copy is the development stamp and nothing
  but a comparison enforces it.
- `tlrelease artifact-verifier-selftest --root .` exercises the artifact
  verifier's, against fabricated missing, malformed, mismatched, and
  rejected-signature inputs, and against a verifier that cannot run — which
  must not be reported as tampering. That script is the VERIFYING.md procedure
  as code, run by the release workflow before publishing, so the documented
  steps are the executed ones and a release cannot ship artifacts its own
  published procedure would reject. `install.sh` performs the same checks with
  its own embedded copy of the pin, because a piped installer has no checkout
  to read; `Tests/ReleaseTests.lean` guards that copy against drift.
- A regeneration comparison on `Tl/Build/Stamp.lean`. Three places state as
  fact that the committed copy is the development stamp; without it a stamped
  copy swept in by `git commit -a` would make every build from that tree claim
  `clean build — commit <stale>`. It is a `tltest` assertion rather than a step
  in this script, because the generator is `tlrelease stamp` and this script
  runs in a job with no Lean toolchain by design — the same reason
  `version-consistency` and `platform-classification` are not gates here. The
  assertion runs the command over a copy of this repository's inputs rather
  than rebuilding the provenance in the test, so a regression in the command's
  own derivation fails it; and it reads the committed bytes with `git show`
  rather than the working tree, so a job that has already stamped — the release
  workflow does — cannot fail it. `--list` names it under "covered by a
  different required gate", so a reader auditing the policy is not told the
  development stamp is unenforced.
- `tlrelease npm-selftest` packs and really installs the npm packages with the
  real client, then drives the launcher through them: the entry list and the
  modes npm publishes, the installed `bin` symlink, argument transparency, exit
  status, and the absent-package diagnosis. It is the second of the channel's
  two nets and covers only what a stub cannot answer — what npm itself does.
  The channel's own decisions are `tlrelease`'s and are covered against a stub
  client in `lake exe tltest`, which is what lets them run where the release
  profile may not reach npm at all.
- `tlrelease installer-selftest --root .` runs the unchanged installer against a fabricated local
  release, covering each refusal path including a rejected signature, a digest
  mismatch, a missing bundle, an unwritable install directory, and every
  unsupported platform.
- `tlrelease version-consistency` compares every place the release version
  is written by hand: the tag, `productVersion`, the Lake package version and
  the pinned literal in `Tests/ReleaseTests.lean`. Nothing compared them before,
  though two error messages instructed the operator to keep the lakefile in
  lockstep with a value neither of them read. The five npm manifests are not
  among them: they are rendered by `tlrelease npm-manifests` at a placeholder
  version, and holding a generated file to a value it deliberately does not
  carry would be a comparison about the generator rather than about the
  release.
- `tlrelease platform-classification` holds the uname mapping that `install.sh`
  and the npm launcher each carry inline — neither can read this repository when
  it runs — to the typed authority in `release/Platform.lean`, which is itself
  cross-checked against `release/targets.json` in both directions. What is
  compared is the classification rather than the wording, which differs
  legitimately between the two (their messages name different tools) but a
  disagreement
  about which system is which would ship the wrong binary.
- Neither generator whose output is signed is a gate in this script. The SBOM
  is `tlrelease sbom`, the release manifest is `tlrelease manifest` and
  `tlrelease manifest-verify`, and each build leg's record is
  `tlrelease build-metadata`; all of them are Lean, and their refusals — a
  candidate whose digest disagrees with what its leg recorded, a record from
  another run, a directory holding an asset nothing describes — are covered by
  `Tests/ReleaseToolTests.lean` under `lake exe tltest`, a required gate on the
  same commit in both workflows. This script runs in a job with no Lean
  toolchain by design, so invoking the built binary here would trade an answer
  in seconds for the whole build matrix. `--list` names them under what a
  different gate covers, so the one place that answers "what does the policy
  cover" does not fall silent about them.
- `Tests/ReleaseToolTests.lean` checks the *reporting* of `tlrelease prereqs` —
  that an unreadable row is counted as unchecked and never as a pass — and
  drives `collectRows` itself over an injected `GithubClient` answering from a
  table, so
  each branch that decides a release has a row: a deferred channel producing no
  prerequisites, a 404 kept apart from any other status, a deployment policy
  that also admits branches, a tag ruleset that covers one tag rather than the
  namespace, and a ruleset the API could not read. The *live* audit is
  deliberately not in this gate: it talks to npm and to the GitHub API, and a
  network check on every commit would make CI flaky and teach people to ignore
  it. It runs in the release workflow instead, before anything is signed.
- `shellcheck -S warning` over every tracked shell file, found by shebang and
  extension rather than listed — a list stops covering a new script silently,
  and the gate refuses outright if the discovery pattern matches nothing.
- A `ruby -c` gate over the tracked formula and the rendered fixtures beside it.
  It skips visibly rather than failing when ruby is absent, and it is an early
  signal rather than a verdict: real Homebrew is the acceptance authority and
  the `homebrew-formula` job below is where it runs.
- actionlint over both workflow files. A workflow cannot validate itself: if
  GitHub refuses to load `release.yml`, nothing runs to say so, and the failure
  would surface only when someone pushed a tag. actionlint shells out to
  shellcheck for every `run:` block and silently does without it when it is
  absent, so the policy script reports a present actionlint with no shellcheck
  as a *skip* rather than a pass — three real shell defects in these workflows
  survived precisely because the runner has shellcheck and the machines they
  were tried on did not.
- A separate `homebrew-formula` job loads, styles and audits four formulae
  with real Homebrew: the tracked placeholder, a fully pinned release, one
  with the Best-effort target dropped, and a prerelease one — Homebrew's version
  scanner drops the SemVer suffix and resolves that formula's urls differently,
  so the job also asserts each resolved url names the tag it should. `ruby -c` proves a formula parses
  and says nothing about whether Homebrew accepts it — a formula whose stable
  spec has no url for the running platform passes `ruby -c` and makes Homebrew
  raise on *load*, for every brew command against the tap.

Each of those scripts carries a `--selftest` arm on one reasoning: a checker
that quietly stopped detecting would pass forever, so it proves it can still
fail before its silence is believed. What replaces that arm for a gate that has
moved into `tlrelease` is a suite in `lake exe tltest` driving the command over
planted inputs — the same evidence, from outside the thing it tests.

### The policy has two profiles, because it gates two different things

`tlrelease policy --profile release --strict` is the release gate: exactly the
checks standing between a defect and a *published* artifact through the channels
`release/plan.json` enables — the GitHub Release, the installer, and the
artifact verifier. It is what `release.yml` runs on the tagged commit and what a
rehearsal runs.

`tlrelease policy --profile ci --strict` is repository hygiene: it includes
Homebrew formula parsing and the native npm suite even while their channels are
disabled. The registry invokes npm validation with cache, userconfig and
globalconfig paths beneath a regular-file blocker; subprocess tests observe
all three poisoned inputs and cleanup. This closes the former unowned npm
workflow-step gap. Tests cover all four npm/Homebrew enablement combinations
through the public policy listing as well as the shared selection function.
The exact shell inventory is mandatory in both profiles; ShellCheck receives its
three survivors directly. `tlrelease homebrew-syntax --root .` discovers every
tracked formula fixture and runs Ruby separately for each, refusing an empty set.

The split is a prerequisite of ADR-0006's dependency budget rather than a
tidying of it. That budget forbids `python`, `python3`, `ruby`, `brew`, `node`
and `npm` on any path reachable from an enabled channel, and one profile could
not both enforce the budget and keep the deferred channels covered: measured
under failing PATH shims, thirteen of the old policy's twenty-one gates invoked
`python3` or `ruby`. Five were the npm and Homebrew gates, which the split
removes from the release profile outright; the rest were v0.1 gates whose
generators have since moved into `tlrelease`.

A gate for a disabled channel is *absent* from the release profile rather than
skipped-as-passing, because a skip is a report about this run and absence is a
statement about the release. Selection is a typed decision from the plan:
enabling a channel adds its gate to the release profile. Both execution and
listing use that same decision, whose characterization theorem is pinned.
The current hermetic job targets the GitHub-only plan. Enabling npm or Homebrew
also requires separating that runtime-stripped evidence from the enabled
channel's packaging environment; adding those runtimes to the stripped image
would erase the dependency-boundary claim it exists to test.

A gate whose *tool* is absent is a different decision, owned by `release/Policy.lean`.
Its characterization theorems and injected-runner/subprocess tests cover tool
present/absent, strict/non-strict, and passed/failed, including multiple required
tools. A strict run refuses a missing tool; a non-strict run reports a skip.

The dependency budget is enforced by the exact three-adapter shell inventory,
typed registry and privileged-workflow schemas, public process corpora, and the
pinned runtime-stripped Linux job described in ADR-0028. The migration lexer,
command-spelling corpus, PATH-shim runner and selftests, shell gate harnesses,
and temporary profile-parity oracle have been deleted together. Their historical
split mattered because the lexer saw literals on untaken paths while the shims
observed dynamic commands resolved through PATH. Neither saw computed absolute
interpreter paths. The hermetic image removes those interpreters altogether;
actual Darwin-only installer paths retain the explicit overview.md assumption.
The narrow shell inventory reads names and shebangs, not executable shell bodies.

`.github/workflows/release.yml` is a separate workflow, triggered by a SemVer
tag ([ADR-0006](ADR-0006-distribution-and-platforms.md)). It re-runs the whole
native policy against the plan, plus the separate version-consistency gate,
against the tagged commit rather than
trusting that the tag happens to point at a commit CI already saw, then builds
the four native artifacts and signs them. Signing runs directly in that workflow because GitHub's OIDC
certificate names the workflow that requested it, and `release/identity.json`
pins that name — indirection through a reusable workflow would change the
identity every verifier checks.

The earlier `lint` job carried the source greps this ADR replaces, plus an
advisory task-ID-leakage warning, and went away with them. The task-ID check
returns as a gating step now that its pattern and exclusion set are a pinned
contract rather than a preference. It is `tlrelease task-id-lint --root .`,
which states the rule once — `release/TaskId.lean` — where the shell it
replaced stated it three times:

- The class: the ADR-0007 display affix followed by at least `shortIdFloor` = 4
  Crockford base32 digits (`0-9 a-z` minus `i l o u`), opened by a token
  boundary — anything that is not a word character, which still admits a
  preceding hyphen, so a compound cannot hide a match while `xtl-8wmb` is not a
  token. The boundary governs both detection and reporting; the shell applied it
  only to its line scan and then re-extracted tokens without it. Matched
  case-insensitively, because the id surface is: `Tl/Cli/Resolve` lowercases a
  token before testing the affix and applies the Crockford aliases, so `TL-…`
  and `tl-…` resolve to the same issue and are equally a leak. Case is where
  that stops: the *symbol* aliases (`o`→`0`, `i`/`l`→`1`) are deliberately not
  admitted into the class — see the residuals below.
- Scope: every tracked file, minus exactly three paths — `docs/`, `README.md`,
  and the registry itself — as one predicate rather than as a pathspec whose
  agreement with the rule had to be checked separately. Fail-closed: a new
  top-level file is in scope automatically, and the file list comes from `git
  ls-files`, so it is tracked content only. A tracked symlink is counted and not
  read, which is what `git grep` does with one — its content is a path, and
  where its target is tracked it is scanned as its own entry — and the count is
  disclosed, so a run says what it covered rather than only that it was clean.
- Bytes, not text: the scan reads each file as bytes, which retires both the
  `-a` that kept `git grep` from skipping a blob it sniffed as binary and the
  `LC_ALL=C` that kept the comparison from depending on a locale. One entry per
  path: `git ls-files -s` writes a record per index stage, so an unresolved merge
  lists a path more than once, and reading it per stage would report one leak as
  several.
- `scripts/task-id-placeholders.txt` lists the tokens that only look like ids —
  synthetic ids in the CLI test fixtures. Registering one is where a human
  asserts it is a placeholder rather than a tracker reference. Both sides of the
  lookup fold case, so a placeholder written the way the CLI also accepts is not
  a leak.
- What a `--selftest` arm used to assert is a corpus in
  `Tests/ReleaseToolTests.lean`: every leak shape the gate must keep matching,
  every non-id it must keep rejecting, each recorded residual below, and the
  command itself over planted checkouts — a leak, a registered placeholder, a
  blob git sniffs as binary, an uppercase rendering, an absent registry, an
  empty one, a scope that selected nothing, a directory that is not a checkout,
  and a tracked file the working tree does not hold. A lint that quietly stopped
  matching would pass forever, which is the failure mode a gate like this
  actually has; the difference from a selftest is that the evidence is no longer
  produced by the thing it is evidence about.

This is not a regression to the greps that were removed. Those approximated
*semantic* properties — an axiom, a Mathlib dependency — with text, and missed
cases the compiled environment sees. Here the prohibited thing *is* a token, so
a text scan states the rule rather than approximating it. The check is still not
conflated with the trust boundary: it reads tracked source, never the log, and
`tlverify` is untouched. Task IDs in commit messages remain permitted and useful
for traceability (AGENTS.md, "Artifacts must be human-readable").

Four residuals are recorded rather than papered over. A bare stored id written
without its `tl-` affix is indistinguishable from any other sixteen-digit token
and is not detected. `docs/` and `README.md` are out of scope because the
prohibition binds code and comments; prose that renders sample CLI output would
otherwise fail on its own examples. And the affix is not distinguishable from a
hyphenated English compound — the Crockford class still covers most letters, so
`tl-managed`, `tl-aware`, `tl-cache` and their like all match. The sanctioned
remedy is to reword the prose, not to register it: the registry means "tokens
that are synthetic ids", and filling it with English would erode the assertion
registering a token is supposed to make. This change reworded one such comment
for exactly that reason. Finally, resolution applies the Crockford symbol
aliases (`o`→`0`, `i`/`l`→`1`), so a hand-typed `tl-o231…` resolves while the
canonical class does not match it. Admitting those three letters would catch a
mistyped reference nobody copy-pasted, at the cost of matching the project's own
vocabulary (`tl-init`, `tl-local`, `tl-list`) — which the previous residual
says to reword, so the tax lands on legitimate prose. Every id tl *renders*
comes from `toCrockford` over an alphabet without `i l o u`, so a copied id is
always caught.

### Warning-free build

`lake build --wfail` is the ordinary build gate. It compiles every module in
the default `Tl` and `Tests` libraries and both shipped/test executables.
Warnings, including `sorry`/`admit`, are errors. Because the verifier is a
deliberately separate, non-default target, CI also runs
`lake build tlverify --wfail` before executing it.

### Lean-native trust verification

`lake exe tlverify` is a separate CI step and the authority for the compiled
trust boundary. Its executable is under `Verify/` and does the following:

1. dynamically imports raw `.olean` data for the production roots (`Tl`,
   `Main`), test roots (`Tests` plus an adversarial fixture), its own root
   (`Verify.Main`), the two launcher supervisors (`Verify.Launcher`,
   `Verify.TestLauncher`), executable Lean tooling (`scripts.GenLicenses`), and
   the release-decision layer (`release.Main`) into
   seven separate environments, each loaded from the roots its scope registers,
   with extension/initializer execution disabled;
2. enumerates current importable `.lean` sources from the repository and
   compares each scoped inventory with Lean's actual imported-module graph;
3. classifies imported first-party modules by actual artifact provenance—their
   resolved `.olean` is under the same project build-library root as the
   verifier—and uses Lean's declaration-to-module ownership data to inspect
   all their declarations;
4. walks stored constant bodies itself and rejects any first-party axiom
   declaration or transitive axiom dependency outside `propext`,
   `Classical.choice`, and `Quot.sound`; serialized axiom-summary extensions
   are not trusted;
5. reads each module's stored direct imports and permits only first-party
   modules, Lean/Std/Batteries, and direct Mathlib imports from the ADR-0009
   allowlist (`Tl.Kernel.Path`, `Tl.Kernel.Reach`, `Tl.Kernel.ReachBFS`);
   spelling a Mathlib dependency as `Aesop`, `Qq`, etc. is not an escape;
6. computes each inspected scope's complete stored constant dependency cone
   across package boundaries and calls `Lean.Environment.replay` from an empty
   environment, independently sending every safe, total declaration through
   Lean's kernel. Lean deliberately skips unsafe/partial executable
   definitions, which cannot justify safe theorems.

The replay is stronger than scanning for known bypass APIs. If a declaration
was placed in an `.olean` through an unchecked insertion path or with kernel
checking disabled, the replayed declaration must still type-check. The policy
therefore targets the semantic result rather than an open-ended list of spellings.

That skip is sound for a specific reason, recorded here because the conclusion
is not self-evident from the code. `Lean.Environment.replay` skips a constant
when `isUnsafe || isPartial`, and neither can hold of a theorem:
`ConstantInfo.isUnsafe` is `false` for every `.thmInfo` by construction, and
`ConstantInfo.isPartial` matches only `.defnInfo` carrying `safety == .partial`
(`Lean/Declaration.lean`). `unsafe theorem` is rejected by the grammar, and the
kernel refuses any safe declaration that references an unsafe one, so a proof
cannot reach the skipped set through a dependency either. `partial def f`
stores the referenceable `f` as an `opaque` constant — replayed and checked —
and marks only the compiled `f._unsafe_rec` partial. The skipped set is
therefore the executable implementation layer, never a proof-relevant one.
Measured on this repository, the skip is 52 of 14996 constants in the
production cone with no theorem depending on any of them.

`Tests/VerifyLoadedTests.lean` pins the rejection against Lean's *real* bypass:
it calls `Kernel.Environment.addDecl` under `debug.skipKernelTC`, which routes
to `addDeclWithoutChecking`, and asserts both that the bypass still succeeds
(otherwise the regression would test nothing) and that replay then rejects the
resulting artifact by name. Such a fixture cannot be a checked-in module: any
audited scope holding it would fail the gate, which is the intended behavior.
A forged `theorem : False := True.intro` passes `lake build --wfail` without a
warning and reports no axioms under `#print axioms`; `lake exe tlverify` is the
only gate that rejects it.

Source inventory is read every time the executable runs. A new unimported
source is visible even with stale local build artifacts; no artifact-deletion
wrapper is necessary. Nested git checkouts are separate source authorities and
are not descended into. Symbolic-link source locations and unclassifiable links
are returned as typed inventory findings rather than thrown as operational IO
failures. Module coverage is an exact set comparison, not
a count threshold. Landmark names in `Verify/Policy.lean` ensure every proved
claim documented in `docs/overview.md` still resolves to a theorem.

Directory and root-source registrations are typed with their owning semantic
scope. The verifier consumes the same entries to collect filesystem inventory,
derive that scope's expected modules, and derive the top-level claimed paths;
there is no independent claimed-path list that can suppress the unclaimed scan
without also making a missing module a scope finding. `lakefile.lean` is a
separate fixed configuration exemption, not an audited root-source entry.

The verifier also covers tests, its own implementation, and the executable
license generator. Because the scopes enumerate named directories, the gate
additionally refuses any top-level Lean source that no scope claims: a new
directory or root module has to join an audited scope before it can be built
and inspected by nothing. `lakefile.lean` necessarily runs before target
construction and cannot audit its own wiring; changes to it and to the CI
invocation remain review/protected-branch obligations, just like removing the
build gate itself.

Two of the gate's own failure modes are self-checks rather than tests. A scope
that imports modules yet selects no declarations, replays no constants, or
reads no import edges is reported: every semantic arm is silent on an empty
selection, so a regressed selection layer would otherwise read as success.

The gate's verdict logic is itself proved, in `Verify/Proofs.lean`. `analyze`,
the two aggregates above it, `gateEvidenceOf` — the assembly the worker actually
calls — and `workerVerdict` are total pure functions of already-collected
evidence, so the
AGENTS.md tiering puts them in the provable tier rather than the tested one: a
`GateClean` structure enumerates every condition `analyze` can report and
`analyze_clean_iff` proves a scope's finding array is empty exactly when all of
them hold, while `importViolations_isEmpty_iff` and `importViolations_size_eq`
prove the nested ADR-0009 traversal reaches every edge of every row and emits
one finding per rejected edge. Example rows cannot close that class, because
the failure being managed is an arm that quietly stops reporting.

`workerVerdict` carries that decision to the exit: it turns the finding array
into what the worker prints, where, and what it returns, so `runChecked` has no
branch of its own and a clean CI run exercises the same lines a failing one
does. Status zero (`workerVerdict_status_zero_iff`) and the completion marker
(`workerVerdict_marker_iff`) each hold exactly when the evidence is empty, the
marker is the report's last line (`workerVerdict_marker_last`, which is what the
supervisor's marker-finality rule requires) and a failing run's report is empty
(`workerVerdict_report_empty`), and the diagnostic stream is the evidence itself
in *both* arms (`workerVerdict_diagnostics`) — stated with no
"only when dirty" hypothesis. Both streams are therefore characterised on both
paths, so neither a clean run nor a failing one can grow an emission that no
theorem sees. Composed with the assembly theorem,
`workerVerdict_marker_iff_clean` states the whole decision in one step: the
marker is printed exactly when all seven scopes are `GateClean` and both
inventory scans are silent.

What stays IO splits two ways, and only one half is tested. The supervisor's
handling of the marker is covered against real worker processes. The emission
itself — `runChecked`'s three unconditional lines writing `verdict.diagnostics`
to stderr, `verdict.report` to stdout, and returning `verdict.status` — is
**not**: no test drives `runChecked` on dirty evidence, so deleting the
diagnostic loop would suppress every finding's remedy while the proofs, the
suite, and a clean CI run all stayed green. That call site is therefore part of
the recorded `Verify/Main.lean` bootstrap-review assumption rather than
something a gate catches: the same protected-review obligation that stops
`Main.lean` forging the completion marker is what stops it dropping the
diagnostics. A branch-free `workerVerdict` is what keeps that obligation small —
there is one emission path, not one per outcome — but small is not zero, and it
is recorded here rather than claimed as covered.

Stored-body axiom propagation is proved too, and it is the piece that most
needed it: `propagatedAxioms` reimplements Lean's `collectAxioms` rather than
trusting serialized summaries produced by the very compilation under audit, so
a bug there is a silent false negative rather than a suspicious verdict.
`propagatedAxioms_sound` and `propagatedAxioms_complete` pin its rows to the
axioms reachable along stored-body edges, in both directions. Making that
provable meant replacing a `while` loop — which elaborates to an opaque
worklist combinator carrying no induction principle — with a fuel-structural
drain that returns `Option` and *refuses* an exhausted bound instead of
returning a truncated map. The refusal is not a formality: completeness holds
at a drained exit, and a truncated map would satisfy soundness while missing
exactly the axiom that mattered.

What is *not* claimed matters as much. Three seams carry one-directional
implications rather than characterisations — `directImportAllowed_cases`,
`completedSuccessfully_exitZero` with `completedSuccessfully_markerFinal`, and
`replayDependencies_superset` (a single replay step, not the `partial def`
closure walk) — and the rest of the collection layer in
`Verify/Environment.lean` stays tested: no theorem says the observed
declaration set is a scope's complete one, or that the replay closure reached a
fixed point. The propagation theorems are themselves relative to the constants
they are handed — exact over that map, silent on whether it is the right one.

These theorems deliberately get no entry in `Tl.Verify.landmarkTheorems` and no
row in the overview's proved-claims table. The landmark list exists to stop the
*product's* documented proved claims from shrinking unnoticed; the gate's own
internal correctness is not a product claim, and mixing the two would make a
landmark failure ambiguous between "a kernel theorem was retired" and "the gate
was refactored". Compilation and replay protection they get for free: the
theorems sit inside the audited verifier scope, so `lake build tlverify --wfail`
fails if one stops compiling and `lake exe tlverify` kernel-replays them on
every run. Deletion protection is separate and explicit, because those two
gates only see a theorem that *breaks*, never one that is *removed*:
`pinnedVerdictLogicTheorems` in `Tests/VerifyTests.lean` names each theorem, so
retiring one without editing that list is a compile error — the same role
`landmarkTheorems` plays for the product's claims, kept in a different list on
purpose.

`Tests/VerifyTests.lean` covers the report branches — including list truncation
and a landmark degraded into an axiom — exact inventory and symlink-refusal
rules (entry and root), typed scope claims feeding their expected-module sets,
the pinned dependency, landmark
and supervision policies, the ADR-0009 violation findings themselves, the
vacuity self-check, stored-body axiom propagation, and kernel replay. Import
audit, replay, expected-landmark, seven named scope-report, source-inventory, and
unclaimed-source evidence are required structure fields; tests inject negative
sentinels through the composed observation/verdict paths, so clean checked-in
environments cannot make their wiring mutation-silent. Which scope a piece of
evidence belongs to is carried by its type rather than by a name written beside
it: `GateScope` indexes both an observation and the loaded environment it is
built from, and the seven reach the verdict through a structure with one
differently-typed field each, so a swapped, duplicated or dropped scope does not
elaborate. The registry that maps a scope to its roots and its source
directories is what review still carries — and a mismatch there is reported by
the missing- and unexpected-module arms rather than passed over. The
replay regression constructs an ill-typed theorem value—representing
the result of unchecked insertion—and asserts that replay rejects it. The
supervision decision is driven against real worker processes (completed,
early exit, non-zero exit, missing), with stdout/stderr forwarding canaries and
an injected runner failure for the process-spawn exception path, rather than
only as a predicate.
`Tests/VerifyLoadedTests.lean` runs where the project `.olean`s are
present (the ordinary Ubuntu/macOS legs, not the binary-only git-floor leg) and
loads the real verifier environment without initializers. It checks module
selection, declaration ownership, project-artifact provenance, stored direct
imports, a cross-package replay closure, and the composed replay-closure →
transitive-axiom → declaration-report wiring; the mutual-inductive sibling arm
has a separate pure fixture. A compiled fixture contains an initializer that
exits the process; every live verifier run
must inspect that fixture without running it, exercising the composed loader,
provenance, ownership, observation, and supervisor path. This integration
canary is kept out of `tltest`, whose git-floor artifact runs without Lean or
`.olean` files. That leg skips the group on an observed fact — `findSysroot`
resolves no toolchain — rather than on an opt-out variable the caller supplies.
An opt-out would let any environment turn the group into a green row whose
stated reason is false, and would need its own assertion that the ordinary legs
left it unset; a fact cannot be asserted from outside the process, so the
input is removed instead of guarded. The harness rejects every accidental
empty test group, so a failed setup cannot erase its own assertion count.

`tlverify` is a minimal Lean supervisor around the audited `tlverifyWorker`.
Status zero alone is insufficient: the worker must emit a fixed completion
marker after every semantic check and verdict. This catches accidental or
regressed early exits that do not emit the verdict. It cannot authenticate the
worker against an initializer deliberately printing the public marker: code in
a process cannot prove to its parent which earlier code in that same process
produced an in-band string. The worker root, launcher, and CI invocation are
therefore an explicit review/protected-branch bootstrap obligation, just like
the workflow's decision to invoke `lake build` at all. The supervision decision
still lives in `Verify/Supervise.lean` and is exercised against real processes.

The gate reads the `.olean` files and runs the worker binary that Lake just
built. CI does not cache `.lake/build`: an earlier commit's project outputs
cannot enter a later commit's build at all. Reusable caches are restored
explicitly, while cache saves are restricted to protected `main`; a PR cannot
plant a toolchain executable or mutable dependency tree for its next commit.
Runtime source inventory independently closes the unimported-source case. The
old source/verdict parser duplicated semantic policy; this supervisor checks
only process completion and contains no trust policy.

### Outside-TCB tests

`lake exe tltest` runs after the verifier. Like `tlverify`, it is a minimal
launcher around a worker and accepts status zero only when `tltestWorker`
emits its fixed marker after the complete registered suite finishes. This prevents an imported
initializer from exiting zero before any assertion runs. The suite covers
serialization, git and filesystem behavior, clocks, imports, CLI contracts,
compiled-kernel/spec cross-checks, and performance regressions. These tests
remain a regression net over the executable, never a substitute for theorems
about provable kernel properties.

For local iteration, `lake exe tltest --list` lists stable group names and
`lake exe tltest --group sync --group store` selects groups without constructing
unselected fixtures. Selection is exact, validated in full before execution,
deduplicated, and executed in registry order. Empty names, missing values,
unknown groups, mixed discovery/selection options, and an empty or malformed
registry refuse rather than running an accidental subset. No arguments still
runs every group; CI continues to use that form. A focused run is explicitly
labelled and emits a different completion verdict, which cannot certify a
full-suite pass. Help and listing use the same request-completion protocol.

`Tests/Runner.lean` flushes START before each group's setup and END after its
assertions, including elapsed monotonic milliseconds and failures. Large release
tool fixture boundaries have additional FIXTURE timings. Empty groups and setup
exceptions become visible failed assertions; subsequent groups still execute.
The test supervisor streams both pipes concurrently, retaining only the last
nonempty stdout line for the existing completion decision. Either reader's
failure requests worker termination and asynchronous reaping, then returns the
error without waiting for the other pipe: a descendant may hold it open. The
worker retains the terminal's process group so terminal interrupts still reach
its fixtures. This is not process containment: the public launcher exits on
failure; an embedding caller must own cleanup of any surviving descendants.
`Tests/RunnerTests.lean` covers selection, registry coverage,
empty/failing/throwing groups, actual launcher argument forwarding, and real
workers with early exits, malformed final markers, pipe bursts, broken consumers,
descendants holding pipes open across a consumer failure,
and a handshake requiring both streams to be flushed before worker completion.
The verifier launcher retains its existing buffered path.

Groups remain sequential: the performance groups require uncontended execution.
Focused runs accelerate local diagnosis, not the required final full validation.

### Git runtime floor

The Ubuntu build uploads `tl`, the `tltest` supervisor, and `tltestWorker`. The `git-floor` job builds git
2.17.1 from a hash-pinned tarball with optional subsystems disabled, puts only
that binary on `PATH` for the tests, runs the complete suite, and checks that
`tl init` and the `doctor --json` `gitVersion` row accept exactly the floor.

### Caches

Three reusable caches are keyed by what invalidates them. Every job may restore
them from a versioned `trusted-main` namespace, but only a successful
protected-`main` push may save them. Versioning prevents this transition from
restoring an older PR-written entry with the same dependency inputs:

| Path | Key basis | Purpose |
| --- | --- | --- |
| `~/.elan` | OS, architecture, `lean-toolchain` | toolchain |
| `~/.cache/mathlib` | manifest and toolchain | platform-independent Mathlib archives |
| `.lake/packages` | manifest | dependency sources only; nested build dirs are pruned before save |

`.lake/build` is deliberately not cached. A commit-keyed entry had no
cross-commit reuse, while any reusable project-output key would trust bytes Lake
validates by input traces rather than by output content.

`.tl/local/` is never cached because copying a replica id would violate the
uniqueness assumption in `docs/overview.md`.

## Rejected alternatives

- **Regex/AWK source scanning.** It must approximate Lean comments, strings,
  raw strings, Unicode identifiers, command wrappers, scoped syntax, and future
  grammar changes. Fixing one missed spelling does not close the class.
- **A custom elaborator command in a non-default probe module.** Lake can replay
  its cached result while the command reads a newer filesystem tree; wrappers
  that delete artifacts and parse printed verdicts compensate for the wrong
  execution model rather than removing it.
- **Mutation tests that rewrite the checkout.** They are slow, require complex
  restoration logic, and still sample spellings. Pure failure fixtures plus an
  actual kernel-replay regression cover the semantic branches without risking
  developer files.
- **Count floors.** Exact source/module sets and named landmarks are available;
  approximate counts add policy knobs without proving coverage.
- **Making `tlverify` a default target.** The ordinary build and the trust audit
  are distinct evidence and should remain separately visible in CI and local
  completion reports.

## Consequences

- The trust gate is Lean code and uses Lean's parser-independent semantic data.
- No Bash trust scripts or source lexer remain.
- A clean `lake build --wfail` is necessary but not sufficient; contributors
  also run `lake exe tlverify` and `lake exe tltest`.
- Adding a source under `Tl/`, `Tests/`, `Verify/`, `VerifyFixture/`,
  `scripts/`, or `release/` requires including it in the corresponding audited
  scope in the same change.
- Adding or retiring a proved claim updates `Verify/Policy.lean` and
  `docs/overview.md` together.
- Widening the axiom allowance or Mathlib scope remains an explicit ADR-level
  trust decision.
