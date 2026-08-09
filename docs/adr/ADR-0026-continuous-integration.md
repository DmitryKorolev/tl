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

The graph is:

1. `task-id-lint`, needing no toolchain;
2. `release-policy`, also needing no toolchain;
3. `build-and-test` on Ubuntu and macOS;
4. `git-floor`, after the build matrix, using the Ubuntu artifacts.

Only `git-floor` carries a `needs:`. The toolchain-free jobs run independently
of the build so a lexical or policy failure and a build failure are both
visible from one run, and they fail in seconds rather than after the matrix.

`release-policy` holds the release-machinery gates that the Lean suite cannot
express:

- `scripts/check-release-identity.sh` checks what the pinned cosign
  certificate expression *means* — that it accepts this repository's release
  workflow on a SemVer tag and rejects adversarial neighbours (a repository
  whose name contains ours, a different workflow in this repository, an
  unescaped-dot match, a non-SemVer tag). `Tests/ReleaseTests.lean` guards that
  every operative copy carries the same text, which is drift; meaning needs a
  regular-expression engine the Lean suite does not have, and an expression
  that is anchored and well-formed while matching the wrong repository would
  pass a text-equality guard and hollow out the fail-closed verifier
  (ADR-0014 T3).
- `scripts/gen-build-provenance.sh --selftest` exercises the stamp generator's
  refusal paths.
- `scripts/verify-release-artifacts.sh --selftest` exercises the artifact
  verifier's, against fabricated missing, malformed, mismatched, and
  rejected-signature inputs. That script is the VERIFYING.md procedure as code,
  shared by the installer and by the release workflow's pre-publish check, so
  the documented steps are the executed ones and a release cannot ship
  artifacts its own published procedure would reject.
- A regeneration diff on `Tl/Build/Stamp.lean`. Three places state as fact that
  the checked-in copy is the development stamp; without this step a stamped
  copy swept in by `git commit -a` would make every build from that tree claim
  `clean build — commit <stale>` while passing the whole suite. It is a CI step
  rather than a `tltest` assertion so the release job, which stamps on purpose,
  is unaffected.

Both scripts carry a `--selftest` arm on the same reasoning as the task-ID
lint: a checker that quietly stopped detecting would pass forever, so it proves
it can still fail before its silence is believed.

`.github/workflows/release.yml` is a separate workflow, triggered by a SemVer
tag ([ADR-0006](ADR-0006-distribution-and-platforms.md)). It re-runs these
gates against the tagged commit rather than trusting that the tag happens to
point at a commit CI already saw, then builds the four native artifacts and
signs them. Signing runs directly in that workflow because GitHub's OIDC
certificate names the workflow that requested it, and `release/identity.json`
pins that name — indirection through a reusable workflow would change the
identity every verifier checks.

The earlier `lint` job carried the source greps this ADR replaces, plus an
advisory task-ID-leakage warning, and went away with them. The task-ID check
returns as its own gating job now that its pattern and exclusion set are a
pinned contract rather than a preference:

- Pattern `(^|[^0-9A-Za-z_])tl-[0-9a-hjkmnp-tv-z]{4,}` — the ADR-0007 display
  affix followed by at least `shortIdFloor` = 4 Crockford base32 digits. The
  leading class is a token boundary that still admits a preceding hyphen, so a
  compound cannot hide a match. Matched case-insensitively, because the id
  surface is: `Tl/Cli/Resolve` lowercases a token before testing the affix and
  applies the Crockford aliases, so `TL-…` and `tl-…` resolve to the same issue
  and are equally a leak. Case is where that stops: the *symbol* aliases
  (`o`→`0`, `i`/`l`→`1`) are deliberately not admitted into the class — see the
  residuals below.
- Scope: every tracked file, minus exactly three pathspecs — `docs/`,
  `README.md`, and the registry itself. Fail-closed: a new top-level file is in
  scope automatically, and `git grep` reads tracked content only.
- `scripts/task-id-placeholders.txt` lists the tokens that only look like ids —
  synthetic ids in the CLI test fixtures. Registering one is where a human
  asserts it is a placeholder rather than a tracker reference.
- `--selftest` runs first and asserts the pattern still matches known leak
  shapes and still rejects known non-ids. A lint that quietly stopped matching
  would pass forever, which is the failure mode a gate like this actually has.

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
   (`Verify.Main`), and executable Lean tooling (`scripts.GenLicenses`) into
   separate environments, with extension/initializer execution disabled;
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
marker is printed exactly when all six scopes are `GateClean` and both inventory
scans are silent.

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
audit, replay, expected-landmark, six named scope-report, source-inventory, and
unclaimed-source evidence are required structure fields; tests inject negative
sentinels through the composed observation/verdict paths, so clean checked-in
environments cannot make their wiring mutation-silent. The
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
emits its fixed marker after `runAll` completes. This prevents an imported
initializer from exiting zero before any assertion runs. The suite covers
serialization, git and filesystem behavior, clocks, imports, CLI contracts,
compiled-kernel/spec cross-checks, and performance regressions. These tests
remain a regression net over the executable, never a substitute for theorems
about provable kernel properties.

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
- Adding a source under `Tl/`, `Tests/`, `Verify/`, `VerifyFixture/`, or
  `scripts/` requires including it in the corresponding audited scope in the
  same change.
- Adding or retiring a proved claim updates `Verify/Policy.lean` and
  `docs/overview.md` together.
- Widening the axiom allowance or Mathlib scope remains an explicit ADR-level
  trust decision.
