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

1. `build-and-test` on Ubuntu and macOS;
2. `git-floor`, after the build matrix, using the Ubuntu artifacts.

The task-ID leakage check remains a manual review obligation until its pattern
and legitimate examples have a recorded contract. It is not conflated with the
trust boundary.

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
