# tl — agent & contributor guide

`tl` ("task list") is a small, formally verified, git-native task tracker
for AI agents. This file is the working guide for anyone — human or agent —
**building tl**. For what tl *is*, read [docs/vision.md](docs/vision.md);
for the decisions and their rationale, read the ADRs in
[docs/adr/](docs/adr/); for the honest proved-vs-tested boundary, read
[docs/overview.md](docs/overview.md).

> Two audiences, don't conflate them: this file is for agents **building**
> tl. Agents **using** tl as a tracker get the usage guide / skill (see
> [ADR-0011](docs/adr/ADR-0011-agent-consumption.md) — machine-readable reads
> and skill), not this.

## Core principles

1. **Prove inside the TCB, test outside it — and every part has a home.**
   This is a three-tier coverage mandate, not a preference:

   - **Provable (the kernel: state, the op fold, `ready`, cycle detection,
     epic rollup, CRDT join laws)** → covered by **Lean theorems, never by
     tests**. A test is not a substitute for a property that can be stated
     and proved. Strengthen an existing theorem rather than adding a parallel
     weaker test.
   - **Not provable in-kernel but testable (the I/O shell: serialization,
     git, clocks, the importer, the CLI)** → covered by **tests, and the
     coverage must be comprehensive.** Untested shell code is a *defect*, not
     an acceptable state: every branch and error path is exercised, and new
     shell code ships with its tests in the **same** change. "It's outside
     the TCB" licenses *testing instead of proving* — it does **not** license
     *not covering it*.
   - **Neither provable nor testable (replica-id uniqueness, HLC monotonic
     persistence, git byte-transport, system clock)** → an **explicit
     carried assumption**, written into the Trusted section of
     [docs/overview.md](docs/overview.md). Never silently relied on; never a
     `sorry` or a new `axiom`.

   Two anti-patterns this rules out: (a) **silently downgrading a provable
   property to "tested only"** because the proof is hard — decompose it,
   prove what you can, and record any residual as a carried assumption (tier
   3), don't swap a theorem for a test; (b) **shipping shell code whose
   branches aren't tested** on the grounds that it's "just I/O." See
   [ADR-0004](docs/adr/ADR-0004-verified-kernel-tcb-boundary.md).

2. **Cross-entity rules are derived or reported, never enforced.** A CRDT
   merge cannot reject a write, so any rule a merge could violate must be a
   *total function of the materialized state*: `blocked` is derived,
   acyclicity is reported (`dep cycles`), epic-`done` is derived, status
   transition legality is a local courtesy guard only. Never add a
   write-time guard for something a merge can break.

3. **Make illegal states unrepresentable.** Use the type system: a closed
   status enum, `Op` constructors as the only mutation path, `Except` for
   operations that can fail. Don't validate after the fact what a type can
   forbid up front.

## Build & validate

- `lake build` — compiles and verifies all proofs. A green build proves the
  *stated* theorems.
- `lake exe tlverify` — a minimal supervisor for the Lean-native
  `tlverifyWorker` trust-boundary gate; status zero is accepted only with the
  worker's fixed end-of-run marker. The marker detects unmarked accidental
  early exits; it is not an authentication boundary against code in the worker
  deliberately forging its own verdict, so `Verify/Main.lean`,
  `Verify/Launcher.lean`, and the workflow remain protected-review bootstrap.
  The worker loads raw compiled production,
  test, verifier, and Lean-tooling environments without
  executing their initializers; matches their modules exactly against the current source inventory;
  rejects first-party axioms and transitive axiom dependencies outside
  `propext` / `Classical.choice` / `Quot.sound`; enforces the ADR-0009 direct
  dependency allowlist from Lean's stored import graph; and independently
  replays every safe, total inspected declaration and its complete stored
  dependency cone from an empty environment through Lean's kernel
  (`Environment.replay` deliberately skips unsafe/partial executable code,
  which cannot justify safe theorems). It also refuses a top-level Lean source
  no scope claims, and reports a scope that selected no declarations, replayed
  nothing, or read no import edges — arms that are silent when empty must not
  read as success. The inventory is
  read on every invocation, so a stale local build cache cannot hide a new
  unimported source. CI does not cache `.lake/build`; PR jobs may restore
  reusable toolchain/dependency caches but only protected `main` may save them.
  Its failure paths, the supervision decision against real
  worker processes, loaded-environment selection/traversal, and an unchecked
  ill-typed theorem are covered in `Tests/VerifyTests.lean` and
  `Tests/VerifyLoadedTests.lean`; the live gate also imports a hostile exit
  initializer as a composed no-execution/supervision canary.
  Its *verdict logic* — the pure functions deciding whether a scope, and then
  the whole run, passes — is **proved** in `Verify/Proofs.lean` under principle 1
  rather than sampled with example rows, as is the stored-body axiom
  propagation those arms report on — a collection-layer function that
  reimplements Lean's own `collectAxioms`, so a bug in it is a silent false
  negative rather than an odd verdict. The rest of the evidence *collection*
  stays tested. Those theorems deliberately get no landmark
  and no docs/overview.md row: landmarks guard the *product's* proved claims,
  not the gate's own internals. They are instead kept from silent deletion by
  `pinnedVerdictLogicTheorems` in `Tests/VerifyTests.lean`. The split, what is
  characterised exactly, and what is only one-directional are recorded in
  [docs/codebase-map.md](docs/codebase-map.md) and
  [ADR-0026](docs/adr/ADR-0026-continuous-integration.md).
- Tests (outside the TCB) validate the compiled binary: round-trip
  serialization (`parse ∘ render = id`), the differential import check
  (`Tl/Import/Bulk` against the committed `Tests/fixtures/import-sample.jsonl`),
  and a property-based cross-check that the
  *compiled* kernel agrees with its proved spec — a regression net over the
  executable (does compilation preserve the theorems?), **never a substitute
  for the `Tl/Kernel` + `Tl/Crdt` theorems** themselves (ADR-0004).
  `lake exe tltest` is a minimal supervisor around `tltestWorker`: status zero
  is accepted only when the worker reaches the harness's final marker, so an
  imported initializer cannot silently exit successfully before assertions run.

CI gates (mirror these locally before declaring done):
- Warning-free `lake build --wfail` and `lake build tlverify --wfail`.
- No `sorry`, `admit`, or new `axiom`. `lake build --wfail` rejects unfinished
  proof warnings; `lake exe tlverify` rejects first-party axioms, forbidden
  transitive dependencies, unimported scoped sources, and declarations that
  fail independent kernel replay. Run both before declaring a theorem done; a
  completion report quoting `#print axioms` for new names is a courtesy, not
  the gate.
- Round-trip + ref-sync (fetch/union/push, push-rejection, no-upstream) +
  differential-import + property tests pass.
  For shell code, "covered" means discrete
  tests for each documented branch/error path touched by the change, including
  each error code it can emit; do not rely on an unspecified
  coverage percentage.
- No task-ID leakage in code and comments (see "Artifacts" below).
  `scripts/check-task-ids.sh` rejects any `tl-`-affixed Crockford token — the
  ADR-0007 display form, four digits or more — in a tracked file outside
  `docs/` and `README.md`, unless it is registered in
  `scripts/task-id-placeholders.txt`. That registry is the pinned exclusion
  set, and registering a token is where a human asserts it is a placeholder and
  not a tracker reference, so a new test id lands there in the same change.

`.github/workflows/ci.yml` mechanizes every gate above
([ADR-0026](docs/adr/ADR-0026-continuous-integration.md)). The task-ID check is
lexical rather than semantic: the prohibited thing *is* a token, so a text scan
states the rule instead of approximating it — unlike the source greps the trust
verifier replaced — and it stays outside the trust boundary, reading tracked
content only and never the log. Four limits are recorded rather than
papered over: a bare stored id written without its `tl-` affix is
indistinguishable from any other sixteen-digit token and is not detected;
`docs/` and `README.md` are out of scope because the prohibition binds code and
comments; and the affix is not distinguishable from a hyphenated English
compound — the affix followed by an ordinary word (`managed`, `aware`) matches,
because the Crockford class still covers most letters. Such prose is reworded
rather than registered: the registry means "synthetic ids", and filling it with
English would erode what registering a token asserts.

If a change adds a proved claim to the docs/overview.md table, add a landmark
theorem for it to `Tl.Verify.landmarkTheorems` in the same change; that list is
what keeps the verifier from passing over a theorem set that quietly shrank. If a
change retires a claim, remove its landmark in the same change — the verifier
fails otherwise, and the message says so.

## Proof guidance

- **Dependencies: `batteries` (std4) by default; Mathlib only under the
  recorded ADR-0009 escape hatch**, scoped to the reachability/cardinality
  proof modules (`Tl/Kernel/Reach.lean` and its dependents) — see
  [ADR-0009](docs/adr/ADR-0009-proof-dependencies.md); do not widen its scope
  without recording it. In the base CRDT/kernel layers: model collections
  over `List` (no `Finset`); prove the CRDT join laws (commutativity /
  associativity / idempotence) directly rather than via Mathlib's lattice
  typeclasses.
- **Avoid `omega`, `decide`, `aesop`, and bare `simp` as proof closers.**
  They produce opaque terms the next agent can't maintain. Prefer explicit
  `calc`, `cases`/`match`, named lemmas, and `simp only [...]` with an
  explicit list.
- **Totality is mandatory where the kernel claims it.** `ready`, `apply`,
  `effectiveStatus`, and cycle detection must be total — including on cyclic
  graphs **and on dangling edges** (both reachable via merge, ADR-0003).
  Use well-founded recursion on a finite visited-set (or a fuel parameter);
  do not assume acyclicity, and do not assume an edge endpoint exists.
- **Decompose.** If a theorem needs more than ~3 lemmas or spans modules,
  break it up first. A small lemma that compiles beats an ambitious proof
  that ends in `sorry`.

The *specific* shape of each kernel function and theorem (signatures,
invariant contents, the one-directional liveness form, the LWW triple key)
is specified once in the ADRs and annotated per-module in
[docs/codebase-map.md](docs/codebase-map.md) — and, once scaffolded, enforced
by the Lean signatures themselves. Read those at the point of use rather than
duplicating them here; this file is process, not spec.

## Code rules

- **Add every new `.lean` file under `Tl/` to the root module (`Tl.lean`).**
  Files not imported by the root are invisible to `lake build`; `tlverify`
  independently compares the current source inventory with that import closure.
  `Tests/ImportsTests.lean` enforces this for the whole class.
- **Never introduce `sorry`** in completed work, and **no new `axiom`** —
  the trust boundary is fixed by [docs/overview.md](docs/overview.md);
  expanding it is a deliberate decision, not a local one.
- **Destructure tuples on bind; no `.2.2.X` projection chains.** 3+ tuples
  get `let (a, b, c) := …`; 4+ component returns consumed by 2+ callers get
  a named structure. Same for multi-conjunction `Prop`s.
- **`Fin`-typed indices** (e.g. `Fin 64`-style bounded indices) over `Nat`
  with side bound proofs, where it applies.
- Naming: `camelCase` for defs, `PascalCase` for types and propositions.
- **Don't regress production code to make a proof easier.** Bridge from the
  efficient form to the spec; don't slow the runtime to simplify a proof
  without explicit approval.
- **Maintain algorithmic efficiency as a principle.** Work proportional to
  the input: memoize shared descents, precompute an index instead of
  rescanning a collection per item, and don't leave accidentally-quadratic
  folds, sorts, or graph walks on command paths. In the kernel the efficient
  form *is* the production code and the theorems are proved about it —
  directly, via a characterization (recurrence) lemma, or via an equivalence
  bridge, whichever proves cheapest; a reference function, when one helps, is
  proof scaffolding, never the shipped path, and is not required. Structural
  efficiency properties (e.g. each node evaluated once per query) are
  themselves provable; wall-clock cost of the compiled binary stays tested,
  not proved (the ADR-0004 tiering). An accepted cost compromise is recorded
  explicitly (ADR or tracked task), never silently. The full discipline —
  the proved/tested/assumed tiering, the op-count + end-to-end regression net,
  and the indexed-view substrate that backs the proved tier — is recorded in
  [ADR-0023](docs/adr/ADR-0023-efficiency-tiering-and-prevention.md) and
  [ADR-0024](docs/adr/ADR-0024-indexed-views-bridge.md).
- **Error messages teach.** Every error's human `message` says what to do next
  (the fix), not just what failed — written for a human *and* an agent that
  branches on the `code` and reads `message` to self-correct. The `code` is the
  stable contract (ADR-0008); a `message` that only restates its code is a defect.

## Artifacts must be human-readable

Code and comments stand on their own for readers who don't have any tracker
open. **Do not reference task-tracker IDs** in code or comments — describe the
substance. (tl is *itself* a tracker; the temptation to cross-reference its own
issue IDs into its own source is exactly the thing to resist.) Cross-references
between code/docs/ADR anchors are fine; references into a tracker are not.
`scripts/check-task-ids.sh` enforces this over tracked code, and
`scripts/task-id-placeholders.txt` is the registry of tokens that only look
like ids.

**Commit messages are the exception, and task IDs there are welcome.** A commit
message is metadata *about* a change rather than part of the artifact, it is
already scoped to the repository's own history, and the traceability is useful:
it is the one place a reader can cheaply ask "what was this for". A commit
message must still explain its substance on its own — an ID is a supplement to
that explanation, never a replacement for it. What stays out of commit messages
is bookkeeping that decays: test counts, session or attribution trailers, and
review-round narration.

## Commit incrementally

Commit helper lemmas and infrastructure as you go — don't wait for the main
theorem. A long-running `lake build` can starve a watchdog; uncommitted work
is lost work. Pattern: write a helper → `lake build` → commit → repeat. Only
commit or push when asked; if on the default branch, branch first.

## Intended module layout

See [docs/codebase-map.md](docs/codebase-map.md). In short: `Tl/Kernel/`
(verified core, no I/O), `Tl/Crdt/` (OR-Set, LWW, join laws), and the tested
shell — `Tl/Format/`, `Tl/Hash/` (pure, tested), `Tl/Store/`, `Tl/Clock/`,
`Tl/Sync/`, `Tl/Import/`, `Tl/Cli/` — with
`Tl.lean` as the root and `Tests/` alongside. `Verify/` holds the separately
built Lean-native trust verifier and its policy/reporting modules.

## Definition of done

1. `lake build --wfail` passes, and `lake exe tlverify` is green.
2. No new `sorry`; no new `axiom`.
3. New theorems listed in the completion report, one line each.
4. **Every outside-TCB change ships with its tests in the same change** —
   round-trip / differential / property, covering each branch and error
   path. A CI lint may additionally guard a whole class, but a lint does not
   excuse missing per-change tests.
5. Any property that is provable but not yet proved is **decomposed and the
   residual recorded as a carried assumption** in `docs/overview.md` — never
   silently downgraded to a test.
6. If the change affects scope or the trust boundary, update
   `docs/vision.md` / `docs/overview.md` in the same change.
