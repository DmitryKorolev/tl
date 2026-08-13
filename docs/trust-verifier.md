# Trust verifier

`tl`'s product guarantees live in Lean theorem statements and proof terms. The
separate `tlverify` executable guards the evidence boundary around those
theorems: it checks that the compiled environments, current source inventory,
dependency policy, and expected theorem set are still the ones the project
claims to inspect.

This page describes that mechanism. It is verifier documentation, not an
additional product-guarantee table; the product claims and theorem anchors live
in [overview.md](overview.md).

## Running the gate

```sh
lake build --wfail
lake build tlverify --wfail
lake exe tlverify
```

The build checks the Lean proof terms. `tlverify` then audits the compiled
boundary and independently replays the declarations it is allowed to inspect.
Both are required evidence.

`lake exe tlverify` is a minimal supervisor around the Lean-native
`tlverifyWorker`. A zero exit status is accepted only when the worker reaches
its fixed end-of-run marker. The marker detects accidental early exits; it is
not an authentication boundary against worker code deliberately forging its
own verdict.

## What the worker checks

### Source and module coverage

The worker loads seven raw compiled environments — production, tests, the
verifier, its two launcher supervisors, executable Lean tooling, and the
`tlrelease` release-decision layer — without executing their initializers. Each
is loaded from the roots its scope registers, and carries that scope in its
type, so the evidence collected from one environment cannot be reported as
another's. For each scope the worker:

- reads the current source inventory on every invocation;
- compares that inventory with Lean's stored import graph;
- verifies declaration ownership and compiled-artifact provenance;
- rejects a top-level Lean source that no scope claims;
- rejects a scope that selects no declarations, replays nothing, or reads no
  import edges; and
- treats `lakefile.lean` as a fixed configuration exemption because Lake
  elaborates it before this gate can run.

Reading the inventory live means a stale `.lake` cache cannot conceal a new,
unimported source file. Directory and root entries carry typed scope ownership,
and those same entries derive the expected module set, so merely naming a new
scope cannot hide its files from inspection.

### Import and axiom policy

The worker enforces ADR-0009's direct-dependency allowlist from Lean's stored
import graph. It rejects first-party axioms and any inspected declaration whose
transitive axiom dependencies exceed the accepted Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound`.

Stored-body axiom propagation is reimplemented rather than trusting axiom
summaries from the compilation under audit. Its pure propagation logic is
proved in both directions: the axioms reported for a declaration are exactly
the axioms reachable through the stored-body dependency map it receives. The
function refuses to answer if its traversal bound is exhausted; it never
returns a knowingly truncated clean result.

That exactness is relative to the dependency map supplied by evidence
collection. Selecting the right declarations and constructing the right map
remain tested collection responsibilities, not assumptions smuggled into the
propagation theorem.

### Independent kernel replay

Every inspected safe, total declaration and its complete stored dependency
cone is replayed from an empty environment through Lean's kernel. This is the
backstop against an unchecked insertion or a declaration admitted only because
normal compiler checking was bypassed.

Lean excludes unsafe and partial executable definitions from this replay.
Those definitions cannot justify safe theorems, so skipping them does not
weaken the theorem boundary.

### Expected theorem landmarks

`Tl.Verify.landmarkTheorems` pins the named theorem anchors for every product
claim in the overview, except totality claims discharged by total definitions.
It also pins the named fast/reference bridges and other proved anchors used by
the tested tier. Tests pin the landmark list itself.

Landmarks guard theorem names and presence. They do not read the English claim
table, interpret what a theorem means, or independently verify that a
definition has the intended product semantics. Retiring or replacing a claim
therefore remains a deliberate review action across the overview, theorem,
landmark list, and tests.

## What is proved and what is tested

The verifier is outside the product trusted computing boundary, and its own
assurance is split deliberately:

- Pure verdict logic is proved in `Verify/Proofs.lean`. Scope analysis and
  run-wide assembly are characterized against a typed `GateClean` structure;
  import-policy decisions and stored-body axiom propagation also have named
  theorems.
- Evidence collection is tested. This includes filesystem inventory,
  declaration and module selection, compiled-artifact provenance, stored
  import rows, replay-closure construction, loaded-environment traversal, and
  process supervision.
- Some helper implications are intentionally one-directional, including the
  supervision status rule, import-allowance case split, and replay dependency
  step. They are not described as stronger equivalences.

Neither half is one of `tl`'s product claims, so verifier-internal theorems do
not receive product landmarks or rows in the overview.

## Failure-path evidence

`Tests/VerifyTests.lean` covers report branches and remedies, clean fixtures,
source inventory, symlink refusal, dependency-policy violations, scope claims,
stored-body axiom propagation, rejection of an ill-typed theorem during replay,
and supervision against real worker processes.

`Tests/VerifyLoadedTests.lean` loads the real compiled environments without
initializers and covers module and declaration selection, artifact provenance,
stored import edges, cross-package replay closure, transitive-axiom observation,
and injected import/replay findings. Empty semantic groups fail rather than
reading as silent success. A hostile exit initializer is included as a live
no-execution and supervision canary.

## Bootstrap boundary

The supervisor marker cannot protect against worker code intentionally
printing that public marker and forging a clean result. `Verify/Main.lean`,
`Verify/Launcher.lean`, and the CI workflow are therefore protected-review
bootstrap code. Branch protection and review policy remain part of the gate's
operational trust, as they do for any CI enforcement mechanism.

Assembling the run is not part of what that review has to catch. A scope's
observation, and the environment it is built from, are typed by which scope they
belong to, and the seven reach the verdict through a structure with one
differently-typed field each, so a swapped, duplicated, or missing scope does
not compile. Review still covers the registry those types are checked against —
the roots and the source directories each scope claims — which the missing- and
unexpected-module arms also compare against each other on every run.

The design rationale and exact policy are recorded in
[ADR-0026](adr/ADR-0026-continuous-integration.md); module ownership and the
proved-versus-tested split are mapped in [codebase-map.md](codebase-map.md).
