# ADR-0028 — Release machinery: typed decisions and narrow adapters

- Status: Accepted (migration in progress)
- Date: 2026-08-14

## Context

The release pipeline began as POSIX shell around a native Lean build. As its
responsibilities grew, that shell accumulated JSON parsing, manifest and SBOM
generation, prerequisite classification, version consistency, channel policy,
npm package construction and publication, Homebrew rendering, and a second
language inside workflow `run:` blocks. Those are programs with data models and
failure semantics, not shell orchestration.

Hardening the scripts exposed the architectural problem. Correctness depended
on duplicated command tables, embedded platform mappings, shell-branch
selftests, a partial shell lexer, and a runtime PATH-shim campaign. Each closed
a real defect, but together they were compensating for decision logic living in
a language that could not represent its states directly. Extending that lexer
until it approximated shell execution was never a project goal.

At the same time, eliminating every shell file would be false economy. Three
programs run precisely where the release binary is unavailable or cannot be
the authority:

1. `install.sh` is the `curl | sh` bootstrap. It must download, authenticate,
   and install `tl` before `tl` exists locally.
2. `scripts/verify-release-artifacts.sh` is the standalone verification
   procedure. It must authenticate a candidate independently of the candidate
   and of repository-built release tooling.
3. `npm/tl/bin/tl` is npm's stable `bin` entry. It must locate the one
   platform-specific optional dependency npm installed before it can run the
   native `tl` binary.

The third boundary is easy to misclassify. It is runtime dispatch, not release
administration. Replacing it with JavaScript would start Node on every command;
using `postinstall` would add an optional, privileged lifecycle mutation and a
new supply-chain surface. The existing POSIX launcher instead ends with
`exec`, after which there is no wrapper process.

ADR-0006 owns supported platforms, channel semantics, licensing, provenance,
and signing identity. ADR-0014 owns the supply-chain threat model. ADR-0026 owns
the CI graph and the evidence its gates require. This ADR refines the overlap:
it owns the release machinery's component boundaries, sources of authority,
and intended implementation shape.

This machinery is a regression boundary over source admitted through protected
review. It defends against malformed or incomplete inputs, accidental workflow
and dependency drift, silent false-success paths, and an unreviewed widening of
the release surface. It is not a sandbox against malicious code already merged
into the workflow, `tlrelease`, the native shim, or one of the three retained
adapters; nor does it establish the integrity of a compromised runner,
toolchain, or gates job. Controls below therefore state only the property they
observe. In particular, a file-set hash establishes same-run transport equality,
an inventory counts declared shell surfaces, and a directory capability limits
path traversal beneath an operator-chosen anchor. None is provenance evidence
or a defense against another process holding the same authority.

## Decision

Everything in this section describes the accepted **end state**. The current
repository remains in the migration state described under “Migration is
explicit”: it still has the separate channel exclusion list, the pre-migration
shell inventory rather than the three files above, and the lexer/PATH-shim pair.
Present tense below is normative, not a claim that the cutover has already
landed.

### One repository-policy executable owns release decisions

`tlrelease`, built separately from the product, owns first-party release
administration. This includes:

- parsing and validating release configuration and evidence;
- build stamping, build metadata, SBOM and release-manifest generation;
- identity, version, target, prerequisite and policy decisions;
- artifact-set verification before signing or downstream publication;
- npm package construction, comparison, planning and publication;
- Homebrew formula rendering, comparison and publication;
- task-ID lint and other repository release-policy checks; and
- the human reports and stable exit behavior for those commands.

The name is historical, but the boundary is deliberate: `tlrelease` is the one
separately built repository-policy executable, not a claim that task-ID leakage
is release semantics. The task-ID command remains a separately reported CI
hygiene gate and never becomes evidence that an artifact is safe to publish.
It lives here so deleting the shell checker does not create a second policy
executable with another command registry and process contract.

GitHub workflow YAML owns scheduling, permissions, secrets, artifact transport,
matrix construction, and the jobs that may request OIDC credentials. Its
`run:` blocks invoke typed commands; they do not implement release policy, parse
release data, or contain publication algorithms.

That boundary is enforced over **authority flow**, not merely over jobs whose
own YAML happens to look privileged. A job is privileged when its effective
permissions (workflow defaults plus job overrides) include a write or
`id-token: write`, or when it receives a publication secret or the protected
`release` environment. Separately, an output is authority-bearing when it
controls whether a privileged job runs, which already-produced identity or
artifact it selects, or where it publishes. The latter rule is transitive
through `needs.*.outputs.*`: moving a policy branch into an apparently
unprivileged producer does not move the branch outside the guard. Every
authority-bearing output is produced by one named `tlrelease` invocation, and
its producer step, output mapping, consumers, and allowed predicate are pinned
together, except for the canonical pre-execution tool file-set hash described
below.
The rest of that producer job does not thereby become privileged: raw payload
builders may retain bounded orchestration, and their byte handoff is governed
by authenticated build evidence and the manifest rather than by pretending a
build script is a policy command.

In the end state, every policy step is exactly one `tlrelease` invocation.
Every `run:` scalar in a privileged job is one complete argv invoking an
executable declared for that job (`tlrelease` or a channel-native tool): no
pipe, redirection, assignment prefix, command substitution, backticks, heredoc,
conditional, loop, or `${{ ... }}` interpolation. Dynamic values enter through
named `env:` bindings and are referenced as quoted, positionally constrained
arguments. Pinned `uses:` steps have a closed action-and-input schema for the
job; an action input that contains script, shell, command, or expression code is
refused unless that exact action and field are modeled as an authority surface.
The job's runner/container identity, each `shell:` value, working directory, and
environment-key set are closed too; in particular no unreviewed `PATH`, loader,
startup-file, or tool-configuration variable may change which executable or
configuration the argv reaches. Job-level `continue-on-error` is forbidden on
every privileged job and every authority-output producer: otherwise a failed
handoff, authentication, or publication can be reported as a successful job
before any dependent job sees it. Step-level `continue-on-error` is forbidden
on the handoff and on every authentication, policy, or publication step.
Unprivileged best-effort builders may use a job-level override only when none of
their outputs is authority-bearing. A privileged job condition, and every
privileged step after the handoff, may not use `always()`, `failure()`,
`cancelled()`, `!cancelled()`, or any other status-function expression that
overrides GitHub's implicit success-only sequencing; a conditional business
predicate relies on that implicit success guard rather than rebuilding it with
Boolean operators.
This deliberately excludes `if: failure()` diagnostic uploads from a privileged
job: the ordinary job log remains immediate evidence, while durable failure
evidence is published before the failing command or collected by a separate
unprivileged diagnostics job from artifacts already handed off. Diagnostics do
not gain an `always()` exception inside an authority-bearing job.

`Tests/ReleaseTests.lean` reads the YAML structure, computes effective
permissions and authority-bearing output reachability, and refuses a privileged
job, authority-output producer, action input, or policy step outside those
forms. YAML quotes around control keys are normalized once. Authority edges
have one accepted spelling, `needs.<job>.outputs.<name>` in lowercase dot form;
bracket/case variants and anchors or aliases standing in for failure-control
values, whole steps, or output mappings are refusals, not edges the reachability
closure silently omits. Its
planted fixtures include workflow-level permission inheritance, a secret-only
job, a `needs` output produced by inline shell, direct expression interpolation,
quoted keys, aliases, case-varied status functions, privileged job- and
step-level status-function overrides, a handoff pattern matching zero or
multiple files, and a pinned action carrying a `script:` input. This is a small
authority and invocation grammar, not a general shell lexer. Unprivileged native-build steps
may remain multi-line build orchestration, but may not parse release
configuration, write an authority-bearing output outside its named producer
step, or publish.

The release-tool handoff is the one pre-execution comparison that cannot ask
`tlrelease` to check itself. It establishes only intra-run transport equality:
the privileged consumer received the same tool bytes the unprivileged gates job
hashed. It is not provenance evidence, does not authenticate the source commit,
and does not survive a compromised gates job; protected review, the gated build,
and the workflow identity carry those separate claims. The reason to replace
the current inline comparison is architectural as well as defensive: its
assignment and conditional cannot satisfy the privileged one-argv grammar.
This intentionally narrow claim follows the threat model in Context.

The value is named `releaseToolFileSetHash`, never `releaseToolDigest`.
`hashFiles` first hashes each matched file and then hashes that set of hashes, so
even for one file its result is not the file's SHA-256 digest. It may be compared
only with another `hashFiles` result over exactly one file containing the
handed-off bytes in the same workflow run. The gated executable is first staged
at the non-hidden path `release-tool/tlrelease`; the producer hashes and uploads
that exact path, rather than relying on `upload-artifact`'s hidden-file policy
for `.lake/`. The consumer path necessarily differs. The drift guard pins the
stage source and destination, upload source, and both hash patterns, requires
each pattern to match exactly one file, and refuses an empty result. The value
is never compared with a manifest digest, a `SHA256SUMS` entry, an artifact
digest, or a build-metadata digest.
The current `releaseToolDigest` remains a raw SHA-256 throughout migration; the
cutover adds `releaseToolFileSetHash` and removes the old output and all four raw
digest comparisons in the same change. Its existing name never changes meaning.

The producer is an explicit runner step in the unprivileged gates job, not a
`jobs.<job_id>.outputs` expression. A preceding unprivileged orchestration step
runs exactly
`install -D -m 0755 .lake/build/bin/tlrelease release-tool/tlrelease`; the
artifact upload names `release-tool/tlrelease`. The producer's exact shape is:

```yaml
- id: tool_file_set_hash
  env:
    RELEASE_TOOL_FILE_SET_HASH: ${{ hashFiles('release-tool/tlrelease') }}
  run: printf '%s\n' "fileSetHash=$RELEASE_TOOL_FILE_SET_HASH" >> "$GITHUB_OUTPUT"
```

The job output `releaseToolFileSetHash` maps only
`steps.tool_file_set_hash.outputs.fileSetHash`. Redirection is permitted here
because gates is unprivileged; the drift guard pins the stage, upload path, hash
path, environment key, output key, producer step, and job-output mapping. A
small real GitHub run exercises the pinned upload action and producer expression
before the old handoff is removed; local parsing cannot establish a hosted
action's file-selection semantics.

After download, each privileged consumer has one canonical step whose `if:`
expression refuses an empty `needs.gates.outputs.releaseToolFileSetHash`, an
empty `hashFiles('tool/tlrelease')`, or unequal values and runs the single argv
`/usr/bin/false`. The immediately following single-argv step runs
`/bin/chmod 0755 tool/tlrelease`. Those two prefixes deliberately differ because
macOS places `false` in `/usr/bin` and `chmod` in `/bin`; both paths also exist
on the supported hosted Ubuntu runner. The drift guard pins both steps, forbids
error/status overrides, and proves they dominate the first and every later
execution of the tool. No arbitrary expression is admitted by this exception.

Download, file-set comparison, the canonical `/usr/bin/false` mismatch guard,
`/bin/chmod`, and the **first** `tlrelease` invocation form one modeled handoff
prefix. Every real consumer and a dedicated capability-free rehearsal consumer
instantiate that same prefix; their steps after the first invocation may differ.
The prefix includes the first invocation, rather than ending at `chmod`, because
its structural purpose is domination: nothing may be inserted between validating
the downloaded bytes and first using them. The rehearsal establishes the prefix
and hosted artifact transport without exercising signing or publication
authority. A real tagged release remains the evidence for privileged effects.

Any inline job with `id-token: write` shares the release workflow identity that
the Sigstore pin accepts. Such a job is therefore behind the same protected
`release` environment as the signing job, even when the token is requested for
npm trusted publishing rather than cosign. It also receives only the minimum
permissions for its channel.

`release/` remains a separately audited scope and may not import `Tl.*`.
Release administration is not part of the shipped product and is not part of
the product TCB. Lean is chosen here for closed data types, total pure
decisions, one parser, and maintainable tests—not to relabel I/O code as proved.

That source boundary applies to native links too. `tlrelease` may link only the
in-repository `tlsys.o` object recorded in ADR-0019, and may reach it only
through release-prefixed bindings; it may not declare a binding to a
product-prefixed `tl_sys_*` symbol. The release drift gate enumerates every
external declaration in the loaded release environment and pins its declaring
module, native symbol, and full Lean signature. It refuses an external
declaration elsewhere in the release scope and any product-prefixed symbol.
The one raw array-taking declaration is private to `release.Sys`; release code
can invoke the primitive only through the public mechanism whose arguments are
the sealed directory and component-list types. The registry pins that compiled
privacy boundary as well as the native symbol and type.
Separately, it pins the executable's complete native/custom linker-input set and
the build recipe that compiles `tlsys.o` from exactly `ffi/tlsys.c`; checking
only `moreLinkObjs` or only the source bindings would leave a substitution gap.
This is separate from the trust verifier's Lean-import audit, which cannot
observe linked objects. Adding an object, build input, or FFI declaration
therefore requires one protected change that states its release contract, adds
its branch tests, amends ADR-0019, and widens the exact registries. Linking the
shared object does not grant ambient authority to every symbol it exports. A
permanent drift row also refuses formatted-native-error classification such as
`contains ":E...:"` anywhere under `release/`; native operation and errno are
structured data, never prose parsed back into policy.

Release evidence writes use a directory-capability API, not an arbitrary path
opened from scratch. Every writing command accepts the same explicit
`--output-dir <dir>` option, defaulting to the process working directory; it
never discovers a repository root or derives a base by splitting the output
path. Its output name is a sealed, non-empty list of validated relative
components. Absolute paths, empty components, `.`, `..`, and embedded NUL are
rejected at the Lean boundary, and the native primitive consumes the component
array without reparsing a path string. A writing command creates no directory
on the way to its output either: a path-resolving `createDirAll` beside the
anchored writer follows a symlinked component and puts the directory outside the
base the writer would then refuse to be redirected out of, which is the boundary
undone by its own preparation. Directories beneath the base are required to
exist, and the writer's refusal names the one that does not. The raw array-taking extern is private to
the binding module, so another release module cannot bypass the sealed
component type by constructing an unchecked array.

Minting the capability intentionally opens the operator-supplied base with
`O_DIRECTORY | O_CLOEXEC`, follows any symlink used to select that base, and
then requires the opened directory to be owned by the effective uid. Applying
`O_NOFOLLOW` to the base would wrongly reject ordinary anchors such as macOS
`/var`, symlinked home directories, and test temporary directories. The
no-follow and ownership walk starts at the first component **beneath** the held
base descriptor. The primitive creates the predictable sibling exclusively
with `O_CREAT | O_EXCL | O_NOFOLLOW`, writes the complete bytes, renames within
the held final-directory descriptor, and removes the sibling only after this
invocation created it. A container therefore supplies a separate writable
scratch mount and a pinned `--user` that owns it; the read-only checkout is not
used as an output capability.

The mechanism reports facts without imposing the product's durability policy:

```text
SyncStrength       = fullBarrier | ordinaryFsync
DirectorySync      = synced | unsynced syncError
CleanupDisposition = notCreated | removed | retained cleanupError
WriteOutcome       = committed SyncStrength DirectorySync
                   | failedBeforeCommit primaryError CleanupDisposition
```

On Darwin, an interrupted `F_FULLFSYNC` is retried; a documented unsupported
result may fall back to ordinary `fsync`, while an operational failure such as
`EIO` or `ENOSPC` refuses before rename. A successful rename followed by a
directory-sync error is still `committed`: subsequent opens in the live release
run observe the replacement, while the durability observation remains available
to report or escalate. Release evidence requires atomic visibility inside the
run, not a promise that survives power loss after the run itself has died, so
release policy accepts `ordinaryFsync` and records an unsynced directory rather
than misreporting a landed write as absent. The product's durable-write contract
is a separate ADR-0015/ADR-0019 policy question over the same mechanism.

Operation and errno are structured fields rendered into teaching messages
above the binding. Public-command and injected-fault tests derive from the
phase and path-shape matrix, including intermediate symlinks and regular files,
invalid components, occupied staging paths, partial and interrupted writes,
both sync strengths, close, rename, post-rename directory sync, permissions,
and cleanup ownership. Per the threat model in Context, the remaining
operator-controlled-base assumption is explicit in `docs/overview.md`: a
process that can mutate accepted directories concurrently can still interfere
after their descriptors have been accepted.

### The signed manifest is the downstream authority

The signed GitHub Release artifact set is the source of payload bytes. Its
`release-manifest.json` is the authoritative typed description of those bytes
and of every downstream channel projection.

Authentication and description remain two explicit checks. The standalone
verifier and pinned cosign identity establish that the artifact set is the one
this repository signed. `tlrelease manifest-verify` establishes that the
directory contains exactly the bytes the manifest describes. Inside
`tlrelease`, full parsing and structural verification then produce the typed
description downstream consumers use: the expected assets are present, no
undescribed asset is admitted, digests agree with build-leg evidence, target
and channel rows are complete, and the release identity is internally
consistent. Neither check substitutes for the other.

Every downstream job authenticates the artifact set **before** parsing the
manifest or acting on any value it contains. npm and Homebrew commands then
consume that description. They must not
independently infer targets from directory listings, recover digests from
`SHA256SUMS`, or recompute prerelease policy from the tag.

The manifest does not grant ambient authority. A verified description says
what may be published; the workflow job's narrowly scoped credential says
where it may be published.

### The plan is the sole channel-enablement authority

`release/plan.json` is parsed into a closed distribution-surface model. It is
the only place that says whether GitHub Release, the installer, npm, or Homebrew
participates in a release.

Each surface has a closed, typed effect set rather than being forced into one
false uniform shape. GitHub Release, npm, and Homebrew are publication channels:
when enabled they contribute their declared prerequisite rows, workflow job,
and publication command. The installer is a repository-served adapter over the
GitHub Release and has no separate publish job or publication command; enabling
it contributes its presence, documentation, and bootstrap-suite obligations.
Tests pin that only the three publication channels carry publication effects
and that the installer does not silently acquire one. An enabled surface
contributes exactly its declared effects; a deferred surface contributes none
of its release-path effects, while its implementation remains exercised by the
ordinary CI profile so it cannot rot. There is no separate exclusion list whose
explanation can drift from the plan.

### Channel publication is a projection, not another build

Every downstream channel packages the already-verified GitHub Release payload.
It never rebuilds `tl` and never substitutes locally derived bytes.

Publication is resumable and fail-closed. Equality is channel-specific rather
than a claim that every carrier has reproducible container bytes:

- absent destination state may be created;
- an existing GitHub asset is equal only when its digest agrees;
- an existing npm version is never republished; it is accepted only when its
  normalized package tree agrees path-for-path on entry type, regular-file
  bytes, and executable mode, independent of tar/gzip metadata. A staged
  symbolic link is refused unless a future npm-native oracle first establishes
  one published representation that can be compared without normalization
  ambiguity;
- an existing Homebrew publication is equal only when the rendered formula
  text agrees;
- conflicting immutable state is refused with the conflicting identity named;
- a partial run can resume without republishing completed units; and
- the user-facing npm launcher is published after its platform packages, so a
  new root version never points at packages that do not yet exist.

The GitHub Release remains valid if a downstream channel fails. Repairing or
resuming a channel does not re-sign or mutate the source payload.

### The installer and standalone verifier have explicit action budgets

`install.sh` may resolve a requested or latest stable version; classify a
supported platform; fetch the named HTTPS release assets; verify the pinned
Sigstore identity and bundles with `cosign`; compute the mandatory digest with
`sha256sum` or `shasum`; honor the explicit
signature-only escape without bypassing the digest; install the binary
atomically; and place an authenticated notice when present. It may not read the
release plan, decide channel publication, invoke a budgeted release runtime
(`python`, `python3`, `ruby`, `brew`, `node`, or `npm`), execute downloaded code
before verification, or fetch from a location not derived from the configured
release repository and version. The system `shasum` on macOS is an explicitly
permitted digest tool even though that program is implemented in Perl; the
contract is over the invoked tool and its purpose, not its private runtime.
It may not source or evaluate tracked repository code; its complete behavior is
in this one adapter.

`scripts/verify-release-artifacts.sh` may read the inert signing pin, enumerate
the explicitly named local subjects, run `sha256sum` or `shasum` and the
supported cosign verification modes, and report authentication results. It may
not fetch, publish, repair, install, read the release plan, invoke a budgeted
release runtime, source a repository policy library, or treat an unavailable
verifier as tampering. Its use of the permitted macOS `shasum` carries the same
tool-versus-implementation distinction as the installer. More generally it may
not source or evaluate any tracked repository code; its complete behavior is in
this one adapter.

Their public black-box suites exercise every supported branch under an isolated
PATH containing only declared fixture tools; the suite proves each stub it
relies on was actually reached. The npm launcher has the equivalent contract
and real `npm pack`/install/process tests in the npm section below. These tests,
the exact action lists above, and the protected-review obligation enforce the
bounded-adapter claim. The macOS limitation that remains after the lexical arm
is retired is stated under external dependencies and in `docs/overview.md`.
This per-adapter fixture isolation is not the retired repository-wide PATH-shim
campaign: it gives one bounded program declared collaborators and fault
responses inside its own tests; it does not scan or claim to police arbitrary
release scripts by intercepting forbidden runtimes.

### npm remains native at invocation time

The public `@taskloop/tl` package has one exact-version optional dependency per
distributed OS/architecture pair. The platform packages contain the same native
binaries described by the signed manifest.

`npm/tl/bin/tl` remains a POSIX-shell dispatcher because npm's root `bin` path
is static and cannot point conditionally into whichever optional dependency was
selected. The launcher may:

- resolve its real package location through npm's symlink;
- classify the supported operating system, architecture, and libc;
- locate a hoisted or nested platform package;
- diagnose an absent, mismatched, unsupported, or non-executable package; and
- `exec` the selected native binary with the original argument vector.

It may not download, install, link, copy, repair, interpret release policy, or
run a lifecycle action. The package has no `preinstall`, `install`, or
`postinstall` script. The launcher uses no JavaScript process. `exec` makes the
native binary own signals, process identity, standard streams, job control, and
exit status directly. It may not source or evaluate tracked repository code;
its complete behavior is in this one adapter.

All npm administration—rendering the five package manifests, staging the
packages, comparing regular-file contents and modes while refusing symbolic
links, selecting `latest` versus `next`, bootstrapping placeholder packages,
checking registry state, and publishing resumably—belongs to `tlrelease` and the
channel-native `npm` client.

The five `package.json` documents are rendered from `release/identity.json` and
`release/targets.json` rather than tracked by hand and patched at staging time.
The `os`, `cpu` and `libc` constraints that decide where npm installs a package,
and the exact-version `optionalDependencies` that decide which packages resolve,
are therefore a function of the release. A Linux target must name a libc family
npm selects on; declaring none renders a package that installs on musl as
readily as on glibc, and declaring one npm does not recognise reads in the
manifest as a constraint while applying none. The tracked copies under `npm/`
are what the renderer produces at version `0.0.0` and are compared against a
fresh render on every commit; they are reviewable, not authoritative, and a
stray `npm publish` from a checkout cannot consume a real release number.
Provenance is declared by everything the workflow publishes and by nothing the
one-time bootstrap produces, because npm generates an attestation only on a CI
provider it supports and refuses the publish anywhere else.

What npm will publish is asked of npm rather than derived from the tree: `npm
pack --dry-run --json` reports the entry list and mode for a directory or a
tarball, which is the question `files`, `.npmignore` and npm's always-included
set jointly answer. A directory argument is passed unambiguously — npm reads a
bare two-segment relative path as a hosted-git shorthand — and the `package.json`
of the directory about to be published is compared against the name and version
this release reports publishing, because npm takes both from that file and from
nothing else.

Publication is surveyed before it acts. Every package's registry state is
established first, and a conflict on any of them refuses before the first
irreversible publish; the dist-tag is read as part of that survey, because it is
separate registry state that a partial run leaves lagging and OIDC trusted
publishing authorizes `npm publish` and no other mutation.

The channel is exercised twice, and so is the launcher. Every decision and
refusal is driven through the public commands against a stub client, which needs
no npm and therefore runs in the ordinary suite; `tlrelease npm-selftest` packs
and installs real packages with the real client and drives the launcher through
them, establishing npm's package layout, executable mode, tarball round-trip and
transparent process behavior. It is a deferred-channel gate rather than part of
the ordinary suite, because the release profile may not reach npm at all. In
addition, the same post-pack launcher bytes run inside the runtime-stripped
inner container against a planted installed-package tree and stub native
binary. Injected `uname` and libc observations drive every supported and
refused platform branch, and the stub proves the final `exec` path was reached.
That second suite requires neither npm nor Node and closes the dependency-budget
claim over the launcher rather than omitting it because it is not a publication
command.

### Homebrew keeps only its required Ruby surface

`Formula/tl.rb` remains Ruby because a Homebrew formula is a Ruby DSL. It is a
rendered channel artifact, not an administration program.

`tlrelease` consumes the verified manifest, renders the complete formula,
removes unavailable best-effort targets, preserves signature and licence
requirements, and refuses to render a formula missing any Supported target. It
compares destination state and updates the tap through explicit external
commands. Real Homebrew remains the acceptance authority for formula load,
style, audit, resolved URLs, and installation behavior; `ruby -c` alone is not
evidence that Homebrew accepts a formula.

### Exactly three tracked shell programs remain

After migration, the tracked shell inventory is exactly:

```text
install.sh
scripts/verify-release-artifacts.sh
npm/tl/bin/tl
```

The deliberately boring inventory unions only (1) tracked paths ending in
`.sh` and (2) tracked regular files whose first line is a recognized shell
shebang. The result must equal the three paths above, and each survivor is
pinned separately to the exact `#!/bin/sh` shebang. An unreadable candidate is
a refusal. There is no configuration escape or registry of extra scripts:
adding one requires changing this ADR and the exact allowlist in the same
protected change. Workflow YAML, the Homebrew Ruby DSL, generated data, and the
npm launcher's final dynamic `exec` are governed by their own typed grammar,
action budget, and process tests rather than being classified as shell programs.

Per the threat model in Context, this check counts declared shell surfaces; it
does not claim to discover a tracked data file that already-trusted shell code
secretly passes to `sh`, or code hidden in a workflow scalar. The survivors may
not source tracked code, start a nested shell, or implement an undeclared
decision under their separately enforced action budgets. Their Lean-driven
black-box harnesses start each adapter as a user would, supply only declared
external-tool stubs, and exercise every supported branch. That is the boundary
against policy growing back into shell. Teaching the inventory a partial argv
or shell grammar would add complexity without defending against malicious code
inside an already admitted adapter.

The three scripts are adapters with bounded decisions, not a shared policy
layer. No surviving shell library is their canonical source. Nothing an adapter
carries is held to a shell file: platform classification is compared with the
typed target model, through `release/Platform.lean` and `tlrelease
platform-classification`; the inert signing pin is render-and-compared with
`release/identity.json`, through `tlrelease check-pin`; and shared utility
behavior is driven through one planted corpus against each public adapter,
which for the installer's digest and case helpers is the installer corpus in
`Tests/ReleaseToolTests.lean`. A block that is more safely generated may
instead be rendered from a typed definition and compared byte-for-byte. Each
replacement was mutation-checked while the old library still existed, because
deleting the literal file the old guard read would otherwise have deleted the
guard rather than migrating it.

No shell parser, command-spelling corpus, or repository-wide PATH-shim framework
is part of the steady-state architecture. The bounded fixture PATHs
inside each retained adapter's own branch tests remain ordinary test doubles.

### External dependencies are typed and exercised at the right boundary

Each `tlrelease` command declares the external tools and channel capabilities it
may use. Policy profiles are derived from the same command registry rather than
maintained as a parallel shell gate list. A command cannot silently become a
smaller check because a tool is missing: required-tool absence is a typed
refusal with a teaching remedy.

Enforcement has four complementary layers:

1. every pure, total acceptance or verdict function whose silent false negative
   could make a gate, evidence set, or publication decision read as valid is
   characterized by a theorem, with any unprovable residual recorded
   explicitly;
2. every I/O and process branch is exercised through public-command fixtures,
   including unavailable, malformed, timeout, non-zero, and conflicting
   external responses;
3. real npm and Homebrew jobs exercise the channel-native tools and packaging
   behavior that stubs cannot establish; and
4. the complete first-party GitHub-only release policy and all three retained
   adapter suites run inside a pinned inner container launched by one outer
   `run:` step, with the checkout mounted read-only, a separate writable scratch
   directory, no container-engine socket, and no network. The drift guard pins the complete
   outer `podman run` argv, including the image identity, read-only checkout
   mount, writable scratch mount, disabled network, absent socket, and numeric
   `--user` matching the scratch owner; these flags are authority-bearing
   configuration, not incidental shell text. Before trusting the run, it checks
   both PATH and the container filesystem for Python, Ruby, Homebrew, Node, and
   npm.

The container engine is rootless Podman; Docker is not a prerequisite. The
runner maps to container uid/gid 0 explicitly, and the inner ownership probes
check it against the scratch mount. Container root has no capabilities and is
the unprivileged runner on the host; it can enumerate the root-owned image
directories without modifying checkout ownership. Implicit writable temporary
mounts are disabled with `--read-only-tmpfs=false`. On macOS local reproduction
uses a Podman Linux machine; ordinary builds and tests need neither engine.

The namespace setting is `--userns host --user 0:0`. The preflight requires
rootless Podman, so “host” here reuses Podman's existing rootless user namespace:
container uid/gid 0 still map to the invoking host user/group, and nonzero image
owners map to allocated subordinate ids. It does not mean host-root execution.
The subordinate range is needed when unpacking a fresh image with nonzero
owners; testing only with cached image layers can hide an invalid single-id
mapping. Reusing this standard mapping also avoids the hosted runner's rejected
`gid_map` from the earlier `keep-id` override to uid/gid 0.

The inner image is defined by what it contains as well as what it excludes. Its
closed, pinned input set includes a POSIX shell and the ordinary file utilities
the adapter suites declare, Git, `sha256sum`, ShellCheck, actionlint, and either
the pinned Lean/Lake toolchain with its dependency cache or digest-verified
handoff binaries for every compiled gate the selected policy invokes. The
standalone verifier selftest supplies its own declared cosign stub and proves
that stub was reached; a row that invokes real cosign instead must receive a
pinned binary and an offline trust root explicitly. No gate may download a
missing tool or refresh trust state through the disabled network. A checked
manifest of these positive inputs is part of the job evidence, so “minimal” is
not an unreviewed base-image property.

Adapter fixtures may add a declared `shasum` stub to their isolated PATH and
must prove that the fallback reached it. That does not make `shasum` an ambient
image dependency: the branch is selected solely by digest-tool availability and
is executed on Linux with a planted collaborator. The real macOS `shasum` is
separately an allowed digest tool under the adapter action budget, even though
its implementation uses Perl.

The inner-container distinction is load-bearing. A GitHub job-level container
may receive the runner's external Node installation so JavaScript actions work;
“not on PATH” would then be the same evidence as a shim. The outer job may use
pinned JavaScript actions as CI infrastructure, but their mounted runtime never
enters the inner container that supplies the dependency-budget evidence.

For Linux-exercised paths, this closes the residual where an interpreter name
or absolute path is assembled at runtime: the interpreter is absent regardless
of spelling, and the read-only/no-network boundary prevents the test from
installing one. It does not prove an unexecuted branch unreachable;
comprehensive public-command tests remain responsible for every branch and
error path.

The residual criterion is whether a forbidden-runtime branch requires the
actual Darwin host to become reachable. The standalone verifier has no such
branch: its `sha256sum`/`shasum` choice depends only on PATH availability, so the
isolated fixture above executes both arms, and `shasum` itself is permitted.
The npm launcher executes supported/refused platform cases and glibc-present
and musl-present cases through injected observations and a planted native
target. The arm64-loader-only and neither-loader file-existence paths are not
yet exercised: hiding the image's real musl loader would also prevent its
dynamic shell and utilities from running. Covering these remaining paths needs
a declared static shell/utility fixture and a separate library observation
mount, without changing launcher bytes or adding container capabilities.

An actual macOS-only branch of `install.sh` is different. Hosted macOS contains
`/usr/bin/python3` and `/usr/bin/ruby`, and the Linux container cannot execute a
Darwin binary path. After the lexical arm is deleted, the claim that an
unobserved installer branch does not invoke a preinstalled absolute forbidden
interpreter rests on the installer action contract, injected-platform
black-box tests, and protected review. This is an explicit carried assumption
in `docs/overview.md`, not evidence the hermetic job produced. The trade is
accepted for the one adapter with actual host-conditional reachability rather
than retaining a general shell parser forever. This bounded residual follows
the threat model in Context: protected review is trusted, while the container is
evidence against accidental dependency growth on the paths it actually runs.

Channel-native jobs are outside the runtime-stripped environment: npm requires
npm/Node, and Homebrew requires Homebrew/Ruby. GitHub Actions' own implementation
runtimes remain CI infrastructure, not first-party release dependencies.

### Coverage follows the repository's three-tier rule

The three-tier rule classifies properties by the consequence of a wrong answer,
not by implementation language. In this separately audited, non-product-TCB
scope, every pure, total acceptance or verdict function whose silent false
negative could make a gate, evidence set, or publication decision read as valid
is characterized by a theorem. Other parsers, renderers, and transformations do
not acquire an open-ended proof obligation merely because they are pure Lean;
they receive comprehensive tests unless a relied-on invariant is promoted to a
formal claim. Any such claim is proved, or decomposed with its residual recorded
as a carried assumption in `docs/overview.md`. Theorems are about the functions
the commands actually call, not nearby examples. Release I/O, subprocess
behavior, filesystem behavior, registry clients, and workflow integration
remain outside the TCB and receive comprehensive branch and error-path tests.

The release proofs do not become product landmarks or proved product claims.
They live in the separately audited release scope and are pinned against silent
deletion by `pinnedReleaseVerdictTheorems` in
`Tests/ReleaseToolTests.lean`, following the same distinction ADR-0026 makes
for the trust verifier's internal verdict theorems. That compile-time registry
names every **non-private release contract theorem**, exhaustively: the question
to ask of it is whether any public theorem in the release scope is missing, not
how many it holds.

Two boundary cases fix what counts. `Check.allHeld_iff_noFailures` is in it,
because a public reusable report/verdict contract is one whether or not a single
command owns it. Private proof scaffolding is not, even where a command's proof
term currently depends on it: the helpers behind `manifestAccepts_iff` and
`auditBlockers_partition` establish nothing those two public statements do not
already expose, so a proof refactor may replace a helper without retiring a
public guarantee.

Adding a new public release contract theorem therefore includes its pin in the
same change. Protected review owns the registry's completeness; compilation owns
the survival of every registered theorem.

### Migration is explicit

Until the cutover lands, ADR-0026's existing policy scripts, dependency-boundary
scan, PATH-shim runner, and channel selftests remain required gates. They are
deleted only after the corresponding public `tlrelease` commands and tests are
live in both workflows.

The cutover and a capability-free GitHub rehearsal both precede the v0.1.0 tag.
The four formerly active GitHub-only defects retired in
`docs/design-backlog.md` are not
deferred to that rehearsal: the existing Lean ports already close them at the
decision layer. `Targets.parse` and manifest assembly refuse an empty target
set, `RunContext` binds every build record to the executing run, the GitHub
client keeps 404 apart from an unreadable response, and
`restrictsTagCreation` requires coverage of the whole release-tag namespace.
Their public-command and pure-decision rows remain required through cutover.
npm and Homebrew may still be disabled in `release/plan.json` for v0.1.0; their
complete implementations and ordinary CI gates land before the shell deletion,
while external namespace/tap bootstrap controls when the channels are enabled.

The migration is a partial order, not an unnecessarily serialized checklist.
Six workstreams may proceed in parallel while the old gates remain live:

- widen the manifest parser into the full typed downstream description, then
  port Homebrew and npm administration to public `tlrelease` commands;
- port build stamping and task-ID lint, including the canonical GitHub
  file-set-hash handoff above and ADR-0026's resulting `gates` → `stamp` edge;
- replace the embedded-copy guard with the typed/rendered and behavioral
  adapter guards above, mutation-checking them while
  `scripts/lib/release-common.sh` still exists (landed: the guard is
  `tlrelease platform-classification` plus the installer corpus, and the
  library's uname reference functions are gone);
- build the nested hermetic harness and the three retained-adapter suites while
  the lexical and runtime arms still provide comparison evidence. The exact
  three-program inventory work moves self-reexecution and nested-shell probes
  out of retained files before tightening the adapter budgets at cutover;
- replace release evidence writes with the directory-capability and typed-outcome
  native interface above. The common `--output-dir` option, component-list
  output path, workflow invocations, `Command.invocation`, and drift-guard
  literals land atomically because no intermediate CLI has coherent callers.
  The same work pins the complete release extern/signature registry, native
  linker inputs, `tlsys.o` build recipe, and the permanent no-formatted-errno
  rule while the old write behavior remains available as a comparison oracle;
- construct the typed policy registry before switching either workflow. During
  coexistence, a temporary parity oracle requires its gate and profile lists to
  equal the shell policy's lists and is mutation-checked. The oracle is deleted
  with the shell policy after the typed registry becomes authoritative.

The cutover then has strict dependencies:

1. all channel commands and their characterization-theorem pins, the typed
   policy registry and parity oracle, the handoff bootstrap, replacement copy
   guards, native write boundary, and hermetic suites are green;
2. CI and release workflows switch to the typed policy registry, the
   authority-flow and invocation grammar becomes a gate, and the final
   cut-over workflow passes in the nested environment;
3. one atomic change deletes the replaced scripts, shared libraries, migration
   lexer, spelling corpus, runtime shims, and parity oracle and installs the
   deliberately lexical two-arm shell inventory over the exact three survivors.
   That change also removes the old boundary command and
   updates ADR-0006's entry-point list, dual-arm rationale, Formula authority,
   interpreter/file inventory, ADR-0026's gate description, the codebase map,
   and any stale shell defects in the design backlog; and
4. the capability-free GitHub rehearsal instantiates the same canonical handoff
   prefix as every real consumer over the cut-over workflow before the v0.1.0
   tag is created. The v0.1.0 release itself, not this rehearsal, exercises OIDC,
   signing, and irreversible publication.

No transitional checker is described as permanent architecture merely because
it is still needed before the atomic deletion.

## Consequences

- Release-administration decisions have one implementation language and one
  typed command registry instead of shell, Python, embedded workflow programs,
  and Lean independently deciding adjacent parts of the same release.
- The shell floor is three files, not zero. Each survives because it is a real
  bootstrap or runtime boundary, not because its logic was too difficult to
  port.
- npm invocation stays native and transparent; installation gains no lifecycle
  hook or arbitrary download.
- npm and Homebrew consume the same verified release description, so target,
  digest, version, and prerelease decisions cannot drift by channel.
- Workflows become easier to review: permissions and job edges remain visible,
  while policy and publication algorithms move into compiled, directly tested
  commands.
- Adding a channel means adding a closed channel value, manifest projection,
  plan state, prerequisites, typed tool requirements, public commands, and CI
  coverage together. If its job can mint a certificate the release pin accepts
  or holds a publication secret, the same protected environment and
  least-privilege review are part of that addition. A string in workflow YAML
  is not sufficient.
- The release executable remains outside the product TCB. Moving code to Lean
  improves representation and testability; it does not make external effects
  formally verified.
- ADR-0006 remains authoritative for what ships and how users authenticate it;
  ADR-0014 remains authoritative for residual trust; ADR-0026 remains
  authoritative for which CI evidence must be visible.

## Alternatives considered

- **Keep hardening the shell implementation.** Rejected. A shell lexer and
  PATH shims can catch spellings and observed executions, but neither provides
  a maintainable model of release state. The nested hermetic job closes dynamic
  interpreter discovery on the Linux-exercised GitHub-only path, while typed
  commands remove the decision code that created the need for lexical policy.
  The narrower macOS residual is carried explicitly rather than misreported as
  hermetic evidence.
- **Eliminate all shell.** Rejected. The installer and standalone verifier
  exist where trusting a repository-built release executable would be circular,
  and npm needs a stable dispatcher before the platform binary can run.
- **Use JavaScript for the npm launcher.** Rejected. It adds Node startup to
  every `tl` invocation and introduces a forwarding process unless it replaces
  itself through platform-specific machinery. POSIX `exec` is smaller and
  preserves native process semantics.
- **Use `postinstall` to select or download the npm binary.** Rejected.
  Lifecycle scripts may be disabled, mutate installation state, run with the
  installing user's privileges, and create a new fetch/integrity boundary. The
  platform binaries instead arrive as exact-version ordinary dependencies.
- **Put release logic directly in workflow YAML.** Rejected. Workflow snippets
  are difficult to execute comprehensively outside GitHub, duplicate policy
  across CI and tagged releases, and mix permissions with data processing.
- **Let each channel rediscover the release independently.** Rejected. Reading
  directory contents, `SHA256SUMS`, and tags separately recreates multiple
  authorities. A signed typed manifest already exists to settle those facts
  once.
- **Make `tlrelease` part of the product executable or TCB.** Rejected. Release
  administration is repository tooling with substantial I/O and external-tool
  behavior. Coupling it to `tl` would enlarge the shipped surface and blur the
  proved-product boundary without strengthening artifact trust.
