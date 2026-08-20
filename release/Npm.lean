/-
The npm channel: the five packages this project publishes, what each one
contains, and what the registry must already hold before one is published over.

Three decisions live here, and each replaces shell that could not make it
safely.

**What a package manifest says.** The five `package.json` documents were tracked
by hand and then patched at staging time by a Python heredoc, with a second
Python pass validating the result against the checkout — a construction step and
a verification step that could disagree about the same file. They are rendered
here instead, from the release identity and the distributed target list, so the
`os`/`cpu`/`libc` constraints that decide *where npm installs a package* and the
exact-version `optionalDependencies` that decide *which packages resolve* are a
function of the release rather than of a file somebody remembered to edit. The
tracked copies under `npm/` are what this renderer produces for version `0.0.0`,
compared byte-for-byte by the suite: they exist so the shape is reviewable in
the repository, not so it is authoritative.

**Whether a published version is the one this release staged.** npm versions are
immutable, so this is the decision that cannot be repaired afterwards. It is
taken over a *normalized package tree* — path, entry type, regular-file digest,
and executable bit — rather than over tarball bytes, because gzip output is not
stable across npm versions or runner images and a byte comparison would report a
conflict on a re-run that changed nothing. A staged symbolic link is refused
outright: npm's served tree does not represent one comparably, so there is
nothing on the published side to compare it against.

**What order the packages go out in.** The launcher declares its platform
packages as exact-version optional dependencies, so it is published last. A
partial run is then always a prefix of a good one, and resuming never leaves a
published launcher resolving names the registry has not received.

`tlrelease` owns all of it; the channel-native `npm` client is invoked only to
talk to the registry. `npm/tl/bin/tl` stays a POSIX-shell dispatcher because npm
needs a static `bin` path to `exec` through (ADR-0028).
-/
import release.Manifest

namespace Release

namespace Npm

open Lean (Json)

/-! ## What a package is

The layout is the tracked one — `tl/` for the launcher and `platform/<target>/`
for each native package — and staging reproduces it rather than inventing a
second set of directory names. One layout means the drift check against the
tracked copies is the same comparison the release performs. -/

/-- Where the launcher package sits, beneath a staging root or beneath `npm/`. -/
def launcherDirectory : String := "tl"

/-- Where one platform package sits. -/
def platformDirectory (target : String) : String := s!"platform/{target}"

/-- The `bin` path npm publishes and the launcher package points its `bin` field
    at. Fixed by npm: the root package's `bin` cannot be chosen per platform, so
    every package puts its executable at the same place. -/
def binRelative : String := "bin/tl"

/-- What `files` lists, and therefore what npm puts in the tarball.

    The binary is here because a platform package has no `bin` field — npm's
    always-included set covers `package.json`, the README, the licence, and
    whatever `main`/`bin` names, and for a platform package that is everything
    *except* the binary. Dropping this entry produces a package that installs
    cleanly and contains no `tl`. -/
def packageFiles : List String :=
  [binRelative, "README.md", "LICENSE", "THIRD-PARTY-LICENSES"]

/-- The two licence files that travel in every distribution artifact
    (ADR-0006). Copied from the repository root at staging time; a second copy
    tracked under `npm/` would be a second thing to drift. -/
def licenceFiles : List String := ["LICENSE", "THIRD-PARTY-LICENSES"]

/-- How a platform is described in prose, for the package `description`.

    Keyed on the pair rather than composed from the two halves, because
    "x86-64", "Apple silicon" and "Intel" are what a reader on that platform
    recognises and none of them is the wire name. Unknown pairs return `none`
    and refuse the render: a package published with the wrong platform prose is
    immutable, and inventing "linux on riscv64" from the wire names would make
    that the silent outcome of adding a target. -/
def platformProse : String → String → Option String
  | "darwin", "arm64" => some "macOS on Apple silicon"
  | "darwin", "x64" => some "macOS on Intel"
  | "linux", "arm64" => some "Linux on arm64"
  | "linux", "x64" => some "Linux on x86-64"
  | _, _ => none

/-- The libc families npm selects on. A value outside this set matches no
    family, so npm applies no constraint and installs the package everywhere —
    which reads in the manifest exactly like a constraint that works. -/
def libcFamilies : List String := ["glibc", "musl"]

/-- Which libc constraint a target's package must declare, or why it may not be
    rendered.

    An operating system whose packages are selected by libc must say which one.
    The published Linux binaries are glibc-linked, and without the constraint
    npm installs them on musl, where the exec fails on a missing loader — so an
    absent `libc` on a Linux target is refused rather than rendered as "runs
    anywhere". macOS has no such split and must not claim one. -/
def libcConstraint (target : Target) : Except String (Option String) :=
  match target.os, target.libc with
  | "linux", none =>
      .error s!"the manifest describes {target.name} without a libc family. npm selects Linux packages on it, and a package that declares none installs on musl as readily as on glibc — where a glibc-linked binary fails to exec on a missing loader. Record the libc in release/targets.json."
  | "linux", some libc =>
      if libcFamilies.contains libc then .ok (some libc)
      else
        .error s!"the manifest describes {target.name} with libc '{libc}', which is not a family npm selects on ({String.intercalate ", " libcFamilies}). npm ignores a constraint it does not recognise, so the package would install everywhere while the manifest reads as though it were constrained."
  | _, none => .ok none
  | os, some libc =>
      .error s!"the manifest describes {target.name} on {os} with libc '{libc}'. Only Linux packages are selected by libc; declaring one elsewhere is a constraint npm does not apply, recorded as though it did."

/-- Whether a string is a published package name this tool may act on.

    Two separate hazards, closed once. npm reads an argument beginning with `-`
    as an option rather than as a package spec, so a name spelled that way would
    silently change what `npm view` or `npm publish` was asked to do; and a name
    carrying whitespace or a second `@` is not a spec npm resolves at all. The
    target half of every platform package name is already closed by
    `validTargetName`; this closes the scope half and the launcher, which come
    from `release/identity.json` and from the signed manifest. -/
def validPackageName (name : String) : Bool :=
  let body := if name.startsWith "@" then (name.drop 1).toString else name
  let plain := body.all fun c =>
    ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-' || c == '_' || c == '.' || c == '/'
  name.startsWith "@" && (body.splitOn "/").length == 2 && plain
    && !body.startsWith "-" && !body.startsWith "."

/-- What the tracked copies claim, and a version this project will never tag.
    A `0.0.0` package pinning `0.0.0` platform packages resolves to nothing a
    user could install by accident. -/
def placeholderVersion : String := "0.0.0"

/-- Everything the five manifests are a function of. -/
structure Spec where
  /-- The launcher's published name, from `release/identity.json`. -/
  launcher : String
  /-- `owner/name`, for the homepage, bug tracker and repository fields. -/
  repository : String
  /-- The version every package in the set carries. One value, because npm
      resolves the optional dependencies by exact version and a set that
      disagreed with itself would resolve to nothing. -/
  version : String
  /-- The targets this release publishes, in manifest order. -/
  targets : List Target
  /-- Whether the packages declare npm provenance.

      True for everything the release workflow publishes, where npm mints the
      attestation from the job's OIDC token. False for the one-time bootstrap,
      which a human publishes by hand under 2FA: npm generates provenance only
      on a CI provider it supports and refuses the publish outright anywhere
      else, so a bootstrap package declaring it is one nobody can publish — and
      the bootstrap is the step the whole channel waits on. -/
  provenance : Bool
  deriving Repr

def Spec.scope (spec : Spec) : String := npmScopeOf spec.launcher

/-- The published name of one platform package. -/
def Spec.platformPackage (spec : Spec) (target : String) : String :=
  npmPlatformPackage spec.scope target

def Spec.homepage (spec : Spec) : String :=
  s!"https://github.com/{spec.repository}#readme"

def Spec.bugs (spec : Spec) : String :=
  s!"https://github.com/{spec.repository}/issues"

def Spec.repositoryUrl (spec : Spec) : String :=
  s!"git+https://github.com/{spec.repository}.git"

/-- The fields every package in the set shares. Written once so a licence or a
    repository url cannot be right in the launcher and wrong in a platform
    package — which is the shape the registry records permanently. -/
private def commonFields (spec : Spec) (name description : String)
    (license : String) : List (String × Json) :=
  [("name", Json.str name),
   ("version", Json.str spec.version),
   ("description", Json.str description),
   ("homepage", Json.str spec.homepage),
   ("bugs", Json.str spec.bugs),
   ("repository", Json.mkObj
     [("type", Json.str "git"), ("url", Json.str spec.repositoryUrl)]),
   ("license", Json.str license),
   ("files", Json.arr (packageFiles.map Json.str).toArray),
   ("publishConfig", Json.mkObj
     ([("access", Json.str "public")]
       ++ (if spec.provenance then [("provenance", Json.bool true)] else [])))]

/-- The launcher's manifest: the package a user installs.

    It declares no `scripts`. A lifecycle script runs with the user's privileges
    at install time, and the launcher's whole contract is that installing it
    does nothing but place files (ADR-0028). The absence is structural — there
    is no field here to put one in. -/
def launcherJson (spec : Spec) (license : String) : Json :=
  let names := spec.targets.map fun target => spec.platformPackage target.name
  Json.mkObj (commonFields spec spec.launcher
      "tl — a formally verified, git-native task tracker for AI agents" license
    ++ [("keywords", Json.arr
          (["task", "tracker", "cli", "agents", "git", "crdt", "lean"].map Json.str).toArray),
        ("bin", Json.mkObj [("tl", Json.str binRelative)]),
        -- First-appearance order, taken from the target list rather than sorted, so
        -- two renders of one release agree.
        ("os", Json.arr (((spec.targets.map (·.os)).eraseDups.map Json.str)).toArray),
        ("cpu", Json.arr (((spec.targets.map (·.cpu)).eraseDups.map Json.str)).toArray),
        ("engines", Json.mkObj [("node", Json.str ">=18")]),
        ("optionalDependencies", Json.mkObj
          (names.map fun name => (name, Json.str spec.version)))])

/-- One platform package's manifest.

    `os`, `cpu` and `libc` are what npm selects on, so they are taken from the
    target row rather than restated: a package whose constraints disagree with
    the binary it carries is installed where it cannot run. The Linux binaries
    are glibc-linked and say so; without the `libc` constraint npm installs them
    on musl, where the exec fails with a message about a missing loader. -/
def platformJson (spec : Spec) (license : String) (target : Target) :
    Except String Json := do
  let prose ← match platformProse target.os target.cpu with
    | some prose => .ok prose
    | none =>
        .error s!"no npm package description is written for os '{target.os}' on cpu '{target.cpu}' ({target.name}). npm versions are immutable, so a description composed from the wire names would be published permanently as the outcome of adding a target. Add the pair to Release.Npm.platformProse."
  let libcField := match ← libcConstraint target with
    | none => []
    | some libc => [("libc", Json.arr #[Json.str libc])]
  return Json.mkObj (commonFields spec (spec.platformPackage target.name)
      s!"The tl binary for {prose}. Installed automatically by {spec.launcher}; not useful on its own."
      license
    ++ [("os", Json.arr #[Json.str target.os]),
        ("cpu", Json.arr #[Json.str target.cpu])]
    ++ libcField)

/-- One package's directory, the bytes of its manifest, and — for a platform
    package — the target it carries the binary for.

    The target travels with the package rather than being looked up again by
    name at staging time. The lookup was over the same list this was rendered
    from, so its "not found" arm could not be reached and could not be tested;
    carrying the value removes the arm rather than documenting it. -/
structure Rendered where
  directory : String
  manifest : String
  target : Option Target

/-- Refuse a spec whose package names are not ones npm reads as package specs.

    Called by the renderer and by the publisher, because the publisher does not
    render: it takes the names from the signed manifest and hands them to `npm
    view` and `npm publish`, which is the point at which a name beginning with
    `-` stops being a name and becomes an option. -/
def Spec.validate (spec : Spec) : Except String Unit := do
  if !validPackageName spec.launcher then
    .error s!"'{spec.launcher}' is not a published package name this tool will act on. It is passed to npm as a package spec, and a name that is not one — beginning with '-', carrying whitespace, or naming no scope — changes what npm was asked to do rather than failing. Fix npmPackage in release/identity.json."
  for target in spec.targets do
    let name := spec.platformPackage target.name
    if !validPackageName name then
      .error s!"'{name}', the platform package for {target.name}, is not a package name this tool will act on. It is composed from the launcher's scope and the target name; fix whichever of the two carries the character."

/-- Every manifest this spec describes: the launcher first, then one per target
    in manifest order.

    Rendered together rather than one call per package, because the drift check
    and the staging command must not be able to disagree about how many packages
    a release has. -/
def renderAll (spec : Spec) (license : String) : Except String (List Rendered) := do
  spec.validate
  let launcher ← render (launcherJson spec license)
  let platforms ← spec.targets.mapM fun target => do
    let manifest ← render (← platformJson spec license target)
    return { directory := platformDirectory target.name, manifest, target := some target }
  return { directory := launcherDirectory, manifest := launcher, target := none } :: platforms

/-! ## What a published version has to contain

npm versions are immutable: a version cannot be republished and unpublishing
does not free the number. So the only question a resumed run may ask about an
existing version is whether what is there is what this release staged, and a
wrong answer to it cannot be repaired afterwards.

The comparison is over the *contents*, not the tarball bytes. gzip output is not
stable across npm versions or runner images, so a byte comparison reports a
conflict on a re-run that changed nothing — and a spurious conflict on an
immutable registry is as expensive as a missed one, because the only remedy is
to burn the version number.

What npm will publish is asked of npm rather than guessed at. `npm pack
--dry-run --json` reports the exact entry list and mode for a directory or a
tarball, which is the same question `files`, `.npmignore` and npm's
always-included set jointly answer; a `find` over the staging tree answers a
different one and was wrong about `bin/tl` in three of the four platform
packages. The bytes come from unpacking, digested through the same resolved
digest tool the rest of this tool uses. -/

/-- One entry npm reports for a package: a path and the POSIX mode it will be
    published with. npm normalizes every mode to `0644` or `0755`, so the only
    bit that carries information is whether the entry is executable. -/
structure PackedEntry where
  path : String
  mode : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Whether a mode names an executable file, by the owner-execute bit.

    npm publishes `0755` for what was executable when it packed and `0644` for
    everything else, so this is the whole of what a mode distinguishes — and
    the launcher package's `bin/tl` losing it produces a package that installs
    and then cannot be run. -/
def executableMode (mode : Nat) : Bool := (mode / 64) % 2 == 1

/-- One entry of a package, as the comparison sees it. -/
structure Entry where
  path : String
  executable : Bool
  digest : String
  deriving DecidableEq, Repr, Inhabited

/-- The comparable form: entries in path order.

    npm reports entries in its own order and a tarball carries whatever order it
    was written in, so a comparison against an unsorted list would report a
    conflict on a package with identical contents. -/
def normalize (entries : List Entry) : List Entry :=
  entries.mergeSort (fun left right => left.path ≤ right.path)

/-- Whether two package trees are the same publication. -/
def treeAgrees (staged published : List Entry) : Bool :=
  normalize staged == normalize published

/-- **Two trees agree exactly when their comparable forms are equal.**

    Left to right is the direction that decides a publication: `true` skips an
    immutable version, so a comparison that drifted into saying it when the
    trees differ would report a package this release did not build as the one it
    did. -/
theorem treeAgrees_iff (staged published : List Entry) :
    treeAgrees staged published = true ↔ normalize staged = normalize published := by
  rw [treeAgrees]
  exact beq_iff_eq

/-! ## What the registry holds -/

/-- What the registry has for one package at this release's version. -/
inductive VersionState where
  | absent
  | identical
  | conflict
  deriving DecidableEq, Repr

/-- Classify one package's published version against what this release staged.

    `none` is "the registry answered, and there is no such version" — never "the
    registry could not be asked". A network failure or an expired credential is
    a refusal at the call site, because reading it as `absent` turns it into a
    publish attempt against a version that may already exist. -/
def versionDisposition (staged : List Entry) (published : Option (List Entry)) :
    VersionState :=
  match published with
  | none => .absent
  | some entries =>
      match treeAgrees staged entries with
      | true => .identical
      | false => .conflict

/-- **A published version is left alone exactly when it holds this package.**

    The consequence of a false `identical` is a release that reports success
    over a registry serving somebody else's bytes under this version, and no way
    to correct it; the consequence of a false `conflict` is a resumed run that
    refuses a package it published itself minutes earlier. Both directions are
    therefore stated. -/
theorem versionDisposition_identical_iff (staged : List Entry)
    (published : Option (List Entry)) :
    versionDisposition staged published = .identical ↔
      ∃ entries, published = some entries ∧ normalize entries = normalize staged := by
  cases published with
  | none =>
      constructor
      · intro impossible; exact VersionState.noConfusion impossible
      · intro ⟨_, isSome, _⟩; cases isSome
  | some entries =>
      rw [versionDisposition]
      cases matched : treeAgrees staged entries with
      | true =>
          constructor
          · intro _
            exact ⟨entries, rfl, ((treeAgrees_iff staged entries).mp matched).symm⟩
          · intro _; rfl
      | false =>
          constructor
          · intro impossible; exact VersionState.noConfusion impossible
          · intro ⟨found, isSome, agree⟩
            rw [← Option.some.inj isSome] at agree
            rw [(treeAgrees_iff staged entries).mpr agree.symm] at matched
            exact Bool.noConfusion matched

/-- **A package is published exactly when the registry has no such version.**

    Stated separately because `absent` and `conflict` are the two answers that
    are not `identical` and they take opposite actions: one publishes and the
    other stops the release. Collapsing them would publish over a conflict. -/
theorem versionDisposition_absent_iff (staged : List Entry)
    (published : Option (List Entry)) :
    versionDisposition staged published = .absent ↔ published = none := by
  cases published with
  | none => exact Iff.intro (fun _ => rfl) (fun _ => rfl)
  | some entries =>
      rw [versionDisposition]
      cases treeAgrees staged entries with
      | true =>
          constructor
          · intro impossible; exact VersionState.noConfusion impossible
          · intro impossible; cases impossible
      | false =>
          constructor
          · intro impossible; exact VersionState.noConfusion impossible
          · intro impossible; cases impossible

/-! ## What order they go out in -/

/-- The publication order: every platform package, then the launcher.

    The launcher declares the platform packages as exact-version optional
    dependencies, so publishing it first leaves a window in which installing
    `@taskloop/tl` resolves nothing to run. On a resumed run the order matters
    more rather than less: it is what makes any partial state a prefix of a good
    one. -/
def publicationOrder (launcher : String) (platforms : List String) : List String :=
  platforms ++ [launcher]

/-- **The launcher is published last, whatever the platform set is.**

    Including when it is empty, which is the case a hand-written loop gets
    wrong: a release publishing no platform package at all still has to publish
    the launcher, and still has to publish it after the nothing that precedes
    it. -/
theorem publicationOrder_launcher_last (launcher : String) (platforms : List String) :
    (publicationOrder launcher platforms).getLast? = some launcher := by
  rw [publicationOrder]
  exact List.getLast?_concat

/-- **Nothing is dropped.** The order is a rearrangement of the packages, not a
    selection from them: a run that published a strict subset and reported
    success is the partial state this order exists to make impossible. -/
theorem publicationOrder_mem_iff (launcher : String) (platforms : List String)
    (name : String) :
    name ∈ publicationOrder launcher platforms ↔ name ∈ platforms ∨ name = launcher := by
  rw [publicationOrder, List.mem_append, List.mem_singleton]

/-! ## Which targets have to be staged

ADR-0006 tiers the targets: a Supported target is release-blocking and a
Best-effort one is not. A missing Supported binary must stop the channel — users
there would install a launcher whose platform package the registry never
received — while a missing Best-effort one is a package this release does not
publish and the launcher simply does not pin. -/

/-- Why a target's absence blocks the npm channel, or nothing. -/
def stagingBlocker (staged : List String) (target : Target) : Option String :=
  if staged.contains target.name || !target.tier.releaseBlocking then none
  else some s!"no binary was staged for {target.name}, which is a Supported target (ADR-0006). Publishing without it leaves everyone on that platform installing a launcher whose platform package the registry never received, and npm versions cannot be reissued to add it later."

/-- Every reason the staged set is not publishable. -/
def stagingBlockers (targets : List Target) (staged : List String) : List String :=
  targets.filterMap (stagingBlocker staged)

/-- Whether the staged set covers every release-blocking target. -/
def stagingCovers (targets : List Target) (staged : List String) : Bool :=
  (stagingBlockers targets staged).isEmpty

/-- One target's row, as the property the verdict is about. A private helper:
    what is relied on is the public statement below, and this is the shape of
    the `if` it is proved through. -/
private theorem stagingBlocker_eq_none_iff (staged : List String) (target : Target) :
    stagingBlocker staged target = none ↔
      (target.tier.releaseBlocking = true → staged.contains target.name = true) := by
  rw [stagingBlocker]
  cases contained : staged.contains target.name with
  | true =>
      rw [Bool.true_or, if_pos rfl]
      exact Iff.intro (fun _ _ => rfl) (fun _ => rfl)
  | false =>
      cases blocking : target.tier.releaseBlocking with
      | true =>
          rw [Bool.false_or, if_neg (fun impossible => Bool.noConfusion impossible)]
          constructor
          · intro impossible; cases impossible
          · intro implication; exact Bool.noConfusion (implication rfl)
      | false =>
          rw [Bool.false_or, if_pos Bool.not_false]
          exact Iff.intro (fun _ blocking => Bool.noConfusion blocking) (fun _ => rfl)

/-- **The staged set is accepted exactly when every Supported target is in it.**

    The verdict and the report are the same list, so a channel cannot publish
    while its own report names a target it did not stage — which is the shape a
    separately computed "problems" list drifts into. -/
theorem stagingCovers_iff (targets : List Target) (staged : List String) :
    stagingCovers targets staged = true ↔
      ∀ target ∈ targets, target.tier.releaseBlocking = true →
        staged.contains target.name = true := by
  rw [stagingCovers, List.isEmpty_iff, stagingBlockers, List.filterMap_eq_nil_iff]
  constructor
  · intro noneOfMem target inTargets
    exact (stagingBlocker_eq_none_iff staged target).mp (noneOfMem target inTargets)
  · intro covered target inTargets
    exact (stagingBlocker_eq_none_iff staged target).mpr (covered target inTargets)

/-! ## The licence of record

The `license` field is what the registry records permanently, and an npm version
cannot be republished once it is wrong. It is read off the repository's own
`LICENSE` rather than written here, so the two cannot disagree — and an
unrecognised licence refuses the render instead of falling back to whatever the
manifests last claimed. -/

/-- The SPDX identifier of the licence this repository publishes under. -/
def spdxOf (path : String) (text : String) : Except String String :=
  let head := (text.take 400).toString
  let mentions (needle : String) : Bool := (head.splitOn needle).length > 1
  if mentions "Apache License" then
    if mentions "Version 2.0" then .ok "Apache-2.0"
    else .error s!"{path} names the Apache License without a version, so the SPDX identifier the npm manifests would publish is not determined. Teach Release.Npm.spdxOf the licence before publishing under it."
  else if mentions "MIT License" then .ok "MIT"
  else
    .error s!"{path} is not a licence this renderer recognises. The `license` field is what the registry records permanently and an npm version cannot be republished, so an unrecognised licence refuses the render rather than repeating whatever the manifests last claimed. Teach Release.Npm.spdxOf the new licence."

/-! ## Reaching the world

Three programs, and each is asked only what it is the authority on. `npm` is
asked what it will publish and what the registry holds; the digest tool computes
content; `tar` unpacks what npm downloaded. Nothing here scans a directory to
predict npm's answer — `files`, `.npmignore` and npm's always-included set
jointly decide the entry list, and a `find` over the staging tree answers a
different question. -/

/-- A directory argument npm cannot read as anything but a directory.

    `npm pack npm-staging/tl` does not pack that directory: `npm-package-arg`
    reads a bare two-segment relative path as the GitHub shorthand
    `owner/repo`, so npm runs `git ls-remote ssh://git@github.com/npm-staging/tl`
    instead — and if that repository exists, publishes *its* contents under this
    release's credential. Three-segment paths do not match the shorthand, which
    is why the platform packages worked and the launcher did not.

    A leading `./` settles it, and settles it the same way `release/Digest.lean`
    settles a digest tool's path argument. -/
def unambiguousDirectory (path : String) : String :=
  if path.startsWith "/" || path.startsWith "./" || path.startsWith "../" then path
  else "./" ++ path

/-- The npm client, as a value rather than a literal, so a suite can drive every
    branch below against a stub that answers from a fixture registry. Real
    releases pass nothing and get the pinned client the workflow installed.

    `globalArgs` is the isolation, and it lives on the client rather than at the
    call sites for one reason: an argument list that each caller appends is one
    a caller can forget, and the caller that forgot was invisible. The gate ran
    every `npm pack --dry-run` against the developer's own `~/.npm` and
    `~/.npmrc` while three neighbouring calls were isolated, so its verdict
    tracked the machine it ran on — which is the one thing a gate may never do.
    Prepended in `attempt`, there is no invocation below that can escape it. -/
structure Client where
  program : String
  globalArgs : List String := []
  deriving Repr

def Client.default : Client := { program := "npm" }

/-- The whole invocation: what this client always passes, then what the caller
    asked for. Named because a refusal has to quote the command that actually
    ran — an operator handed a shorter one cannot reproduce the failure, and the
    isolation is exactly the part that would be missing from it. -/
def Client.invocation (client : Client) (args : List String) : List String :=
  client.globalArgs ++ args

/-- Run the client and hand back the whole outcome: several call sites branch on
    a non-zero status rather than requiring zero, because "there is no such
    version" is one of npm's answers and not a failure. -/
private def Client.attempt (client : Client) (args : List String) :
    IO RunOutcome :=
  Release.run client.program (client.invocation args).toArray

/-- Run the client, requiring success. -/
private def Client.must (client : Client) (what : String) (args : List String) :
    Decision String := do
  match ← ofIO (do return .ok (← client.attempt args)) with
  | .completed output =>
      if output.exitCode == 0 then return output.stdout
      else
        let detail := if output.stderr.trimAscii.isEmpty then output.stdout else output.stderr
        decline s!"{what}: `{client.program} {String.intercalate " " (client.invocation args)}` exited {output.exitCode}. {detail.trimAscii}"
  | outcome =>
      decline s!"{what}: {outcome.failureMessage.getD s!"{client.program} could not be run"}"

/-- The entries `npm pack --dry-run --json` reports for a directory or tarball.

    Asked of npm rather than derived, which is the whole point: this is the
    published entry list by construction, including the `bin/tl` that ships only
    because `files` names it. -/
private def packedEntries (client : Client) (what : String) (spec : String) :
    Decision (List PackedEntry) := do
  let stdout ← client.must what ["pack", spec, "--dry-run", "--json"]
  let cursor : Cursor := { document := s!"`{client.program} pack {spec} --dry-run --json`" }
  let root ← ofExcept (parseDocument cursor stdout)
  let rows ← ofExcept (asArray cursor root)
  match rows with
  | [(packageCursor, package)] =>
      let (filesCursor, files) ← ofExcept (field packageCursor package "files")
      let entries ← ofExcept (asArray filesCursor files)
      let parsed ← ofExcept (entries.mapM fun (entryCursor, entry) => do
        let path ← stringField entryCursor entry "path"
        let mode ← natField entryCursor entry "mode"
        return ({ path, mode } : PackedEntry))
      -- Directory members carry no content and npm's own tarballs have none,
      -- but a tarball written by `tar` does, and npm reports them — as the
      -- empty path for the root and a trailing '/' for the rest. Dropped rather
      -- than refused: they are not entries a comparison of contents is about,
      -- and refusing would make a published version this tool cannot read.
      let parsed := parsed.filter fun entry =>
        !entry.path.isEmpty && !entry.path.endsWith "/"
      if parsed.isEmpty then
        decline s!"{what}: npm reports that {spec} would publish no files at all. An empty package compares equal to any other empty package, so the comparison that decides whether an immutable version is published over would be made against nothing."
      return parsed
  | rows =>
      decline s!"{what}: `{client.program} pack --json` described {rows.length} packages for {spec}, and exactly one was expected. Publishing on a reading this tool does not understand is how a wrong tarball reaches an immutable registry."

/-- Refuse a staging tree containing anything but directories and regular files.

    A symbolic link is the case worth naming: npm's served tree does not
    represent one comparably, so there is nothing on the published side to
    compare it against and no equality that could be established. Everything
    else that is neither a directory nor a regular file is refused for the same
    reason — it is not a thing a published package contains. -/
private partial def refuseIrregular (root : String) : IO (Except String Unit) := do
  try
    -- The root itself, first. `isDir` follows a link, so a package directory
    -- that *is* a symbolic link passes every check beneath it while being a
    -- thing npm's served tree cannot represent.
    match (← (System.FilePath.mk root).symlinkMetadata).type with
    | .dir => pure ()
    | _ =>
        return .error s!"{root} is not a directory. A staged npm package is one, and a link standing in for it is not something the registry's served tree can represent."
    for entry in ← System.FilePath.readDir root do
      let path := entry.path
      let metadata ← path.symlinkMetadata
      match metadata.type with
      | .dir =>
          match ← refuseIrregular path.toString with
          | .error message => return .error message
          | .ok _ => pure ()
      | .file => pure ()
      | .symlink =>
          return .error s!"{path} is a symbolic link. npm's published tree does not represent one comparably, so a staged link could never be compared against what the registry serves — and an npm version is immutable, so a comparison that cannot be made must not be answered either way."
      | .other =>
          return .error s!"{path} is neither a directory nor a regular file. A published npm package contains neither, so this staging tree is not one the registry would ever hold."
    return .ok ()
  catch error =>
    return .error s!"could not read the staging tree at {root}: {error}"

/-- Turn npm's entry list into the comparison unit by digesting each path.

    The digests come from the files themselves rather than from npm, which
    reports a size and no content hash. A path npm named and the tree does not
    hold is a refusal: the two answers describe one package, and a missing file
    is a package that would compare equal to a shorter one. -/
private def entriesOf (digester : Digester) (root : String) (packed : List PackedEntry) :
    Decision (List Entry) :=
  packed.mapM fun entry => do
    let path := root ++ "/" ++ entry.path
    let present ← ofIO (do return .ok (← System.FilePath.pathExists path))
    if !present then
      decline s!"npm listed {entry.path} as part of this package and {path} is not there. The two answers describe one package; comparing the shorter of them would compare something neither side holds."
    let digest ← ofIO (digester.digest path)
    return { path := entry.path, executable := executableMode entry.mode, digest := digest.hex }

/-- Where a dist-tag currently points, or `none` when it is unset.

    A *read*, never a write. OIDC trusted publishing authorizes `npm publish`
    and no other registry mutation, so this job has no credential for `npm
    dist-tag add` and attempting one would turn the single path that recovers a
    partial publish into a guaranteed failure. Reading is a public registry GET
    and needs no credential. -/
private def distTagTarget (client : Client) (name tag : String) :
    Decision (Option String) := do
  let outcome ← ofIO (do
    return .ok (← client.attempt ["view", name, s!"dist-tags.{tag}"]))
  match outcome with
  | .completed output =>
      -- npm answers an unset tag with status zero and an empty line, so a
      -- non-zero status is never that answer — it is an error. Read as "unset"
      -- it produces a refusal telling an operator to run `npm dist-tag add`,
      -- which is a registry mutation prescribed on an answer nobody read.
      if output.exitCode != 0 then
        decline s!"could not read the '{tag}' dist-tag of {name}: npm exited {output.exitCode}. {output.stderr.trimAscii}"
      let value := output.stdout.trimAscii.toString
      return if value.isEmpty then none else some value
  | outcome =>
      decline s!"could not read the '{tag}' dist-tag of {name}: {outcome.failureMessage.getD s!"{client.program} could not be run"}. The tag is what `npm install` resolves, so a release must not report success without knowing where it points."

/-- What the registry holds for one exact version, as the comparison unit, or
    `none` when there is no such version.

    A network failure, an expired credential or an npm this tool cannot read is
    a refusal rather than `none`: read as absence it becomes a publish attempt
    against a version that may already exist, and the resulting `E403` is the
    good case — the bad one is a race that succeeds. -/
private def publishedEntries (client : Client) (digester : Digester) (scratch : String)
    (name version : String) : Decision (Option (List Entry)) := do
  let spec := s!"{name}@{version}"
  let outcome ← ofIO (do return .ok (← client.attempt ["view", spec, "version"]))
  match outcome with
  | .completed output =>
      if output.exitCode != 0 then
        -- npm reports a missing package and a missing version the same way.
        let markers := ["E404", "404 Not Found", "is not in this registry", "No match found"]
        if markers.any (fun marker => (output.stderr.splitOn marker).length > 1) then
          return none
        else
          decline s!"could not find out whether {spec} already exists. Publishing without knowing that risks either a spurious E403 or a silent gap, so nothing is published from here. npm said: {output.stderr.trimAscii}"
      -- It exists, so the only question left is whether it is this package.
      let download := scratch ++ "/published"
      ofIO (do
        try
          IO.FS.createDirAll download
          return .ok ()
        catch error => return .error s!"could not create {download}: {error}")
      let _ ← client.must s!"downloading {spec} to compare it"
        ["pack", spec, "--pack-destination", download]
      let tarballs ← ofIO (do
        try
          let entries ← System.FilePath.readDir download
          return .ok (entries.toList.map (·.path.toString))
        catch error => return .error s!"could not read {download}: {error}")
      match tarballs.filter (·.endsWith ".tgz") with
      | [tarball] =>
          let unpacked := scratch ++ "/unpacked"
          ofIO (do
            try
              IO.FS.createDirAll unpacked
              return .ok ()
            catch error => return .error s!"could not create {unpacked}: {error}")
          let extracted ← ofIO (do
            return .ok (← Release.succeeded "tar" #["-xzf", tarball, "-C", unpacked]))
          match extracted with
          | .error message =>
              decline s!"{spec} was downloaded and could not be unpacked ({message}). Nothing has been published by this run; compare it by hand before publishing anything else."
          | .ok _ =>
              -- npm's tarballs put everything under `package/`, and asking npm
              -- to read the tarball back is what keeps the entry list and the
              -- modes coming from one authority on both sides.
              let packed ← packedEntries client s!"reading the published {spec}" tarball
              return some (← entriesOf digester (unpacked ++ "/package") packed)
      | found =>
          decline s!"downloading {spec} produced {found.length} tarballs in {download}, and exactly one was expected. The comparison that decides whether an immutable version is published over must not pick one of several."
  | outcome =>
      decline s!"could not ask the registry about {spec}: {outcome.failureMessage.getD s!"{client.program} could not be run"}"

/-! ## The tracked copies

`npm/tl/package.json` and `npm/platform/<target>/package.json` are what this
renderer produces at version `0.0.0`. They are tracked so the shape is
reviewable in the repository and so the launcher package has something to sit
beside; they are not authoritative, and the suite compares them against a fresh
render on every commit. -/

private def manifestsOptions : List OptionSpec :=
  [{ name := "identity", takesValue := true },
   { name := "targets", takesValue := true },
   { name := "license", takesValue := true },
   outputDirectoryOption]

private structure ManifestsArgs where
  identityPath : String
  targetsPath : String
  licensePath : String
  base : Write.OutputDirectory
  baseText : String

private def manifestsArgs (options : Options) : Except String ManifestsArgs := do
  let baseText := (options.value? "output-dir").getD "."
  return {
    identityPath := ← options.required "identity"
    targetsPath := ← options.required "targets"
    licensePath := ← options.required "license"
    base := ← Write.OutputDirectory.parse "--output-dir" baseText
    baseText }

private def manifestsDecision (args : ManifestsArgs) : Decision String := do
  let identity ← readParsed args.identityPath Identity.parse
  let targets ← readParsed args.targetsPath Targets.parse
  let licenseText ← ofIO (readTextFile args.licensePath)
  let license ← ofExcept (spdxOf args.licensePath licenseText)
  let spec : Spec :=
    { launcher := identity.npmPackage
      repository := identity.repository
      version := placeholderVersion
      targets := targets.targets, provenance := true }
  let rendered ← ofExcept (renderAll spec license)
  let mut disclosures := []
  for package in rendered do
    -- The directory has to exist before the anchored writer descends into it,
    -- and a package directory that is not there is a package this repository
    -- does not track — created rather than refused, so adding a target is one
    -- edit to release/targets.json.
    ofIO (do
      try
        IO.FS.createDirAll (args.baseText ++ "/" ++ package.directory)
        return .ok ()
      catch error =>
        return .error s!"could not create {args.baseText}/{package.directory}: {error}")
    let path ← ofExcept
      (Write.OutputPath.parse "the package manifest" (package.directory ++ "/package.json"))
    let disclosure ← ofIO (writeEvidence args.base path package.manifest)
    disclosures := disclosures ++ disclosure.toList
  return disclosing
    s!"wrote {rendered.length} package manifest(s) under {args.baseText} at version {spec.version}, licence {license}"
    disclosures.head?

private def manifestsCommand : Command :=
  optionCommand "npm-manifests"
    "--identity <path> --targets <path> --license <path> [--output-dir <dir>]"
    "Render the five tracked npm package manifests from the release identity and target list."
    ["--identity", "release/identity.json", "--targets", "release/targets.json",
     "--license", "LICENSE", "--output-dir", "npm"]
    manifestsOptions manifestsArgs manifestsDecision

/-! ## Staging

The five packages are built into a fresh tree from the signed release rather
than assembled in place. Publishing must never depend on files being rearranged
inside the working checkout: the platform packages hold no binary in git, and a
staging directory that already had contents used to produce nested `tl/tl/…`
trees that npm then packed, publishing whichever layout it found first. -/

private def ensureDirectory (path : String) : Decision Unit :=
  ofIO (do
    try
      IO.FS.createDirAll path
      return .ok ()
    catch error => return .error s!"could not create {path}: {error}")

/-- Copy one file, and say which one when it fails. `executable` sets the mode
    npm reads to decide whether the published entry is `0755` — the launcher's
    `bin/tl` and each platform binary need it, and a package published without
    it installs and then cannot be run. -/
private def copyFile (source destination : String) (executable : Bool := false) :
    Decision Unit :=
  ofIO (do
    try
      IO.FS.writeBinFile destination (← IO.FS.readBinFile source)
      if executable then
        IO.setAccessRights destination
          { user := { read := true, write := true, execution := true }
            group := { read := true, execution := true }
            other := { read := true, execution := true } }
      return .ok ()
    catch error => return .error s!"could not copy {source} to {destination}: {error}")

/-- Refuse a staging root that is not a fresh directory. -/
private def requireFreshDirectory (path : String) : Decision Unit := do
  let present ← ofIO (do return .ok (← System.FilePath.pathExists path))
  if present then
    let isDirectory ← ofIO (do return .ok (← System.FilePath.isDir path))
    if !isDirectory then
      decline s!"'{path}' exists and is not a directory, so there is nowhere to stage the packages. Pass a path this command may create."
    let entries ← ofIO (do
      try
        return .ok ((← System.FilePath.readDir path).toList.length)
      catch error => return .error s!"could not read {path}: {error}")
    if entries != 0 then
      decline s!"'{path}' already exists and is not empty. Staging into it would leave a previous run's files inside the packages this one publishes, and npm publishes what it finds. Remove it, or pass a fresh path."
  ensureDirectory path

private def stageOptions : List OptionSpec :=
  [{ name := "root", takesValue := true },
   { name := "dist", takesValue := true },
   { name := "manifest", takesValue := true },
   { name := "staging", takesValue := true }]

private structure StageArgs where
  root : String
  dist : String
  manifestPath : String
  staging : String
  stagingBase : Write.OutputDirectory

private def stageArgs (options : Options) : Except String StageArgs := do
  let staging ← options.required "staging"
  return {
    root := ← options.required "root"
    dist := ← options.required "dist"
    manifestPath := ← options.required "manifest"
    staging
    stagingBase := ← Write.OutputDirectory.parse "--staging" staging }

/-- The spec a verified release stages from. Every value comes from the signed
    manifest; nothing here consults `release/targets.json`. -/
def specOf (description : ManifestDescription) : Spec :=
  { launcher := description.npm.packages.headD ""
    repository := description.repository
    version := description.version.render
    targets := description.pinned.map (·.1), provenance := true }

private def stageDecision (args : StageArgs) : Decision String := do
  let description ← readParsed args.manifestPath ManifestDescription.parse
  let identity ← readParsed (args.root ++ "/release/identity.json") Identity.parse
  let licenseText ← ofIO (readTextFile (args.root ++ "/LICENSE"))
  let license ← ofExcept (spdxOf (args.root ++ "/LICENSE") licenseText)
  -- Which names this release publishes under. The manifest's own coherence
  -- check holds its package list to the shape of its first element, and says
  -- so: it cannot know what that first element ought to be. This is where it
  -- is known — a manifest describing a coherent package set under somebody
  -- else's scope is publishable until something compares it with the identity
  -- every other consumer is pinned to.
  match description.npm.packages.head? with
  | some launcher =>
      if launcher != identity.npmPackage then
        decline s!"the manifest publishes '{launcher}' and {args.root}/release/identity.json pins the published package as '{identity.npmPackage}'. Every other consumer — VERIFYING.md, the installer, the prose documents — is pinned to that name, so this would publish a release nobody is told to install."
  | none =>
      decline "the manifest lists no npm packages, so there is no launcher to publish and nothing for the platform packages to be pinned by."
  -- ADR-0006's tiers, applied to this channel's consequence: a Supported target
  -- with no binary would leave everyone on that platform installing a launcher
  -- whose platform package the registry never received.
  match stagingBlockers description.distributedTargets description.publishedTargets with
  | [] => pure ()
  | blockers =>
      decline ("this release does not publish every Supported target, so the npm packages may not be staged from it.\n"
        ++ String.join (blockers.map fun blocker => s!"  {blocker}\n"))
  let spec := specOf description
  let rendered ← ofExcept (renderAll spec license)
  requireFreshDirectory args.staging
  let digester ← ofIO Digester.resolve
  for package in rendered do
    let directory := args.staging ++ "/" ++ package.directory
    ensureDirectory (directory ++ "/bin")
    let path ← ofExcept
      (Write.OutputPath.parse "the package manifest" (package.directory ++ "/package.json"))
    let _ ← ofIO (writeEvidence args.stagingBase path package.manifest)
    -- The README is per-package prose tracked beside the manifest; the two
    -- licence files travel in every distribution artifact (ADR-0006) and are
    -- copied from the repository root rather than tracked twice.
    copyFile s!"{args.root}/npm/{package.directory}/README.md" s!"{directory}/README.md"
    for licence in licenceFiles do
      copyFile s!"{args.root}/{licence}" s!"{directory}/{licence}"
    match package.target with
    | none =>
        copyFile s!"{args.root}/npm/{launcherDirectory}/{binRelative}"
          s!"{directory}/{binRelative}" (executable := true)
    | some target =>
        copyFile s!"{args.dist}/{target.asset}" s!"{directory}/{binRelative}"
          (executable := true)
        -- Against the signed digest, not against the file's presence. The
        -- assets are verified as a set upstream; this is the step that says
        -- *this* package carries *that* binary, and it is the only comparison
        -- npm can never make for a user afterwards.
        let got ← ofIO (digester.digest s!"{directory}/{binRelative}")
        let expected ← match description.pinned.find? fun (row, _) => row.name == target.name with
          | some (_, expected) => pure expected
          -- The package set and the pin list are both `description.pinned`, so
          -- this arm is unreachable for any manifest that parsed. It is a
          -- refusal rather than a skip because the two ways to be wrong here
          -- are not symmetric: a missing pin that skipped the comparison would
          -- publish an unchecked binary, which is the one outcome this whole
          -- command exists to prevent.
          | none =>
              decline s!"no digest is pinned for {target.name}, and a package was staged for it. Nothing is published from a comparison that did not happen; this is a defect in tlrelease rather than in the release."
        if got.hex != expected.hex then
          decline s!"the binary staged for {target.name} hashes to {got.hex} and the manifest pins {expected.hex} for it. The npm package would ship a binary other than the one this release signed; nothing further has been staged."
  return s!"staged {rendered.length} package(s) for {description.tag} under {args.staging}, licence {license}, every binary matching the digest the manifest pins"

private def stageCommand : Command :=
  optionCommand "npm-stage"
    "--root <dir> --dist <dir> --manifest <path> --staging <dir>"
    "Build the npm packages around the signed release binaries, into a fresh tree."
    ["--root", ".", "--dist", "dist", "--manifest", "dist/release-manifest.json",
     "--staging", "npm-staging"]
    stageOptions stageArgs stageDecision

/-! ## Publication

Cross-registry publication cannot be transactional — GitHub, npm and the
Homebrew tap share no commit — so the property aimed at is not all-or-nothing.
It is that **every step is safe to retry and repeated execution converges the
registry to the staged tree**: ask what is there, publish what is absent, leave
what already matches, and stop on what conflicts. -/

private def publishOptions : List OptionSpec :=
  [{ name := "staging", takesValue := true },
   { name := "manifest", takesValue := true },
   { name := "npm", takesValue := true },
   { name := "plan", takesValue := false }]

private structure PublishArgs where
  staging : String
  manifestPath : String
  client : Client
  plan : Bool

private def publishArgs (options : Options) : Except String PublishArgs := do
  return {
    staging := ← options.required "staging"
    manifestPath := ← options.required "manifest"
    client := match options.value? "npm" with
      | some program => { program }
      | none => Client.default
    plan := options.given "plan" }

/-- Where one published package name is staged. The launcher and the platform
    packages are laid out exactly as they are tracked, so this is a lookup
    rather than a second naming scheme. -/
private def stagedDirectoryOf (spec : Spec) (name : String) : Option String :=
  if name == spec.launcher then some launcherDirectory
  else (spec.targets.find? fun target => spec.platformPackage target.name == name).map
    fun target => platformDirectory target.name

/-- What the directory about to be published calls itself.

    Every other step in this command works from a *name*: the registry is asked
    about `{name}@{version}`, the comparison is against that version, and the
    report says so. npm takes neither from any of that — it reads the
    directory's own `package.json`. Until they are compared, the existence
    check and the act are about different objects, and a staging tree from
    another release publishes under its own identity while the log says
    otherwise. -/
private def stagedIdentity (directory : String) : Decision (String × String) := do
  let path := directory ++ "/package.json"
  let text ← ofIO (readTextFile path)
  ofExcept do
    let cursor : Cursor := { document := path }
    let root ← parseDocument cursor text
    return (← nonEmptyStringField cursor root "name",
            ← nonEmptyStringField cursor root "version")

/-- What a survey established about one package, and what remains to be done
    about it. -/
private structure Surveyed where
  name : String
  directory : String
  state : VersionState
  /-- What the survey has to say about it, whatever happens next. -/
  line : String

/-- Establish, without publishing anything, what the registry holds for one
    package and whether this staging tree is the one that produced it.

    Separated from the act because the two together were interleaved: a launcher
    already published with different contents was discovered only after all four
    platform packages had been irreversibly published at that version. The whole
    survey runs first, so the pre-publication state is observed before the first
    irreversible step. -/
private def surveyOne (args : PublishArgs) (spec : Spec) (digester : Digester)
    (scratch : String) (distTag : String) (pinned : List (Target × Sha256))
    (name : String) : Decision Surveyed := do
  -- The launcher carries a dispatcher from this repository rather than a
  -- release asset, so it has no pin; every platform package has one.
  let pinnedFor := (pinned.find? fun (target, _) =>
    spec.platformPackage target.name == name).map fun (target, digest) =>
      (target.name, digest)
  let relative ← match stagedDirectoryOf spec name with
    | some relative => pure relative
    | none =>
        decline s!"the manifest lists {name} among the packages this release publishes and the staged tree has no directory for it. Both come from the same manifest, so this is a defect in the staging step rather than something to work around by publishing what is there."
  let directory := args.staging ++ "/" ++ relative
  let isDirectory ← ofIO (do return .ok (← System.FilePath.isDir directory))
  if !isDirectory then
    decline s!"{directory} is not a directory, so {name} was never staged. Stage the packages first with `tlrelease npm-stage`."
  -- Before npm is asked anything about it: a staged link could never be
  -- compared against what the registry serves.
  ofIO (refuseIrregular directory)
  -- What npm will actually publish from here, before anything is asked about
  -- what the registry holds under some other name.
  let (stagedName, stagedVersion) ← stagedIdentity directory
  if stagedName != name then
    decline s!"{directory} calls itself '{stagedName}' and this release publishes '{name}' from it. npm takes the published name from that file and nothing else does, so the registry would receive one package while this run reported another. Re-run `tlrelease npm-stage` against a fresh directory."
  if stagedVersion != spec.version then
    decline s!"{directory} carries version {stagedVersion} and this release publishes {spec.version}. npm takes the published version from that file, so the immutable version this run reported checking is not the one it would create. Re-run `tlrelease npm-stage` against a fresh directory."
  -- And the binary, against the digest the manifest pins for it. `npm-stage`
  -- checked this when it wrote the tree, but these are two invocations with
  -- independent `--staging` values and nothing linking them: a tree left over
  -- from another release is a directory that exists and packs cleanly. The
  -- comparison is cheap and the publication it guards is irreversible.
  match pinnedFor with
  | some (target, expected) =>
      let got ← ofIO (digester.digest s!"{directory}/{binRelative}")
      if got.hex != expected.hex then
        decline s!"the tree staged at {directory} carries a binary for {target} hashing to {got.hex}, and the manifest pins {expected.hex}. This staging tree is not the one this release produced; nothing is published from it. Re-run `tlrelease npm-stage` against a fresh directory."
  | none => pure ()
  let stagedPacked ← packedEntries args.client s!"reading the staged {name}"
    (unambiguousDirectory directory)
  let staged ← entriesOf digester directory stagedPacked
  let published ← publishedEntries args.client digester scratch name spec.version
  let describe (entries : List Entry) : String :=
    String.intercalate ", " ((normalize entries).map fun entry =>
      s!"{entry.path} {entry.digest.take 12}{if entry.executable then " x" else ""}")
  match versionDisposition staged published with
  | .conflict =>
      return { name, directory, state := .conflict
               line := s!"{name}@{spec.version} is on the registry and its contents differ.\n    staged:    {describe staged}\n    published: {describe (published.getD [])}" }
  | .identical =>
      -- The version is right; the dist-tag is separate state and can lag a
      -- partial run. On a first publish it is set by `npm publish --tag`, so
      -- this only ever arises on a retry — which is exactly the run that must
      -- not report success over a registry still resolving to the previous
      -- release.
      let pointsAt ← distTagTarget args.client name distTag
      if pointsAt == some spec.version then
        return { name, directory, state := .identical
                 line := s!"{name}@{spec.version} is already published, matches this staging tree, and '{distTag}' points at it" }
      let where? := pointsAt.getD "<unset>"
      if args.plan then
        return { name, directory, state := .identical
                 line := s!"{name}@{spec.version} is already published and matches, but '{distTag}' points at {where?} — a manual dist-tag repair would be needed" }
      decline s!"{name}@{spec.version} is published and matches this staging tree, but the '{distTag}' dist-tag points at {where?}. Everyone resolving that tag gets the wrong version. This job publishes over OIDC trusted publishing, which authorizes 'npm publish' and no other registry mutation, so it cannot move the tag: run it by hand under 2FA — 'npm dist-tag add {name}@{spec.version} {distTag}' — and re-run this job to confirm."
  | .absent =>
      return { name, directory, state := .absent
               line := s!"{name}@{spec.version} is not on the registry" }

/-- Publish one surveyed package. Only ever called for `.absent`. -/
private def publishOne (args : PublishArgs) (spec : Spec) (distTag : String)
    (surveyed : Surveyed) : Decision String := do
  let name := surveyed.name
  let outcome ← ofIO (do return .ok (← args.client.attempt
    ["publish", unambiguousDirectory surveyed.directory, "--provenance", "--access", "public",
     "--tag", distTag]))
  match outcome with
  | .completed output =>
      if output.exitCode == 0 then
        return s!"published {name}@{spec.version} (--tag {distTag})"
      -- npm's own message for the first release is an authentication error,
      -- and the actual cause is a missing prerequisite.
      let authMarkers := ["ENEEDAUTH", "E401", "401 Unauthorized",
        "Unable to authenticate", "trusted publish"]
      if authMarkers.any (fun marker => (output.stderr.splitOn marker).length > 1) then
        decline s!"publishing {name}@{spec.version} failed to authenticate. If this is the first release that is expected and not a workflow bug: npm configures trusted publishing per package and only for a package that already exists, so every package must be bootstrapped by hand before the first tag. Follow docs/release-prerequisites.md, then re-run this job — it is idempotent, so anything already published is left alone. npm said: {output.stderr.trimAscii}"
      decline s!"publishing {name}@{spec.version} failed. Nothing about this run is lost: re-run the job and it will leave whatever already published alone and continue from here. npm said: {output.stderr.trimAscii}"
  | outcome =>
      decline s!"could not publish {name}@{spec.version}: {outcome.failureMessage.getD s!"{args.client.program} could not be run"}"

private def publishDecision (args : PublishArgs) : Decision String := do
  let description ← readParsed args.manifestPath ManifestDescription.parse
  let spec := specOf description
  ofExcept spec.validate
  let platforms := spec.targets.map fun target => spec.platformPackage target.name
  let order := publicationOrder spec.launcher platforms
  let digester ← ofIO Digester.resolve
  let scratch ← ofIO (do
    try
      return .ok (← IO.FS.createTempDir).toString
    catch error => return .error s!"could not create a scratch directory to compare published packages in: {error}")
  -- Survey first, publish second. An immutable registry makes the order matter:
  -- a conflict found on the last package is a conflict found after four
  -- irreversible publications.
  let mut surveyed : List Surveyed := []
  for name in order do
    -- A fresh scratch per package: the download and unpack directories are
    -- reused by name, and a previous package's tarball left in place would be
    -- compared against this one.
    let perPackage := s!"{scratch}/{surveyed.length}"
    ensureDirectory perPackage
    surveyed := surveyed ++
      [← surveyOne args spec digester perPackage description.npm.distTag description.pinned name]
  match surveyed.filter (·.state == .conflict) with
  | [] => pure ()
  | conflicts =>
      decline ("npm versions are immutable — a version that is there cannot be replaced, and unpublishing does not free the number. Nothing has been published by this run.\n"
        ++ String.join (conflicts.map fun row => s!"  {row.line}\n")
        ++ "Either this version was published from a different build, or this staging tree is not the one that produced it. Decide deliberately: bump the version everywhere and re-tag, or confirm the published package is correct.")
  let mut lines : List String := []
  let mut published := 0
  let mut planned := 0
  let mut matched := 0
  for row in surveyed do
    match row.state with
    | .identical =>
        matched := matched + 1
        lines := lines ++ [row.line]
    | .absent =>
        if args.plan then
          planned := planned + 1
          lines := lines ++
            [s!"would publish {row.name}@{spec.version} (--tag {description.npm.distTag})"]
        else
          lines := lines ++ [← publishOne args spec description.npm.distTag row]
          published := published + 1
    | .conflict => pure ()
  ofIO (do
    try
      IO.FS.removeDirAll scratch
      return .ok ()
    catch _ =>
      -- A scratch directory that could not be removed is not a publication
      -- failure and must not be reported as one.
      return .ok ())
  let report := String.join (lines.map fun line => s!"\n  {line}")
  if args.plan then
    return s!"--plan only: {planned} package(s) would be published under '{description.npm.distTag}', {matched} already match{report}"
  return s!"{published} published, {matched} already present and matching, under the '{description.npm.distTag}' dist-tag{report}"

private def publishCommand : Command :=
  optionCommand "npm-publish"
    "--staging <dir> --manifest <path> [--plan] [--npm <program>]"
    "Publish the staged packages, resumably: absent is published, identical is skipped, different stops the release."
    ["--staging", "npm-staging", "--manifest", "dist/release-manifest.json", "--plan"]
    publishOptions publishArgs publishDecision

/-! ## The one-time bootstrap

npm configures trusted publishing per package, and only for a package that
already exists. The package names this project publishes do not, so the first
tagged release cannot authenticate: it would publish the GitHub Release and the
Homebrew formula and then fail at `npm publish`, leaving a red release with its
artifacts already public. Somebody has to create the names by hand, under 2FA,
and that is the only manual step in the channel.

What this removes is every way of getting it wrong. Publishing `0.0.0` from a
checkout used to be the runbook, and it did not work: the tracked manifests
carried the real version, the platform directories held no binary or licence
files until staging, and the default dist-tag is `latest` — so the placeholder
would have become what `npm install @taskloop/tl` resolved to. This builds the
packages instead and prints the exact commands. -/

/-- The dist-tag the placeholders are published under: one no user resolves. -/
def bootstrapTag : String := "bootstrap"

/-- What a placeholder package carries instead of a binary. It must not look
    like a broken tl — it says what it is and exits non-zero, so anyone who
    reaches it learns why rather than filing a bug about a corrupt install. -/
def placeholderLauncher : String :=
  "#!/bin/sh\n\
   echo \"tl: this is a bootstrap placeholder package (version 0.0.0), published only so that npm trusted publishing could be configured for this package name before the first real release. It contains no tl binary.\" >&2\n\
   echo \"tl: install a real release with 'npm install -g @taskloop/tl', or see https://github.com/DmitryKorolev/tl\" >&2\n\
   exit 1\n"

/-- What a bootstrap package says about itself, for anyone who opens it on
    npmjs.com and finds a version with no binary in it. -/
def bootstrapReadme (name : String) : String :=
  s!"# {name} {placeholderVersion}\n\n\
     This version is a placeholder. It exists only so that npm trusted publishing \
     could be configured for this package name before the first real release: npm \
     configures it per package, and only for a package that already exists.\n\n\
     It contains no tl binary, and the executable it does contain exits non-zero \
     saying so.\n\n\
     Install a real release with `npm install -g @taskloop/tl`, or see \
     https://github.com/DmitryKorolev/tl\n"

private def bootstrapOptions : List OptionSpec :=
  [{ name := "root", takesValue := true },
   { name := "identity", takesValue := true },
   { name := "targets", takesValue := true },
   { name := "output", takesValue := true }]

private structure BootstrapArgs where
  root : String
  identityPath : String
  targetsPath : String
  output : String
  outputBase : Write.OutputDirectory

private def bootstrapArgs (options : Options) : Except String BootstrapArgs := do
  let output ← options.required "output"
  return {
    root := ← options.required "root"
    identityPath := ← options.required "identity"
    targetsPath := ← options.required "targets"
    output
    outputBase := ← Write.OutputDirectory.parse "--output" output }

private def bootstrapDecision (args : BootstrapArgs) : Decision String := do
  let identity ← readParsed args.identityPath Identity.parse
  let targets ← readParsed args.targetsPath Targets.parse
  let licenseText ← ofIO (readTextFile (args.root ++ "/LICENSE"))
  let license ← ofExcept (spdxOf (args.root ++ "/LICENSE") licenseText)
  let spec : Spec :=
    { launcher := identity.npmPackage, repository := identity.repository
      version := placeholderVersion, targets := targets.targets, provenance := false }
  let rendered ← ofExcept (renderAll spec license)
  requireFreshDirectory args.output
  for package in rendered do
    let directory := args.output ++ "/" ++ package.directory
    ensureDirectory (directory ++ "/bin")
    let path ← ofExcept
      (Write.OutputPath.parse "the package manifest" (package.directory ++ "/package.json"))
    let _ ← ofIO (writeEvidence args.outputBase path package.manifest)
    -- Its own README, not the production one. The tracked README tells the
    -- reader to `npm install -g` and run tl; on a package holding no binary
    -- that is an instruction that does not work, published permanently.
    let name := match package.target with
      | none => spec.launcher
      | some target => spec.platformPackage target.name
    ofIO (do
      try
        IO.FS.writeFile s!"{directory}/README.md" (bootstrapReadme name)
        return .ok ()
      catch error => return .error s!"could not write {directory}/README.md: {error}")
    for licence in licenceFiles do
      copyFile s!"{args.root}/{licence}" s!"{directory}/{licence}"
    -- Every package gets the placeholder, the launcher included: the real
    -- launcher would try to exec a platform package that carries nothing.
    let binary := s!"{directory}/{binRelative}"
    ofIO (do
      try
        IO.FS.writeFile binary placeholderLauncher
        IO.setAccessRights binary
          { user := { read := true, write := true, execution := true }
            group := { read := true, execution := true }
            other := { read := true, execution := true } }
        return .ok ()
      catch error => return .error s!"could not write {binary}: {error}")
  let names := publicationOrder spec.launcher
    (spec.targets.map fun target => spec.platformPackage target.name)
  let directories := publicationOrder launcherDirectory
    (spec.targets.map fun target => platformDirectory target.name)
  let commands := String.join (directories.map fun directory =>
    s!"\n  npm publish {args.output}/{directory} --access public --tag {bootstrapTag}")
  return s!"prepared {rendered.length} bootstrap package(s) at version {placeholderVersion} under {args.output}. \
    Publish them by hand, under 2FA, in this order — the launcher last, so it never resolves to packages that do not exist:{commands}\n  \
    Then register this repository, its release workflow and its environment as the trusted publisher of each of {String.intercalate ", " names} on npmjs.com, and enable the channel in release/plan.json. \
    The placeholder versions stay published afterwards — unpublishing is restricted and would free nothing. \
    Check 'npm dist-tag ls' for each package before you finish: npm sets 'latest' on a package's first publish whatever --tag says, and a 'latest' left pointing at {placeholderVersion} is what everyone installing {spec.launcher} would get until the first real release. \
    Nothing checks that for you: 'tlrelease prereqs' carries the npm rows rather than reading the registry, because that would put npm on the v0.1 dependency path."

private def bootstrapCommand : Command :=
  optionCommand "npm-bootstrap"
    "--root <dir> --identity <path> --targets <path> --output <dir>"
    "Build the one-time placeholder packages that let npm trusted publishing be configured."
    ["--root", ".", "--identity", "release/identity.json",
     "--targets", "release/targets.json", "--output", "npm-bootstrap"]
    bootstrapOptions bootstrapArgs bootstrapDecision

/-! ## The second net: real npm

Everything above is decided by this tool and tested against a stub, which is
what lets those rows run in a suite the release path may not spend an npm on.
What a stub cannot establish is npm's own behaviour: which files a package
actually contains, what mode they are published with, where an optional
dependency lands, and whether the `bin` symlink npm creates resolves back to a
binary the launcher can `exec`.

So this is the other net, and it is a deferred-channel gate rather than part of
the ordinary suite (ADR-0026's dependency budget). It packs and installs real
packages with the real client and drives the launcher through them. Its subject
is `npm/tl/bin/tl` — the one npm-side adapter that stays POSIX shell, because
npm's root `bin` path is static and cannot point conditionally into whichever
platform package was selected. -/

/-- The host's target name, as the launcher would classify it. Test machinery,
    so it asks `uname` the way the launcher does rather than reaching for a
    platform authority that describes the shell arms. -/
private def hostTarget : Decision String := do
  let ofUname (flag : String) : Decision String := do
    match ← ofIO (do return .ok (← Release.succeeded "uname" #[flag])) with
    | .ok output => return output.stdout.trimAscii.toString
    | .error message => decline s!"could not run `uname {flag}`: {message}"
  let os ← ofUname "-s"
  let arch ← ofUname "-m"
  let osName ← match os with
    | "Darwin" => pure "darwin"
    | "Linux" => pure "linux"
    | other => decline s!"this selftest installs and runs the host platform's package, and does not know the operating system '{other}'."
  let archName ← match arch with
    | "arm64" => pure "arm64"
    | "aarch64" => pure "arm64"
    | "x86_64" => pure "x64"
    | "amd64" => pure "x64"
    | other => decline s!"this selftest installs and runs the host platform's package, and does not know the architecture '{other}'."
  return s!"{osName}-{archName}"

/-- A stub native binary: it reports its arguments one per line, so a launcher
    that re-split them is visible, and exits with a status no shell produces by
    accident, so a status the launcher invented rather than passed through is
    visible too. -/
private def stubBinary : String :=
  "#!/bin/sh\nfor argument in \"$@\"; do printf '%s\\n' \"$argument\"; done\nexit 7\n"

private def selftestOptions : List OptionSpec :=
  [{ name := "root", takesValue := true },
   { name := "npm", takesValue := true }]

private structure SelftestArgs where
  root : String
  client : Client

private def selftestArgs (options : Options) : Except String SelftestArgs := do
  return {
    root := ← options.required "root"
    client := match options.value? "npm" with
      | some program => { program }
      | none => Client.default }

/-- One row of the gate: what it establishes, and whether it did. -/
private structure Row where
  name : String
  held : Bool
  detail : String

/-- npm invoked with its state pinned to this run.

    Without this every row runs against the caller's `~/.npm` and `~/.npmrc`, so
    the gate's verdict tracks the machine rather than the code. `--offline` is
    the other half and not merely cache isolation: the launcher declares the
    platform packages as optional dependencies, so an install resolves those
    names against the registry — a network round trip inside a gate whose whole
    claim is that it depends on nothing but this checkout, and one that retries
    with backoff rather than failing when the registry is unreachable.

    All three config layers, not just the user's. npm reads a global `npmrc`
    beside its own installation as well as `~/.npmrc`, and a machine that set a
    registry or a cache there would reach every row that `--userconfig` alone
    left open. The scratch files are created empty rather than left absent: an
    unreadable path and an empty file are the same configuration, but only one
    of them says so to anyone reading the run.

    Carried on the client rather than appended per call — see `Client`. -/
private def hermetic (scratch : String) : List String :=
  ["--cache", scratch ++ "/cache", "--userconfig", scratch ++ "/npmrc",
   "--globalconfig", scratch ++ "/globalrc",
   "--no-audit", "--no-fund", "--ignore-scripts", "--offline"]

private def selftestDecision (args : SelftestArgs) : Decision String := do
  let target ← hostTarget
  let scratch ← ofIO (do
    try return .ok (← IO.FS.createTempDir).toString
    catch error => return .error s!"could not create a scratch directory: {error}")
  ensureDirectory (scratch ++ "/cache")
  for configuration in ["npmrc", "globalrc"] do
    ofIO (do
      try
        IO.FS.writeFile (scratch ++ "/" ++ configuration) ""
        return .ok ()
      catch error => return .error s!"could not write {scratch}/{configuration}: {error}")
  -- Every npm invocation below goes through this one, and none of them adds
  -- isolation of its own: the client carries it, so a row added later is
  -- isolated by construction rather than by its author remembering to be.
  let client : Client := { args.client with globalArgs := hermetic scratch }
  -- The package set, at the placeholder version, with stub binaries. Built
  -- through the same renderer a release stages with, so what npm packs here is
  -- the shape it would pack then.
  let identity ← readParsed (args.root ++ "/release/identity.json") Identity.parse
  let targets ← readParsed (args.root ++ "/release/targets.json") Targets.parse
  let licenseText ← ofIO (readTextFile (args.root ++ "/LICENSE"))
  let license ← ofExcept (spdxOf (args.root ++ "/LICENSE") licenseText)
  let spec : Spec :=
    { launcher := identity.npmPackage, repository := identity.repository
      version := placeholderVersion, targets := targets.targets, provenance := true }
  let rendered ← ofExcept (renderAll spec license)
  let staging := scratch ++ "/staging"
  let stagingBase ← ofExcept (Write.OutputDirectory.parse "the staging root" staging)
  ensureDirectory staging
  for package in rendered do
    let directory := staging ++ "/" ++ package.directory
    ensureDirectory (directory ++ "/bin")
    let path ← ofExcept
      (Write.OutputPath.parse "the package manifest" (package.directory ++ "/package.json"))
    let _ ← ofIO (writeEvidence stagingBase path package.manifest)
    copyFile s!"{args.root}/npm/{package.directory}/README.md" s!"{directory}/README.md"
    for licence in licenceFiles do
      copyFile s!"{args.root}/{licence}" s!"{directory}/{licence}"
    if package.directory == launcherDirectory then
      copyFile s!"{args.root}/npm/{launcherDirectory}/{binRelative}"
        s!"{directory}/{binRelative}" (executable := true)
    else
      ofIO (do
        try
          IO.FS.writeFile s!"{directory}/{binRelative}" stubBinary
          IO.setAccessRights s!"{directory}/{binRelative}"
            { user := { read := true, write := true, execution := true }
              group := { read := true, execution := true }
              other := { read := true, execution := true } }
          return .ok ()
        catch error => return .error s!"could not write the stub binary: {error}")
  let mut rows : List Row := []
  -- What npm says it will publish. This is the row a `find` over the staging
  -- tree cannot produce: a platform package has no `bin` field, so its binary
  -- ships only because `files` names it, and dropping that entry yields a
  -- package that installs cleanly and contains no tl.
  for package in rendered do
    let entries ← packedEntries client s!"reading the staged {package.directory}"
      (staging ++ "/" ++ package.directory)
    let binary := entries.find? fun entry => entry.path == binRelative
    rows := rows ++ [
      { name := s!"npm packs {package.directory} with its binary at {binRelative}"
        held := binary.isSome
        detail := s!"npm would publish {String.intercalate ", " (entries.map (·.path))}" },
      { name := s!"npm publishes {package.directory}'s binary executable"
        held := match binary with
          | some entry => executableMode entry.mode
          | none => false
        detail := s!"mode was {(binary.map (·.mode)).getD 0}, and a package installed without the bit installs and then cannot be run" },
      { name := s!"{package.directory} carries no node_modules"
        held := entries.all fun entry => !entry.path.startsWith "node_modules"
        detail := "a packed node_modules would ship whatever a previous install left in the tree" },
      -- ADR-0006: the notice travels in every distribution artifact. `files`
      -- is what puts them there, and a package publishes without them exactly
      -- as cleanly as with them.
      { name := s!"{package.directory} ships the licence notices"
        held := licenceFiles.all fun licence => entries.any (·.path == licence)
        detail := s!"npm would publish {String.intercalate ", " (entries.map (·.path))}" }]
  -- Pack for real, then install, then run.
  let packed := scratch ++ "/packed"
  ensureDirectory packed
  let tarballOf (relative : String) : Decision String := do
    let before ← ofIO (do
      try return .ok ((← System.FilePath.readDir packed).toList.map (·.fileName))
      catch error => return .error s!"could not read {packed}: {error}")
    let _ ← client.must s!"packing {relative}"
      ["pack", staging ++ "/" ++ relative, "--pack-destination", packed]
    let after ← ofIO (do
      try return .ok ((← System.FilePath.readDir packed).toList.map (·.fileName))
      catch error => return .error s!"could not read {packed}: {error}")
    match after.filter (!before.contains ·) with
    | [one] => return packed ++ "/" ++ one
    | found =>
        decline s!"packing {relative} produced {found.length} new tarballs in {packed}, and exactly one was expected."
  let launcherTarball ← tarballOf launcherDirectory
  let platformTarball ← tarballOf (platformDirectory target)
  -- The published half of every immutable-version comparison reads a *tarball*
  -- back through npm rather than a directory, and nothing else exercises that
  -- spelling. If npm's answer for a tarball spec is not the shape this tool
  -- parses, every already-published comparison fails at release time, on the
  -- one path that cannot be retried.
  let fromDirectory ← packedEntries client "reading the staged launcher"
    (unambiguousDirectory (staging ++ "/" ++ launcherDirectory))
  let fromTarball ← packedEntries client "reading the packed launcher"
    (unambiguousDirectory launcherTarball)
  rows := rows ++ [
    { name := "npm reads a tarball back as the same entry set it packed"
      held := normalize (fromDirectory.map fun entry =>
                { path := entry.path, executable := executableMode entry.mode, digest := "" })
        == normalize (fromTarball.map fun entry =>
                { path := entry.path, executable := executableMode entry.mode, digest := "" })
      detail := s!"directory: {String.intercalate ", " (fromDirectory.map (·.path))}; tarball: {String.intercalate ", " (fromTarball.map (·.path))}" }]
  let install (prefix? : String) (tarballs : List String) : Decision Unit := do
    ensureDirectory prefix?
    let _ ← client.must s!"installing into {prefix?}"
      (["install"] ++ tarballs ++ ["--prefix", prefix?])
    return ()
  let drive (prefix? : String) (arguments : List String) : Decision ProcessOutput := do
    let launcher := prefix? ++ "/node_modules/.bin/tl"
    match ← ofIO (do return .ok (← Release.run launcher arguments.toArray)) with
    | .completed output => return output
    | outcome => decline s!"could not run {launcher}: {outcome.failureMessage.getD "unknown"}"
  let complete := scratch ++ "/complete"
  install complete [launcherTarball, platformTarball]
  -- Two arguments, the second holding a space: a launcher that re-split them
  -- would show three lines rather than two.
  let ran ← drive complete ["create", "a task"]
  let lines := (ran.stdout.splitOn "\n").filter (!·.isEmpty)
  rows := rows ++ [
    { name := "the installed .bin/tl symlink resolves to the platform package's binary"
      held := lines == ["create", "a task"]
      detail := s!"the binary saw {lines.length} argument(s): {String.intercalate " | " lines}" },
    { name := "exec passes the binary's exit status through the launcher"
      held := ran.exitCode == 7
      detail := s!"the launcher exited {ran.exitCode} where the binary exits 7" }]
  -- `npm install -g` is the documented install, and it puts the launcher
  -- somewhere else: a `bin/` beside the prefix rather than `node_modules/.bin`.
  let global := scratch ++ "/global"
  ensureDirectory global
  let _ ← client.must "installing globally"
    ["install", "--global", launcherTarball, platformTarball, "--prefix", global]
  let globallyRan ← ofIO (do
    return .ok (← Release.run (global ++ "/bin/tl") #["create", "a task"]))
  rows := rows ++ [
    { name := "a global install's bin/tl execs the host platform's binary"
      held := match globallyRan with
        | .completed output =>
            output.exitCode == 7
              && (output.stdout.splitOn "\n").filter (!·.isEmpty) == ["create", "a task"]
        | _ => false
      detail := s!"{global}/bin/tl: {(match globallyRan with | .completed output => s!"exit {output.exitCode}, stdout {output.stdout.trimAscii}" | outcome => outcome.failureMessage.getD "did not run")}" }]
  -- And the diagnosis when the platform package is absent, which is what a user
  -- on an unsupported platform, or one who omitted optional dependencies, sees.
  let launcherOnly := scratch ++ "/launcher-only"
  install launcherOnly [launcherTarball]
  let missing ← drive launcherOnly ["version"]
  rows := rows ++ [
    { name := "an absent platform package is diagnosed rather than executed"
      held := missing.exitCode == 1 && (missing.stderr.splitOn "is not installed").length > 1
      detail := s!"exit {missing.exitCode}, stderr: {missing.stderr.trimAscii}" }]
  ofIO (do
    try
      IO.FS.removeDirAll scratch
      return .ok ()
    catch _ => return .ok ())
  -- A run that performed no rows must not read as a clean one.
  if rows.isEmpty then
    decline "this selftest performed no rows at all, so every condition held by having nothing to hold of."
  match rows.filter (!·.held) with
  | [] => return s!"{rows.length} row(s) over real npm packages for {target}: packing, install layout, argument transparency, exit status, and the absent-package diagnosis"
  | failures =>
      decline ("real npm does not behave the way this channel assumes.\n"
        ++ String.join (failures.map fun row => s!"  {row.name}: {row.detail}\n"))

private def selftestCommand : Command :=
  optionCommand "npm-selftest" "--root <dir> [--npm <program>]"
    "Pack and install real npm packages, and drive the launcher through them."
    ["--root", "."]
    selftestOptions selftestArgs selftestDecision

def npmCommands : List Command :=
  [manifestsCommand, stageCommand, publishCommand, bootstrapCommand, selftestCommand]

end Npm

export Npm (npmCommands)

end Release
