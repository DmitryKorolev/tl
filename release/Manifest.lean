/-
The canonical description of one release, written once and read everywhere.

Every job downstream of signing used to reconstruct, independently, what a
release consists of: the sign job built an asset list with `find`, the Homebrew
generator re-derived the platform set from `SHA256SUMS`, the npm job re-derived
it from which files happened to be present, and each carried its own copy of
the tier policy. Four derivations of one fact is four chances to disagree, and
the disagreements are invisible — each job's answer looks reasonable on its own.

So the release is described once, here, and the description is signed alongside
`SHA256SUMS`. `manifest-verify` is how a later job consumes it: the directory
must hold exactly what the manifest says, with the digests it names, and
anything extra or missing is a refusal. A job that has verified the manifest
does not re-derive anything.

What this deliberately does not do is replace the signature. The manifest is
evidence *about* a set of bytes; `scripts/verify-release-artifacts.sh` is what
establishes that those bytes are the ones this repository signed, and it runs
first everywhere both are used.

## The split between collecting and deciding

Walking a directory, typing its entries, reading files and hashing them is I/O,
and it is tested. Deciding is pure, and the two decisions that can fail
silently carry theorems: `manifestAccepts_iff` here, and `metadataAccepts_iff`
in `release/Model.lean`. The seam between them is a value — `DirectoryEvidence`
for verification, `TargetEvidence` for generation — so the verdicts can be
driven to every branch without a filesystem, which is what makes the failure
paths cheap enough to cover exhaustively.

## What the shell got wrong, beyond the language

Four defects are closed structurally rather than by being more careful:

- `required=$(rc_targets supported)` as an *assignment prefix* on the `python3`
  command discarded the substitution's status, so an unreadable
  `release/targets.json` produced empty tier lists — and a manifest describing
  a release with no targets, which skipped every per-leg comparison and was
  then signed. Here the target list is parsed into `Targets`, whose parser
  refuses an empty one, and generation refuses unless the evidence covers every
  target in it exactly once.
- The run identity was compared leg-to-leg only, so four artifacts carried in
  from an earlier run of the same workflow agreed with each other perfectly.
  `RunContext` is now a fact the release is held to, and the leg-to-leg
  agreement is checked as well rather than instead.
- Each binary was hashed three times — once to compare against its leg's
  record, once for the target row, once for the asset row. Every file here is
  hashed exactly once and the digest is carried.
- Non-regular directory entries were skipped silently. A symbolic link in a
  release directory is described by the digest of what it points at while what
  a consumer receives is the link; it is refused.
-/
import release.Command
import release.Digest
import release.Json
import release.Model

namespace Release

open Lean (Json)

/-! ## What kind of thing an asset is -/

/-- What a published file is, as far as a consumer needs to know.

    A closed enumeration with an `other` case rather than an open string: the
    classification is a courtesy to a reader of the release page, and a file
    this generator does not recognise is described as unrecognised rather than
    left out — the manifest's job is to account for everything in the
    directory. -/
inductive AssetKind where
  | binary
  | buildMetadata
  | linkAudit
  | notice
  | sbom
  | documentation
  | other
  deriving DecidableEq, Repr

def AssetKind.wire : AssetKind → String
  | .binary => "binary"
  | .buildMetadata => "build-metadata"
  | .linkAudit => "link-audit"
  | .notice => "notice"
  | .sbom => "sbom"
  | .documentation => "documentation"
  | .other => "other"

/-- The published notice files, named once. -/
private def noticeNames : List String := ["LICENSE", "THIRD-PARTY-LICENSES"]

private def documentationNames : List String := ["REBUILDING.md"]

/-- Classify one file. The binary case is decided against the target list
    rather than against the asset prefix alone, so a file merely *shaped* like a
    binary is `other` and is still described. -/
def classifyAsset (targets : List Target) (name : String) : AssetKind :=
  if targets.any (·.asset == name) then .binary
  else if targets.any (·.buildMetadataAsset == name) then .buildMetadata
  else if targets.any (·.linkAuditAsset == name) then .linkAudit
  else if noticeNames.contains name then .notice
  else if name.endsWith ".spdx.json" then .sbom
  else if documentationNames.contains name then .documentation
  else .other

/-- One described file. -/
structure Asset where
  name : String
  sha256 : Sha256
  kind : AssetKind
  deriving Repr

/-! ## Verification: does this directory hold what the manifest describes?

The evidence is two lists rather than one map, because the two are collected
differently and answer different questions. The names answer "is anything here
that this release does not account for", which needs no bytes read. The digests
answer "are these the bytes", and are collected only for the files the manifest
describes — hashing a file nothing describes would read a large file to answer
a question its *name* has already answered. -/

/-- The release directory as the check saw it. -/
structure DirectoryEvidence where
  names : List String
  digests : List (String × Sha256)
  deriving Repr

/-- The signature bundle for an asset, by name. -/
def bundleName (asset : String) : String := asset ++ ".sigstore.json"

/-- The two files a manifest structurally cannot describe.

    They are hashed *into* each other's world: `SHA256SUMS` lists the manifest,
    so the manifest cannot list the sums file without one of them having to be
    written twice. Named once, because three things depend on the same answer —
    what generation omits, what verification tolerates, and which bundles are
    accounted for — and two of those disagreeing is a release that refuses
    itself. -/
def structurallyUndescribable (manifestName : String) : List String :=
  ["SHA256SUMS", manifestName]

/-- Everything a signature bundle may be named for.

    The described assets *and* the two above. The workflow signs `SHA256SUMS`
    explicitly and every name in its asset list — which includes the manifest,
    because that is a regular file in the directory — so the bundles for those
    two exist in every real release. An earlier version of this admitted
    bundles only for described assets and therefore rejected every directory the
    pipeline actually produces. -/
def bundleSubjects (manifestName : String) (assets : List Asset) : List String :=
  structurallyUndescribable manifestName ++ assets.map (·.name)

/-- What a release directory may hold without the manifest describing it.

    The bundles are admitted *by subject*, not by suffix. Written as "anything
    ending .sigstore.json", the one category of file this check cannot inspect
    became a category anyone could add a member to: a file named for nothing in
    the release would be published beside the signed set, and accounted for by
    neither the manifest nor SHA256SUMS, which excludes the same suffix. -/
def allowedUndescribed (manifestName : String) (assets : List Asset) (name : String) : Bool :=
  (structurallyUndescribable manifestName).contains name
    || (bundleSubjects manifestName assets).any fun subject => bundleName subject == name

/-- One described asset: it is present, and its bytes are the ones the manifest
    names. -/
def describedCheck (directory : String) (evidence : DirectoryEvidence)
    (asset : Asset) : Check :=
  match evidence.digests.lookup asset.name with
  | some digest =>
      { held := digest == asset.sha256,
        failure := s!"{asset.name} hashes to {digest.hex}, but the manifest says {asset.sha256.hex}." }
  | none =>
      { held := false,
        failure :=
          if evidence.names.contains asset.name then
            s!"{asset.name} is in {directory} and the manifest describes it, but no digest was collected for it. That is this program failing to look rather than the directory being wrong, and the two must not be reported as the same thing."
          else
            s!"{asset.name} is described by the manifest but is not in {directory}." }

def describedChecks (directory : String) (assets : List Asset)
    (evidence : DirectoryEvidence) : List Check :=
  assets.map (describedCheck directory evidence)

/-- One file present: the manifest accounts for it.

    An extra asset in a signed release is not a harmless surplus. It is
    published under the same release, next to files this pipeline produced, and
    a user has no way to tell it apart from one that was. -/
def undescribedCheck (directory : String) (manifestName : String)
    (assets : List Asset) (name : String) : Check :=
  { held := allowedUndescribed manifestName assets name || assets.any (·.name == name),
    failure := s!"{name} is in {directory} but the manifest does not describe it — a release must not publish an asset nothing accounts for. The only exceptions are SHA256SUMS, the manifest itself, and a .sigstore.json bundle named for an asset the manifest does describe." }

def undescribedChecks (directory : String) (manifestName : String)
    (assets : List Asset) (evidence : DirectoryEvidence) : List Check :=
  evidence.names.map (undescribedCheck directory manifestName assets)

def manifestChecks (directory : String) (manifestName : String) (assets : List Asset)
    (evidence : DirectoryEvidence) : List Check :=
  describedChecks directory assets evidence
    ++ undescribedChecks directory manifestName assets evidence

/-- Whether the directory matches the manifest. -/
def manifestAccepts (directory : String) (manifestName : String) (assets : List Asset)
    (evidence : DirectoryEvidence) : Bool :=
  Check.allHeld (manifestChecks directory manifestName assets evidence)

/-- Every check built by mapping over a list holds exactly when the property it
    encodes holds of every element.

    The one piece of list plumbing both halves of the theorem below need, stated
    once so neither has to repeat it. -/
private theorem all_mapped_held_iff {α : Type} (build : α → Check) (items : List α)
    (property : α → Prop) (encodes : ∀ item, (build item).held = true ↔ property item) :
    (items.map build).all (·.held) = true ↔ ∀ item ∈ items, property item := by
  rw [List.all_eq_true]
  constructor
  · intro held item member
    exact (encodes item).mp (held (build item) (List.mem_map.mpr ⟨item, member, rfl⟩))
  · intro every check member
    have ⟨item, isMember, isCheck⟩ := List.mem_map.mp member
    rw [← isCheck]
    exact (encodes item).mpr (every item isMember)

private theorem describedCheck_held_iff (directory : String) (evidence : DirectoryEvidence)
    (asset : Asset) :
    (describedCheck directory evidence asset).held = true ↔
      evidence.digests.lookup asset.name = some asset.sha256 := by
  rw [describedCheck]
  match lookup : evidence.digests.lookup asset.name with
  | none =>
      constructor
      · intro absurdity; exact Bool.noConfusion absurdity
      · intro absurdity; cases absurdity
  | some digest =>
      constructor
      · intro matched
        rw [beq_iff_eq] at matched
        rw [matched]
      · intro isDigest
        rw [Option.some.inj isDigest]
        exact beq_self_eq_true _

private theorem undescribedCheck_held_iff (directory : String) (manifestName : String)
    (assets : List Asset) (name : String) :
    (undescribedCheck directory manifestName assets name).held = true ↔
      allowedUndescribed manifestName assets name = true
        ∨ ∃ asset ∈ assets, asset.name = name := by
  rw [undescribedCheck, Bool.or_eq_true]
  constructor
  · intro held
    match held with
    | .inl allowed => exact .inl allowed
    | .inr described =>
        have ⟨asset, isMember, named⟩ := List.any_eq_true.mp described
        exact .inr ⟨asset, isMember, beq_iff_eq.mp named⟩
  · intro accounted
    match accounted with
    | .inl allowed => exact .inl allowed
    | .inr ⟨asset, isMember, named⟩ =>
        exact .inr (List.any_eq_true.mpr ⟨asset, isMember, beq_iff_eq.mpr named⟩)

/-- **The directory matches exactly when every described asset is present with
    the digest the manifest names, and nothing present is undescribed.**

    Both directions matter and each rules out a different way of being useless,
    in opposite directions.

    *Left to right* is soundness, and it is what forces every check to still be
    there. Dropping `undescribedChecks` makes the verdict strictly more
    accepting, so a directory holding an extra file passes while the right-hand
    side's second conjunct is false — this implication fails and the theorem
    stops compiling. Any check quietly removed from the list breaks this
    direction, which is the failure that is invisible in the output.

    *Right to left* is completeness, and it is what a verdict that accepts
    nothing cannot satisfy. A check list that refused every directory would
    prove the first direction trivially.

    Stated about the evidence value and not about a directory, deliberately.
    Walking, typing, reading and hashing are I/O and are tested; what is proved
    is that *given* what was collected, the verdict says exactly this. Reading
    it as a statement about a filesystem would claim the collection is correct,
    which no theorem here establishes. -/
theorem manifestAccepts_iff (directory : String) (manifestName : String)
    (assets : List Asset) (evidence : DirectoryEvidence) :
    manifestAccepts directory manifestName assets evidence = true ↔
      (∀ asset ∈ assets, evidence.digests.lookup asset.name = some asset.sha256)
        ∧ (∀ name ∈ evidence.names,
            allowedUndescribed manifestName assets name = true
              ∨ ∃ asset ∈ assets, asset.name = name) := by
  rw [manifestAccepts, Check.allHeld, manifestChecks, List.all_append, Bool.and_eq_true,
    describedChecks, undescribedChecks,
    all_mapped_held_iff _ _ _ (describedCheck_held_iff directory evidence),
    all_mapped_held_iff _ _ _ (undescribedCheck_held_iff directory manifestName assets)]

/-- Why the directory does not match, or nothing at all. -/
def manifestFailures (directory : String) (manifestName : String) (assets : List Asset)
    (evidence : DirectoryEvidence) : List String :=
  Check.failures (manifestChecks directory manifestName assets evidence)

/-- **`manifest-verify` reports nothing exactly when every described asset is
    present with the digest the manifest names and nothing present is
    undescribed.**

    `manifestAccepts_iff` characterises the verdict; the command calls the
    report. On its own that would leave the theorem about a function nothing
    reaches. Composed with `Check.allHeld_iff_noFailures` it lands on the list
    the command branches on, which is where the guarantee has to be. -/
theorem manifestFailures_isEmpty_iff (directory : String) (manifestName : String)
    (assets : List Asset) (evidence : DirectoryEvidence) :
    manifestFailures directory manifestName assets evidence = [] ↔
      (∀ asset ∈ assets, evidence.digests.lookup asset.name = some asset.sha256)
        ∧ (∀ name ∈ evidence.names,
            allowedUndescribed manifestName assets name = true
              ∨ ∃ asset ∈ assets, asset.name = name) :=
  Iff.trans
    (Check.allHeld_iff_noFailures (manifestChecks directory manifestName assets evidence)).symm
    (manifestAccepts_iff directory manifestName assets evidence)

/-! ## Generation: what the release consists of -/

/-- What the collector found for one target.

    `absent` carries nothing because there is nothing to carry; whether that is
    acceptable is a question about the target's tier, answered where the
    decision is. The two companion files are reported as found or not rather
    than refused on the spot, for the same reason: whether a binary may be
    published without its leg's record is policy, and policy lives in the pure
    layer where every branch of it is reachable from a test without a
    filesystem. -/
inductive ArtifactEvidence where
  | absent
  | present (digest : Sha256) (build : Option BuildMetadata) (linkAuditPresent : Bool)
  deriving Repr

structure TargetEvidence where
  target : Target
  found : ArtifactEvidence
  deriving Repr

/-- What signing is about to publish.

    Private constructor: `Manifest.of` is the only way in, and it refuses every
    release this pipeline must not describe. The npm and Homebrew plans are
    *derived* below rather than stored, so they cannot disagree with the target
    outcomes they are computed from — the shell stored them and the two were
    free to drift. -/
structure Manifest where
  private mk ::
  version : Version
  commit : Commit
  identity : Identity
  toolchain : String
  lakeManifestSha256 : Sha256
  outcomes : List TargetOutcome
  assets : List Asset

def Manifest.publishedTargets (manifest : Manifest) : List String :=
  manifest.outcomes.filterMap fun outcome =>
    outcome.published?.map fun published => published.target.name

/-- The npm scope, which is the owner half of the package name. -/
def Manifest.npmScope (manifest : Manifest) : String :=
  (manifest.identity.npmPackage.splitOn "/").headD manifest.identity.npmPackage

/-- A prerelease must not become what `npm install` resolves to. Read off the
    parsed version rather than by looking for a `-` in a string, which is how a
    prerelease reached the `latest` tag once already. -/
def Manifest.npmDistTag (manifest : Manifest) : String :=
  if manifest.version.isPrerelease then "next" else "latest"

def Manifest.npmPackages (manifest : Manifest) : List String :=
  manifest.identity.npmPackage
    :: manifest.publishedTargets.map fun name => s!"{manifest.npmScope}/tl-bin-{name}"

def Manifest.homebrewTap (manifest : Manifest) : String :=
  manifest.identity.homebrewTap

/-- A tap carries one formula, so a prerelease is generated and attached but
    never pushed (ADR-0006). -/
def Manifest.homebrewPush (manifest : Manifest) : Bool :=
  !manifest.version.isPrerelease

/-- Everything generation needs, as one value. Nothing here does I/O; the
    command below reads the world and hands this over. -/
structure ManifestInputs where
  version : Version
  facts : ReleaseFacts
  identity : Identity
  targets : Targets
  evidence : List TargetEvidence
  directory : List (String × Sha256)

/-- What became of one target, or why the release cannot be described.

    A Supported target that did not arrive stops the release; a Best-effort one
    that did not is recorded as unpublished, which is a statement rather than an
    omission — a consumer reading the manifest can tell "we did not build this"
    from "we do not know about this". -/
private def outcomeOfEvidence (facts : ReleaseFacts) (target : Target)
    (found : ArtifactEvidence) : Except String TargetOutcome :=
  match found with
  | .absent =>
      if target.tier.releaseBlocking then
        .error s!"{target.asset} is missing, and '{target.name}' is a Supported target — release-blocking under ADR-0006. Fix the failing build leg; do not publish a partial release."
      else .ok (.absent target)
  | .present digest build linkAuditPresent =>
      match build with
      -- Mandatory, not "compared when the file happens to be there". Written
      -- the other way this was fail-open in the worst direction: delete the
      -- record and the binary published with no comparison at all, so the check
      -- that exists to prove the signed bytes were smoke-tested was satisfied
      -- by removing the evidence for it.
      | none =>
          .error s!"{target.asset} is present but {target.buildMetadataAsset} is not. Every published target carries the record its own build leg wrote — that record is the only thing tying the signed bytes to the leg that smoke-tested them, so its absence is a refusal rather than a check that gets skipped. Fix the upload in the build job."
      | some build =>
          if !linkAuditPresent then
            .error s!"{target.asset} is present but {target.linkAuditAsset} is not. ADR-0006 requires the link-time audit for every binary release, and it is produced per target by the leg that built it. Fix the upload in the build job."
          else
            (PublishedTarget.of facts target digest build).map TargetOutcome.published

/-- Which run a leg says produced it: the workflow and the run within it.

    Both, not the run id alone. Ids are per repository and per workflow, so two
    different workflows in one repository can legitimately record the same id —
    and outside a workflow, where there is no ambient identity to hold each leg
    to, this comparison is the only thing left saying the legs belong together.
    Comparing half of it would let a binary built by `ci.yml` sit in a release
    beside three built by `release.yml`. -/
private def recordedRun (build : BuildMetadata) : String :=
  s!"{build.workflowRef} run {build.runId}"

/-- The first pair of published legs that disagree about which run built them.

    Checked as well as the per-leg agreement with `RunContext`, not instead of
    it: outside a workflow there is no ambient run, and inside one this catches
    a leg whose record agrees with the ambient values for the wrong reason.
    Adjacent pairs of the recorded runs, so this is one pass. -/
private def crossedRuns : List (String × String) → Option (String × String × String)
  | [] => none
  | [_] => none
  | (name, run) :: rest@((nextName, nextRun) :: _) =>
      if run == nextRun then crossedRuns rest
      else some (name, nextName, s!"{run} and {nextRun}")

/-- The first name listed twice, if any. -/
private def repeatedName : List String → Option String
  | [] => none
  | name :: rest => if rest.contains name then some name else repeatedName rest

/-- Assemble the description of a release, refusing every one this pipeline
    must not publish. -/
def Manifest.of (inputs : ManifestInputs) : Except String Manifest := do
  -- Refused here as well as in `Targets.parse`, and not as belt and braces: an
  -- empty list makes every loop below vacuous, so a manifest would be rendered
  -- and signed having compared nothing — which is exactly what an unreadable
  -- targets file did to the shell. A check whose failure mode is "passes
  -- silently when the input is empty" is worth stating twice.
  if inputs.targets.targets.isEmpty then
    .error "the target list is empty, so this manifest would describe a release with no targets — and every per-leg comparison below would pass by having nothing to compare. That is a signed document asserting a release whose contents nothing looked at, which is the opposite of a smaller release."
  -- The evidence covers the target list exactly. This is what an unreadable
  -- `release/targets.json` used to defeat: with an empty list every per-leg
  -- comparison was skipped, and a signed manifest asserted a release whose
  -- contents nothing had looked at. Stated as a correspondence rather than as
  -- a count, so a row for a target that is not in the list is caught too.
  for target in inputs.targets.targets do
    let matching := inputs.evidence.filter (·.target.name == target.name)
    if matching.isEmpty then
      .error s!"no evidence was collected for the target '{target.name}', which release/targets.json lists. A manifest that simply omitted it would describe a smaller release than the one being cut, and nothing downstream could tell that from a release that really is smaller."
    if matching.length > 1 then
      .error s!"evidence for the target '{target.name}' was collected {matching.length} times. Which row applies would depend on lookup order."
  for row in inputs.evidence do
    if (inputs.targets.find? row.target.name).isNone then
      .error s!"evidence was collected for '{row.target.name}', which release/targets.json does not list. The target list is what decides whether a missing artifact blocks the release, so an artifact outside it has no tier and cannot be published."
  -- The target is taken from the parsed list, and only the *findings* come from
  -- the evidence row. Reading `row.target` instead would let a caller decide a
  -- target's tier by supplying it — and demoting a Supported target to
  -- best-effort turns a release-blocking absence into a row saying "not built",
  -- which is a partial release that describes itself as complete.
  let outcomes ← inputs.targets.targets.mapM fun target =>
    match inputs.evidence.find? (·.target.name == target.name) with
    | some row => outcomeOfEvidence inputs.facts target row.found
    | none =>
        -- Unreachable: the loop above refused unless every target has a row.
        .error s!"no evidence was collected for the target '{target.name}'."
  let recordedRuns := outcomes.filterMap fun outcome =>
    outcome.published?.map fun published => (published.target.name, recordedRun published.build)
  match crossedRuns recordedRuns with
  | some (first, second, ids) =>
      .error s!"the '{first}' and '{second}' legs record different runs ({ids}). These binaries were not produced by one run of this workflow."
  | none => pure ()
  -- A record or an audit for a binary that did not arrive. Left alone it is
  -- hashed, described in the manifest and signed, while nothing ever compares
  -- it to anything — a published document about an artifact this release does
  -- not contain.
  for row in inputs.evidence do
    match row.found with
    | .present _ _ _ => pure ()
    | .absent =>
        let orphans := [row.target.buildMetadataAsset, row.target.linkAuditAsset].filter
          fun name => inputs.directory.any (·.1 == name)
        match orphans with
        | [] => pure ()
        | name :: _ =>
            .error s!"{name} is in the release directory but {row.target.asset} is not. That describes a leg that recorded what it built and then did not deliver it; publishing the record alone would sign a document about an artifact this release does not contain. Fix the upload in the build job, or remove the leftover file."
  match repeatedName (inputs.directory.map (·.1)) with
  | some name =>
      .error s!"'{name}' was collected twice from the release directory. A directory cannot hold two entries under one name, so this is the collector having listed something twice; the manifest would describe one of them and verification would compare against the other."
  | none => pure ()
  if inputs.directory.isEmpty then
    .error "the release directory holds no assets to describe. An empty manifest would read as a release with nothing in it rather than as a broken step."
  -- Sorted by name here rather than trusted to arrive sorted: the manifest is
  -- hashed into SHA256SUMS and signed, so its bytes must be a function of its
  -- content and not of the order a directory listing happened to return.
  let ordered := inputs.directory.mergeSort (fun left right => left.1 ≤ right.1)
  let assets := ordered.map fun (name, digest) =>
    { name, sha256 := digest, kind := classifyAsset inputs.targets.targets name }
  return ⟨inputs.version, inputs.facts.commit, inputs.identity, inputs.facts.toolchain,
    inputs.facts.lakeManifestSha256, outcomes, assets⟩

/-! ## The document -/

private def buildJson (build : BuildMetadata) : Json :=
  Json.mkObj [
    ("target", Json.str build.target),
    ("sha256", Json.str build.sha256.hex),
    ("commit", Json.str build.commit.hex),
    ("tier", Json.str build.tier.wire),
    ("runner", Json.str build.runner),
    ("runnerOs", Json.str build.runnerOs),
    ("runnerArch", Json.str build.runnerArch),
    ("containerImage", Json.str build.containerImage),
    ("toolchain", Json.str build.toolchain),
    ("lakeManifestSha256", Json.str build.lakeManifestSha256.hex),
    ("workflowRef", Json.str build.workflowRef),
    ("runId", Json.str build.runId),
    ("runAttempt", Json.str build.runAttempt)]

/-- What a target *is*, as opposed to what became of it.

    The platform fields travel in the manifest so a channel projecting this
    release does not have to read `release/targets.json` from a checkout to
    learn where a binary runs. Both downstream channels need them — Homebrew to
    choose the `on_macos`/`on_arm` block a url is written in, npm to fill each
    platform package's `os`, `cpu` and `libc` — and a checkout's target list is
    a fact about the working tree rather than about the release being published,
    so reading it there would put back a second derivation of the thing this
    document exists to state once. -/
private def platformJson (target : Target) : List (String × Json) :=
  [("target", Json.str target.name),
   ("tier", Json.str target.tier.wire),
   ("os", Json.str target.os),
   ("cpu", Json.str target.cpu),
   ("libc", match target.libc with
     | some libc => Json.str libc
     | none => Json.null)]

/-- A target row. An absent target keeps every key with a `null` value rather
    than dropping the keys: a consumer reading `asset` gets "there is none"
    instead of a missing-key error, and the two rows have the same shape. -/
private def outcomeJson : TargetOutcome → Json
  | .published published =>
      Json.mkObj (platformJson published.target ++ [
        ("published", Json.bool true),
        ("asset", Json.str published.asset),
        ("sha256", Json.str published.digest.hex),
        ("build", buildJson published.build)])
  | .absent target =>
      Json.mkObj (platformJson target ++ [
        ("published", Json.bool false),
        ("asset", Json.null),
        ("sha256", Json.null),
        ("build", Json.null)])

private def assetJson (asset : Asset) : Json :=
  Json.mkObj [
    ("name", Json.str asset.name),
    ("sha256", Json.str asset.sha256.hex),
    ("kind", Json.str asset.kind.wire)]

/-- The schema this document declares.

    Bumped when a consumer would have to change. The per-target platform fields
    are required rather than additive, and this stayed at 1 because no manifest
    at this version has ever been published: the first release cuts the first
    one. A reader given an older document refuses it for the missing field
    rather than for the version, which is the right message for a document that
    does not exist. -/
def manifestSchemaVersion : Nat := 1

def Manifest.toJson (manifest : Manifest) : Json :=
  Json.mkObj [
    ("schemaVersion", Json.num manifestSchemaVersion),
    ("product", Json.str "tl"),
    ("version", Json.str manifest.version.render),
    ("tag", Json.str manifest.version.tag),
    ("commit", Json.str manifest.commit.hex),
    ("repository", Json.str manifest.identity.repository),
    ("toolchain", Json.str manifest.toolchain),
    ("lakeManifestSha256", Json.str manifest.lakeManifestSha256.hex),
    ("signing", Json.mkObj [
      ("certificateOidcIssuer", Json.str manifest.identity.certificateOidcIssuer),
      ("certificateIdentityRegexp", Json.str manifest.identity.certificateIdentityRegexp),
      ("workflow", Json.str manifest.identity.releaseWorkflow)]),
    ("targets", Json.arr (manifest.outcomes.map outcomeJson).toArray),
    ("assets", Json.arr (manifest.assets.map assetJson).toArray),
    ("npm", Json.mkObj [
      ("distTag", Json.str manifest.npmDistTag),
      ("packages", Json.arr (manifest.npmPackages.map Json.str).toArray)]),
    ("homebrew", Json.mkObj [
      ("tap", Json.str manifest.homebrewTap),
      ("push", Json.bool manifest.homebrewPush),
      ("pinnedTargets", Json.arr (manifest.publishedTargets.map Json.str).toArray)])]

def renderManifest (manifest : Manifest) : Except String String := render manifest.toJson

/-! ## Reading a manifest back

The signed manifest is the authoritative description of a release, so this reads
all of it. It used to read the tag and the asset table, which is the whole of
what `manifest-verify` consumes, and every other consumer re-derived what it
needed from a directory listing or from `SHA256SUMS` — the four-derivations
problem this module's header is about, still present on the read side.

Reading it whole also means the document is checked for *internal agreement*
once, here, before any channel acts on any part of it. A target row whose
embedded build record describes a different target, an asset digest that
disagrees with the target row naming the same file, an npm package list that
does not follow from the targets that were published, a Homebrew section pinning
a target this release did not publish: each is a signed document contradicting
itself, and each would otherwise be found — or not — by whichever channel
happened to read that section.

The signature is what establishes the document is ours; this is what establishes
it says one thing. Neither substitutes for the other. -/

/-- The signing pins a manifest records, read back.

    Carried rather than skipped because they are what a consumer would have to
    trust some *other* copy of if the manifest did not state them, and the
    project already has five copies of that pin. -/
structure ManifestSigning where
  certificateOidcIssuer : String
  certificateIdentityRegexp : String
  workflow : String
  deriving Repr

/-- What a manifest says became of one target.

    The published case carries the leg's own record, parsed by the same parser
    that read the `build-metadata-*.json` asset — so a record the standalone
    document would be refused for cannot enter through the manifest instead. -/
inductive ManifestOutcome where
  | published (asset : String) (sha256 : Sha256) (build : BuildMetadata)
  | absent
  deriving Repr

/-- One target row of a manifest: what the target is, and what became of it. -/
structure ManifestTarget where
  target : Target
  outcome : ManifestOutcome
  deriving Repr

/-- The asset and digest a row publishes, when it publishes one. -/
def ManifestTarget.published? (row : ManifestTarget) : Option (String × Sha256) :=
  match row.outcome with
  | .published asset digest _ => some (asset, digest)
  | .absent => none

/-- The npm projection of a release, as the manifest states it. -/
structure ManifestNpmPlan where
  distTag : String
  packages : List String
  deriving Repr

/-- The Homebrew projection of a release, as the manifest states it. -/
structure ManifestHomebrewPlan where
  tap : String
  push : Bool
  pinnedTargets : List String
  deriving Repr

/-- A manifest, read back whole. -/
structure ManifestDescription where
  schemaVersion : Nat
  product : String
  version : Version
  tag : String
  commit : Commit
  repository : String
  toolchain : String
  lakeManifestSha256 : Sha256
  signing : ManifestSigning
  targets : List ManifestTarget
  assets : List Asset
  npm : ManifestNpmPlan
  homebrew : ManifestHomebrewPlan

/-- The targets this release published, in manifest order. The order is part of
    the document: `release/targets.json` lists Supported targets before
    Best-effort ones, and a consumer that re-sorted would produce a different
    formula or package set for the same release. -/
def ManifestDescription.publishedTargets (description : ManifestDescription) : List String :=
  description.targets.filterMap fun row => row.published?.map fun _ => row.target.name

/-- Every target this release published, with the digest to pin for it. What a
    channel projection is built from. -/
def ManifestDescription.pinned (description : ManifestDescription) : List (Target × Sha256) :=
  description.targets.filterMap fun row =>
    row.published?.map fun (_, digest) => (row.target, digest)

/-- What the release says about each distributed target, published or not. The
    tier lives here, so a channel decides what an absence means without reading
    a checkout's own target list. -/
def ManifestDescription.distributedTargets (description : ManifestDescription) : List Target :=
  description.targets.map (·.target)

/-- The scope half of a package name, which is the owner every platform package
    is published under. -/
def npmScopeOf (package : String) : String := (package.splitOn "/").headD package

/-- The platform package for one target, under a scope. The one site that knows
    how a platform package is spelled on the reading side; `Manifest.npmPackages`
    is the one that knows it on the writing side, and the coherence check below
    is what holds them together. -/
def npmPlatformPackage (scope target : String) : String := s!"{scope}/tl-bin-{target}"

/-- What `npm install` would resolve to for a release at this version. A
    prerelease must not become `latest`, and the decision is read off the parsed
    version rather than by looking for a `-` in a string. -/
def npmDistTagFor (version : Version) : String :=
  if version.isPrerelease then "next" else "latest"

/-- The package list a release at this version, publishing these targets, must
    carry: the launcher first, then one platform package per published target,
    in target order. -/
def npmPackagesFor (launcher : String) (published : List String) : List String :=
  launcher :: published.map (npmPlatformPackage (npmScopeOf launcher))

private def parseAsset (cursor : Cursor) (value : Json) : Except String Asset := do
  let name ← nonEmptyStringField cursor value "name"
  let sha256 ← Sha256.parse (cursor.at "sha256").render
    (← nonEmptyStringField cursor value "sha256")
  -- The kind is carried through as it was written. It is a courtesy to a
  -- reader and no verdict branches on it, so a kind this build does not know
  -- is not a reason to refuse a manifest an older one wrote.
  let kindText ← nonEmptyStringField cursor value "kind"
  let kind := match AssetKind.wire .binary == kindText, kindText with
    | true, _ => AssetKind.binary
    | false, text =>
        ([AssetKind.buildMetadata, .linkAudit, .notice, .sbom, .documentation].find?
          (·.wire == text)).getD .other
  return { name, sha256, kind }

private def parseSigning (cursor : Cursor) (root : Json) : Except String ManifestSigning := do
  let (inner, found) ← field cursor root "signing"
  return {
    certificateOidcIssuer := ← nonEmptyStringField inner found "certificateOidcIssuer"
    certificateIdentityRegexp := ← nonEmptyStringField inner found "certificateIdentityRegexp"
    workflow := ← nonEmptyStringField inner found "workflow" }

/-- One target row.

    An unpublished target keeps every key with a `null` value rather than
    dropping them, so the two shapes are the same shape — and this reads them
    back that way. A row saying it published nothing while carrying an asset
    name is not a row with a harmless leftover field: whichever half a consumer
    read would decide whether that platform is served. -/
private def parseTargetRow (cursor : Cursor) (value : Json) : Except String ManifestTarget := do
  -- The same reader `release/targets.json` goes through. The row states the
  -- platform so a channel projecting this release needs no checkout to learn
  -- where the binary runs, and one reader is what keeps the two statements of a
  -- target from being two definitions of one.
  let target ← parseTarget cursor value
  if ← boolField cursor value "published" then
    let asset ← nonEmptyStringField cursor value "asset"
    let sha256 ← Sha256.parse (cursor.at "sha256").render
      (← nonEmptyStringField cursor value "sha256")
    let (buildCursor, buildValue) ← field cursor value "build"
    let build ← BuildMetadata.ofJson buildCursor buildValue
    return { target, outcome := .published asset sha256 build }
  else
    for key in ["asset", "sha256", "build"] do
      match field? value key with
      | some .null => pure ()
      | some _ =>
          (cursor.at key).fail s!"is set on a row that says it published nothing. The two halves of this row disagree about whether this release serves '{target.name}', and a consumer would act on whichever half it happened to read."
      | none =>
          (cursor.at key).fail s!"is missing from the row for '{target.name}'. An unpublished target keeps every key with a null value, so that a reader gets \"there is none\" rather than a missing-key error and the two row shapes stay one shape."
    return { target, outcome := .absent }

private def parseNpmPlan (cursor : Cursor) (root : Json) : Except String ManifestNpmPlan := do
  let (inner, found) ← field cursor root "npm"
  return {
    distTag := ← nonEmptyStringField inner found "distTag"
    packages := ← stringArrayField inner found "packages" }

private def parseHomebrewPlan (cursor : Cursor) (root : Json) :
    Except String ManifestHomebrewPlan := do
  let (inner, found) ← field cursor root "homebrew"
  return {
    tap := ← nonEmptyStringField inner found "tap"
    push := ← boolField inner found "push"
    pinnedTargets := ← stringArrayField inner found "pinnedTargets" }

/-! ### Does the document say one thing?

Every row below compares two statements the manifest makes about the same fact.
Nothing here reads a file or a directory: this is the document against itself,
which is why it is a `Check` list with a theorem rather than a sequence of `if`s
in the parser. A row silently dropped from it makes the verdict strictly more
accepting, and the shape of that failure — a channel publishing on the strength
of a section nothing compared — is the one this port exists to remove. -/

/-- A list of names carries no repeat. The failure names the offender, which is
    why the condition and the message are two readings of one lookup. -/
private def uniqueNamesCheck (names : List String) (explain : String → String) : Check :=
  { held := (repeatedName names).isNone,
    failure := match repeatedName names with
      | some name => explain name
      | none => "" }

/-- What one published target row has to agree with the rest of the document
    about. An unpublished row states nothing that could disagree. -/
def targetRowChecks (description : ManifestDescription) (row : ManifestTarget) : List Check :=
  match row.outcome with
  | .absent => []
  | .published asset digest build =>
      [{ held := asset == assetNameFor row.target.name,
         failure := s!"the '{row.target.name}' row names the asset '{asset}', but a target's asset is composed from its name and would be '{assetNameFor row.target.name}'. A consumer downloading what this row names would fetch a file this release does not describe." },
       { held := (description.assets.find? (·.name == asset)).map (·.sha256) == some digest,
         failure := s!"the '{row.target.name}' row gives {asset} the digest {digest.hex}, and the asset table does not agree — either it does not list that file at all, or it lists a different digest for it. The manifest is the one description of this release and it contradicts itself here; a channel pinning the digest from one section would serve bytes the other section refuses." },
       { held := build.target == row.target.name,
         failure := s!"the '{row.target.name}' row embeds a build record for '{build.target}'. The records were crossed between rows, so this one does not describe its own binary." },
       { held := build.tier == row.target.tier,
         failure := s!"the '{row.target.name}' row records tier '{row.target.tier.wire}' and embeds a build record saying '{build.tier.wire}'. The tier decides whether an absent artifact blocks a release, so a document that states it twice must state it once." },
       { held := build.sha256 == digest,
         failure := s!"the '{row.target.name}' row gives its asset the digest {digest.hex} and embeds a build record for {build.sha256.hex}. These are not the bytes that leg built and smoke-tested." },
       { held := build.commit == description.commit,
         failure := s!"the '{row.target.name}' leg records commit {build.commit.hex}, and this release is {description.commit.hex}. The legs this manifest describes did not all build the same source." },
       { held := build.toolchain == description.toolchain,
         failure := s!"the '{row.target.name}' leg built with toolchain '{build.toolchain}', and this release records '{description.toolchain}'. The artifacts this manifest describes do not all come from the pinned toolchain." },
       { held := build.lakeManifestSha256 == description.lakeManifestSha256,
         failure := s!"the '{row.target.name}' leg recorded a lake-manifest digest of {build.lakeManifestSha256.hex}, and this release records {description.lakeManifestSha256.hex}. The legs did not all build against the same dependency set." }]

/-- Every way the document can contradict itself, each with what to say. -/
def descriptionChecks (description : ManifestDescription) : List Check :=
  [{ held := description.schemaVersion == manifestSchemaVersion,
     failure := s!"declares schema version {description.schemaVersion}, and this build reads version {manifestSchemaVersion}. A schema is bumped exactly when a consumer would have to change, so reading this one anyway would be acting on a document whose meaning is not the one this code implements." },
   { held := description.product == "tl",
     failure := s!"describes the product '{description.product}'. This is tl's release machinery and it has no way to publish anything else; a manifest for another product reaching here is a wrong file rather than a wider capability." },
   { held := description.tag == description.version.tag,
     failure := s!"records the tag '{description.tag}' and the version '{description.version.render}', whose tag is '{description.version.tag}'. Every url a channel composes takes the tag and every version a channel claims takes the version, so a document that disagrees with itself here publishes a package pointing at a release that does not exist." },
   { held := !description.targets.isEmpty,
     failure := "lists no targets. Every per-target comparison below would then hold by having nothing to compare, and a channel would project a release that builds nothing." },
   uniqueNamesCheck (description.targets.map (·.target.name)) fun name =>
     s!"lists the target '{name}' twice. Every lookup takes the first match, so which row applies would depend on document order — and if the two disagree about the tier they disagree about whether this release is complete.",
   { held := !description.assets.isEmpty,
     failure := "describes no assets. A manifest with an empty asset table would accept any directory at all, including an empty one, so it is refused rather than satisfied." },
   uniqueNamesCheck (description.assets.map (·.name)) fun name =>
     s!"describes '{name}' twice. Verification looks each name up once, so which digest applies would depend on row order — and two rows naming one file disagree about it, or one of them is redundant.",
   { held := description.npm.distTag == npmDistTagFor description.version,
     failure := s!"records the npm dist-tag '{description.npm.distTag}' for version {description.version.render}, whose tag is '{npmDistTagFor description.version}'. A prerelease published as 'latest' is what `npm install tl` resolves to for everyone, and npm versions cannot be withdrawn." },
   { held := description.npm.packages == npmPackagesFor (description.npm.packages.headD "")
       description.publishedTargets,
     failure := s!"records an npm package list that does not follow from the targets it published. It must be the launcher package followed by one platform package per published target, in target order: {String.intercalate ", " (npmPackagesFor (description.npm.packages.headD "<none>") description.publishedTargets)}. A package published from a list that disagrees with the target rows either points at a binary this release does not have, or omits a platform it does." },
   { held := description.homebrew.push == !description.version.isPrerelease,
     failure := s!"records homebrew push {description.homebrew.push} for version {description.version.render}. A tap carries one formula, so pushing a prerelease makes `brew install tl` resolve to it (ADR-0006); the decision follows from the version and this document states a different one." },
   { held := description.homebrew.pinnedTargets == description.publishedTargets,
     failure := s!"pins the Homebrew targets [{String.intercalate ", " description.homebrew.pinnedTargets}] while publishing [{String.intercalate ", " description.publishedTargets}]. The formula refuses to install on a platform outside that list, so a document that disagrees with itself here either refuses a platform this release serves or promises one it does not." }]
  ++ description.targets.flatMap (targetRowChecks description)

/-- Whether the document agrees with itself. -/
def descriptionCoherent (description : ManifestDescription) : Bool :=
  Check.allHeld (descriptionChecks description)

/-- Why it does not, or nothing at all. -/
def descriptionProblems (description : ManifestDescription) : List String :=
  Check.failures (descriptionChecks description)

/-- What a published target row asserts about the rest of the document. -/
def ManifestTarget.coherentWith (description : ManifestDescription) (row : ManifestTarget) : Prop :=
  match row.outcome with
  | .absent => True
  | .published asset digest build =>
      asset = assetNameFor row.target.name
        ∧ (description.assets.find? (·.name == asset)).map (·.sha256) = some digest
        ∧ build.target = row.target.name
        ∧ build.tier = row.target.tier
        ∧ build.sha256 = digest
        ∧ build.commit = description.commit
        ∧ build.toolchain = description.toolchain
        ∧ build.lakeManifestSha256 = description.lakeManifestSha256

/-- Everything the document asserts about itself, other than per target. -/
def ManifestDescription.selfConsistent (description : ManifestDescription) : Prop :=
  description.schemaVersion = manifestSchemaVersion
    ∧ description.product = "tl"
    ∧ description.tag = description.version.tag
    ∧ description.targets ≠ []
    ∧ (repeatedName (description.targets.map (·.target.name))).isNone = true
    ∧ description.assets ≠ []
    ∧ (repeatedName (description.assets.map (·.name))).isNone = true
    ∧ description.npm.distTag = npmDistTagFor description.version
    ∧ description.npm.packages
        = npmPackagesFor (description.npm.packages.headD "") description.publishedTargets
    ∧ description.homebrew.push = !description.version.isPrerelease
    ∧ description.homebrew.pinnedTargets = description.publishedTargets

/-- A list with something in it is not the empty list. Stated once because four
    rows above are "this section is populated" and the `Bool`/`Prop` step is the
    same each time. -/
private theorem not_isEmpty_iff {α : Type} (items : List α) :
    (!items.isEmpty) = true ↔ items ≠ [] := by
  match items with
  | [] =>
      constructor
      · intro absurdity; exact Bool.noConfusion absurdity
      · intro empty; exact absurd rfl empty
  | head :: rest =>
      constructor
      · intro _; exact List.cons_ne_nil head rest
      · intro _; rfl

/-- Every check produced by expanding each element into a list holds exactly
    when the property each list encodes holds of every element.

    The companion of `all_mapped_held_iff` for the rows that contribute more
    than one comparison. Proved by induction rather than by a `simp` set so the
    step it takes is visible: one element's checks and the rest's are an
    append, and `List.all_append` splits it. -/
private theorem all_flatMapped_held_iff {α : Type} (build : α → List Check) (items : List α)
    (property : α → Prop)
    (encodes : ∀ item, (build item).all (·.held) = true ↔ property item) :
    (items.flatMap build).all (·.held) = true ↔ ∀ item ∈ items, property item := by
  induction items with
  | nil =>
      constructor
      · intro _ item member; exact absurd member (List.not_mem_nil)
      · intro _; rfl
  | cons head rest step =>
      rw [List.flatMap_cons, List.all_append, Bool.and_eq_true, encodes head, step]
      constructor
      · rintro ⟨headHolds, restHolds⟩ item member
        match List.mem_cons.mp member with
        | .inl isHead => rw [isHead]; exact headHolds
        | .inr inRest => exact restHolds item inRest
      · intro every
        exact ⟨every head List.mem_cons_self,
          fun item member => every item (List.mem_cons_of_mem head member)⟩

private theorem targetRowChecks_held_iff (description : ManifestDescription)
    (row : ManifestTarget) :
    (targetRowChecks description row).all (·.held) = true ↔ row.coherentWith description := by
  rw [targetRowChecks, ManifestTarget.coherentWith]
  match row.outcome with
  | .absent =>
      constructor
      · intro _; trivial
      · intro _; rfl
  | .published _ _ _ =>
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]

/-- **A manifest is accepted exactly when every statement it makes twice it
    makes the same way both times.**

    Left to right is what keeps the row list from silently shrinking: dropping
    any row makes the verdict strictly more accepting, so a document violating
    the dropped row would satisfy the left side and fail the right, and this
    implication would stop compiling. That is the failure worth guarding here,
    because a manifest that passes is one three channels then publish from
    without looking again.

    Right to left is what a verdict that accepts nothing cannot satisfy, and it
    is not hypothetical: the checks are quantified over the target rows, so a
    reader that refused every document — or one that mistakenly required an
    unpublished row to carry a build record — would prove soundness trivially
    and fail here. -/
theorem descriptionCoherent_iff (description : ManifestDescription) :
    descriptionCoherent description = true ↔
      description.selfConsistent ∧ ∀ row ∈ description.targets, row.coherentWith description := by
  rw [descriptionCoherent, Check.allHeld, descriptionChecks, List.all_append, Bool.and_eq_true,
    all_flatMapped_held_iff _ _ _ (targetRowChecks_held_iff description),
    ManifestDescription.selfConsistent]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    not_isEmpty_iff, uniqueNamesCheck]

/-- **The report is empty exactly when the document agrees with itself.**

    `descriptionCoherent_iff` characterises the verdict; the parser branches on
    the report, so without this the theorem would be about a function nothing
    reaches. -/
theorem descriptionProblems_isEmpty_iff (description : ManifestDescription) :
    descriptionProblems description = [] ↔
      description.selfConsistent ∧ ∀ row ∈ description.targets, row.coherentWith description :=
  Iff.trans (Check.allHeld_iff_noFailures (descriptionChecks description)).symm
    (descriptionCoherent_iff description)

/-- Read a manifest whole, and refuse one that contradicts itself.

    Structure first, then agreement. A field of the wrong type is reported where
    it is, naming the path, because that is a document someone can fix; a
    document that parses and disagrees with itself is reported as every
    disagreement at once, because fixing one of them a release at a time is not
    a thing anyone should do to a signed artifact set. -/
def ManifestDescription.parse (document : String) (text : String) :
    Except String ManifestDescription := do
  let cursor : Cursor := { document }
  let root ← parseDocument cursor text
  let (targetsCursor, targetsFound) ← field cursor root "targets"
  let targetRows ← asArray targetsCursor targetsFound
  let (assetsCursor, assetsFound) ← field cursor root "assets"
  let assetRows ← asArray assetsCursor assetsFound
  let description : ManifestDescription := {
    schemaVersion := ← natField cursor root "schemaVersion"
    product := ← nonEmptyStringField cursor root "product"
    version := ← Version.parse (cursor.at "version").render
      (← nonEmptyStringField cursor root "version")
    tag := ← nonEmptyStringField cursor root "tag"
    commit := ← Commit.parse (cursor.at "commit").render
      (← nonEmptyStringField cursor root "commit")
    repository := ← nonEmptyStringField cursor root "repository"
    toolchain := ← nonEmptyStringField cursor root "toolchain"
    lakeManifestSha256 := ← Sha256.parse (cursor.at "lakeManifestSha256").render
      (← nonEmptyStringField cursor root "lakeManifestSha256")
    signing := ← parseSigning cursor root
    targets := ← targetRows.mapM fun (rowCursor, row) => parseTargetRow rowCursor row
    assets := ← assetRows.mapM fun (rowCursor, row) => parseAsset rowCursor row
    npm := ← parseNpmPlan cursor root
    homebrew := ← parseHomebrewPlan cursor root }
  match descriptionProblems description with
  | [] => return description
  | problems =>
      .error (s!"{document}: this manifest contradicts itself, so nothing may be published from it.\n"
        ++ String.join (problems.map fun problem => s!"  it {problem}\n")
        ++ "The manifest is signed alongside SHA256SUMS. A document that disagrees with itself was either assembled by a build this one cannot read, or edited after signing; regenerate it from the release rather than reconciling it by hand.")

/-! ## Collecting the evidence

The I/O half. Walking, typing, reading and hashing; no decisions except the
ones a filesystem forces — this is not a directory, this entry is not a regular
file, this file could not be read. Everything else is handed to the pure layer
above as a value. -/

/-- Every regular file in the release directory.

    A non-regular entry is a refusal rather than something to skip, which is
    the opposite of what the Python did. A release directory holds the bytes it
    publishes: a symbolic link would be described in the manifest by the digest
    of whatever it points at while what a consumer receives is the link, and a
    subdirectory means the download step flattened less than it was asked to.
    Skipping either leaves something in the directory that the manifest does not
    account for, which is exactly what `manifest-verify` exists to catch — one
    step too late to be useful. -/
def collectNames (directory : String) : IO (Except String (List String)) := do
  if !(← System.FilePath.isDir directory) then
    return .error s!"'{directory}' is not a directory."
  match ← (System.FilePath.readDir directory).toBaseIO with
  | .error error => return .error s!"'{directory}' could not be listed ({error})."
  | .ok entries =>
      let mut names : Array String := #[]
      for entry in entries do
        match ← unhashableReason (directory ++ "/" ++ entry.fileName) with
        | some reason =>
            return .error s!"{reason} A release directory holds the files it publishes and nothing else; the manifest describes every one of them, so an entry that is not a file cannot be described and must not simply be left out."
        | none => names := names.push entry.fileName
      return .ok names.toList

/-- The files this release describes: everything present except the three
    things a manifest structurally cannot describe.

    The *same* predicate `manifest-verify` uses to decide what may be present
    and undescribed. One definition, deliberately: written twice, a file
    omitted here and not allowed there would be generated into a release and
    then reported as an extra asset by the job that verifies it — a release
    that refuses itself. -/
def describableNames (manifestName : String) (names : List String) : List String :=
  -- Bundles are excluded by suffix here and admitted by subject there, and the
  -- two agree: this runs before anything is signed, so no bundle exists yet,
  -- and one that did would be named for something about to be described or for
  -- one of the two files that cannot be.
  names.filter fun name =>
    !((structurallyUndescribable manifestName).contains name || name.endsWith ".sigstore.json")

/-- One target's evidence, from files already listed and hashed.

    The digests are looked up rather than recomputed: every describable file has
    been hashed once already, and the binary is the largest thing in the
    directory. -/
private def artifactEvidence (directory : String) (names : List String)
    (digests : List (String × Sha256)) (target : Target) :
    IO (Except String ArtifactEvidence) := do
  match digests.lookup target.asset with
  | none => return .ok .absent
  | some digest =>
      let metadataName := target.buildMetadataAsset
      if !names.contains metadataName then
        return .ok (.present digest none (names.contains target.linkAuditAsset))
      match ← readTextFile (directory ++ "/" ++ metadataName) with
      | .error message => return .error message
      | .ok text =>
          match BuildMetadata.parse metadataName text with
          | .error message => return .error message
          | .ok build =>
              return .ok (.present digest (some build) (names.contains target.linkAuditAsset))

/-! ## The commands -/

private def runContextOptions : List OptionSpec :=
  [{ name := "workflow-ref", takesValue := true },
   { name := "run-id", takesValue := true },
   { name := "outside-workflow", takesValue := false }]

/-- Which run this release is being cut by, said out loud.

    There is no default. An unset environment variable used to disable the
    workflow-ref comparison silently, so the choice is now one a caller makes
    and is seen to have made: either both halves of the run identity, or an
    explicit statement that there is no run. -/
def runContextOf (options : Options) : Except String RunContext :=
  match options.value? "workflow-ref", options.value? "run-id",
        options.given "outside-workflow" with
  | some workflowRef, some runId, false => .ok (.inWorkflow workflowRef runId)
  | none, none, true => .ok .outsideWorkflow
  | _, _, true =>
      .error "--outside-workflow was given together with --workflow-ref or --run-id. They are the two answers to one question; passing both leaves it open which one this run is."
  | some _, none, false =>
      .error "--workflow-ref was given without --run-id. Half a run identity is not one: the workflow would be compared and the run within it would not, so a leg from an earlier run of this same workflow would pass. Pass both, or --outside-workflow."
  | none, some _, false =>
      .error "--run-id was given without --workflow-ref. Half a run identity is not one: run ids are per workflow, so a leg produced by a different workflow that happened to reach the same id would pass. Pass both, or --outside-workflow."
  | none, none, false =>
      .error "the run this release is being cut by was not given. Pass --workflow-ref and --run-id together, so every build leg's record can be held to this run, or --outside-workflow to state that there is no run to hold them to. There is no default: an absent run identity used to disable the comparison rather than fail it, which is why every leg agreeing with every other leg was the only thing left being checked."

private def manifestOptions : List OptionSpec :=
  [{ name := "dist", takesValue := true },
   { name := "tag", takesValue := true },
   { name := "commit", takesValue := true },
   { name := "toolchain", takesValue := true },
   { name := "lake-manifest", takesValue := true },
   { name := "targets", takesValue := true },
   { name := "identity", takesValue := true },
   outputOption, outputDirectoryOption] ++ runContextOptions

/-- The basename of a path, for the one thing the manifest cannot describe:
    itself.

    `getLastD` rather than `getLast!`: `splitOn` never returns an empty list, so
    the fallback is unreachable — but a panicking projection in a release tool
    is a way for a decision to become a crash, and this executable's contract is
    that every path ends in a decision. -/
private def baseName (path : String) : String :=
  let segments := path.splitOn "/"
  segments.getLastD path

/-- Everything `manifest` was told, with the option names resolved. -/
private structure ManifestArgs where
  dist : String
  tag : String
  commit : String
  toolchainPath : String
  lakeManifestPath : String
  targetsPath : String
  identityPath : String
  base : Write.OutputDirectory
  output : Write.OutputPath
  run : RunContext

private def manifestArgs (options : Options) : Except String ManifestArgs := do
  let (base, output) ← resolveOutput options
  return {
    dist := ← options.required "dist"
    tag := ← options.required "tag"
    commit := ← options.required "commit"
    toolchainPath := ← options.required "toolchain"
    lakeManifestPath := ← options.required "lake-manifest"
    targetsPath := ← options.required "targets"
    identityPath := ← options.required "identity"
    base, output
    run := ← runContextOf options }

private def manifestDecision (args : ManifestArgs) : Decision String := do
  let version ← ofExcept (Version.parseTag "--tag" args.tag)
  let commit ← ofExcept (Commit.parse "--commit" args.commit)
  let toolchain ← readParsed args.toolchainPath parseToolchain
  let targets ← readParsed args.targetsPath Targets.parse
  let identity ← readParsed args.identityPath Identity.parse
  let names ← ofIO (collectNames args.dist)
  let digester ← ofIO Digester.resolve
  let lakeManifestSha256 ← ofIO (digester.digest args.lakeManifestPath)
  let facts : ReleaseFacts := { commit, toolchain, lakeManifestSha256, run := args.run }
  -- Every describable file, hashed exactly once and carried. The Python hashed
  -- each binary three times: once against its leg's record, once for its target
  -- row, once for its asset row.
  let describable := describableNames args.output.leaf.text names
  let digests ← ofIO (do
    let mut collected : Array (String × Sha256) := #[]
    for name in describable do
      match ← digester.digest (args.dist ++ "/" ++ name) with
      | .error message => return .error message
      | .ok digest => collected := collected.push (name, digest)
    return .ok collected.toList)
  let evidence ← ofIO (do
    let mut rows : Array TargetEvidence := #[]
    for target in targets.targets do
      match ← artifactEvidence args.dist names digests target with
      | .error message => return .error message
      | .ok found => rows := rows.push { target, found }
    return .ok rows.toList)
  let manifest ← ofExcept (Manifest.of {
    version, facts, identity, targets, evidence, directory := digests })
  let document ← ofExcept (renderManifest manifest)
  let disclosure ← ofIO (writeEvidence args.base args.output document)
  let published := manifest.publishedTargets.length
  return disclosing
    s!"wrote {args.output.render} in {args.base.path} — {manifest.assets.length} assets, {published} of {manifest.outcomes.length} targets published"
    disclosure

private def manifestCommand : Command :=
  optionCommand "manifest" "--dist <dir> --tag <vX.Y.Z> --commit <sha> …"
    "Describe this release once, for every job downstream of signing to read instead of re-deriving it."
    ["--dist", "dist", "--tag", "v0.1.0", "--commit", "0123456789abcdef0123456789abcdef01234567",
     "--toolchain", "lean-toolchain", "--lake-manifest", "lake-manifest.json",
     "--targets", "release/targets.json", "--identity", "release/identity.json",
     "--output", "release-manifest.json", "--output-dir", "dist", "--outside-workflow"]
    manifestOptions manifestArgs manifestDecision
    (usageArguments :=
      "--dist <dir> --tag <vX.Y.Z> --commit <sha> --toolchain <lean-toolchain> --lake-manifest <lake-manifest.json> --targets <targets.json> --identity <identity.json> --output <name> [--output-dir <dir>] (--workflow-ref <ref> --run-id <id> | --outside-workflow)")

private def verifyOptions : List OptionSpec :=
  [{ name := "dist", takesValue := true },
   { name := "manifest", takesValue := true }]

private structure VerifyArgs where
  dist : String
  manifestPath : String

private def verifyArgs (options : Options) : Except String VerifyArgs := do
  return { dist := ← options.required "dist", manifestPath := ← options.required "manifest" }

private def verifyDecision (args : VerifyArgs) : Decision String := do
  let description ← readParsed args.manifestPath ManifestDescription.parse
  let names ← ofIO (collectNames args.dist)
  let manifestName := baseName args.manifestPath
  let digester ← ofIO Digester.resolve
  -- Only the files the manifest describes are hashed. An undescribed one is
  -- refused for its name, and reading a large file to establish something its
  -- name has already established is work for nothing.
  let digests ← ofIO (do
    let mut collected : Array (String × Sha256) := #[]
    for asset in description.assets do
      if names.contains asset.name then
        match ← digester.digest (args.dist ++ "/" ++ asset.name) with
        | .error message => return .error message
        | .ok digest => collected := collected.push (asset.name, digest)
    return .ok collected.toList)
  let evidence : DirectoryEvidence := { names, digests }
  match manifestFailures args.dist manifestName description.assets evidence with
  | [] =>
      return s!"{args.dist} matches the manifest for {description.tag} ({description.assets.length} assets)"
  | failures =>
      decline (s!"{args.dist} does not match the manifest.\n"
        ++ String.join (failures.map fun failure => s!"  {failure}\n")
        ++ "The manifest is signed alongside SHA256SUMS, so a mismatch means either the wrong directory or a modified one. Do not publish it.")

private def verifyCommand : Command :=
  optionCommand "manifest-verify" "--dist <dir> --manifest <path>"
    "Refuse unless the directory holds exactly what the manifest describes, with the digests it names."
    ["--dist", "dist", "--manifest", "dist/release-manifest.json"]
    verifyOptions verifyArgs verifyDecision

def manifestCommands : List Command := [manifestCommand, verifyCommand]

end Release
