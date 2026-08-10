/-
What a release *is*, as types.

The organising rule is the project's third principle: make illegal states
unrepresentable. Each type below exists because the shell had a way to hold a
value that should not exist, and held it silently.

- `Sha256` and `Commit` are opaque: their constructors are private and the only
  way in is a parser. The shell compared uppercase hex against lowercase output
  and read a valid sums file as tampering, and accepted a digest of the wrong
  length because nothing checked one.
- `Version` carries a parsed SemVer, so "is this a prerelease" is a field
  rather than a search for `-` in a string — which is how a prerelease reached
  the `latest` dist tag.
- `PublishedTarget` carries its build metadata by construction. The shell
  modelled this as an optional field on a target and then checked the option in
  nine places, one of which could be skipped by an empty target list.
- `ChannelStatus` makes `enabled` and `plannedFor` exclusive, so a channel
  cannot be both live and deferred.
- `AuditOutcome` separates *missing* from *could not check*. Collapsing those
  two is the defect that would abort a legitimate release by telling the
  operator to fix something already correct.

Parsers return `Except String`; only validated values reach a decision
function. Nothing here does I/O, so every function in this module is total and
testable without a filesystem.
-/
import release.Json

namespace Release

open Lean (Json)

/-! ## Digests and commits -/

private def isLowerHex (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

private def allLowerHex (text : String) : Bool := text.toList.all isLowerHex

/-- A SHA-256 digest: exactly 64 lowercase hex characters.

    No `Inhabited`, deliberately. Deriving it manufactures `⟨""⟩` — a value
    this type's own parser refuses — and hands it out through every `getD`,
    `Array.get!` and `default` in reach, which is precisely the "malformed text
    cannot inhabit this type" property the private constructor exists to give.
    An opaque type with a derived default is not opaque. -/
structure Sha256 where
  private mk ::
  hex : String
  deriving DecidableEq, Repr

/-- Lowercase is the canonical form and the only accepted one, deliberately.
    Case-folding on the way in would re-admit the confusion this type exists to
    remove: every producer in this pipeline emits lowercase, so uppercase means
    the value came from somewhere unexpected, and that is worth a refusal
    rather than a silent normalisation. -/
def Sha256.parse (what : String) (text : String) : Except String Sha256 :=
  if text.length != 64 then
    .error s!"{what}: '{text}' is not a SHA-256 digest — it is {text.length} characters, and a SHA-256 digest is 64."
  else if !allLowerHex text then
    .error s!"{what}: '{text}' is not a SHA-256 digest — it must be lowercase hexadecimal. Uppercase is refused rather than folded: every producer here emits lowercase, so uppercase means the value came from somewhere this pipeline does not control."
  else .ok ⟨text⟩

/-- A full git object id: 40 lowercase hex characters. Abbreviated ids are
    refused — an artifact set has to agree on the whole commit, and a prefix
    can become ambiguous later in the repository's life. -/
structure Commit where
  private mk ::
  hex : String
  deriving DecidableEq, Repr

def Commit.parse (what : String) (text : String) : Except String Commit :=
  if text.length != 40 then
    .error s!"{what}: '{text}' is not a full git object id — it is {text.length} characters, and a full object id is 40. An abbreviation is refused; the artifacts must agree on the whole commit."
  else if !allLowerHex text then
    .error s!"{what}: '{text}' is not a full git object id — it must be lowercase hexadecimal."
  else .ok ⟨text⟩

/-! ## Versions and tags -/

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def isAlphanumeric (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- A numeric SemVer component: digits, and no leading zero unless it is `0`.
    The pinned certificate identity accepts no other shape, so a tag like
    `v01.2.3` produces artifacts nothing could verify. -/
private def parseNumeric (what : String) (text : String) : Except String Nat :=
  if text.isEmpty then .error s!"{what}: a version component is empty."
  else if !text.toList.all isDigit then
    .error s!"{what}: '{text}' is not a number."
  else if text.length > 1 && text.startsWith "0" then
    .error s!"{what}: '{text}' has a leading zero, which SemVer does not allow."
  else .ok (text.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0)

/-- The prerelease suffix, held as its raw text rather than a list of
    identifiers so that rendering is exactly what was parsed. The accepted
    shape is alphanumeric runs separated by `.` or `-`, matching the pinned
    certificate expression — which is what makes `v1.2.3-rc-1` legal here even
    though strict SemVer would read it differently. -/
private def validPrerelease (text : String) : Bool :=
  let parts := (text.splitOn ".").flatMap (·.splitOn "-")
  !parts.isEmpty && parts.all fun part => !part.isEmpty && part.toList.all isAlphanumeric

/-- A release version. `prerelease` being a field, rather than something
    recomputed from the string, is what stops a prerelease from being treated
    as a stable release by one consumer and not another. -/
structure Version where
  private mk ::
  major : Nat
  minor : Nat
  patch : Nat
  prerelease : Option String
  deriving DecidableEq, Repr

def Version.isPrerelease (version : Version) : Bool := version.prerelease.isSome

def Version.render (version : Version) : String :=
  let core := s!"{version.major}.{version.minor}.{version.patch}"
  match version.prerelease with
  | none => core
  | some suffix => core ++ "-" ++ suffix

/-- The tag form, which is the version with a leading `v`. -/
def Version.tag (version : Version) : String := "v" ++ version.render

private def semverShape : String :=
  "vMAJOR.MINOR.PATCH with no leading zeroes, optionally followed by a -prerelease suffix of alphanumeric parts separated by '.' or '-'"

/-- Parse a version with no leading `v`. Build metadata (`+…`) is refused: the
    pinned certificate identity does not accept it, so a tag carrying one would
    build artifacts that could not be signed with an identity any verifier
    accepts. -/
def Version.parse (what : String) (text : String) : Except String Version := do
  if text.any (· == '+') then
    .error s!"{what}: '{text}' carries SemVer build metadata, which the pinned signing identity does not accept. Nothing built from it could be signed."
  let (core, prerelease) :=
    match text.splitOn "-" with
    | [] => (text, none)
    | [only] => (only, none)
    | first :: rest => (first, some (String.intercalate "-" rest))
  match core.splitOn "." with
  | [major, minor, patch] =>
      let major ← parseNumeric what major
      let minor ← parseNumeric what minor
      let patch ← parseNumeric what patch
      match prerelease with
      | none => return ⟨major, minor, patch, none⟩
      | some suffix =>
          if !validPrerelease suffix then
            .error s!"{what}: '{text}' has a prerelease suffix this pipeline does not accept. Expected {semverShape}."
          else return ⟨major, minor, patch, some suffix⟩
  | _ =>
      .error s!"{what}: '{text}' is not a release version. Expected {semverShape}."

/-- Parse a tag, which must carry the leading `v`. -/
def Version.parseTag (what : String) (text : String) : Except String Version :=
  if !text.startsWith "v" then
    .error s!"{what}: '{text}' is not a release tag — it does not begin with 'v'. Expected {semverShape}."
  else Version.parse what (text.drop 1 |>.toString)

/-! ## Targets and tiers -/

/-- ADR-0006's two support tiers. A Supported target is release-blocking; a
    Best-effort one is built and smoke-tested, and its absence is a recorded
    outcome rather than a failure — so every consumer needs a defined behaviour
    for it, which an enumeration forces and a string does not. -/
inductive Tier where
  | supported
  | bestEffort
  deriving DecidableEq, Repr, Inhabited

def Tier.wire : Tier → String
  | .supported => "supported"
  | .bestEffort => "best-effort"

def Tier.parse (what : String) (text : String) : Except String Tier :=
  if text == "supported" then .ok .supported
  else if text == "best-effort" then .ok .bestEffort
  else .error s!"{what}: '{text}' is not a support tier. release/targets.json uses 'supported' or 'best-effort'."

def Tier.releaseBlocking : Tier → Bool
  | .supported => true
  | .bestEffort => false

/-- One distributed target. `name` is stored bare — `linux-x64`, not the asset
    name — because the asset prefix followed by a target reads as a tracker id
    to the task-ID lint. Every consumer composes the asset name through
    `Target.asset`, which is also why that prefix appears in exactly one
    place. -/
structure Target where
  name : String
  tier : Tier
  os : String
  cpu : String
  libc : Option String
  deriving Repr, Inhabited

/-- The published asset name for a target. The one site that knows how an
    asset name is spelled. -/
def Target.asset (target : Target) : String := "tl-" ++ target.name

def Target.buildMetadataAsset (target : Target) : String :=
  "build-metadata-" ++ target.name ++ ".json"

def Target.linkAuditAsset (target : Target) : String :=
  "link-audit-" ++ target.name ++ ".txt"

def parseTarget (cursor : Cursor) (value : Json) : Except String Target := do
  let name ← nonEmptyStringField cursor value "target"
  let tier ← Tier.parse (cursor.at "tier").render (← stringField cursor value "tier")
  let os ← nonEmptyStringField cursor value "os"
  let cpu ← nonEmptyStringField cursor value "cpu"
  -- Optional, but not optional-or-whatever: absent is a target with no libc
  -- floor, and present-but-not-a-string is a malformed file. Reading the
  -- second as the first is the absent/malformed conflation this whole module
  -- exists to remove, and it was the one field here still doing it.
  let libc ← match field? value "libc" with
    | none => pure none
    | some found => do
        let text ← asString (cursor.at "libc") found
        pure (some text)
  return { name, tier, os, cpu, libc }

/-- The distributed target set, in file order. Order is part of the contract:
    the manifest lists Supported targets before Best-effort ones, and a
    consumer that re-derived the order would produce a different document for
    the same release. -/
structure Targets where
  targets : List Target
  deriving Inhabited

def Targets.parse (document : String) (text : String) : Except String Targets := do
  let cursor : Cursor := { document }
  let root ← parseDocument cursor text
  let (inner, found) ← field cursor root "targets"
  let rows ← asArray inner found
  let targets ← rows.mapM fun (rowCursor, row) => parseTarget rowCursor row
  if targets.isEmpty then
    inner.fail "lists no targets. A release with no targets is not a smaller release, it is a release that builds nothing — the empty list is refused rather than carried."
  return { targets }

def Targets.ofTier (targets : Targets) (tier : Tier) : List Target :=
  targets.targets.filter (·.tier == tier)

def Targets.find? (targets : Targets) (name : String) : Option Target :=
  targets.targets.find? (·.name == name)

/-! ## Channels and the release plan -/

/-- The four ADR-0006 channels. Closed, so a plan naming a channel nothing
    implements is refused at the boundary rather than silently ignored. -/
inductive Channel where
  | githubRelease
  | installer
  | npm
  | homebrew
  deriving DecidableEq, Repr, Inhabited

def Channel.wire : Channel → String
  | .githubRelease => "github-release"
  | .installer => "installer"
  | .npm => "npm"
  | .homebrew => "homebrew"

def Channel.all : List Channel := [.githubRelease, .installer, .npm, .homebrew]

def Channel.parse (what : String) (text : String) : Except String Channel :=
  match Channel.all.find? (fun channel => channel.wire == text) with
  | some channel => .ok channel
  | none =>
      .error s!"{what}: '{text}' is not a distribution channel. ADR-0006 defines {String.intercalate ", " (Channel.all.map Channel.wire)}."

/-- Enabled, or deferred to a named release. Exclusive by construction: an
    enabled channel has no future version to name, and a deferred one must name
    the release it is planned for, so deferral cannot quietly become
    abandonment. -/
inductive ChannelStatus where
  | enabled
  | deferred (plannedFor : String)
  deriving DecidableEq, Repr, Inhabited

def ChannelStatus.isEnabled : ChannelStatus → Bool
  | .enabled => true
  | .deferred _ => false

structure ChannelRow where
  channel : Channel
  status : ChannelStatus
  deriving Repr, Inhabited

/-- Which channels this release publishes through. Every channel has exactly
    one row, checked on parse: a plan that simply omitted a channel would make
    "disabled" and "forgotten" the same state, and this file is what the
    prerequisites, the workflow jobs and the release policy are derived from. -/
structure ReleasePlan where
  private mk ::
  rows : List ChannelRow

def ReleasePlan.status (plan : ReleasePlan) (channel : Channel) : ChannelStatus :=
  match plan.rows.find? (·.channel == channel) with
  | some row => row.status
  -- Unreachable for a parsed plan: `ReleasePlan.parse` refuses one whose rows
  -- do not cover every channel, `mk` is private, and there is no `Inhabited`
  -- instance to manufacture a rowless plan through a `default`. Deferred is
  -- the fail-closed answer if that ever stops being true — an unknown channel
  -- is one nothing should publish through.
  | none => .deferred "unknown"

def ReleasePlan.enabled (plan : ReleasePlan) (channel : Channel) : Bool :=
  (plan.status channel).isEnabled

def ReleasePlan.enabledChannels (plan : ReleasePlan) : List Channel :=
  Channel.all.filter plan.enabled

private def parseChannelRow (cursor : Cursor) (value : Json) : Except String ChannelRow := do
  let channelText ← stringField cursor value "channel"
  let channel ← Channel.parse (cursor.at "channel").render channelText
  let (enabledCursor, enabledValue) ← field cursor value "enabled"
  let enabled ← asBool enabledCursor enabledValue
  let plannedFor := field? value "plannedFor"
  match enabled, plannedFor with
  | true, none => return { channel, status := .enabled }
  | true, some _ =>
      cursor.fail s!"has channel '{channelText}' both enabled and carrying plannedFor. An enabled channel is being published now and has no future release to name; drop plannedFor, or set enabled to false."
  | false, none =>
      cursor.fail s!"has channel '{channelText}' disabled with no plannedFor. A deferred channel must name the release it is planned for, so deferral cannot decay into abandonment; add plannedFor, or enable the channel."
  | false, some planned =>
      match planned.getStr? with
      | .ok text =>
          if text.isEmpty then
            cursor.fail s!"has channel '{channelText}' deferred to an empty release. Name the release it is planned for."
          else return { channel, status := .deferred text }
      | .error _ => (cursor.at "plannedFor").fail "is not a string."

def ReleasePlan.parse (document : String) (text : String) : Except String ReleasePlan := do
  let cursor : Cursor := { document }
  let root ← parseDocument cursor text
  let (inner, found) ← field cursor root "channels"
  let entries ← asArray inner found
  let rows ← entries.mapM fun (rowCursor, row) => parseChannelRow rowCursor row
  -- Every channel exactly once. Missing would conflate "disabled" with
  -- "forgotten"; duplicated would make the answer depend on lookup order.
  for channel in Channel.all do
    let matching := rows.filter (·.channel == channel)
    if matching.isEmpty then
      inner.fail s!"has no row for the '{channel.wire}' channel. Every channel needs a row, so that a channel nobody edited is deliberately off rather than merely absent."
    if matching.length > 1 then
      inner.fail s!"has {matching.length} rows for the '{channel.wire}' channel. Keep one row per channel; with two, which one applies depends on lookup order."
  return ⟨rows⟩

/-! ## The signing identity -/

structure Identity where
  repository : String
  npmPackage : String
  releaseWorkflow : String
  certificateOidcIssuer : String
  certificateIdentityRegexp : String
  deriving Repr, Inhabited

/-- The owner half of `owner/name`, which is the Homebrew tap's namespace. -/
def Identity.owner (identity : Identity) : String :=
  (identity.repository.splitOn "/").headD identity.repository

def Identity.parse (document : String) (text : String) : Except String Identity := do
  let cursor : Cursor := { document }
  let root ← parseDocument cursor text
  return {
    repository := ← nonEmptyStringField cursor root "repository"
    npmPackage := ← nonEmptyStringField cursor root "npmPackage"
    releaseWorkflow := ← nonEmptyStringField cursor root "releaseWorkflow"
    certificateOidcIssuer := ← nonEmptyStringField cursor root "certificateOidcIssuer"
    certificateIdentityRegexp := ← nonEmptyStringField cursor root "certificateIdentityRegexp" }

/-! ## What a build leg recorded -/

/-- One leg's record of what it built. Every field is required and non-empty:
    the shell tested these with `not build.get(field)`, which cannot tell an
    absent field from `""`, `0` or `false`, so a record hollowed out in any of
    those ways produced the same message and a record hollowed out in a way
    that happened to be truthy produced none.

    `runnerOs`, `runnerArch`, `containerImage` and `runAttempt` are recorded
    for a reader and deliberately not validated — they describe the machine,
    not the artifact, and inventing a check for them would be a check nothing
    could fail. -/
structure BuildMetadata where
  target : String
  sha256 : Sha256
  commit : Commit
  tier : Tier
  runner : String
  toolchain : String
  lakeManifestSha256 : Sha256
  workflowRef : String
  runId : String
  runnerOs : String := ""
  runnerArch : String := ""
  containerImage : String := ""
  runAttempt : String := ""
  deriving Repr

def BuildMetadata.parse (document : String) (text : String) : Except String BuildMetadata := do
  let cursor : Cursor := { document }
  let root ← parseDocument cursor text
  let _ ← getObj cursor root
  let optional (name : String) : String :=
    ((field? root name).bind fun found => (found.getStr?).toOption).getD ""
  return {
    target := ← nonEmptyStringField cursor root "target"
    sha256 := ← Sha256.parse (cursor.at "sha256").render (← nonEmptyStringField cursor root "sha256")
    commit := ← Commit.parse (cursor.at "commit").render (← nonEmptyStringField cursor root "commit")
    tier := ← Tier.parse (cursor.at "tier").render (← nonEmptyStringField cursor root "tier")
    runner := ← nonEmptyStringField cursor root "runner"
    toolchain := ← nonEmptyStringField cursor root "toolchain"
    lakeManifestSha256 := ← Sha256.parse (cursor.at "lakeManifestSha256").render
      (← nonEmptyStringField cursor root "lakeManifestSha256")
    workflowRef := ← nonEmptyStringField cursor root "workflowRef"
    runId := ← nonEmptyStringField cursor root "runId"
    runnerOs := optional "runnerOs"
    runnerArch := optional "runnerArch"
    containerImage := optional "containerImage"
    runAttempt := optional "runAttempt" }

/-- A target that was built and will be published. It carries its digest and
    its leg's complete record *by construction*, so no consumer can reach a
    published target whose evidence was never collected — which is exactly what
    an empty target list did to the shell generator's nine checks. -/
structure PublishedTarget where
  target : Target
  digest : Sha256
  build : BuildMetadata
  deriving Repr

def PublishedTarget.asset (published : PublishedTarget) : String := published.target.asset

/-- What became of a target in this release. `absent` carries no evidence
    because there is none to carry; whether an absent target is acceptable is a
    question about its tier, answered where the decision is made. -/
inductive TargetOutcome where
  | published (details : PublishedTarget)
  | absent (target : Target)
  deriving Repr

def TargetOutcome.target : TargetOutcome → Target
  | .published details => details.target
  | .absent target => target

def TargetOutcome.published? : TargetOutcome → Option PublishedTarget
  | .published details => some details
  | .absent _ => none

/-! ## Audit outcomes -/

/-- What an audit of one external prerequisite found.

    The four cases are separate because they demand different responses, and
    the shell had only the first two. Collapsing `operationalError` into
    `missing` is the recorded defect that would abort a legitimate release with
    a remedy telling the operator to fix something already correct: "the API
    did not answer" and "the thing is not there" are not the same finding, and
    only one of them is about the repository's configuration. `carried` is an
    assumption recorded in docs/overview.md — it follows its declared policy
    but never counts as verified, because nothing checked it. -/
inductive AuditOutcome where
  | verified
  | missing (remedy : String)
  | carried (assumption : String)
  | operationalError (detail : String)
  deriving Repr, Inhabited

def AuditOutcome.label : AuditOutcome → String
  | .verified => "VERIFIED"
  | .missing _ => "MISSING"
  | .carried _ => "CARRIED"
  | .operationalError _ => "ERROR"

/-- Whether this outcome permits a release to proceed. An operational error
    does not: an audit that could not run has established nothing, and reading
    its silence as permission is the failure this whole port exists to
    prevent. -/
def AuditOutcome.permitsRelease : AuditOutcome → Bool
  | .verified => true
  | .carried _ => true
  | .missing _ => false
  | .operationalError _ => false

end Release
