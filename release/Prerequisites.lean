/-
The external state a release depends on, and which of it this release needs.

None of this lives in the repository. The `release` environment and its
reviewers, the ruleset that decides who may create a `v*` tag, whether the
repository is public at all — these are GitHub configuration, and declaring
them in a workflow file does not create them. Until this audit existed the
first tag would have published GitHub assets and then failed somewhere further
down, with the artifacts already public.

## The three distinctions this module is built around

**Missing is not unchecked.** `AuditOutcome` has separate cases and neither
permits a release, but they have opposite remedies: "create the ruleset" versus
"find out why the API would not answer". Collapsing them is the recorded defect
that aborts a legitimate release by telling the operator to create something
that already exists — and it is reachable from one 5xx on a detail call.

**Not applicable is not satisfied.** Prerequisites are derived from the typed
plan, so a release that publishes only through the GitHub Release produces no
npm rows and no tap rows *at all*. The shell audit predating this emitted five
npm rows and a tap row as MISSING on a GitHub-only release and would have
stopped the sign job for channels that release does not use.

**A property is not a proxy for it.** A count of protection rules is satisfied
by a wait timer; a count of rulesets by an unrelated branch rule. Both passed
while required reviewers and protected tag creation were absent. The predicates
below are over the structure the security model actually needs — and the tag
ruleset one has been a proxy in all three review rounds (a count, then a
prefix), which is why `coversEveryReleaseTag` asks whether the include set
covers *every* `v*` tag rather than whether one pattern looks v-ish.

## Where the boundary is

`gh` remains the GitHub API client — writing an HTTP client here would be a
much larger trusted surface than shelling out to the one the operator is
already authenticated with. What crosses back is bytes: `gh api` is asked for
raw JSON and this module parses it, rather than being asked to project fields
with `--jq`. That keeps one JSON semantics in the tool instead of two, and it
is what lets an unreadable response be *unchecked* rather than empty.
-/
import release.Command
import release.Model
import release.Process

namespace Release

open Lean (Json)

/-! ## What the audit asks about -/

/-- One thing a release depends on. Closed, because applicability is derived
    from it: an open string could name a prerequisite the plan has no opinion
    about, and "which channel is this for" would become a guess. -/
inductive PrerequisiteKind where
  | repositoryPublic
  | releaseEnvironment
  | releaseReviewers
  | deploymentPolicy
  | tagRuleset
  | npmPackages
  | npmTrustedPublishing
  | homebrewTap
  | homebrewToken
  | homebrewSigningKey
  deriving DecidableEq, Repr

/-- Which channel a prerequisite belongs to, or `none` for the ones every
    release needs whatever it publishes through.

    This is the whole of the applicability rule, in one place. Written as a
    condition at each row instead, a new channel would mean finding every row
    that mentions it. -/
def PrerequisiteKind.channel : PrerequisiteKind → Option Channel
  | .repositoryPublic | .releaseEnvironment | .releaseReviewers
  | .deploymentPolicy | .tagRuleset => none
  | .npmPackages | .npmTrustedPublishing => some .npm
  | .homebrewTap | .homebrewToken | .homebrewSigningKey => some .homebrew

/-- Whether this release needs that prerequisite at all.

    A deferred channel's rows are not run and not reported as outstanding: a
    release that publishes nothing to npm needs nothing from npm. That is a
    third state beside verified and missing, and giving it a name is what stops
    it from being spelled as either. -/
def PrerequisiteKind.applicable (plan : ReleasePlan) (kind : PrerequisiteKind) : Bool :=
  match kind.channel with
  | none => true
  | some channel => plan.enabled channel

def PrerequisiteKind.all : List PrerequisiteKind :=
  [.repositoryPublic, .releaseEnvironment, .releaseReviewers, .deploymentPolicy,
   .tagRuleset, .npmPackages, .npmTrustedPublishing, .homebrewTap, .homebrewToken,
   .homebrewSigningKey]

/-- The prerequisites this release actually depends on. -/
def applicableKinds (plan : ReleasePlan) : List PrerequisiteKind :=
  PrerequisiteKind.all.filter (·.applicable plan)

/-! ## What the audit found -/

/-- One row of the audit: what was asked, and what came back.

    A row exists only for an applicable prerequisite. There is no `notApplicable`
    outcome, deliberately — an outcome is a finding, and "this release does not
    need it" is not a finding about it. The deferred channels are reported
    separately, below the rows, so a reader can see that they were considered. -/
structure Row where
  kind : PrerequisiteKind
  summary : String
  outcome : AuditOutcome
  deriving Repr

/-! ## The verdict

Two properties, both if-and-only-ifs, and they are what the shell reported by
counting three variables it incremented from twenty places. -/

/-- Whether the release may proceed on the strength of this audit. -/
def auditPermits (rows : List Row) : Bool := rows.all (·.outcome.permitsRelease)

/-- **A release may proceed exactly when every row is verified or is an
    explicitly carried assumption.**

    Left to right is what an operator relies on. Right to left is what a verdict
    that permits nothing cannot satisfy — and, more usefully, what keeps
    `operationalError` from being folded into permission later: an audit that
    could not run has established nothing, and reading its silence as consent is
    the failure this whole layer exists to prevent. -/
theorem auditPermits_iff (rows : List Row) :
    auditPermits rows = true ↔
      ∀ row ∈ rows, row.outcome = .verified ∨ ∃ assumption, row.outcome = .carried assumption := by
  rw [auditPermits, List.all_eq_true]
  constructor
  · intro permits row member
    have held := permits row member
    match outcome : row.outcome with
    | .verified => exact .inl rfl
    | .carried assumption => exact .inr ⟨assumption, rfl⟩
    | .missing _ => rw [outcome] at held; exact Bool.noConfusion held
    | .operationalError _ => rw [outcome] at held; exact Bool.noConfusion held
  · intro accounted row member
    match accounted row member with
    | .inl isVerified => rw [isVerified]; rfl
    | .inr ⟨_, isCarried⟩ => rw [isCarried]; rfl

/-- The rows that stop the release, with what to do about each. -/
def auditBlockers (rows : List Row) : List Row :=
  rows.filter (fun row => !row.outcome.permitsRelease)

/-- **The audit reports a blocker exactly when the release may not proceed.**

    Stated because the verdict and the report are read by different people —
    the workflow branches on the status, the operator reads the rows — and a
    release that stopped for a reason nothing printed is one nobody can fix. -/
theorem auditBlockers_isEmpty_iff (rows : List Row) :
    auditBlockers rows = [] ↔ auditPermits rows = true := by
  rw [auditPermits, auditBlockers, List.all_eq_true]
  constructor
  · intro empty row member
    have absent := List.filter_eq_nil_iff.mp empty row member
    match permits : row.outcome.permitsRelease with
    | true => rfl
    | false => exact absurd (by rw [permits]; rfl) absent
  · intro permits
    refine List.filter_eq_nil_iff.mpr ?_
    intro row member
    rw [permits row member]
    exact Bool.noConfusion

/-- Whether anything is outright *missing*, kept apart from whether anything
    could not be checked. Both block; only one is about this repository's
    configuration, and telling an operator to create something that already
    exists is how a correct release gets abandoned. -/
private def isMissing : AuditOutcome → Bool
  | .missing _ => true
  | _ => false

private def isUnchecked : AuditOutcome → Bool
  | .operationalError _ => true
  | _ => false

def auditMissing (rows : List Row) : List Row := rows.filter (isMissing ·.outcome)

def auditUnchecked (rows : List Row) : List Row := rows.filter (isUnchecked ·.outcome)

/-- An outcome blocks exactly when it is one of the two blocking cases.

    The case split written once, so the partition below is list plumbing rather
    than four cases repeated per direction. -/
private theorem blocking_cases (outcome : AuditOutcome) :
    outcome.permitsRelease = false ↔ (isMissing outcome = true ∨ isUnchecked outcome = true) := by
  cases outcome with
  | verified =>
      constructor
      · intro absurdity; exact Bool.noConfusion absurdity
      · intro cases'
        match cases' with
        | .inl absurdity => exact Bool.noConfusion absurdity
        | .inr absurdity => exact Bool.noConfusion absurdity
  | carried _ =>
      constructor
      · intro absurdity; exact Bool.noConfusion absurdity
      · intro cases'
        match cases' with
        | .inl absurdity => exact Bool.noConfusion absurdity
        | .inr absurdity => exact Bool.noConfusion absurdity
  | missing _ =>
      constructor
      · intro _; exact .inl rfl
      · intro _; rfl
  | operationalError _ =>
      constructor
      · intro _; exact .inr rfl
      · intro _; rfl

/-- **Every blocker is either missing or unchecked, and never both.**

    The mixed case is the one worth stating rather than leaving implicit: an
    audit with one absent ruleset and one unreachable endpoint has two blockers
    and reports both, and its remedy is not the union of two sentences
    pretending to be one finding. -/
theorem auditBlockers_partition (rows : List Row) :
    auditBlockers rows = [] ↔ auditMissing rows = [] ∧ auditUnchecked rows = [] := by
  rw [auditBlockers, auditMissing, auditUnchecked, List.filter_eq_nil_iff,
    List.filter_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro notBlocking
    constructor
    · intro row member missing
      have permits : row.outcome.permitsRelease = true := by
        match held : row.outcome.permitsRelease with
        | true => rfl
        | false => exact absurd (by rw [held]; rfl) (notBlocking row member)
      rw [(blocking_cases row.outcome).mpr (.inl missing)] at permits
      exact Bool.noConfusion permits
    · intro row member unchecked
      have permits : row.outcome.permitsRelease = true := by
        match held : row.outcome.permitsRelease with
        | true => rfl
        | false => exact absurd (by rw [held]; rfl) (notBlocking row member)
      rw [(blocking_cases row.outcome).mpr (.inr unchecked)] at permits
      exact Bool.noConfusion permits
  · intro ⟨noMissing, noUnchecked⟩ row member blocking
    have notPermitting : row.outcome.permitsRelease = false := by
      match held : row.outcome.permitsRelease with
      | false => rfl
      | true =>
          rw [held] at blocking
          exact absurd blocking (by exact Bool.noConfusion)
    match (blocking_cases row.outcome).mp notPermitting with
    | .inl missing => exact noMissing row member missing
    | .inr unchecked => exact noUnchecked row member unchecked

/-! ## The typed predicates

Each of these is the property the security model needs, not a count that a
different feature also satisfies. -/

/-- The include patterns whose presence covers *every* `v*` tag.

    A closed set rather than a shape test, and that is the point. The two
    previous versions of this check counted rulesets and then tested
    `startswith("refs/tags/v")`; the second accepts a ruleset naming the single
    tag `refs/tags/v1.0.0`, or the one release line `refs/tags/v1.*`, as one
    restricting creation of `v*` tags — leaving every other `v*` tag creatable
    by anyone. A pattern outside this set is not assumed to cover anything. -/
def coveringTagPatterns : List String :=
  ["~ALL", "refs/tags/*", "refs/tags/**", "refs/tags/v*", "refs/tags/v**"]

/-- A ruleset's ref conditions, as the two lists that decide coverage. -/
structure RefConditions where
  included : List String
  excluded : List String
  deriving Repr

/-- Whether these conditions cover every tag this project releases under.

    An exclude list disqualifies outright rather than being reasoned about: an
    excluded `refs/tags/v0.*` leaves the whole 0.x line unrestricted while the
    include set still reads as complete, and deciding which holes matter is
    exactly the interpretation a gate should refuse to perform. -/
def coversEveryReleaseTag (conditions : RefConditions) : Bool :=
  conditions.excluded.isEmpty && conditions.included.any (coveringTagPatterns.contains ·)

/-- A ruleset, reduced to what qualifies it. -/
structure TagRuleset where
  identifier : String
  enforcement : String
  conditions : RefConditions
  ruleTypes : List String
  deriving Repr

/-- Whether this ruleset actually restricts who may create a release tag.

    Three independent things, because a ruleset can have any two. In evaluate
    mode it reports and permits; over the wrong refs it restricts something
    else; without a `creation` rule it restricts updates and deletions of a tag
    that anyone may still create in the first place. -/
def restrictsTagCreation (ruleset : TagRuleset) : Bool :=
  ruleset.enforcement == "active"
    && coversEveryReleaseTag ruleset.conditions
    && ruleset.ruleTypes.contains "creation"

/-- What the `release` environment's protection rules amount to.

    `requiredReviewers` is an `Option Nat` and not a `Nat`, because "there is a
    required-reviewers rule with nobody in it" and "there is no such rule" are
    different configurations with different fixes — and an empty reviewer list
    approves itself, which is the more dangerous of the two precisely because it
    looks configured. -/
structure EnvironmentProtection where
  requiredReviewers : Option Nat
  deriving Repr

/-- A deployment branch policy entry, carrying the type it was declared with.

    The type is kept because filtering the branch entries out before looking
    made an environment admitting `main` *and* `v*` report as one restricted to
    `v*` tags — and the branch half is the half that lets a push reach the
    signing job. -/
structure PolicyEntry where
  entryType : String
  name : String
  deriving Repr

/-- Whether the deployment policy admits only release tags.

    Any branch entry disqualifies: a branch reaching this environment means a
    push can reach the job that signs. -/
def policyAdmitsOnlyReleaseTags (entries : List PolicyEntry) : Bool :=
  !entries.isEmpty
    && entries.all fun entry => entry.entryType == "tag" && entry.name.startsWith "v"

/-! ## Asking GitHub

`gh` is the API client; this module reads the bytes. -/

/-- What an API call produced. `notFound` is separated at the boundary because
    it is the one HTTP status that is an *answer* — the thing is not there —
    while every other failure means the question was not asked. -/
inductive ApiResult where
  | body (json : Json)
  | notFound
  | failed (detail : String)

/-- How `gh` reports an HTTP 404.

    Matched on the message rather than on a status this program can read,
    because `gh api` exits 1 for every HTTP error alike. Kept honest by what
    depends on it: nothing that could turn a refusal into a pass. `notFound`
    produces `missing` and `failed` produces `operationalError`, and *neither
    permits a release* — the classification decides which remedy an operator is
    shown, so a wording change in a future `gh` costs a less helpful sentence
    and never a wrong verdict. -/
private def notFoundMarkers : List String := ["HTTP 404", "Not Found"]

private def looksNotFound (text : String) : Bool :=
  notFoundMarkers.any fun marker => (text.splitOn marker).length > 1

/-- The largest page GitHub will return, so one request covers every
    configuration this audit is realistically asked about. -/
def maximumPageSize : Nat := 100

/-- One `gh api` call, with its status as a value and its body parsed here.

    `--cache 0s` because this audit is asked precisely when someone has just
    changed the configuration, and a cached answer would report the state before
    the change with no sign that it had.

    `per_page` because a page is not a list. GitHub defaults these endpoints to
    thirty rows, so thirty tag policies followed by a branch policy on page two
    would be read as a policy admitting only tags — a false pass on the one row
    that decides whether a push can reach the job that signs. A hundred is not a
    proof that everything was read, which is why the callers that can tell also
    check the count the API reports and refuse when it exceeds what arrived.

    The command is a parameter for the same reason `Digest`'s candidates are:
    what this function *decides* — a page of JSON is an answer, a 404 is an
    answer, anything else is not — was otherwise reachable only by having a real
    `gh`, a real repository and a real network in a particular state, which is
    to say not reachable at all. The tests pass the path of a script that
    answers the way each of those cases does. -/
def githubApiWith (command : String) (path : String)
    (timeoutMs : Nat := defaultTimeoutMs) : IO ApiResult := do
  let separator := if (path.splitOn "?").length > 1 then "&" else "?"
  let paged := s!"{path}{separator}per_page={maximumPageSize}"
  let outcome ← run command #["api", paged, "--cache", "0s"] timeoutMs
  match outcome, outcome.failureMessage with
  | _, some message => return .failed message
  | .completed output, none =>
      if output.succeeded then
        match Json.parse output.stdout with
        | .ok json => return .body json
        | .error why =>
            return .failed s!"'{command} api {paged}' succeeded and returned something that is not JSON ({why}). That is not evidence about the thing being asked for."
      else if looksNotFound output.stderr then return .notFound
      else
        return .failed s!"'{command} api {paged}' failed: {output.stderr.trimAscii.toString}"
  | _, none => return .failed s!"'{command} api {paged}' produced neither an outcome nor a reason."

def githubApi (path : String) (timeoutMs : Nat := defaultTimeoutMs) : IO ApiResult :=
  githubApiWith "gh" path timeoutMs

/-- How this module asks GitHub anything.

    A function rather than a direct call, so the audit can be driven from a
    table in a test. Everything below the API boundary — the ruleset loop, the
    row classification, the aggregation, the command's own verdict — was
    otherwise reachable only by having a real repository in a particular state,
    which is to say not reachable at all. The default is the real client; the
    tests pass one that answers from a list. -/
abbrev GithubClient := String → IO ApiResult

/-! ## Reading the answers

Each of these turns one API result into one row. The shape is always the same:
a body is inspected against a typed predicate, `notFound` is `missing` because
that is an answer, and `failed` is `operationalError` because it is not. -/

/-- A row from an API result, with the three cases spelled once.

    `decide` receives a parsed body and returns the outcome; the other two
    cases are fixed here so no collector can accidentally report an unreachable
    endpoint as an absent thing. -/
private def rowOf (kind : PrerequisiteKind) (summary : String) (result : ApiResult)
    (absent : String) (decide : Json → AuditOutcome) : Row :=
  match result with
  | .body json => { kind, summary, outcome := decide json }
  | .notFound => { kind, summary, outcome := .missing absent }
  | .failed detail =>
      { kind, summary,
        outcome := .operationalError s!"{detail} That is not evidence about the thing being asked for; re-run when the API is reachable rather than changing configuration that may already be correct." }

private def readString (json : Json) (field : String) : Option String :=
  (json.getObjVal? field).toOption.bind (·.getStr?.toOption)

private def readArray (json : Json) (field : String) : Option (List Json) :=
  (json.getObjVal? field).toOption.bind fun value =>
    (value.getArr?.toOption).map (·.toList)

/-- Whether the repository serves release assets to an anonymous client.

    First, because everything else assumes it. A private repository answers an
    unauthenticated fetch of `/releases/latest` with a 404, so `install.sh`,
    `brew install tl` and the whole of VERIFYING.md do not work — and the audit
    used to report seven missing prerequisites while the eighth, the one that
    makes the other seven pointless, went unmentioned. -/
def repositoryRow (repository : String) (result : ApiResult) : Row :=
  rowOf .repositoryPublic s!"the repository {repository} is public" result
    s!"the repository {repository} was not found. Release assets are served from it, so nothing this pipeline publishes would be reachable."
    fun json =>
      match readString json "visibility" with
      | some "public" => .verified
      | some visibility =>
          .missing s!"the repository is {visibility}, not public. A private repository serves release assets only to authenticated clients, so install.sh, 'brew install tl' and the whole of VERIFYING.md cannot work, and deployment protection rules are a paid feature there. Make it public, or defer the installer and Homebrew channels in release/plan.json deliberately — that file is where which channels a release publishes is decided."
      | none =>
          .operationalError "the repository metadata carried no readable 'visibility'. That is a response this audit does not understand rather than a private repository; check 'gh api repos/<owner>/<name>'."

/-- The reviewer rule, out of the environment body.

    An empty reviewer list is its own finding and the more dangerous of the two,
    because it looks configured: a required-reviewers rule with nobody in it
    approves itself. -/
def environmentProtectionOf (json : Json) : EnvironmentProtection :=
  match readArray json "protection_rules" with
  | none => { requiredReviewers := none }
  | some rules =>
      match rules.find? fun rule => readString rule "type" == some "required_reviewers" with
      | none => { requiredReviewers := none }
      | some rule =>
          { requiredReviewers := some ((readArray rule "reviewers").getD []).length }

def environmentRow (result : ApiResult) : Row :=
  rowOf .releaseEnvironment "the 'release' environment exists" result
    "the 'release' environment does not exist. It is what holds the approval gate between pushing a tag and signing whatever that tag points at; declaring it in the workflow does not create it. Create it per docs/release-prerequisites.md."
    fun _ => .verified

def reviewersRow (result : ApiResult) : Row :=
  rowOf .releaseReviewers "the 'release' environment requires a reviewer" result
    "the 'release' environment does not exist, so it requires nobody."
    fun json =>
      match (environmentProtectionOf json).requiredReviewers with
      | none =>
          .missing "the 'release' environment has no required-reviewers rule. Its other rules — a wait timer, a branch policy — do not gate approval, so without this anyone who can create a tag can make the workflow sign whatever that tag points at."
      | some 0 =>
          .missing "the 'release' environment has a required-reviewers rule with nobody in it, which approves itself. Add at least one reviewer per docs/release-prerequisites.md."
      | some _ => .verified

def policyEntriesOf (json : Json) : List PolicyEntry :=
  ((readArray json "branch_policies").getD []).filterMap fun entry =>
    match readString entry "type", readString entry "name" with
    | some entryType, some name => some { entryType, name }
    | _, _ => none

/-- The verdict over a *complete* entry list. Separated so the truncation
    check in the row above it cannot be reached around. -/
private def deploymentVerdict (entries : List PolicyEntry) : AuditOutcome :=
  if policyAdmitsOnlyReleaseTags entries then .verified
  else if entries.isEmpty then
    .missing "the 'release' environment's deployment policy names nothing, so it restricts nothing. Add a tag pattern of v* per docs/release-prerequisites.md."
  else
    .missing s!"the 'release' environment admits {String.intercalate ", " (entries.map fun entry => s!"{entry.entryType}:{entry.name}")}. A branch entry lets a push reach the job that signs, and a tag pattern outside v* admits a ref this pipeline never releases from; the policy must name tag patterns beginning with v and nothing else."

def deploymentPolicyRow (result : ApiResult) : Row :=
  rowOf .deploymentPolicy "the 'release' environment admits only release tags" result
    "the 'release' environment has no custom deployment policy, so every ref may deploy to it."
    fun json =>
      let entries := policyEntriesOf json
      -- The endpoint reports how many rows exist. Fewer arriving than it counts
      -- means a page was read as a list, and the entries missing from it are
      -- exactly the ones this row would have refused for.
      match (json.getObjVal? "total_count").toOption.bind (·.getNat?.toOption) with
      | some total =>
          if total > entries.length then
            .operationalError s!"the deployment policy reports {total} entries and {entries.length} arrived, so this read one page of a longer list. The entries that did not arrive are the ones this check would refuse for, so a pass here would mean nothing."
          else deploymentVerdict entries
      | none => deploymentVerdict entries

/-- One ruleset, reduced to what qualifies it. -/
def tagRulesetOf (identifier : String) (json : Json) : TagRuleset :=
  let conditions :=
    match (json.getObjVal? "conditions").toOption.bind
        (fun c => (c.getObjVal? "ref_name").toOption) with
    | none => { included := [], excluded := [] }
    | some refName =>
        let names (field : String) : List String :=
          ((readArray refName field).getD []).filterMap (·.getStr?.toOption)
        { included := names "include", excluded := names "exclude" }
  { identifier,
    enforcement := (readString json "enforcement").getD "",
    conditions,
    ruleTypes := ((readArray json "rules").getD []).filterMap (readString · "type") }

/-! ## The audit

The one place the rows are collected, in the order an operator wants them:
whether the repository is reachable at all, then the gate between a tag and a
signature, then who may create the tag. -/

/-- The row every applicable prerequisite gets when `gh` itself cannot answer.

    Not `missing`: nothing was looked at. This is the case the shell reached
    whenever `gh` was absent or unauthenticated, and reporting it as an absent
    environment would send an operator to create one that exists. -/
private def uncheckedRow (kind : PrerequisiteKind) (summary : String)
    (reason : String) : Row :=
  { kind, summary, outcome := .operationalError reason }

/-- A secret's scope is not readable from anywhere but a run that uses it.

    A carried assumption rather than a check, and it follows its declared policy
    without ever counting as verified — which is exactly what the third
    `AuditOutcome` case is for. -/
private def carriedTokenRow : Row :=
  { kind := .homebrewToken,
    summary := "HOMEBREW_TAP_TOKEN grants write access to the tap",
    outcome := .carried "A secret's scope is not readable from a workflow, so this is recorded rather than checked. Confirm it by running the release once, or by testing the token by hand. Store it in the protected release environment, which publish-homebrew declares." }

/-- The tap signing key is a secret too, and its match with the tracked signer
    record is checked by the publication itself, before anything is written. -/
private def carriedSigningKeyRow : Row :=
  { kind := .homebrewSigningKey,
    summary := "HOMEBREW_TAP_SIGNING_KEY holds the private key of the signer in release/tap-signer.json",
    outcome := .carried "A secret is not readable from here, so this is recorded rather than checked. homebrew-publish refuses before writing anything when the key is absent, needs a passphrase, or is not the recorded signer; `tlrelease homebrew-publish --dry-run` with the key checks it in advance. Store it in the protected release environment, which publish-homebrew declares." }

/-- Collect the tag-ruleset row.

    Every ruleset that could not be read is counted, because an unreadable one
    is not a ruleset that fails to qualify: skipping them silently turned one
    5xx on a detail call into "no active ruleset restricts creation of v* tags",
    a missing row that aborts a correctly configured release. -/
private def tagRulesetRow (ask : GithubClient) (repository : String) : IO Row := do
  let summary := "an active ruleset restricts creation of v* tags"
  match ← ask s!"repos/{repository}/rulesets" with
  | .failed detail =>
      return uncheckedRow .tagRuleset summary
        s!"the rulesets listing could not be read ({detail}). That is not evidence that no ruleset exists."
  | .notFound =>
      return uncheckedRow .tagRuleset summary
        "the rulesets endpoint answered 404, which is a repository this audit cannot see rather than a repository with no rulesets."
  | .body listing =>
      let entries := match listing.getArr?.toOption with
        | some values => values.toList
        | none => []
      let tagEntries := entries.filter fun entry => readString entry "target" == some "tag"
      let mut unreadable := 0
      let mut qualifying : Option String := none
      for entry in tagEntries do
        if qualifying.isSome then
          -- One qualifying ruleset is the whole question; the rest are not
          -- fetched, so a repository with many rulesets costs one call.
          pure ()
        else
          let identifier := match (entry.getObjVal? "id").toOption with
            | some value => (value.getNat?.toOption).map toString |>.getD ""
            | none => ""
          if identifier.isEmpty then
            unreadable := unreadable + 1
          else
            match ← ask s!"repos/{repository}/rulesets/{identifier}" with
            | .body detail =>
                if restrictsTagCreation (tagRulesetOf identifier detail) then
                  qualifying := some identifier
                else pure ()
            | _ => unreadable := unreadable + 1
      match qualifying with
      | some identifier =>
          let row : Row :=
            { kind := .tagRuleset
              summary := s!"ruleset #{identifier} restricts creation of every v* tag"
              outcome := .verified }
          return row
      | none =>
        if unreadable != 0 then
          return uncheckedRow .tagRuleset summary
            s!"{unreadable} ruleset(s) could not be read, and none of the ones that could read as covering every v* tag. An unreadable ruleset is not an absent one — re-run when the API is reachable rather than creating a ruleset that may already exist."
        let row : Row :=
          { kind := .tagRuleset
            summary := summary
            outcome := .missing "no active ruleset restricts creation of v* tags. A ruleset that exists but targets branches, is in evaluate mode, carries no creation restriction, or whose ref conditions do not cover *every* v* tag leaves tag creation open — naming one tag or one release line restricts that tag or that line and nothing else. Coverage means an include pattern of ~ALL, refs/tags/*, refs/tags/** or refs/tags/v*, and no exclude list. The sign job's ancestry check is a backstop: it sees what the tag points at, never who pushed it." }
        return row

/-- Whether `gh` is present and authenticated. Asked once: without it every row
    below is unchecked for the same reason, and saying so nine times is not a
    report. -/
def githubReachable : IO (Except String Unit) := do
  match ← run "gh" #["auth", "status"] with
  | .completed output =>
      if output.succeeded then return .ok ()
      else return .error s!"gh is not authenticated ('gh auth login'), so the GitHub API could not be asked: {output.stderr.trimAscii.toString}"
  | outcome =>
      return .error ((outcome.failureMessage).getD "gh could not be run.")

/-- The whole audit, for the channels this release publishes through. -/
def collectRows (ask : GithubClient) (reachable : IO (Except String Unit))
    (identity : Identity) (plan : ReleasePlan) : IO (List Row) := do
  let repository := identity.repository
  let applicable := applicableKinds plan
  let wanted (kind : PrerequisiteKind) : Bool := applicable.contains kind
  match ← reachable with
  | .error reason =>
      -- Every applicable row, unchecked for one stated reason. Emitting them
      -- rather than none is what keeps the count honest: an audit that printed
      -- nothing would read as an audit with nothing to report.
      return applicable.map fun kind =>
        uncheckedRow kind "the GitHub configuration this release depends on" reason
  | .ok () =>
      let mut rows : Array Row := #[]
      rows := rows.push (repositoryRow repository (← ask s!"repos/{repository}"))
      let environment ← ask s!"repos/{repository}/environments/release"
      rows := rows.push (environmentRow environment)
      rows := rows.push (reviewersRow environment)
      rows := rows.push (deploymentPolicyRow
        (← ask s!"repos/{repository}/environments/release/deployment-branch-policies"))
      rows := rows.push (← tagRulesetRow ask repository)
      if wanted .homebrewTap then
        let tap := s!"{identity.owner}/homebrew-tap"
        rows := rows.push (rowOf .homebrewTap s!"the Homebrew tap {tap} exists"
          (← ask s!"repos/{tap}")
          s!"the Homebrew tap {tap} does not exist or is not visible. A release with this channel enabled pushes the generated formula there and fails if it cannot. Create the tap per docs/release-prerequisites.md, or defer the Homebrew channel in release/plan.json — that file is where the decision lives."
          fun _ => .verified)
        rows := rows.push carriedTokenRow
        rows := rows.push carriedSigningKeyRow
      if wanted .npmPackages then
        -- The registry is npm's boundary, not gh's, and this release does not
        -- reach it: the npm channel is deferred for v0.1, so these rows are
        -- unreachable today. They are carried rather than checked because
        -- reaching them would put `npm` on the v0.1 dependency path, which the
        -- budget forbids — and the npm port is where they get a real check.
        rows := rows.push
          { kind := .npmPackages
            summary := "the npm packages exist"
            outcome := .carried "npm configures trusted publishing only for a package that already exists, so the names are bootstrapped by hand before the channel is enabled (docs/release-prerequisites.md). Checking them here would put npm on the v0.1 dependency path." }
        rows := rows.push
          { kind := .npmTrustedPublishing
            summary := "trusted publishing is configured for each npm package"
            outcome := .carried "Configured per package in the npm web UI and not readable without authenticating to the registry. Confirm it when the channel is enabled." }
      return rows.toList

/-- The channels this release does not publish through, and what they are
    waiting for. Reported beside the rows rather than as rows: a deferred
    channel is not an outstanding prerequisite, and printing it as one is what
    made the shell audit stop a GitHub-only release. -/
def deferredNotes (plan : ReleasePlan) : List String :=
  Channel.all.filterMap fun channel =>
    match plan.status channel with
    | .enabled => none
    | .deferred planned =>
        some s!"the '{channel.wire}' channel is deferred to {planned.render}, so this release needs none of its prerequisites."

/-! ## The command -/

private def prereqsOptions : List OptionSpec :=
  [{ name := "identity", takesValue := true }, { name := "plan", takesValue := true }]

private structure PrereqsArgs where
  identityPath : String
  planPath : String

private def prereqsArgs (options : Options) : Except String PrereqsArgs := do
  return { identityPath := ← options.required "identity", planPath := ← options.required "plan" }

def outcomeLine (row : Row) : String :=
  match row.outcome with
  | .verified => s!"  ok        {row.summary}"
  | .carried assumption => s!"  carried   {row.summary}\n            {assumption}"
  | .missing remedy => s!"  MISSING   {row.summary}\n            {remedy}"
  | .operationalError detail => s!"  unchecked {row.summary}\n            {detail}"

/-- What the audit prints, and what it decides, from the rows it collected.

    Pure, and separated from the reading and the printing for the reason
    `Verify.Report.workerVerdict` is: everything a reader of a release log sees,
    and the difference between a release proceeding and stopping, is decided
    here rather than in the `IO` that surrounds it — so both are reachable in a
    test over rows, including the mixed case where some rows are configuration
    to create and others are questions that could not be asked.

    Every row is rendered, in order, before any verdict. An audit that printed
    only its failures would leave an operator unable to tell a clean sweep from
    a run that checked two things. -/
def auditReport (repository : String) (plan : ReleasePlan) (rows : List Row) :
    List String × Except String String :=
  let lines :=
    (deferredNotes plan).map (fun note => s!"  deferred  {note}") ++ rows.map outcomeLine
  match auditBlockers rows with
  | [] =>
      (lines, .ok s!"{rows.length} prerequisite(s) for {repository} hold, for the channels this release publishes through")
  | blockers =>
      let missing := (auditMissing rows).length
      let unchecked := (auditUnchecked rows).length
      -- The two counts separately, because they have opposite remedies and the
      -- mixed case is the one worth naming: some of this is configuration to
      -- create, and some of it is an API to come back to.
      (lines, .error s!"{blockers.length} prerequisite(s) stop this release — {missing} missing, {unchecked} unchecked. A missing row is configuration this repository does not have; an unchecked one is a question that could not be asked, and reading its silence as consent is what this audit exists to prevent. Neither permits a release.")

private def prereqsDecision (args : PrereqsArgs) : Decision String := do
  let identity ← readParsed args.identityPath Identity.parse
  let plan ← readParsed args.planPath ReleasePlan.parse
  let rows ← attempt "the prerequisite audit could not run"
    (collectRows githubApi githubReachable identity plan)
  let (lines, verdict) := auditReport identity.repository plan rows
  for line in lines do
    IO.println line
  ofExcept verdict

private def prereqsCommand : Command :=
  optionCommand "prereqs" "--identity <identity.json> --plan <plan.json>"
    "Audit the external state this release depends on, for the channels it publishes through."
    ["--identity", "release/identity.json", "--plan", "release/plan.json"]
    prereqsOptions prereqsArgs prereqsDecision

def prerequisiteCommands : List Command := [prereqsCommand]

end Release
