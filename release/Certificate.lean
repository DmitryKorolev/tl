/-
Which certificate identity this project will accept, and the one expression
that says so.

## The problem this replaces

`cosign` is given a Go RE2 expression and matches a certificate's SAN against
it. That expression was *configuration*: a string in `release/identity.json`
that a human wrote and a shell gate checked by compiling it with Python's `re`
and trying it against adversarial candidates. Three things were wrong with
that, in increasing order of seriousness.

It needed `python3` on a strict-policy path, which the v0.1 dependency budget
forbids. It checked a Go RE2 expression with a *different* engine — Python's
`re` is a superset, so lookaround and backreferences compiled there and would
make cosign error on every call, which the script had to refuse by hand. And
underneath both: a configurable expression can be anchored, well-formed, pass
every adversarial candidate anyone thought of, and still be permissive in a way
nobody enumerated. A pin nobody can get wrong beats a pin that is checked.

## What replaces it

The expression is *generated*, from structured values that cannot express a
permissive policy: a repository, a workflow path, and the fixed tag grammar
`Version.parseTag` already owns. There is no configuration knob that widens
what is accepted, because there is no knob — `certificateIdentityRegexp` in
`release/identity.json` is a generated mirror, held to equal what this module
renders.

Two things this deliberately does **not** do.

It does not implement a regular-expression matcher. A second matcher would be a
second semantics, and its agreement with RE2 would be an assumption dressed as
a check. The policy is instead defined *structurally* — `parseSan` below — and
the rendered expression is the projection of that policy into the one syntax
cosign speaks. The theorem is about the structure; nothing here claims Lean
verifies RE2.

It does not claim the rendered expression is what cosign will do with it. That
is a carried assumption, recorded in docs/overview.md: cosign interprets the
emitted fragment according to documented Go RE2 syntax. What this removes is
the far larger surface of a hand-written expression; what remains is a fixed
fragment, generated from literals, that the v0.1 release candidate exercises
against real cosign.
-/
import release.Command
import release.Model

namespace Release

/-! ## The fixed parts

Every literal cosign is given, in one place. A reader checking this against a
certificate does not have to find them scattered through a renderer. -/

/-- The prefix Fulcio puts in front of `GITHUB_WORKFLOW_REF`. -/
def sanPrefix : String := "https://github.com/"

/-- What separates the workflow path from the ref it ran on. -/
def sanRefSeparator : String := "@"

/-- The only ref namespace a release may be signed from. A branch ref is not a
    release: `refs/heads/main` moves, so an identity accepting one would accept
    every future commit on that branch under the same certificate. -/
def sanTagNamespace : String := "refs/tags/"

/-! ## The structural policy

The policy is this parser, not the expression. An accepted identity is one that
names exactly the configured repository, exactly the configured workflow path,
a tag ref, and a tag `Version.parseTag` accepts — which is the same grammar the
tag check before the build matrix uses, so a tag that would produce an
unsignable artifact is refused in one place rather than two. -/

/-- What an accepted SAN says. Structured rather than a string, so the checks
    below compare values a parser produced and never substrings of text. -/
structure SigningIdentity where
  repository : String
  workflowPath : String
  version : Version
  deriving Repr

/-- Split at the *first* occurrence, keeping the remainder whole.

    `String.splitOn` on `/` would give five pieces for a repository containing
    one, and reassembling them is where an off-by-one lives. -/
private def splitFirst (text : String) (separator : String) : Option (String × String) :=
  match text.splitOn separator with
  | [] => none
  | [_] => none
  | first :: rest => some (first, String.intercalate separator rest)

/-- Read a certificate SAN as the thing it names, or say why it is not one this
    project signs with.

    Every refusal names what was expected, because this message is what an
    operator sees when a release will not verify — and "the identity does not
    match" without saying which part is a message that sends them to read a
    regular expression. -/
def parseSan (san : String) : Except String SigningIdentity := do
  if !san.startsWith sanPrefix then
    .error s!"'{san}' does not begin with {sanPrefix}. A certificate this project accepts is a GitHub Actions workflow identity, and Fulcio writes those with that prefix."
  let afterPrefix := (san.drop sanPrefix.length).toString
  -- The repository is the first two path segments, and the workflow path is
  -- everything up to the `@`. Taken in that order because a workflow path
  -- contains `/` and an owner name does not.
  match splitFirst afterPrefix sanRefSeparator with
  | none =>
      .error s!"'{san}' carries no '{sanRefSeparator}', so it names no ref. A workflow identity is <repository>/<workflow path>{sanRefSeparator}<ref>."
  | some (pathPart, refPart) =>
      match pathPart.splitOn "/" with
      | owner :: name :: workflowSegments =>
          if owner.isEmpty || name.isEmpty then
            .error s!"'{san}' names no repository — the owner or the name is empty."
          else if workflowSegments.isEmpty then
            .error s!"'{san}' names a repository but no workflow file."
          else if !refPart.startsWith sanTagNamespace then
            .error s!"'{san}' was signed from '{refPart}', which is not a tag. A release is signed from {sanTagNamespace}: a branch ref moves, so an identity accepting one would accept every future commit on that branch under the same certificate."
          else do
            let tag := (refPart.drop sanTagNamespace.length).toString
            let version ← Version.parseTag s!"the tag in '{san}'" tag
            return { repository := owner ++ "/" ++ name,
                     workflowPath := String.intercalate "/" workflowSegments,
                     version }
      | _ => .error s!"'{san}' does not name an <owner>/<name> repository."

/-- Whether this project would accept that certificate.

    Two comparisons and nothing else, over values a parser produced. There is no
    substring test here and no expression: a SAN that merely *contains* this
    repository's name cannot satisfy an equality between parsed segments. -/
def identityAccepts (identity : Identity) (san : String) : Bool :=
  match parseSan san with
  | .error _ => false
  | .ok signing =>
      signing.repository == identity.repository
        && signing.workflowPath == identity.releaseWorkflow

/-- **A certificate is accepted exactly when its SAN parses and names this
    repository and this workflow.**

    The if-and-only-if the port asks for, and it is stated over the *structured*
    value rather than over the rendered expression — nothing here claims Lean
    implements or verifies RE2.

    Both directions carry weight. Left to right is what an operator relies on: a
    certificate that got past this really does name this repository, this
    workflow, and a tag `Version.parseTag` accepts, because a SAN failing any of
    those does not parse. Right to left is what a check that accepts nothing
    cannot satisfy — and, since `parseSan` is the only thing standing between a
    SAN and acceptance, it is also what keeps a comparison from being dropped:
    remove either equality and a SAN naming another repository would satisfy the
    left side while failing the right. -/
theorem identityAccepts_iff (identity : Identity) (san : String) :
    identityAccepts identity san = true ↔
      ∃ signing, parseSan san = .ok signing
        ∧ signing.repository = identity.repository
        ∧ signing.workflowPath = identity.releaseWorkflow := by
  rw [identityAccepts]
  match parsed : parseSan san with
  | .error _ =>
      constructor
      · intro absurdity; exact Bool.noConfusion absurdity
      · intro ⟨_, isOk, _, _⟩; cases isOk
  | .ok signing =>
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      constructor
      · intro ⟨sameRepository, sameWorkflow⟩
        exact ⟨signing, rfl, sameRepository, sameWorkflow⟩
      · intro ⟨other, isOk, sameRepository, sameWorkflow⟩
        have : other = signing := Except.ok.inj isOk.symm
        rw [this] at sameRepository sameWorkflow
        exact ⟨sameRepository, sameWorkflow⟩

/-! ## Rendering the policy into the one syntax cosign speaks -/

/-- A character that may appear in a repository or a workflow path.

    Narrow on purpose, and refusing rather than escaping. Every character
    outside this class either needs escaping in RE2 or cannot appear in a
    GitHub repository name or a path under `.github/workflows/`; refusing them
    means the escaping below has exactly one case to get right instead of
    twenty, and a configuration that would need the other nineteen is a
    configuration to look at rather than to render. -/
private def renderableChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9')
    || c == '-' || c == '_' || c == '.' || c == '/'

/-- One literal, escaped for RE2.

    `.` is the only metacharacter the class above admits, and it is escaped
    rather than left alone because an unescaped `.` matches any character —
    which is how `github.com` in a hand-written pin would also match
    `githubXcom`, and how a repository named `a.b` would also match `axb`. -/
private def escapeLiteral (what : String) (text : String) : Except String String := do
  if text.isEmpty then
    .error s!"{what} is empty. An empty segment would render an expression that constrains nothing where it is supposed to constrain everything."
  for c in text.toList do
    if !renderableChar c then
      .error s!"{what} contains '{c}', which this generator will not render into a regular expression. Repository names and workflow paths are letters, digits, '-', '_', '.' and '/'; anything else either needs an escape this generator does not emit or does not belong in the value."
  return String.join (text.toList.map fun c => if c == '.' then "\\." else String.singleton c)

/-- The tag grammar, as RE2, and the *only* variable part of the expression.

    It is a constant rather than something derived from `Version.parseTag`,
    because Lean cannot compile a parser into a regular expression and
    pretending otherwise would be the second-semantics mistake this module
    exists to avoid. What keeps the two in step is the adversarial table in
    `Tests/ReleaseToolTests.lean`: every candidate is run through `parseSan`,
    which uses the parser, and the same candidates are the ones a reader checks
    this fragment against. The residual — that cosign reads this fragment the
    way Go RE2 documents — is a carried assumption in docs/overview.md, and the
    v0.1 release candidate is what exercises it against real cosign. -/
def tagExpression : String :=
  "v(0|[1-9][0-9]*)\\.(0|[1-9][0-9]*)\\.(0|[1-9][0-9]*)(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?"

/-- The one canonical certificate identity expression.

    Fully anchored at both ends. The tail anchor is not pedantry: cosign matches
    unanchored, and a git tag name may contain `/`, so a head-only expression
    accepts an identity that merely *begins* with this repository's. -/
def renderIdentityExpression (identity : Identity) : Except String String := do
  let repository ← escapeLiteral "the repository" identity.repository
  let workflow ← escapeLiteral "the release workflow path" identity.releaseWorkflow
  let host ← escapeLiteral "the certificate host" "github.com"
  return "^https://" ++ host ++ "/" ++ repository ++ "/" ++ workflow
    ++ sanRefSeparator ++ sanTagNamespace ++ tagExpression ++ "$"

/-- The SAN a run of this workflow on `tag` would present. Composed from the
    same pieces the expression is rendered from, so the accept/reject table can
    be driven with real identities rather than with strings someone typed. -/
def certificateSan (identity : Identity) (tag : String) : String :=
  sanPrefix ++ identity.repository ++ "/" ++ identity.releaseWorkflow
    ++ sanRefSeparator ++ sanTagNamespace ++ tag

/-! ## Holding the configuration to the canonical rendering -/

/-- What `release/identity.json` must say about the expression.

    Retained as a field rather than deleted, because four other consumers read
    it — VERIFYING.md, the installer, the standalone verifier and the Homebrew
    formula all quote the expression, and a config that stopped carrying it
    would break the one interface this change is supposed to preserve. It is a
    *mirror*: held to equal what this module renders, so it cannot be widened by
    editing it. -/
def identityExpressionChecks (identity : Identity) (rendered : String) : List Check :=
  [{ held := identity.certificateIdentityRegexp == rendered,
     failure := s!"release/identity.json carries a certificate identity expression this build does not render.\n  it says:     {identity.certificateIdentityRegexp}\n  it must say: {rendered}\nThe expression is generated from the repository and the workflow path plus the fixed tag grammar; it is a mirror of that rendering and not a value to edit. An expression that is anchored and well-formed can still be permissive in a way nobody enumerated, which is why it is no longer configuration. Copy the rendering above into release/identity.json, and take the difference between the two as the thing to look at rather than as a formatting detail." }]

/-- The adversarial cases the old shell gate ran against a regex engine, as
    structured expectations.

    Kept as a *live check* rather than only as tests, and driven through
    `parseSan`, so what is exercised is the policy rather than a second copy of
    it. The pin used to be checked by compiling it with Python's `re` — a
    different engine from cosign's RE2 — and the list of what an expression must
    reject is the part of that gate worth keeping. -/
def identityDiscriminationChecks (identity : Identity) : List Check :=
  let accepted (tag : String) : Check :=
    { held := identityAccepts identity (certificateSan identity tag),
      failure := s!"the pinned identity rejects this repository's own release workflow on the tag {tag}, so nothing this project signs could be verified against it." }
  let rejected (what : String) (san : String) : Check :=
    { held := !identityAccepts identity san,
      failure := s!"the pinned identity accepts {what} ({san}). Anything that can present that certificate could sign artifacts every verifier of this project would accept." }
  [accepted "v0.1.0", accepted "v1.2.3", accepted "v10.20.30",
   accepted "v1.2.3-rc.1", accepted "v1.2.3-rc-1",
   rejected "another repository's release workflow"
     (sanPrefix ++ "someone-else/tl/" ++ identity.releaseWorkflow ++ "@refs/tags/v1.2.3"),
   rejected "this repository's CI workflow"
     (sanPrefix ++ identity.repository ++ "/.github/workflows/ci.yml@refs/tags/v1.2.3"),
   rejected "a branch ref rather than a tag"
     (sanPrefix ++ identity.repository ++ "/" ++ identity.releaseWorkflow ++ "@refs/heads/main"),
   rejected "a tag with a leading zero, which the pinned grammar refuses"
     (certificateSan identity "v01.2.3"),
   rejected "a tag with no leading v" (certificateSan identity "1.2.3"),
   rejected "a tag carrying build metadata, which cannot be signed"
     (certificateSan identity "v1.2.3+build"),
   -- The one a head-only expression admits, and the reason for the tail anchor:
   -- a git tag name may contain '/'.
   rejected "a tag whose name extends past the version"
     (certificateSan identity "v1.2.3/extra"),
   -- The one an unanchored expression admits.
   rejected "an identity that merely contains this repository's"
     ("https://evil.example/" ++ sanPrefix ++ identity.repository ++ "/"
       ++ identity.releaseWorkflow ++ "@refs/tags/v1.2.3"),
   rejected "an identity that merely begins with this repository's"
     (sanPrefix ++ identity.repository ++ "-fork/" ++ identity.releaseWorkflow
       ++ "@refs/tags/v1.2.3")]

/-- Everything the committed configuration is held to. -/
def identityChecks (identity : Identity) (rendered : String) : List Check :=
  identityExpressionChecks identity rendered ++ identityDiscriminationChecks identity

/-! ## The commands -/

private def identityOptions : List OptionSpec :=
  [{ name := "identity", takesValue := true }]

private def identityCheckDecision (identityPath : String) : Decision String := do
  let identity ← readParsed identityPath Identity.parse
  let rendered ← ofExcept (renderIdentityExpression identity)
  match Check.failures (identityChecks identity rendered) with
  | [] =>
      return s!"{identityPath} pins one canonical identity, and it discriminates: {rendered}"
  | failures =>
      decline (s!"the pinned signing identity does not hold.\n"
        ++ String.join (failures.map fun failure => s!"  {failure}\n")
        ++ "Every verifier of this project — VERIFYING.md, the installer, the standalone artifact verifier and the Homebrew formula — is pinned to this expression, so an identity that is wrong here makes genuine releases unverifiable, and one that is too wide makes forged ones verifiable.")

private def identityCheckCommand : Command :=
  optionCommand "identity-check" "--identity <identity.json>"
    "Refuse unless the pinned signing identity is the canonical one and discriminates."
    ["--identity", "release/identity.json"]
    identityOptions (fun options => options.required "identity") identityCheckDecision

private def acceptsOptions : List OptionSpec :=
  [{ name := "identity", takesValue := true }, { name := "san", takesValue := true }]

private structure AcceptsArgs where
  identityPath : String
  san : String

private def acceptsArgs (options : Options) : Except String AcceptsArgs := do
  return { identityPath := ← options.required "identity", san := ← options.required "san" }

/-- Whether a certificate identity this run would present is one the project
    accepts.

    Called twice in the release workflow, before anything is built and again
    before anything is signed, and both were inline Python compiling the pinned
    expression with a different engine from the one cosign uses. The answer is
    now the structural policy `identityAccepts_iff` characterises. -/
private def acceptsDecision (args : AcceptsArgs) : Decision String := do
  let identity ← readParsed args.identityPath Identity.parse
  if identityAccepts identity args.san then
    return s!"{args.san} is an identity this project accepts"
  else
    -- Why, not just "no". This runs either before a build or before a signature,
    -- and an operator told only that the identity does not match is sent to
    -- read a regular expression to find out which part of it did not.
    let reason := match parseSan args.san with
      | .error message => message
      | .ok signing =>
          if signing.repository != identity.repository then
            s!"it names the repository '{signing.repository}', and this project is '{identity.repository}'."
          else
            s!"it names the workflow '{signing.workflowPath}', and this project signs from '{identity.releaseWorkflow}'."
    decline s!"{args.san} is not an identity this project accepts: {reason} Every verifier is pinned to that identity, so artifacts signed as this would be unverifiable — which is worse than not shipping them, because a signature nobody can check still looks like one. Either the workflow moved, which is an identity rotation (follow VERIFYING.md), or the tag is outside the accepted SemVer shape."

private def acceptsCommand : Command :=
  optionCommand "identity-accepts" "--identity <identity.json> --san <certificate identity>"
    "Refuse unless that certificate identity is one this project would sign as."
    ["--identity", "release/identity.json",
     "--san", "https://github.com/owner/repo/.github/workflows/release.yml@refs/tags/v0.1.0"]
    acceptsOptions acceptsArgs acceptsDecision

def certificateCommands : List Command := [identityCheckCommand, acceptsCommand]

end Release
