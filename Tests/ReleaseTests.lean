/-
`Tests.ReleaseTests` -- the release-machinery guards.

Two of them:

1. A drift guard for the signed-release identity pinned by ADR-0006 /
   ADR-0014. `release/identity.json` is the machine-readable current pin;
   VERIFYING.md and the ADR must carry the same operative values. The installer
   and Homebrew formula join this guard when their files land.
2. Build provenance (`tl version`): every `Tl.Build.Kind` branch of both
   renderings, and a drift guard binding the generated `Tl.Build.Stamp` pins to
   `lean-toolchain` / `lake-manifest.json` on disk — the compiled constants
   cannot be varied at test time, so the renderings are exercised through
   explicit `Provenance` values and the *compiled* one is checked separately.

Tested release shell (ADR-0004); no Mathlib (ADR-0009).
-/
import Lean.Data.Json
import Tests.Harness
import Tests.JsonUtil
import Tl.Build.Provenance
import Tl.Cli.Commands
import Tl.Hash.Sha256
import release.Model

namespace Tl.Tests

open Lean (Json)
open System (FilePath)

private def has (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

private def readRequired (path : FilePath) : IO (Except String String) := do
  if !(← path.pathExists) then
    return .error s!"missing {path} under cwd {(← IO.currentDir)}"
  return .ok (← IO.FS.readFile path)

def releaseIdentityTests : IO (List Outcome) := do
  let configPath : FilePath := "release/identity.json"
  let verifyingPath : FilePath := "VERIFYING.md"
  let distributionPath : FilePath := "docs/adr/ADR-0006-distribution-and-platforms.md"
  let threatPath : FilePath := "docs/adr/ADR-0014-threat-model.md"
  let installerPath : FilePath := "install.sh"
  let configRaw ← readRequired configPath
  let verifyingRaw ← readRequired verifyingPath
  let distributionRaw ← readRequired distributionPath
  let threatRaw ← readRequired threatPath
  let mut outs := [
    check "release identity: canonical config exists" configRaw.isOk s!"{configRaw}",
    check "release identity: VERIFYING.md exists" verifyingRaw.isOk s!"{verifyingRaw}",
    check "release identity: ADR-0006 exists" distributionRaw.isOk s!"{distributionRaw}",
    check "release identity: ADR-0014 exists" threatRaw.isOk s!"{threatRaw}" ]
  let some configText := configRaw.toOption
    | return outs
  let some config := (Json.parse configText).toOption
    | return outs ++ [check "release identity: canonical config parses as JSON" false
        "release/identity.json is malformed"]
  outs := outs ++ [check "release identity: canonical config parses as JSON" true]
  let fields := ["repository", "npmPackage", "releaseWorkflow",
    "certificateOidcIssuer", "certificateIdentityRegexp"]
  for field in fields do
    outs := outs ++ [check s!"release identity: canonical field {field} is present"
      (jStr config field).isSome s!"release/identity.json lacks string field {field}"]
  let some repository := jStr config "repository" | return outs
  let some npmPackage := jStr config "npmPackage" | return outs
  let some workflow := jStr config "releaseWorkflow" | return outs
  let some issuer := jStr config "certificateOidcIssuer" | return outs
  let some identity := jStr config "certificateIdentityRegexp" | return outs
  outs := outs ++ [
    checkEq "release identity: final repository is pinned" repository "DmitryKorolev/tl",
    checkEq "release identity: npm package is pinned" npmPackage "@taskloop/tl",
    checkEq "release identity: direct workflow path is pinned" workflow ".github/workflows/release.yml",
    checkEq "release identity: GitHub OIDC issuer is pinned" issuer
      "https://token.actions.githubusercontent.com",
    check "release identity: certificate expression is start-anchored" (identity.startsWith "^") identity,
    check "release identity: certificate expression is end-anchored" (identity.endsWith "$") identity,
    check "release identity: certificate expression fixes repository and workflow"
      (has identity "DmitryKorolev/tl/\\.github/workflows/release\\.yml@refs/tags/v") identity ]
  -- The installer is a piped shell script: it cannot read release/identity.json
  -- out of a checkout, so it carries its own copy of the issuer and the
  -- certificate expression. That copy is the one users actually verify
  -- against, which makes drift here a silent downgrade of the check rather
  -- than a documentation lapse.
  let installerRaw ← readRequired (installerPath : FilePath)
  outs := outs ++ [check "release identity: the installer exists" installerRaw.isOk s!"{installerRaw}"]
  -- Per-file expectations rather than one list applied everywhere. The prose
  -- documents describe the whole arrangement, so they carry every pin; the
  -- installer is a verifier, so it carries the values a verifier acts on. It
  -- has no reason to name the npm package, and it holds the workflow path only
  -- inside the (escaped) certificate expression, so demanding the plain string
  -- there would be a coincidence to satisfy rather than an invariant to keep.
  let allPins := [("repository", repository), ("npm package", npmPackage),
    ("workflow", workflow), ("OIDC issuer", issuer), ("certificate identity", identity)]
  let verifierPins := [("repository", repository), ("OIDC issuer", issuer),
    ("certificate identity", identity)]
  -- The Homebrew formula is the fourth home of the same pin, and the one a
  -- `brew install` user relies on. Like the installer it is a verifier, so it
  -- carries the verifier pins.
  let formulaRaw ← readRequired ("Formula/tl.rb" : FilePath)
  outs := outs ++ [check "release identity: the Homebrew formula exists" formulaRaw.isOk s!"{formulaRaw}"]
  -- The fifth home of the pin, and the one the scripted verifier actually
  -- reads: two inert lines a POSIX shell can take without a JSON parser. It
  -- carries the verifier pins for the same reason install.sh does.
  let pinRaw ← readRequired ("release/identity.pin" : FilePath)
  outs := outs ++ [check "release identity: the two-line pin exists" pinRaw.isOk s!"{pinRaw}"]
  let docs := [("VERIFYING.md", verifyingRaw, allPins), ("ADR-0006", distributionRaw, allPins),
    ("ADR-0014", threatRaw, allPins), ("install.sh", installerRaw, verifierPins),
    ("Formula/tl.rb", formulaRaw, verifierPins),
    ("release/identity.pin", pinRaw, verifierPins)]
  for (name, raw, pins) in docs do
    match raw with
    | .error _ => pure ()
    | .ok content =>
        for (label, value) in pins do
          outs := outs ++ [check s!"release identity: {name} carries {label} pin"
            (has content value) s!"{name} does not contain canonical {label} value {value}"]
  -- The escape hatch has one name. Two spellings across the installer and the
  -- scripted procedure would leave a user who read the documented one silently
  -- running the check they meant to skip, or vice versa.
  let verifierScriptRaw ← readRequired ("scripts/verify-release-artifacts.sh" : FilePath)
  for (name, raw) in [("install.sh", installerRaw),
      ("scripts/verify-release-artifacts.sh", verifierScriptRaw)] do
    match raw with
    | .error e => outs := outs ++ [check s!"release identity: {name} is readable" false e]
    | .ok content =>
        outs := outs ++ [
          check s!"release identity: {name} uses the documented skip variable"
            (has content "TL_INSTALL_SKIP_SIGNATURE")
            s!"{name} does not mention TL_INSTALL_SKIP_SIGNATURE, the escape hatch ADR-0006 and VERIFYING.md name",
          check s!"release identity: {name} has no second name for the skip variable"
            (!has content "TL_VERIFY_SKIP_SIGNATURE")
            s!"{name} still mentions TL_VERIFY_SKIP_SIGNATURE — one escape hatch, one name"]
  -- The transparency-log bypass is checked behaviourally rather than here.
  -- Both shell verifiers now embed a stub cosign that *rejects* the flag, so
  -- the string legitimately appears in each file and a text scan would report
  -- the guard as the violation. Each script's `--selftest` asserts on the
  -- arguments actually passed, which is the property that matters.
  return outs

/-! ## The release plan, and the documents that describe it

`release/plan.json` is where "which channels does a release actually publish"
is written, and several documents now state the answer in prose. This guards
the two things that would silently diverge: the file's own shape, and whether
VERIFYING.md still tells a user the same thing the file says.

`enabled` and `plannedFor` are exclusive by construction — an enabled channel
has no future version to name, and a deferred one must name the release it is
planned for so deferral cannot decay into abandonment. -/

def releasePlanTests : IO (List Outcome) := do
  let raw ← readRequired ("release/plan.json" : FilePath)
  let some text := raw.toOption
    | return [check "release plan: release/plan.json exists" false s!"{raw}"]
  let some plan := (Json.parse text).toOption
    | return [check "release plan: release/plan.json parses as JSON" false text]
  let rows := jArr plan "channels"
  let named (name : String) : Option Json :=
    rows.find? fun row => jStr row "channel" == some name
  let mut outs := [
    check "release plan: release/plan.json parses as JSON" true,
    checkEq "release plan: every ADR-0006 channel has exactly one row" rows.length 4]
  -- v0.1.0 publishes through these two and defers the other two. The values are
  -- pinned rather than merely read: VERIFYING.md tells users npm and Homebrew
  -- are not published, and flipping a channel on without revisiting that
  -- sentence would make the document wrong in the direction users act on.
  for (channel, wantEnabled) in
      [("github-release", true), ("installer", true), ("npm", false), ("homebrew", false)] do
    match named channel with
    | none => outs := outs ++ [check s!"release plan: '{channel}' has a row" false
        s!"release/plan.json has no row for the channel {channel}"]
    | some row =>
        let enabled := (row.getObjVal? "enabled" |>.toOption).bind (·.getBool?.toOption)
        let plannedFor := jStr row "plannedFor"
        -- Read off the row's own two fields, not off `wantEnabled`. Comparing
        -- against the expectation would make this row restate the one above it
        -- and say nothing about the file: an `enabled` channel that still
        -- carried a `plannedFor` passed it.
        let exclusive := match enabled, plannedFor with
          | some true, none => true
          | some false, some _ => true
          | _, _ => false
        outs := outs ++ [
          checkEq s!"release plan: '{channel}' is {if wantEnabled then "enabled" else "deferred"}"
            enabled (some wantEnabled),
          check s!"release plan: '{channel}' names a target release iff it is deferred"
            exclusive
            s!"channel {channel} has enabled={enabled} and plannedFor={plannedFor}; a deferred channel must name the release it is planned for, an enabled one must not, and every row must state `enabled`"]
  -- A deferral has to point forwards. `plannedFor` parses as a version, but a
  -- version already shipped is not a deferral — it is a channel that quietly
  -- missed its release and would keep saying "planned for 0.2.0" through 0.2.0
  -- and everything after it.
  --
  -- Decided by the model rather than re-derived here. `tlrelease plan-deferrals`
  -- applies the same rule to the tag at release time, and two definitions of
  -- "still ahead" would eventually disagree about whether a release may be cut.
  -- The failure text is the list of offending messages, so a plan that stopped
  -- parsing reports that rather than an empty sweep.
  outs := outs ++ [
    checkEq s!"release plan: no channel is deferred to a release {Tl.Cli.productVersion} has already reached"
      (match Release.ReleasePlan.parse "release/plan.json" text,
             Release.Version.parse "the product version" Tl.Cli.productVersion with
       | .ok plan, .ok current =>
           (plan.staleDeferrals current).map fun row =>
             Release.ReleasePlan.staleDeferralMessage row.1 row.2 current
       | .error message, _ => [message]
       | _, .error message => [message])
      []]
  -- The user-facing half. A reader deciding how to install tl reads this
  -- sentence, so it is the one that must not outlive the decision behind it.
  let verifying ← readRequired ("VERIFYING.md" : FilePath)
  match verifying with
  | .error e => outs := outs ++ [check "release plan: VERIFYING.md is readable" false e]
  | .ok content =>
      outs := outs ++ [
        check "release plan: VERIFYING.md says npm and Homebrew are not published yet"
          (has content "npm and Homebrew are **not published in v0.1.0**")
          "VERIFYING.md no longer states which channels v0.1.0 publishes through"]
  return outs

/-! ## Privileged release jobs are reachable only from a pushed tag

`github.ref_type == 'tag'` is satisfied by a `workflow_dispatch` against a tag
ref, and by any trigger added later that can name one. The `stamp` job refuses
that particular combination, but a rehearsal should be *incapable* of signing
rather than dependent on an upstream job having refused first — so every job
that mints an OIDC token, writes to the repository, or reads a secret carries
the full `push` + tag condition.

The guard is stated over what makes a job privileged rather than over a list of
job names, so a privileged job added later is covered without anyone
remembering to extend this test. -/

private def dropIndent (line : String) : String :=
  String.ofList (line.toList.dropWhile (· == ' '))

private def trimmed (text : String) : String := text.trimAscii.toString

private def dropFromComment : List Char → Option Char → List Char
  | [], _ => []
  | c :: rest, previous =>
      if c == '#' && (previous.isNone || previous == some ' ' || previous == some '\t') then []
      else c :: dropFromComment rest (some c)

/-- A line with any trailing comment removed, and both ends trimmed.

    Removing it rather than only refusing lines that *begin* with `#` is what
    makes `contents: write # create the release` read as a grant. Without this
    the value is `write # create the release`, which matches nothing, and a job
    silently stops counting as privileged the day someone annotates its
    permissions. -/
private def withoutComment (body : String) : String :=
  trimmed (String.ofList (dropFromComment body.toList none))

/-- A scalar with the quotes *around the whole of it* removed. YAML spells
    `write`, `"write"` and `'write'` identically, and a scan that knew only the
    first read a quoted permission as no permission at all. -/
private def unquote (text : String) : String :=
  if text.length ≥ 2 &&
      ((text.startsWith "\"" && text.endsWith "\"")
        || (text.startsWith "'" && text.endsWith "'")) then
    String.ofList ((text.toList.drop 1).dropLast)
  else text

/-- A `key: value` line split at the first colon, with YAML's semantically
    irrelevant quotes removed from both sides.

    Quoted control keys are not exotic to the YAML parser: `"if"` and `if`
    are the same key. Leaving quotes on the key made the policy parser assign
    them different authority, which is exactly the kind of syntax drift this
    guard exists to refuse. -/
private def keyValue (body : String) : String × String :=
  match body.splitOn ":" with
  | [] => ("", "")
  | key :: rest =>
      (unquote (trimmed key), unquote (trimmed (String.intercalate ":" rest)))

/-- A bare YAML key: a job name or a permission name, with nothing quoted,
    nested or flow-style about it.

    Uppercase belongs here because a GitHub job id may contain it. Refusing one
    did not make this guard stricter — it made the header unreadable, and an
    unreadable header folds its job into the one above and hands it that job's
    `if:`. Anything still unreadable is reported rather than folded. -/
private def isBareKey (name : String) : Bool :=
  !name.isEmpty && name.toList.all fun c =>
    ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9')
      || c == '-' || c == '_'

/-- Whether a workflow line actually *grants* privilege, as opposed to
    discussing it. Both files reason about `id-token: write` in prose — the
    build job's comment explains why it takes none — so a substring scan over
    the block would report every commented job as privileged and the guard
    would pass by accident.

    Stated over the *shape* of a grant rather than a list of four permission
    names. An earlier version enumerated them, which left `write-all` and any
    permission GitHub adds later invisible: a job could acquire a capability
    and drop out of this guard in the same edit. For the same reason the value
    is unquoted and the comment stripped before it is read, and a secret is
    recognised through the bracket form as well as the dotted one — each of
    those was a spelling that silently removed a job from this guard. -/
private def grantsPrivilege (line : String) : Bool :=
  let body := withoutComment (dropIndent line)
  if body.isEmpty then false
  else
    let (key, value) := keyValue body
    -- `<name>: write`, whatever <name> is and however the value is spelled.
    (isBareKey key && (value == "write" || value == "write-all"))
      -- The blanket grants.
      || body == "write-all"
      -- A secret reaching the job by any route: `secrets.NAME`, the bracket
      -- form `secrets['NAME']`, or a `secrets:` key of its own.
      || has body "secrets." || has body "secrets[" || key == "secrets"
      -- Flow style: `permissions: {contents: write}` on one line. Refused as a
      -- grant whatever it contains, because this scan reads block style and a
      -- form it cannot read must not pass for an absent one.
      || (key == "permissions" && has value "{")
      -- An alias or anchor may stand for a permission mapping. The guard does
      -- not interpret YAML indirection; it treats taking one here as a grant,
      -- so an alias cannot make a privileged job look unprivileged.
      || (key == "permissions" && (value.startsWith "*" || value.startsWith "&"))
      -- A protected environment. ADR-0028 puts every job that can mint a
      -- certificate this release's pin accepts, or that receives a publication
      -- secret, behind the same environment as the signing job — so naming one
      -- is itself the capability, whether or not the secret is spelled in this
      -- job's own YAML.
      || key == "environment"

/-- A top-level job block: the job's name and the lines belonging to it. -/
private structure JobBlock where
  name : String
  lines : List String

/-- A top-level job header — indented exactly two spaces, a bare name, then
    `:` and nothing but an optional comment. Tolerating the trailing comment
    matters: without it such a header is not recognised, the job folds into the
    preceding block, and it silently inherits that job's `if:` for the purposes
    of every check below. -/
private def jobHeader? (line : String) : Option String :=
  if !(line.startsWith "  ") || line.startsWith "   " then none
  else
    let body := dropIndent line
    if body.startsWith "#" then none
    else
      match body.splitOn ":" with
      | name :: rest =>
          let tail := dropIndent (String.intercalate ":" rest)
          if isBareKey name && (tail.isEmpty || tail.startsWith "#") then some name
          else none
      | [] => none

/-- A workflow's `jobs:` mapping, as this scan could read it. -/
private structure JobScan where
  jobs : List JobBlock
  /-- Lines sitting exactly where a top-level job header does that this scan
      cannot read as one. Reported rather than folded into the preceding job:
      a header this parser skips silently attributes its job's permissions to
      the job above and gives it that job's `if:`, so a privileged job could
      join the file already covered by somebody else's guard. -/
  unreadable : List String

/-- Split a workflow file into its top-level job blocks: everything after the
    column-zero `jobs:` key, up to the next column-zero key. -/
private def jobScan (content : String) : JobScan := Id.run do
  let mut inJobs := false
  let mut blocks : List JobBlock := []
  let mut unreadable : List String := []
  let mut current : Option (String × List String) := none
  for line in content.splitOn "\n" do
    if !inJobs then
      if line == "jobs:" then inJobs := true
      continue
    -- A column-zero key ends the `jobs:` mapping.
    if line != "" && !line.startsWith " " && !line.startsWith "#" then
      break
    match jobHeader? line with
    | some name =>
        if let some (n, ls) := current then blocks := blocks ++ [{ name := n, lines := ls.reverse }]
        current := some (name, [])
    | none =>
        -- Inside `jobs:`, a line indented exactly two spaces is a job header or
        -- it is nothing; a job's own keys sit at four. One this parser cannot
        -- read is therefore a header it must not pass over.
        if line.startsWith "  " && !line.startsWith "   "
            && !(withoutComment (dropIndent line)).isEmpty then
          unreadable := unreadable ++ [line]
        if let some (n, ls) := current then current := some (n, line :: ls)
  if let some (n, ls) := current then blocks := blocks ++ [{ name := n, lines := ls.reverse }]
  return { jobs := blocks, unreadable }

/-- The job's own `if:`, as one string — indented four spaces, so a step's `if:`
    is not it, and folded continuations (`if: >-` and the more-indented lines
    under it) are joined in. A condition too long for one line is exactly the
    case worth reading correctly, since that is what a condition acquires when
    it grows a second clause. -/
private def jobIf (block : JobBlock) : String :=
  let step := fun (acc : List String × Bool) (line : String) =>
    let (collected, taking) := acc
    let ownIf :=
      if line.startsWith "    " && !line.startsWith "     " then
        let (key, _) := keyValue (withoutComment (dropIndent line))
        key == "if"
      else false
    if ownIf then (collected ++ [line], true)
    else if taking && line.startsWith "      " then (collected ++ [line], true)
    else (collected, false)
  let (collected, _) := block.lines.foldl step ([], false)
  String.intercalate " " (collected.map fun line => withoutComment (dropIndent line))

/-- The condition itself: the job's `if:` with the key, any block-scalar
    indicator and any surrounding quotes removed, and runs of whitespace
    collapsed. Normalising here is what lets the caller compare against one
    canonical string instead of pattern-matching the ways YAML can spell it. -/
private def conditionOf (block : JobBlock) : String :=
  let raw := jobIf block
  let body := if raw.startsWith "if:" then String.ofList (raw.toList.drop 3) else raw
  let words := body.splitOn " " |>.filter fun w =>
    !w.isEmpty && w != ">-" && w != ">" && w != "|" && w != "|-"
  let joined := String.intercalate " " words
  -- Only the quotes *around the whole scalar*, never the ones inside it: an
  -- inverted condition has to be quoted, because `!` opens a YAML tag, and
  -- unwrapping that is what exposes the `!` to the comparison. Stripping every
  -- quote instead would also strip the literals in `== 'push'` and leave the
  -- canonical form unmatchable.
  if (joined.startsWith "\"" && joined.endsWith "\"")
      || (joined.startsWith "'" && joined.endsWith "'") then
    String.ofList ((joined.toList.drop 1).dropLast)
  else joined

/-- The workflow-level `permissions:` block, as its lines.

    Everything else here reads only the `jobs:` mapping, so a workflow-level
    default — which applies to every job that declares none — would be invisible
    to it. Rather than model inheritance, the caller requires the default to be
    exactly the read-only one: then a job is privileged exactly when its own
    block says so, which is the assumption the scan rests on.

    A blank line and a comment do not end a YAML block mapping, so neither ends
    this scan. One that stopped at the first annotation would report whatever it
    had read so far as the whole default, and a permission written underneath a
    comment would grant every job in the file something this guard never saw. -/
private def headerPermissions (content : String) : List String := Id.run do
  let header := (content.splitOn "\njobs:\n").headD content
  let mut inside := false
  let mut collected : List String := []
  for line in header.splitOn "\n" do
    let body := withoutComment line
    if body == "permissions:" && !line.startsWith " " then inside := true
    else if inside then
      if body.isEmpty then pure ()
      else if line.startsWith "  " then collected := collected ++ [body]
      else inside := false
  return collected

/-- Exactly the read-only default, not "contains `contents: read`". Adding
    `id-token: write` underneath leaves that substring intact and grants every
    job in the file a signing token. -/
private def defaultPermissionIsReadOnly (content : String) : Bool :=
  headerPermissions content == ["contents: read"]

private def guardExpression : String :=
  "github.event_name == 'push' && github.ref_type == 'tag'"

/-- Whether a job condition confines the job to a pushed tag.

    A narrow canonical shape, and every other form rejected. A substring test
    accepts `!(<guard>)`, which contains the guard and inverts it — the job then
    runs everywhere *except* a pushed tag. Requiring the guard as a *prefix* is
    not enough either: `&&` binds tighter than `||` in a GitHub expression, so
    `<guard> && true || github.event_name == 'schedule'` begins with the guard,
    narrows it with `&&`, and still runs on every scheduled run. Hence no `||`
    anywhere. A disjunction is refused rather than analysed, because the
    alternative is writing an expression evaluator in a drift guard. -/
private def narrowsToPushedTag (condition : String) : Bool :=
  (condition == guardExpression || condition.startsWith (guardExpression ++ " &&"))
    && !has condition "||"

/-! ## Failure propagation, and who it binds

GitHub sequences jobs and steps on success by default, and there are exactly two
ways to override that: `continue-on-error`, which reports a failed unit as
successful, and a status function in an `if:`, which runs a unit *because*
something before it failed. Either one, on the wrong unit, turns a failed
handoff, authentication or publication into a job the next one reads as green.

ADR-0028 binds the rule to two classes of job, and the second is the one a
reader would not guess. **Privileged**: a write permission, a secret, or the
protected environment. **Authority-output producer**: a job at least one of
whose outputs decides whether a privileged job runs, which already-produced
artifact it takes, or where it publishes. Moving a policy branch into an
apparently unprivileged producer does not move it out of the guard, and the
rule is transitive through `needs.*.outputs.*` — an output assembled from
another job's output carries the same weight.

What stays allowed is what the release actually needs: the build matrix's
best-effort leg is unprivileged and declares no outputs, so its job-level
`continue-on-error` is exactly the case the ADR preserves. -/

/-- A key at a job's own indentation: four spaces, and not more. -/
private def jobLevelKey? (line : String) : Option (String × String) :=
  if !(line.startsWith "    ") || line.startsWith "     " then none
  else
    let body := withoutComment (dropIndent line)
    if body.isEmpty then none else
      let (key, value) := keyValue body
      if isBareKey key then some (key, value) else none

/-- A key belonging to a step: either the first key on the `- ` line that opens
    one, or a key of the step's own mapping.

    Both forms are read because `- continue-on-error: true` and a
    `continue-on-error:` line under a `- name:` are the same declaration, and a
    scan that knew only the second would be walked around by writing the
    first. -/
private def stepLevelKey? (line : String) : Option (String × String) :=
  let body := withoutComment line
  if body.isEmpty then none
  else
    let inner :=
      if line.startsWith "      - " then some (dropIndent (String.ofList (body.toList.drop 2)))
      else if line.startsWith "        " then some body
      else none
    match inner with
    | none => none
    | some text =>
        let (key, value) := keyValue text
        if isBareKey key then some (key, value) else none

/-- The `name: value` rows of a job's `outputs:` mapping.

    Read by tracking which job-level key is open, so a `needs.*.outputs.*`
    reference in an `env:` block is not mistaken for an output definition. -/
private def outputEntries (block : JobBlock) : List (String × String) := Id.run do
  let mut inside := false
  let mut rows : List (String × String) := []
  for line in block.lines do
    if (withoutComment line).isEmpty then continue
    match jobLevelKey? line with
    | some (key, _) => inside := key == "outputs"
    | none =>
        if inside && line.startsWith "      " then
          let (key, value) := keyValue (withoutComment (dropIndent line))
          if isBareKey key then rows := rows ++ [(key, value)]
  return rows

/-- The leading run of characters a YAML key or a GitHub identifier is made
    of, which is how a reference is ended without knowing what follows it. -/
private def identifierHead (text : String) : String :=
  String.ofList (text.toList.takeWhile fun c =>
    ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9')
      || c == '-' || c == '_')

private def withoutSpaces (text : String) : String :=
  String.ofList (text.toList.filter fun c => c != ' ' && c != '\t')

/-- Every `needs.<job>.outputs.<name>` in some text, as pairs. -/
private def needsOutputRefs (text : String) : List (String × String) :=
  let compact := withoutSpaces text
  ((compact.splitOn "needs.").drop 1).filterMap fun tail =>
    let job := identifierHead tail
    let rest := String.ofList (tail.toList.drop job.length)
    if job.isEmpty || !rest.startsWith ".outputs." then none
    else
      let name := identifierHead (String.ofList (rest.toList.drop ".outputs.".length))
      if name.isEmpty then none else some (job, name)

/-- The lines of a block that belong to some `if:` expression — the key line
    and every more-indented line continuing it, so a folded condition is read
    whole rather than at its first line. -/
private def conditionLines (lines : List String) : List String := Id.run do
  let mut collected : List String := []
  let mut indent := 0
  let mut taking := false
  for line in lines do
    let body := withoutComment line
    let width := line.toList.takeWhile (· == ' ') |>.length
    if taking && width > indent && !body.isEmpty then
      collected := collected ++ [body]
    else if (keyValue body).1 == "if" then
      collected := collected ++ [body]
      taking := true
      indent := width
    else if !body.isEmpty then
      taking := false
  return collected

/-- The status functions that override GitHub's success-only sequencing.
    `success()` is here too: written as the whole condition it is redundant, and
    written beside one of the others it is what makes the expression look like
    an ordinary predicate. -/
private def statusFunctions : List String :=
  ["always()", "failure()", "cancelled()", "success()"]

private def namesStatusFunction (text : String) : Option String :=
  statusFunctions.find? (has (withoutSpaces text).toLower ·)

/-- A spelling the authority parser deliberately does not interpret.

    GitHub accepts bracket dereferences and case-insensitive context/property
    names. This guard has one canonical authority grammar instead: dot-form,
    lowercase `needs` and `outputs`. A bound job using another spelling is a
    refusal, never an authority edge silently omitted from the closure. -/
private def nonCanonicalAuthorityReference (text : String) : Bool :=
  let compact := withoutSpaces text
  let lower := compact.toLower
  let dotNeeds := has lower "needs."
  let bracketAfterNeeds :=
    ((lower.splitOn "needs.").drop 1).any fun tail => has tail "["
  has lower "needs["
    || (dotNeeds && (!has compact "needs." || bracketAfterNeeds
      || (has lower ".outputs." && !has compact ".outputs.")))

private def yamlControlIndirection (key value : String) : Bool :=
  (key == "if" || key == "continue-on-error")
    && (value.startsWith "*" || value.startsWith "&")

private def stepMappingIndirection (line : String) : Bool :=
  if line.startsWith "      - " then
    let item := withoutComment (String.ofList (line.toList.drop 8))
    item.startsWith "*" || item.startsWith "&"
  else false

/-- Which jobs produce an output some privileged job or some condition acts on.

    Two seeds and one closure. A reference inside any `if:` is authority-bearing
    because that expression decides whether a unit runs at all; a reference
    anywhere inside a privileged job is authority-bearing because that job holds
    the credential and the value is choosing what it acts on. The closure is the
    ADR's transitivity: an authority-bearing output assembled from another job's
    output makes that one authority-bearing too, so a policy branch cannot be
    moved one job upstream to get out of the guard.

    Iterated a bounded number of times rather than recursively: the edge
    relation is over a finite job list, so `jobs.length` rounds reach the
    fixpoint, and a bound the reader can see beats a termination argument. -/
private def authorityProducers (scan : JobScan) : List String := Id.run do
  let privilegedNames := (scan.jobs.filter (·.lines.any grantsPrivilege)).map (·.name)
  let mut authority : List (String × String) := []
  for block in scan.jobs do
    let conditions := conditionLines block.lines
    for line in conditions do
      authority := authority ++ needsOutputRefs line
    if privilegedNames.contains block.name then
      for line in block.lines do
        authority := authority ++ needsOutputRefs (withoutComment line)
  for _ in scan.jobs do
    let mut grown := authority
    for block in scan.jobs do
      for (name, definition) in outputEntries block do
        if authority.contains (block.name, name) then
          for reference in needsOutputRefs definition do
            if !grown.contains reference then grown := grown ++ [reference]
    authority := grown
  return (scan.jobs.filterMap fun block =>
    if (outputEntries block).any fun (name, _) => authority.contains (block.name, name) then
      some block.name
    else none)

/-- The two overrides, over the jobs the rule binds.

    Stricter than ADR-0028's minimum in one stated place: the ADR forbids
    step-level `continue-on-error` on the handoff and on every authentication,
    policy or publication step, and this forbids it on every step of a bound
    job. Deciding lexically which step is a "policy step" would be a list of
    command spellings — the shape this repository keeps deleting — so the
    narrower rule is the one that would rot. Relaxing this means classifying
    steps, not adding an exception. -/
private def failurePropagationViolations (scan : JobScan) : List String := Id.run do
  let privilegedNames := (scan.jobs.filter (·.lines.any grantsPrivilege)).map (·.name)
  let producers := authorityProducers scan
  let mut violations : List String := []
  for block in scan.jobs do
    let privileged := privilegedNames.contains block.name
    let producer := producers.contains block.name
    if !privileged && !producer then continue
    let because :=
      if privileged then "holds a credential" else "produces an output a privileged job acts on"
    for line in block.lines do
      if stepMappingIndirection line then
        violations := violations ++
          [s!"job '{block.name}' {because} uses an anchored or aliased whole step — the authority grammar cannot inspect the failure controls hidden in that mapping. Expand the step in this bound job."]
      match jobLevelKey? line with
      | some (key, value) =>
          if yamlControlIndirection key value then
            violations := violations ++
              [s!"job '{block.name}' {because} uses YAML indirection for {key} — the authority grammar does not resolve anchors or aliases. Write the condition or failure policy directly on the bound job so review and this guard see the same value."]
          else if key == "continue-on-error" then
            violations := violations ++
              [s!"job '{block.name}' {because} and sets continue-on-error: {value} — a failed handoff, authentication or publication would then be reported as a successful job before anything downstream could see it. Job-level best-effort is for an unprivileged builder none of whose outputs is authority-bearing."]
      | _ => pure ()
      match stepLevelKey? line with
      | some (key, value) =>
          if yamlControlIndirection key value then
            violations := violations ++
              [s!"job '{block.name}' {because} uses YAML indirection for a step's {key} — expand the anchor or alias in this bound job so failure propagation is explicit."]
          else if key == "continue-on-error" then
            violations := violations ++
              [s!"job '{block.name}' {because} and has a step with continue-on-error: {value} — the step reports success it did not have, and every step after it runs on that. Remove it; a step that may legitimately fail belongs in a separate unprivileged job."]
      | _ => pure ()
    for line in conditionLines block.lines do
      match namesStatusFunction line with
      | some named =>
          violations := violations ++
            [s!"job '{block.name}' {because} and its condition uses {named} — a status function overrides the implicit success-only sequencing, so the unit runs after something before it has already failed. A conditional business predicate relies on that implicit guard instead of rebuilding it."]
      | none => pure ()
  return violations

/-- Every way a workflow fails the pushed-tag rule; the empty list is the
    passing state.

    Stated over the text rather than over the file, so the rules that judge the
    committed workflow can also be driven with fabricated ones. The parser is
    the part of this guard most able to fail silently — a shape it cannot read
    produces no job, no privilege and no violation — so it is exercised against
    workflows written to break it rather than only against the one in the tree. -/

private def privilegeViolations (content : String) : List String := Id.run do
  let scan := jobScan content
  let mut violations : List String := []
  unless defaultPermissionIsReadOnly content do
    violations := violations ++
      [s!"the workflow-level permission default is not exactly `permissions:` / `contents: read` — it reads {headerPermissions content}, so a job declaring no permissions block may still be privileged and this scan would not see it"]
  for line in scan.unreadable do
    violations := violations ++
      [s!"'{line}' sits where a top-level job header does but is not one this scan can read, so it folds into the job above and inherits that job's `if:`"]
  for block in scan.jobs do
    for line in block.lines do
      if nonCanonicalAuthorityReference (withoutComment line) then
        violations := violations ++
          [s!"job '{block.name}' uses a non-canonical needs/output reference — write `needs.<job>.outputs.<name>` in lowercase dot form. Bracket or case-variant spellings are refused rather than omitted from the authority graph."]
      match jobLevelKey? line with
      | some ("outputs", value) =>
          if value.startsWith "*" || value.startsWith "&" then
            violations := violations ++
              [s!"job '{block.name}' defines outputs through YAML indirection — authority-output reachability requires the output names and definitions to be written directly in each job. Expand the anchor or alias so an edge cannot disappear from the graph."]
      | _ => pure ()
    if block.lines.any grantsPrivilege && !narrowsToPushedTag (conditionOf block) then
      violations := violations ++
        [s!"privileged job '{block.name}' has if: {conditionOf block} — it must be exactly `{guardExpression}`, optionally narrowed with `&&` and never widened with `||`. Anything else (a negation, a disjunction, a quoted form, another clause first) is refused rather than interpreted."]
  return violations ++ failurePropagationViolations scan

/-! ## The guard's own parser, against workflows written to defeat it

The rows above judge one file, and every one of them is quantified over a list
this parser produced: a shape the parser cannot read yields no job, no
privilege, and a clean sweep. So the parser is driven here with fabricated
workflows instead — each one differing from a passing workflow in exactly one
way, and each one a spelling that at some point *did* slip past.

Every row states which side it is on: a workflow the guard must accept, or one
it must refuse and the phrase the refusal must carry. -/

private def readOnlyHeader : String := "permissions:\n  contents: read\n"

/-- A whole workflow: a header, an ordinary unprivileged job, and the job under
    test. The `build` job is there so that a parser which found nothing would
    fail the accepting rows too. -/
private def workflowWith (header : String) (job : String) : String :=
  "on:\n  push:\n    tags: ['v*']\n\n" ++ header ++
  "\njobs:\n  build:\n    runs-on: ubuntu-latest\n    steps:\n      - run: echo build\n" ++ job

private def fabricated (job : String) : String := workflowWith readOnlyHeader job

/-- A job with a `contents: write` grant and whatever condition is given. -/
private def guardedJob (condition : String) : String :=
  "  publish:\n" ++ condition ++
  "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - run: echo publish\n"

private def properGuard : String :=
  "    if: github.event_name == 'push' && github.ref_type == 'tag'\n"

/-- A job with no condition at all, carrying whatever body is given. Anything
    the scan reads as a grant here must be refused, because nothing confines it. -/
private def ungatedJob (body : String) : String :=
  "  publish:\n    runs-on: ubuntu-latest\n" ++ body ++ "    steps:\n      - run: echo publish\n"

/-- An unprivileged producer whose output a privileged job's condition reads,
    with whatever extra body is given attached to the producer. -/
private def producerWorkflow (producerBody : String) (producer : String) (output : String) :
    String :=
  s!"  {producer}:\n    runs-on: ubuntu-latest\n" ++ producerBody ++
  s!"    outputs:\n      {output}: " ++ "${{ steps.plan.outputs." ++ output ++ " }}\n" ++
  "    steps:\n      - id: plan\n        run: echo plan\n" ++
  s!"  publish:\n    needs: [{producer}]\n" ++
  "    if: github.event_name == 'push' && github.ref_type == 'tag' && needs." ++ producer ++
  ".outputs." ++ output ++ " == 'true'\n" ++
  "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - run: echo publish\n"

private def workflowGuardTests : List Outcome :=
  -- (label, workflow, the phrase a refusal must carry — none means it must pass)
  let cases : List (String × String × Option String) := [
    ("the canonical guard passes",
      fabricated (guardedJob properGuard), none),
    ("a guard narrowed with && passes",
      fabricated (guardedJob
        "    if: github.event_name == 'push' && github.ref_type == 'tag' && github.repository == 'o/r'\n"),
      none),
    ("a folded condition is read across its continuation lines",
      fabricated (guardedJob
        "    if: >-\n      github.event_name == 'push' && github.ref_type == 'tag'\n      && needs.gates.outputs.npm == 'true'\n"),
      none),
    -- `&&` binds tighter than `||`, so this begins with the guard, narrows it,
    -- and still runs on every scheduled run.
    ("a guard widened with || after an && is refused",
      fabricated (guardedJob
        "    if: github.event_name == 'push' && github.ref_type == 'tag' && true || github.event_name == 'schedule'\n"),
      some "never widened with `||`"),
    ("an inverted guard is refused",
      fabricated (guardedJob
        "    if: \"!(github.event_name == 'push' && github.ref_type == 'tag')\"\n"),
      some "privileged job 'publish'"),
    ("a guard reached only as the second disjunct is refused",
      fabricated (guardedJob
        "    if: github.event_name == 'schedule' || (github.event_name == 'push' && github.ref_type == 'tag')\n"),
      some "privileged job 'publish'"),
    ("a privileged job with no condition at all is refused",
      fabricated (ungatedJob "    permissions:\n      contents: write\n"),
      some "privileged job 'publish'"),
    -- The spellings of a grant. Each of these once read as *no* grant, which
    -- dropped the job out of the guard rather than failing it.
    ("a quoted permission value is still a grant",
      fabricated (ungatedJob "    permissions:\n      contents: \"write\"\n"),
      some "privileged job 'publish'"),
    ("a single-quoted permission value is still a grant",
      fabricated (ungatedJob "    permissions:\n      id-token: 'write'\n"),
      some "privileged job 'publish'"),
    ("quoted permission keys are still grants",
      fabricated (ungatedJob "    \"permissions\":\n      \"contents\": write\n"),
      some "privileged job 'publish'"),
    ("a permission annotated with a trailing comment is still a grant",
      fabricated (ungatedJob "    permissions:\n      contents: write # create the release\n"),
      some "privileged job 'publish'"),
    ("the bracket form of a secret is still a grant",
      fabricated (ungatedJob "    env:\n      GH_TOKEN: ${{ secrets['TAP_TOKEN'] }}\n"),
      some "privileged job 'publish'"),
    ("the dotted form of a secret is still a grant",
      fabricated (ungatedJob "    env:\n      GH_TOKEN: ${{ secrets.TAP_TOKEN }}\n"),
      some "privileged job 'publish'"),
    ("inherited secrets are a grant",
      fabricated ("  publish:\n    uses: ./.github/workflows/other.yml\n    secrets: inherit\n"),
      some "privileged job 'publish'"),
    ("a flow-style permissions block is a grant whatever it contains",
      fabricated (ungatedJob "    permissions: {contents: write}\n"),
      some "privileged job 'publish'"),
    ("a blanket write-all is a grant",
      fabricated (ungatedJob "    permissions: write-all\n"),
      some "privileged job 'publish'"),
    -- Job headers. A header this scan cannot read is the worst case: the job
    -- folds into the one above and is judged by that job's condition.
    ("a job id containing uppercase is read, not folded into the job above",
      fabricated (guardedJob properGuard ++
        "  publishMirror:\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - run: echo mirror\n"),
      some "privileged job 'publishMirror'"),
    ("a quoted job header is refused rather than folded",
      fabricated ("  \"publish\":\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n"),
      some "is not one this scan can read"),
    ("a flow-style job header is refused rather than folded",
      fabricated ("  publish: {runs-on: ubuntu-latest}\n"),
      some "is not one this scan can read"),
    -- What must *not* be refused: a job that takes nothing, and one that only
    -- talks about privilege.
    ("an unprivileged job needs no condition",
      fabricated (ungatedJob "    env:\n      LEVEL: info\n"), none),
    ("discussing a permission in a comment is not taking one",
      fabricated (ungatedJob
        "    # this job takes none; contents: write would let it publish\n"),
      none),
    -- The workflow-level default, which licenses reading only the jobs.
    ("a default that grants more than read is refused",
      workflowWith "permissions:\n  contents: read\n  id-token: write\n" (guardedJob properGuard),
      some "permission default"),
    -- A comment does not end a YAML block mapping, so it must not end this scan.
    ("a comment inside the default block does not hide what follows it",
      workflowWith "permissions:\n  contents: read\n# needed to mint the token\n  id-token: write\n"
        (guardedJob properGuard),
      some "permission default"),
    ("a blank line inside the default block does not hide what follows it",
      workflowWith "permissions:\n  contents: read\n\n  id-token: write\n" (guardedJob properGuard),
      some "permission default"),
    ("a flow-style default is refused rather than read as absent",
      workflowWith "permissions: {}\n" (guardedJob properGuard),
      some "permission default"),
    ("a read-all default is refused rather than read as read-only",
      workflowWith "permissions: read-all\n" (guardedJob properGuard),
      some "permission default"),
    ("no default at all is refused",
      workflowWith "" (guardedJob properGuard), some "permission default"),
    -- Naming a protected environment is itself the capability: it is what puts
    -- a job behind the same gate as signing, and the secret it receives need
    -- not be spelled in this job's own YAML.
    ("a protected environment is a grant",
      fabricated (ungatedJob "    environment: release\n"),
      some "privileged job 'publish'"),
    ("a permission mapping reached through an alias is still a grant",
      fabricated (
        "  anchor:\n" ++ properGuard ++
        "    runs-on: ubuntu-latest\n    permissions: &write\n      contents: write\n    steps:\n      - run: echo anchor\n" ++
        "  publish:\n    runs-on: ubuntu-latest\n    permissions: *write\n    steps:\n      - run: echo publish\n"),
      some "privileged job 'publish'"),
    -- Failure propagation. Both overrides, on both classes of job the rule
    -- binds, and each of them a shape that reports a failure as a success.
    ("a privileged guard narrowed with a status function is refused",
      fabricated (guardedJob
        "    if: github.event_name == 'push' && github.ref_type == 'tag' && !cancelled()\n"),
      some "status function"),
    ("a privileged job with job-level continue-on-error is refused",
      fabricated (guardedJob properGuard ++
        "  publishTwo:\n" ++ properGuard ++
        "    runs-on: ubuntu-latest\n    continue-on-error: true\n    permissions:\n      contents: write\n    steps:\n      - run: echo publish\n"),
      some "job 'publishTwo' holds a credential and sets continue-on-error"),
    ("a privileged step with continue-on-error is refused",
      fabricated ("  publish:\n" ++ properGuard ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - name: publish\n        continue-on-error: true\n        run: echo publish\n"),
      some "has a step with continue-on-error"),
    ("a quoted continue-on-error key is the same refusal",
      fabricated ("  publish:\n" ++ properGuard ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - name: publish\n        \"continue-on-error\": true\n        run: echo publish\n"),
      some "has a step with continue-on-error"),
    -- The same declaration written as the first key of the step, which a scan
    -- that only knew the mapping form would walk straight past.
    ("a privileged step's continue-on-error on the dash line is refused",
      fabricated ("  publish:\n" ++ properGuard ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - continue-on-error: true\n        run: echo publish\n"),
      some "has a step with continue-on-error"),
    ("a privileged step conditioned on a status function is refused",
      fabricated ("  publish:\n" ++ properGuard ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - name: upload the diagnostics\n        if: always()\n        run: echo upload\n"),
      some "status function"),
    ("quoted and case-varied status syntax is still refused",
      fabricated ("  publish:\n" ++ properGuard ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - name: upload the diagnostics\n        \"if\": ALWAYS()\n        run: echo upload\n"),
      some "status function"),
    ("a status condition reached through a YAML alias is refused",
      fabricated (
        "  ordinary:\n    runs-on: ubuntu-latest\n    steps:\n      - if: &after_failure always()\n        run: echo ordinary\n" ++
        "  publish:\n" ++ properGuard ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - if: *after_failure\n        run: echo diagnostics\n"),
      some "YAML indirection"),
    ("a whole step reached through a YAML alias is refused",
      fabricated (
        "  ordinary:\n    runs-on: ubuntu-latest\n    steps:\n      - &after_failure\n        if: always()\n        run: echo ordinary\n" ++
        "  publish:\n" ++ properGuard ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - *after_failure\n"),
      some "aliased whole step"),
    -- The class a reader would not guess. This job takes nothing, but a
    -- privileged job's condition reads its output, so a failure it reported as
    -- success would decide whether that job runs.
    ("an authority-output producer with continue-on-error is refused",
      fabricated (producerWorkflow "    continue-on-error: true\n" "gates" "npm"),
      some "job 'gates' produces an output a privileged job acts on and sets continue-on-error"),
    ("a bracket-form authority reference is refused instead of omitted",
      fabricated (
        "  gates:\n    runs-on: ubuntu-latest\n    continue-on-error: true\n    outputs:\n      npm: ${{ steps.plan.outputs.npm }}\n    steps:\n      - id: plan\n        run: echo npm\n" ++
        "  publish:\n    needs: [gates]\n" ++
        "    if: github.event_name == 'push' && github.ref_type == 'tag' && needs['gates']['outputs']['npm'] == 'true'\n" ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - run: echo publish\n"),
      some "non-canonical needs/output reference"),
    ("a case-variant authority reference is refused instead of omitted",
      fabricated (
        "  gates:\n    runs-on: ubuntu-latest\n    continue-on-error: true\n    outputs:\n      npm: ${{ steps.plan.outputs.npm }}\n    steps:\n      - id: plan\n        run: echo npm\n" ++
        "  publish:\n    needs: [gates]\n" ++
        "    if: github.event_name == 'push' && github.ref_type == 'tag' && NEEDS.gates.OUTPUTS.npm == 'true'\n" ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - run: echo publish\n"),
      some "non-canonical needs/output reference"),
    ("an output mapping reached through a YAML alias is refused",
      fabricated (
        "  plan:\n    runs-on: ubuntu-latest\n    outputs: &planned_outputs\n      npm: ${{ steps.read.outputs.npm }}\n    steps:\n      - id: read\n        run: echo npm\n" ++
        "  gates:\n    needs: [plan]\n    runs-on: ubuntu-latest\n    continue-on-error: true\n    outputs: *planned_outputs\n    steps:\n      - run: echo gates\n" ++
        "  publish:\n    needs: [gates]\n" ++
        "    if: github.event_name == 'push' && github.ref_type == 'tag' && needs.gates.outputs.npm == 'true'\n" ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - run: echo publish\n"),
      some "defines outputs through YAML indirection"),
    -- And moving the branch one job upstream does not move it out of the
    -- guard: `plan`'s output is what `gates`'s authority-bearing output is
    -- assembled from.
    ("a producer feeding a producer is refused transitively",
      fabricated (
        "  plan:\n    runs-on: ubuntu-latest\n    continue-on-error: true\n    outputs:\n      npm: ${{ steps.read.outputs.npm }}\n    steps:\n      - id: read\n        run: echo npm\n" ++
        "  gates:\n    needs: [plan]\n    runs-on: ubuntu-latest\n    outputs:\n      npm: ${{ needs.plan.outputs.npm }}\n    steps:\n      - run: echo gates\n" ++
        "  publish:\n    needs: [gates]\n" ++
        "    if: github.event_name == 'push' && github.ref_type == 'tag' && needs.gates.outputs.npm == 'true'\n" ++
        "    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n      - run: echo publish\n"),
      some "job 'plan' produces an output a privileged job acts on"),
    -- What must stay allowed, and is the reason the rule is not "no job may
    -- ever be best-effort": the build matrix's Best-effort leg takes nothing
    -- and declares no outputs.
    ("an unprivileged builder may be best-effort",
      fabricated (
        "  legs:\n    runs-on: ubuntu-latest\n    continue-on-error: true\n    steps:\n      - run: echo build\n"),
      none),
    -- An output nothing acts on is not authority-bearing, so declaring one does
    -- not make an ordinary job into a privileged one.
    ("a producer whose output nobody acts on may be best-effort",
      fabricated (
        "  measure:\n    runs-on: ubuntu-latest\n    continue-on-error: true\n    outputs:\n      seconds: ${{ steps.time.outputs.seconds }}\n    steps:\n      - id: time\n        run: echo seconds\n"),
      none)]
  cases.flatMap fun (label, content, expected) =>
    let violations := privilegeViolations content
    match expected with
    | none =>
        [checkEq s!"workflow guard: {label}" violations []]
    | some needle =>
        [check s!"workflow guard: {label}"
          (violations.any (has · needle))
          s!"expected a violation containing '{needle}'; got {violations}"]

def releaseWorkflowPrivilegeTests : IO (List Outcome) := do
  let path : FilePath := ".github/workflows/release.yml"
  let raw ← readRequired path
  let some content := raw.toOption
    | return [check "release workflow: the workflow is readable" false s!"{raw}"]
  let scan := jobScan content
  let names := scan.jobs.map (·.name)
  let privilegedNames := (scan.jobs.filter fun b => b.lines.any grantsPrivilege).map (·.name)
  -- Non-vacuity first. Every assertion below is universally quantified over a
  -- list this parser produced, so a parser that silently found nothing would
  -- report a clean sweep over an empty set.
  let mut outs := [
    check "release workflow: the job scan finds the build matrix"
      (names.contains "build") s!"parsed job names: {names}",
    check "release workflow: the privilege scan finds the signing job"
      (privilegedNames.contains "sign") s!"jobs found privileged: {privilegedNames}",
    check "release workflow: the privilege scan finds the publishing job"
      (privilegedNames.contains "publish-release") s!"jobs found privileged: {privilegedNames}",
    -- The build job reasons about `id-token: write` in a comment and takes
    -- none. If it ever reads as privileged, `grantsPrivilege` has regressed to
    -- a substring scan and the checks below stop meaning anything.
    check "release workflow: discussing a permission does not grant it"
      (!privilegedNames.contains "build") s!"jobs found privileged: {privilegedNames}",
    checkEq "release workflow: every privileged job is confined to a pushed tag"
      (privilegeViolations content) []]
  -- The channels a release publishes through are decided in release/plan.json,
  -- and each deferred channel's publish job must be gated on that decision
  -- rather than merely expected not to run. Without this the workflow ran
  -- `publish-npm` and `publish-homebrew` on any pushed tag while four
  -- documents said v0.1.0 published through neither: a v0.1.0 tag would have
  -- published the GitHub Release and then failed for a tap credential the
  -- release had deliberately deferred.
  for (channel, job) in [("npm", "publish-npm"), ("homebrew", "publish-homebrew")] do
    match scan.jobs.find? (·.name == job) with
    | none =>
        outs := outs ++ [check s!"release workflow: the '{job}' job exists" false
          s!"no job named {job}; if the channel was removed rather than deferred, drop this row with it"]
    | some block =>
        outs := outs ++ [
          check s!"release workflow: '{job}' is gated on the plan's '{channel}' channel"
            (has (jobIf block) s!"needs.gates.outputs.{channel} == 'true'")
            s!"job-level if: {jobIf block} — a channel release/plan.json disables must have no job to run, not a job that is merely not expected to",
          check s!"release workflow: '{job}' depends on the job that reads the plan"
            (block.lines.any fun line => line.startsWith "    needs:" && has line "gates")
            s!"{job} does not list `gates` in needs, so needs.gates.outputs is always empty — and an empty output compares unequal to 'true', which disables the channel for a reason nobody chose"]
  return outs ++ workflowGuardTests

/-! ## Build provenance (`tl version`, ADR-0006 "Tool versioning") -/

open Tl.Build (Provenance Kind)

/-- A stand-in stamp. Only `commit`/`dirty` decide the kind, so the pins are
    fixed here and varied only in the drift guard below. -/
private def sampleStamp (commit : String) (dirty : Bool) : Provenance :=
  { commit, dirty, toolchain := "leanprover/lean4:v4.33.0",
    manifestDigest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" }

def buildProvenanceTests : IO (List Outcome) := do
  let devClean := sampleStamp "" false
  -- A development build with a dirty tree still reports `development`: with no
  -- commit there is nothing for `dirty` to be relative to.
  let devDirty := sampleStamp "" true
  let stamped := sampleStamp "9af04c0ba31b6ecf3ad3ebe2f24fb86171a144c0" false
  let stampedDirty := sampleStamp "9af04c0ba31b6ecf3ad3ebe2f24fb86171a144c0" true
  let mut outs := [
    checkEq "build provenance: no commit is a development build" devClean.kind Kind.development,
    checkEq "build provenance: no commit stays development even with a dirty tree"
      devDirty.kind Kind.development,
    checkEq "build provenance: a commit from a clean tree is a clean build"
      stamped.kind Kind.clean,
    checkEq "build provenance: a commit from a dirty tree is a dirty build"
      stampedDirty.kind Kind.dirty,
    checkEq "build provenance: kind wire spellings"
      (Kind.development.name, Kind.dirty.name, Kind.clean.name)
      ("development", "dirty", "clean"),
    checkEq "build provenance: a development build has no short commit"
      devClean.shortCommit "",
    checkEq "build provenance: the short commit is the leading 12 hex characters"
      stamped.shortCommit "9af04c0ba31b" ]
  -- --json, per kind. `commit` is null exactly for a development build.
  for (label, p, expectKind, expectCommit) in
      [("development", devClean, "development", none),
       ("dirty", stampedDirty, "dirty", some stamped.commit),
       ("clean", stamped, "clean", some stamped.commit)] do
    let j := Tl.Cli.buildProvenanceJson p
    outs := outs ++ [
      checkEq s!"build provenance json ({label}): kind" (jStr j "kind") (some expectKind),
      checkEq s!"build provenance json ({label}): commit" (jStr j "commit") expectCommit,
      checkEq s!"build provenance json ({label}): dirty"
        ((jGet j "dirty").bind (·.getBool?.toOption)) (some p.dirty),
      checkEq s!"build provenance json ({label}): toolchain"
        (jStr j "toolchain") (some p.toolchain),
      checkEq s!"build provenance json ({label}): manifest digest"
        (jStr j "manifestDigest") (some p.manifestDigest)]
  -- Human output, per kind: parity with the json (same facts), and each kind's
  -- distinguishing claim actually stated.
  let humanDev := Tl.Cli.buildProvenanceHuman devClean
  let humanDirty := Tl.Cli.buildProvenanceHuman stampedDirty
  let humanClean := Tl.Cli.buildProvenanceHuman stamped
  outs := outs ++ [
    check "build provenance human (development): says no commit was stamped"
      (has humanDev "development build" && has humanDev "no source commit") humanDev,
    check "build provenance human (development): names no commit"
      (!has humanDev stamped.commit && !has humanDev stamped.shortCommit) humanDev,
    check "build provenance human (dirty): names the commit and disclaims it"
      (has humanDirty "dirty build" && has humanDirty stamped.shortCommit
       && has humanDirty "does not describe this binary") humanDirty,
    check "build provenance human (clean): names the commit"
      (has humanClean "clean build" && has humanClean stamped.shortCommit) humanClean]
  for (label, human) in [("development", humanDev), ("dirty", humanDirty), ("clean", humanClean)] do
    outs := outs ++ [
      check s!"build provenance human ({label}): carries the toolchain pin"
        (has human "leanprover/lean4:v4.33.0") human,
      check s!"build provenance human ({label}): carries the manifest digest prefix"
        (has human "0123456789ab") human]
  -- The compiled `tl version` payload: the additive `build` object joins the
  -- ADR-0020 shape without displacing `version` / `logFormat`, and human output
  -- carries the same build line (human/json parity).
  let out := Tl.Cli.cmdVersion
  let compiled := Tl.Build.current
  outs := outs ++ [
    checkEq "tl version: product version" (jStr out.data "version") (some "0.1.0"),
    checkEq "tl version: log format" ((jGet out.data "logFormat").bind (·.getNat?.toOption)) (some 2),
    check "tl version: the build object is present" (jGet out.data "build").isSome
      "tl version --json lost its build provenance",
    checkEq "tl version: the build object is this binary's stamp"
      ((jGet out.data "build").map (·.compress))
      (some (Tl.Cli.buildProvenanceJson compiled).compress),
    check "tl version: human output carries the build line"
      (has out.human (Tl.Cli.buildProvenanceHuman compiled)) out.human]
  -- The `build` object's key set, pinned exactly rather than by presence.
  --
  -- `Tests/CliTests.lean` used to compare the whole `tl version --json`
  -- envelope against a hand-written literal; it now splices
  -- `buildProvenanceJson` into the expected string, so both sides of that
  -- comparison move together for anything inside `build`. The rows above check
  -- that each of the five known fields is present and correct, which a sixth
  -- field satisfies just as well — so an added key would ship in every
  -- release's wire output with nothing failing. ADR-0020 froze this shape at
  -- the first release, and an additive field is a schema decision, not an
  -- incidental one.
  let buildKeys : List String :=
    match jGet out.data "build" with
    | some (Json.obj fields) => (fields.toArray.map (·.1)).toList
    | _ => []
  outs := outs ++ [
    checkEq "tl version: the build object has exactly the ADR-0006 fields"
      (buildKeys.mergeSort (· ≤ ·))
      ["commit", "dirty", "kind", "manifestDigest", "toolchain"]]
  -- Drift guard: the generated stamp's pins must match the checkout. Both are
  -- regenerated by `tlrelease stamp`.
  let toolchainOnDisk := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  let manifestBytes ← IO.FS.readBinFile "lake-manifest.json"
  let manifestOnDisk := Tl.Hash.Sha256.toHex (Tl.Hash.Sha256.digest manifestBytes)
  outs := outs ++ [
    checkEq "build provenance: the stamped toolchain matches lean-toolchain"
      compiled.toolchain toolchainOnDisk,
    checkEq "build provenance: the stamped manifest digest matches lake-manifest.json"
      compiled.manifestDigest manifestOnDisk,
    check "build provenance: a stamped commit is a full 40-character git object id"
      (compiled.commit.isEmpty || compiled.commit.length == 40)
      s!"stamped commit '{compiled.commit}' is neither empty nor a full object id",
    check "build provenance: a development stamp never claims dirtiness"
      (!compiled.commit.isEmpty || !compiled.dirty)
      "the generated stamp has no commit but reports dirty := true"]
  return outs

end Tl.Tests
