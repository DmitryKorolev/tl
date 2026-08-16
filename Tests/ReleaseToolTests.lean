/-
`Tests.ReleaseToolTests` — the `tlrelease` decision layer.

Outside the TCB and therefore tested rather than proved (ADR-0004), with one
exception noted where it applies: a pure verdict function whose failure mode is
a silent false negative carries a theorem instead, in the `Verify/Proofs.lean`
style. Nothing here is a landmark claim — landmarks guard the *product's*
proved claims, and release administration is not the product.

Driven in-process against `release.Cli` rather than by spawning the binary:
the branches that matter are the refusals, and a refusal is easier to pin down
by its exit status and the text it teaches than by a process's output stream.
`release.Main` exists only so that this import does not collide with the
harness's own `main`.
-/
import Tests.Harness
import release.Cli

namespace Tl.Tests

open Lean (Json)
open Release

/-! ## JSON: typed access and deterministic rendering -/

private def cur : Cursor := { document := "fixture.json" }

private def errorOf : Except String α → String
  | .error message => message
  | .ok _ => "<no error>"

private def okOr (fallback : String) : Except String String → String
  | .ok value => value
  | .error _ => fallback

private def mentions (result : Except String α) (needle : String) : Bool :=
  ((errorOf result).splitOn needle).length > 1

/-- The exact bytes `json.dump(sample, indent=2, sort_keys=True)` writes,
    followed by a newline — checked against real Python once, pinned here so
    the property survives without a Python dependency at test time. It covers
    sorted keys, two-space indent, empty containers, and every escape class:
    quote, backslash, tab, newline, carriage return, backspace, form feed, a
    C0 control, DEL, and non-ASCII.

    Byte-stability is the point. The manifest and the SBOM are hashed into
    `SHA256SUMS` and signed, so their bytes must be a function of their content
    and of nothing else. -/
private def goldenRender : String :=
  "{\n  \"alpha\": [\n    \"a\",\n    42,\n    true,\n    null\n  ],\n" ++
  "  \"backspaceFormfeed\": \"\\b\\f\",\n" ++
  "  \"deep\": [\n    {\n      \"x\": [\n        0\n      ]\n    }\n  ],\n" ++
  "  \"empty\": \"\",\n" ++
  "  \"escapes\": \"quote\\\" back\\\\slash tab\\tnew\\nret\\rctrl\\u0001 del\\u007f\",\n" ++
  "  \"nested\": {\n    \"a\": [],\n    \"b\": {}\n  },\n" ++
  "  \"unicode\": \"caf\\u00e9 \\u2014 na\\u00efve \\u2713\",\n" ++
  "  \"zeta\": 1\n}\n"

private def goldenSample : Json := Json.mkObj [
  ("zeta", Json.num 1),
  ("alpha", Json.arr #[Json.str "a", Json.num 42, Json.bool true, Json.null]),
  ("nested", Json.mkObj [("b", Json.mkObj []), ("a", Json.arr #[])]),
  ("escapes", Json.str "quote\" back\\slash tab\tnew\nret\rctrl\x01 del\x7f"),
  ("unicode", Json.str "caf\u00e9 \u2014 na\u00efve \u2713"),
  ("backspaceFormfeed", Json.str "\x08\x0c"),
  ("empty", Json.str ""),
  ("deep", Json.arr #[Json.mkObj [("x", Json.arr #[Json.num 0])]])]

private def jsonTests : List Outcome :=
  let obj := Json.mkObj [("name", Json.str "tl"), ("count", Json.num 2),
    ("flag", Json.bool true), ("blank", Json.str ""),
    ("list", Json.arr #[Json.str "a", Json.str "b"])]
  [ -- Rendering.
    checkEq "json: rendering is byte-for-byte the pinned document"
      (okOr "<error>" (render goldenSample)) goldenRender,
    -- The determinism that matters is not that a pure function repeats
    -- itself, but that the bytes do not depend on the order the object was
    -- built in. A signed manifest whose bytes tracked insertion order would
    -- hash differently for the same release.
    checkEq "json: the bytes do not depend on the order keys were inserted"
      (okOr "<a>" (render (Json.mkObj [("b", Json.num 2), ("a", Json.num 1)])))
      (okOr "<b>" (render (Json.mkObj [("a", Json.num 1), ("b", Json.num 2)]))),
    checkEq "json: an empty object renders inline" (okOr "" (render (Json.mkObj []))) "{}\n",
    checkEq "json: an empty array renders inline" (okOr "" (render (Json.arr #[]))) "[]\n",
    -- A non-integer number and an astral character are refused rather than
    -- guessed at: both would need a format decision this encoder should not
    -- make silently, and no release document contains either.
    check "json: a non-integer number is refused, not approximated"
      (mentions (render (Json.num ⟨15, 1⟩)) "only integers"),
    -- 100 spelled as 1000e-1. Refusing this would reject a perfectly good
    -- integer for how it happened to be represented.
    checkEq "json: an integer written with an exponent still renders as an integer"
      (okOr "<refused>" (render (Json.num ⟨1000, 1⟩))) "100\n",
    checkEq "json: a negative integer renders" (okOr "<refused>" (render (Json.num ⟨-7, 0⟩))) "-7\n",
    check "json: a character outside the BMP is refused rather than mis-encoded"
      (mentions (render (Json.str (String.singleton (Char.ofNat 0x1f600))))
        "Basic Multilingual Plane"),
    -- `U+` is hexadecimal by convention. In decimal the refusal named U+128512,
    -- which is past the largest code point there is, so the number a reader
    -- looked up was not the character that stopped the render.
    check "json: the astral refusal names the code point in hexadecimal"
      (mentions (render (Json.str (String.singleton (Char.ofNat 0x1f600)))) "U+1F600"),
    -- Reading: the happy paths.
    checkEq "json: a document parses" ((parseDocument cur "{\"a\": 1}").toOption.isSome) true,
    checkEq "json: a string field reads" (okOr "" (stringField cur obj "name")) "tl",
    checkEq "json: an absent optional field is none" (field? obj "absent").isNone true,
    checkEq "json: a present optional field is some" (field? obj "name").isSome true,
    check "json: an array field reads its elements"
      (match field cur obj "list" with
       | .ok (inner, found) => (asArray inner found).toOption.map (·.length) == some 2
       | .error _ => false),
    check "json: a boolean field reads"
      (match field cur obj "flag" with
       | .ok (inner, found) => (asBool inner found).toOption == some true
       | .error _ => false),
    check "json: an object reads as its fields"
      ((getObj cur obj).toOption.map (·.length) == some 5),
    -- Reading: every refusal, each naming the document and the path.
    check "json: malformed input is refused as invalid JSON"
      (mentions (parseDocument cur "{ not json") "is not valid JSON"),
    check "json: a malformed document says how to fix it"
      (mentions (parseDocument cur "{ not json") "Regenerate it"),
    check "json: an absent required field is named"
      (mentions (stringField cur obj "missing") "has no 'missing' field"),
    check "json: a refusal carries the document it came from"
      (mentions (stringField cur obj "missing") "fixture.json"),
    check "json: a field of the wrong type is refused"
      (mentions (stringField cur obj "count") "is not a string"),
    check "json: a wrong-type refusal carries the path to the field"
      (mentions (stringField cur obj "count") "fixture.json at count"),
    check "json: a non-object is refused where an object is required"
      (mentions (getObj cur (Json.str "not an object")) "is not a JSON object"),
    check "json: reading a field of a non-object is refused"
      (mentions (stringField cur (Json.arr #[]) "name") "is not a JSON object"),
    check "json: a non-boolean is refused where a boolean is required"
      (mentions (asBool cur (Json.str "true")) "is not a boolean"),
    check "json: a non-array is refused where an array is required"
      (mentions (asArray cur (Json.str "a")) "is not an array"),
    -- Empty is distinguished from absent: the shell's `not build.get(field)`
    -- could not tell them apart, so a hollowed-out record and a missing one
    -- produced the same message and the same non-diagnosis.
    check "json: an empty required string is refused"
      (mentions (nonEmptyStringField cur obj "blank") "is empty"),
    check "json: an empty string is refused differently from an absent one"
      (errorOf (nonEmptyStringField cur obj "blank")
        != errorOf (nonEmptyStringField cur obj "missing")),
    checkEq "json: a cursor with no path names just the document" cur.render "fixture.json",
    checkEq "json: a cursor path is rendered dotted"
      ((cur.at "targets").at "[0]").render "fixture.json at targets.[0]"]

/-- Run a dispatch and capture what it told each stream. Both are captured,
    because *which* stream a message reaches is part of the contract: usage
    goes to stderr on a refusal so a caller redirecting stdout still sees why,
    and to stdout on an explicit `--help` so it can be paged. -/
private def dispatchCaptured (args : List String) : IO (UInt32 × String × String) := do
  let out ← IO.mkRef { : IO.FS.Stream.Buffer }
  let err ← IO.mkRef { : IO.FS.Stream.Buffer }
  let status ← IO.withStdout (IO.FS.Stream.ofBuffer out) <|
    IO.withStderr (IO.FS.Stream.ofBuffer err) <| dispatch args
  return (status, String.fromUTF8! (← out.get).data, String.fromUTF8! (← err.get).data)

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- Drive one subcommand in-process, capturing its status and both streams.
    Looked up in the same table `dispatch` reads, so a command that stopped
    being registered fails these rows rather than silently skipping them. -/
private def runCommand (name : String) (args : List String) : IO (UInt32 × String × String) := do
  match commands.find? (·.name == name) with
  | none => return (255, "", s!"no command named {name}")
  | some command =>
      let out ← IO.mkRef { : IO.FS.Stream.Buffer }
      let err ← IO.mkRef { : IO.FS.Stream.Buffer }
      let status ← IO.withStdout (IO.FS.Stream.ofBuffer out) <|
        IO.withStderr (IO.FS.Stream.ofBuffer err) <| command.run args
      return (status, String.fromUTF8! (← out.get).data, String.fromUTF8! (← err.get).data)

/-! ## The typed model

Every constructor that can refuse has a row for each way it refuses. These are
the types that exist because the shell could hold a value that should not
exist, so a parser that quietly accepted one would put the whole port back
where it started. -/

/-- Precedence between two spellings, as an `Option` so that a fixture this
    parser refuses is distinguishable from a comparison that came out `false`.
    Every row below would otherwise pass vacuously the day one of its versions
    stopped parsing. -/
private def exceeds? (later earlier : String) : Option Bool :=
  match Version.parse "later" later, Version.parse "earlier" earlier with
  | .ok later, .ok earlier => some (later.exceeds earlier)
  | _, _ => none

private def modelTests : List Outcome :=
  let digest := String.ofList (List.replicate 64 'a')
  let commit := String.ofList (List.replicate 40 'b')
  let version (text : String) := Version.parse "v" text
  let rendered (text : String) : String :=
    match Version.parse "v" text with
    | .ok parsed => parsed.render
    | .error _ => "<refused>"
  [ -- Digests.
    check "model: a well-formed digest parses" (Sha256.parse "d" digest).toOption.isSome,
    check "model: a short digest is refused with its length"
      (mentions (Sha256.parse "d" "abc") "it is 3 characters"),
    check "model: a long digest is refused" (mentions (Sha256.parse "d" (digest ++ "a")) "65 characters"),
    check "model: an uppercase digest is refused rather than folded"
      (mentions (Sha256.parse "d" (String.ofList (List.replicate 64 'A'))) "lowercase"),
    check "model: a digest refusal says why folding is not done"
      (mentions (Sha256.parse "d" (String.ofList (List.replicate 64 'A')))
        "this pipeline does not control"),
    check "model: a non-hex digest is refused"
      (mentions (Sha256.parse "d" (String.ofList (List.replicate 64 'z'))) "hexadecimal"),
    -- Commits.
    check "model: a full object id parses" (Commit.parse "c" commit).toOption.isSome,
    check "model: an abbreviated commit is refused"
      (mentions (Commit.parse "c" "bbbbbbb") "40"),
    check "model: an abbreviated commit says why a prefix is not enough"
      (mentions (Commit.parse "c" "bbbbbbb") "agree on the whole commit"),
    check "model: a non-hex commit is refused"
      (mentions (Commit.parse "c" (String.ofList (List.replicate 40 'g'))) "hexadecimal"),
    -- Versions. The accepted shape is the pinned certificate expression's, so
    -- a version this refuses is one whose artifacts could not be signed.
    checkEq "model: a plain version round-trips" (rendered "1.2.3") "1.2.3",
    checkEq "model: a dot-separated prerelease round-trips" (rendered "1.2.3-rc.1") "1.2.3-rc.1",
    checkEq "model: a dash-separated prerelease round-trips" (rendered "1.2.3-rc-1") "1.2.3-rc-1",
    checkEq "model: an uppercase prerelease round-trips" (rendered "1.2.3-RC.1") "1.2.3-RC.1",
    checkEq "model: a zero version round-trips" (rendered "0.0.0") "0.0.0",
    check "model: a plain version is not a prerelease"
      ((version "1.2.3").toOption.map (·.isPrerelease) == some false),
    check "model: a suffixed version is a prerelease"
      ((version "1.2.3-rc.1").toOption.map (·.isPrerelease) == some true),
    check "model: a leading zero is refused" (mentions (version "01.2.3") "leading zero"),
    check "model: a two-component version is refused"
      (mentions (version "1.2") "not a release version"),
    -- The remedy has to be the shape the reader is being asked for. Showing the
    -- tag form to somebody editing `plannedFor` sent them to write `v0.2.0`
    -- into a field this parser then refuses on `v` as a numeric component — a
    -- correction whose only reward is a second, less legible refusal.
    check "model: a bare version's remedy shows the bare shape"
      (mentions (version "1.2") "Expected MAJOR.MINOR.PATCH"),
    check "model: a tag's remedy shows the tag shape"
      (mentions (Version.parseTag "t" "1.2.3") "Expected vMAJOR.MINOR.PATCH"),
    check "model: a four-component version is refused"
      (mentions (version "1.2.3.4") "not a release version"),
    check "model: a non-numeric component is refused" (mentions (version "1.x.3") "not a number"),
    check "model: an empty prerelease is refused" (mentions (version "1.2.3-") "prerelease suffix"),
    check "model: build metadata is refused" (mentions (version "1.2.3+build") "build metadata"),
    check "model: build metadata says nothing could be signed"
      (mentions (version "1.2.3+build") "could be signed"),
    checkEq "model: a version renders back as a tag"
      (match Version.parseTag "t" "v1.2.3-rc.1" with
       | .ok parsed => parsed.tag
       | .error _ => "<refused>") "v1.2.3-rc.1",
    check "model: a tag without the leading v is refused"
      (mentions (Version.parseTag "t" "1.2.3") "does not begin with 'v'"),
    check "model: an uppercase V is refused"
      (mentions (Version.parseTag "t" "V1.2.3") "does not begin with 'v'"),
    -- Precedence. The one question asked of it is whether a deferral names a
    -- release still ahead of the one being cut, and it decides whether a
    -- release aborts, so every rule of SemVer §11 that a plan can reach has a
    -- row. Comparing the triple alone got the prerelease rows wrong.
    checkEq "model: a later patch exceeds an earlier one" (exceeds? "1.2.4" "1.2.3") (some true),
    checkEq "model: an earlier patch does not exceed a later one"
      (exceeds? "1.2.3" "1.2.4") (some false),
    checkEq "model: a version does not exceed itself" (exceeds? "1.2.3" "1.2.3") (some false),
    checkEq "model: a later minor outranks a much later patch"
      (exceeds? "1.3.0" "1.2.99") (some true),
    checkEq "model: a later major outranks a much later minor"
      (exceeds? "2.0.0" "1.99.0") (some true),
    -- Numerically, not as text: "10" sorts before "9" lexically.
    checkEq "model: components compare numerically" (exceeds? "0.10.0" "0.9.0") (some true),
    -- The rule the triple-only comparison got wrong. Cutting 0.2.0-rc.1, a
    -- channel deferred to 0.2.0 is still a deferral to a release ahead of it.
    checkEq "model: a release exceeds its own prerelease"
      (exceeds? "0.2.0" "0.2.0-rc.1") (some true),
    checkEq "model: a prerelease does not exceed its own release"
      (exceeds? "0.2.0-rc.1" "0.2.0") (some false),
    checkEq "model: a later prerelease exceeds an earlier one"
      (exceeds? "1.2.3-rc.2" "1.2.3-rc.1") (some true),
    checkEq "model: numeric prerelease identifiers compare numerically"
      (exceeds? "1.2.3-rc.10" "1.2.3-rc.9") (some true),
    checkEq "model: more prerelease identifiers outrank a prefix of them"
      (exceeds? "1.2.3-alpha.1" "1.2.3-alpha") (some true),
    checkEq "model: a prefix does not outrank the longer identifier list"
      (exceeds? "1.2.3-alpha" "1.2.3-alpha.1") (some false),
    checkEq "model: alphanumeric prerelease identifiers compare by ASCII"
      (exceeds? "1.2.3-beta" "1.2.3-alpha") (some true),
    checkEq "model: an alphanumeric identifier outranks a numeric one"
      (exceeds? "1.2.3-alpha.beta" "1.2.3-alpha.1") (some true),
    -- The dash form parses as one identifier, not two, which is the reading
    -- the pinned certificate expression gives it.
    checkEq "model: a dash-separated prerelease compares as a single identifier"
      (exceeds? "1.2.3-rc-2" "1.2.3-rc-1") (some true),
    -- Tiers and targets.
    checkEq "model: the supported tier parses" (Tier.parse "t" "supported").toOption (some .supported),
    checkEq "model: the best-effort tier parses"
      (Tier.parse "t" "best-effort").toOption (some .bestEffort),
    check "model: an unknown tier is refused" (mentions (Tier.parse "t" "maybe") "not a support tier"),
    check "model: only the supported tier is release-blocking"
      (Tier.supported.releaseBlocking && !Tier.bestEffort.releaseBlocking),
    -- Channels.
    check "model: every channel's wire name parses back to it"
      (Channel.all.all fun channel => (Channel.parse "c" channel.wire).toOption == some channel),
    check "model: an unknown channel is refused"
      (mentions (Channel.parse "c" "flatpak") "not a distribution channel"),
    check "model: an unknown channel lists the ones that exist"
      (mentions (Channel.parse "c" "flatpak") "github-release"),
    -- Audit outcomes: the distinction the shell did not have.
    check "model: a verified prerequisite permits release" AuditOutcome.verified.permitsRelease,
    check "model: a carried assumption permits release"
      (AuditOutcome.carried "reviewer identity").permitsRelease,
    check "model: a missing prerequisite does not permit release"
      (!(AuditOutcome.missing "create it").permitsRelease),
    check "model: an operational error does not permit release"
      (!(AuditOutcome.operationalError "gh timed out").permitsRelease),
    check "model: an operational error is labelled differently from a missing one"
      ((AuditOutcome.operationalError "x").label != (AuditOutcome.missing "y").label)]

/-! ## The documents, real and fabricated

The real `release/*.json` files are parsed, because a model that no longer
describes them is a model of nothing. The refusals are driven with fabricated
text, because the point is to reach branches the committed files cannot. -/

private def digest64 : String := String.ofList (List.replicate 64 'a')
private def commit40 : String := String.ofList (List.replicate 40 'b')

/-- A complete build-metadata record. Fields are removed and corrupted from
    this one at a time, so every row differs from a passing document in exactly
    one way. -/
private def buildMetadataFields : List (String × String) :=
  [("target", "\"linux-x64\""), ("sha256", s!"\"{digest64}\""),
   ("commit", s!"\"{commit40}\""), ("tier", "\"supported\""),
   ("runner", "\"ubuntu-latest\""), ("toolchain", "\"leanprover/lean4:v4.33.0\""),
   ("lakeManifestSha256", s!"\"{digest64}\""),
   ("workflowRef", "\"owner/repo/.github/workflows/release.yml@refs/tags/v1.2.3\""),
   ("runId", "\"42\"")]

private def objectOf (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (key, value) => s!"\"{key}\": {value}") ++ "}"

private def completeBuildMetadata : String := objectOf buildMetadataFields

/-- The optional half of a build-metadata record: recorded for a reader, and
    deliberately unvalidated as *content* — but still a string or a malformed
    file. -/
private def optionalBuildFields : List String :=
  ["runnerOs", "runnerArch", "containerImage", "runAttempt"]

/-- One `release/targets.json` row. The platform is derived from the target's
    own name rather than fixed, because the manifest carries `os` and `cpu` for
    every row and both downstream channels project from them — a fixture where
    every target claimed one platform would make a formula with two identical
    blocks look correct. -/
private def targetRow (name : String) (tier : String) : String :=
  let os := if name.startsWith "darwin" then "darwin" else "linux"
  let cpu := if name.endsWith "arm64" then "arm64" else "x64"
  "{\"target\": \"" ++ name ++ "\", \"tier\": \"" ++ tier ++ "\", \"os\": \"" ++ os
    ++ "\", \"cpu\": \"" ++ cpu ++ "\"}"

private def targetsOf (rows : List String) : String :=
  "{\"targets\": [" ++ String.intercalate "," rows ++ "]}"

/-- A target matching `completeBuildMetadata` except where a row varies it, so
    each `PublishedTarget.of` row differs from a passing pairing in one way. -/
private def sampleTarget (name : String) (tier : Tier) : Target :=
  { name, tier, os := "linux", cpu := "x64", libc := some "glibc" }

private def sampleWorkflowRef : String :=
  "owner/repo/.github/workflows/release.yml@refs/tags/v1.2.3"

/-- The release-wide facts `completeBuildMetadata` agrees with, so a row that
    varies one of them differs from a passing comparison in exactly that one
    thing. -/
private def factsOf (run : RunContext) : Except String ReleaseFacts := do
  let commit ← Commit.parse "c" commit40
  let lakeManifestSha256 ← Sha256.parse "m" digest64
  return { commit, toolchain := "leanprover/lean4:v4.33.0", lakeManifestSha256, run }

private def sampleFacts : Except String ReleaseFacts :=
  factsOf (.inWorkflow sampleWorkflowRef "42")

private def planRow (channel : String) (enabled : Bool) (plannedFor : Option String) : String :=
  let base := s!"\"channel\": \"{channel}\", \"enabled\": {if enabled then "true" else "false"}"
  match plannedFor with
  | none => "{" ++ base ++ "}"
  | some planned => "{" ++ base ++ s!", \"plannedFor\": {planned}" ++ "}"

private def planOf (rows : List String) : String :=
  "{\"channels\": [" ++ String.intercalate "," rows ++ "]}"

private def defaultPlanRows : List String :=
  [planRow "github-release" true none, planRow "installer" true none,
   planRow "npm" false (some "\"0.2.0\""), planRow "homebrew" false (some "\"0.2.0\"")]

/-- Malformations of the two-line pin, each one thing wrong with an otherwise
    valid file. These are the same refusals `scripts/verify-release-artifacts.sh`
    applies to the file it reads; keeping both definitions in step is why the
    generator reads its own output back before writing it. -/
private def validExpression : String := "^https://github.com/x$"

/-- An identity carrying only the two fields a pin is made of; the rest are
    irrelevant here and stated once rather than at every call site. -/
private def identityOf (issuer expression : String) : Identity :=
  { repository := "r", npmPackage := "n", releaseWorkflow := "w"
    certificateOidcIssuer := issuer, certificateIdentityRegexp := expression }

private def documentTests : IO (List Outcome) := do
  let targetsText ← IO.FS.readFile "release/targets.json"
  let planText ← IO.FS.readFile "release/plan.json"
  let identityText ← IO.FS.readFile "release/identity.json"
  let pinText ← IO.FS.readFile "release/identity.pin"
  let targets := Targets.parse "release/targets.json" targetsText
  let plan := ReleasePlan.parse "release/plan.json" planText
  let identity := Identity.parse "release/identity.json" identityText
  let expectedPin := identity >>= renderPin
  -- Pair a target with the committed build record, varying one thing at a time.
  let publishedOf (target : Target) (digestText : String) : Except String PublishedTarget := do
    let build ← BuildMetadata.parse "b" completeBuildMetadata
    let digest ← Sha256.parse "d" digestText
    let facts ← sampleFacts
    PublishedTarget.of facts target digest build
  -- The deferral deadline, against the committed plan. `none` means a fixture
  -- stopped parsing, which must not read as "no stale deferrals".
  let staleAt (text : String) : Option (List String) :=
    match plan, Version.parse "current" text with
    | .ok plan, .ok current => some ((plan.staleDeferrals current).map (fun row => row.1.wire))
    | _, _ => none
  let mut outs := [
    -- The drift guard. `release/identity.pin` is what the scripted verifier
    -- and the installer selftest actually read, so a stale one is a signature
    -- check against the wrong identity — which looks like a verification
    -- failure rather than a broken verifier.
    checkEq "pin: the committed pin is exactly what the identity produces"
      pinText (okOr "<the identity itself was refused>" expectedPin),
    check "pin: the committed pin reads back through the verifier's own rules"
      (parsePin "release/identity.pin" pinText).toOption.isSome
      (errorOf (parsePin "release/identity.pin" pinText)),
    -- Generation refusals: a pin that cannot be read back unambiguously is
    -- never written, because the moment to catch it is generation.
    check "pin: an identity with an empty issuer produces no pin"
      (mentions (renderPin (identityOf "" validExpression)) "is empty"),
    check "pin: an issuer containing a line break produces no pin"
      (mentions (renderPin (identityOf "https://a\nhttps://b" validExpression)) "contains a line break"),
    check "pin: a line break is refused because it would change what the file says"
      (mentions (renderPin (identityOf "https://a\nhttps://b" validExpression)) "exactly two lines"),
    check "pin: a carriage return produces no pin"
      (mentions (renderPin (identityOf "https://a\r" validExpression))
        "contains a line break"),
    -- Printable ASCII, and nothing else. The shell verifier deletes exactly
    -- this range from the pin it reads and refuses whatever is left, so a value
    -- these two readers judged differently would be a pin one accepted and the
    -- other rejected — which looks like a broken signature rather than a broken
    -- pin. A NUL is the case a shell cannot even report: it vanishes on the way
    -- into a variable, so this side is the one that has to refuse it.
    check "pin: a tab produces no pin"
      (mentions (renderPin (identityOf "https://a\tb" validExpression))
        "outside printable ASCII"),
    check "pin: a NUL byte produces no pin"
      (mentions (renderPin (identityOf ("https://a" ++ String.singleton (Char.ofNat 0))
        validExpression)) "outside printable ASCII"),
    check "pin: a non-ASCII character produces no pin"
      (mentions (renderPin (identityOf "https://tokén.example" validExpression))
        "outside printable ASCII"),
    check "pin: a refusal for a stray byte says who reads the pin"
      (mentions (renderPin (identityOf "https://a\tb" validExpression)) "handed to cosign"),
    check "pin: a NUL byte in a pin being read back is refused"
      (mentions (parsePin "p" ("https://a" ++ String.singleton (Char.ofNat 0) ++ "\n"
        ++ validExpression ++ "\n")) "outside printable ASCII"),
    check "pin: a non-ASCII character in the expression is refused on read"
      (mentions (parsePin "p" ("https://a\n^https://tokén$\n")) "outside printable ASCII"),
    check "pin: an expression unanchored at the head produces no pin"
      (mentions (renderPin (identityOf "https://a" "https://github.com/x$"))
        "not anchored at ^"),
    check "pin: an expression unanchored at the tail produces no pin"
      (mentions (renderPin (identityOf "https://a" "^https://github.com/x"))
        "not anchored at $"),
    -- Reading refusals, matching the shell's one for one.
    check "pin: an empty pin is refused"
      (mentions (parsePin "p" "") "the pin is exactly two"),
    check "pin: a pin with only one line is refused"
      (mentions (parsePin "p" "https://a\n") "the pin is exactly two"),
    check "pin: a pin with three lines is refused"
      (mentions (parsePin "p" s!"https://a\n{validExpression}\nhttps://evil\n") "exactly two"),
    check "pin: a third line says why it is not merely ignored"
      (mentions (parsePin "p" s!"https://a\n{validExpression}\nhttps://evil\n")
        "a second, different pin"),
    check "pin: a pin with no trailing newline is refused"
      (mentions (parsePin "p" s!"https://a\n{validExpression}") "does not end with a newline"),
    check "pin: a pin with an empty first line is refused"
      (mentions (parsePin "p" s!"\n{validExpression}\n") "is empty"),
    check "pin: a pin with an unanchored expression is refused"
      (mentions (parsePin "p" "https://a\nhttps://github.com/x\n") "not anchored"),
    check "pin: a well-formed pin yields the issuer and the expression"
      ((parsePin "p" s!"https://a\n{validExpression}\n").toOption.map
        (fun i => (i.certificateOidcIssuer, i.certificateIdentityRegexp))
        == some ("https://a", validExpression)),
    -- The committed files, against the model that is about to decide over them.
    check "documents: the committed targets file parses" targets.toOption.isSome
      (errorOf targets),
    check "documents: it lists the four ADR-0006 targets"
      (targets.toOption.map (·.targets.length) == some 4),
    check "documents: three targets are release-blocking and one is not"
      (targets.toOption.map (fun t => (t.ofTier .supported).length) == some 3 &&
       targets.toOption.map (fun t => (t.ofTier .bestEffort).length) == some 1),
    -- Composed, never written out: the asset prefix followed by a target name
    -- reads as a tracker id to the task-ID lint, which is why the target file
    -- stores names bare and one function knows how an asset is spelled.
    check "documents: an asset name is the prefix composed with the target"
      (match targets.toOption.bind (·.find? "linux-x64") with
       | some target => target.asset == "tl" ++ "-" ++ "linux-x64"
       | none => false),
    check "documents: an unknown target is not found"
      (targets.toOption.bind (·.find? "solaris-sparc") |>.isNone),
    check "documents: the committed plan parses" plan.toOption.isSome (errorOf plan),
    check "documents: the plan enables exactly the GitHub release and the installer"
      (plan.toOption.map (·.enabledChannels) == some [.githubRelease, .installer]),
    check "documents: npm and Homebrew are deferred in the committed plan"
      (plan.toOption.map (fun p => p.enabled .npm || p.enabled .homebrew) == some false),
    check "documents: the committed identity parses" identity.toOption.isSome (errorOf identity),
    check "documents: the identity's owner is the tap namespace"
      (identity.toOption.map (·.owner) == some "DmitryKorolev"),
    -- Targets: the refusals.
    check "documents: a targets file with no rows is refused"
      (mentions (Targets.parse "t" "{\"targets\": []}") "lists no targets"),
    check "documents: an empty target list says why it is not a smaller release"
      (mentions (Targets.parse "t" "{\"targets\": []}") "builds nothing"),
    check "documents: a targets file with no targets key is refused"
      (mentions (Targets.parse "t" "{}") "has no 'targets' field"),
    check "documents: a malformed targets file is refused"
      (mentions (Targets.parse "t" "not json") "is not valid JSON"),
    check "documents: a target row missing its name is refused"
      (mentions (Targets.parse "t" "{\"targets\": [{\"tier\": \"supported\"}]}") "has no 'target' field"),
    check "documents: a target row whose libc is not a string is refused, not read as absent"
      (mentions (Targets.parse "t"
        "{\"targets\": [{\"target\": \"x\", \"tier\": \"supported\", \"os\": \"l\", \"cpu\": \"c\", \"libc\": 2}]}")
        "is not a string"),
    check "documents: a target row with no libc is accepted"
      (Targets.parse "t"
        "{\"targets\": [{\"target\": \"x\", \"tier\": \"supported\", \"os\": \"l\", \"cpu\": \"c\"}]}").toOption.isSome,
    check "documents: a target row with an unknown tier is refused"
      (mentions (Targets.parse "t"
        "{\"targets\": [{\"target\": \"x\", \"tier\": \"best\", \"os\": \"l\", \"cpu\": \"c\"}]}")
        "not a support tier"),
    -- Duplicate target names. Every lookup takes the first match, so a repeat
    -- makes the answer depend on file order — and if the two rows disagree on
    -- the tier they disagree about whether a missing artifact blocks a release.
    check "documents: two rows with distinct target names are accepted"
      (Targets.parse "t" (targetsOf [targetRow "linux-x64" "supported",
        targetRow "darwin-arm64" "supported"])).toOption.isSome,
    check "documents: a repeated target name is refused"
      (mentions (Targets.parse "t" (targetsOf [targetRow "linux-x64" "supported",
        targetRow "linux-x64" "supported"])) "the target 'linux-x64' 2 times"),
    check "documents: a repeated target name says why order must not decide"
      (mentions (Targets.parse "t" (targetsOf [targetRow "linux-x64" "supported",
        targetRow "linux-x64" "best-effort"])) "whether a missing artifact blocks the release"),
    check "documents: a third repeat is counted, not merely noticed"
      (mentions (Targets.parse "t" (targetsOf [targetRow "linux-x64" "supported",
        targetRow "linux-x64" "supported", targetRow "linux-x64" "supported"])) "3 times"),
    -- The plan: exclusivity, completeness, and uniqueness.
    check "documents: a plan enabling a channel that also names a target release is refused"
      (mentions (ReleasePlan.parse "p" (planOf
        [planRow "github-release" true (some "\"0.3.0\""), planRow "installer" true none,
         planRow "npm" false (some "\"0.2.0\""), planRow "homebrew" false (some "\"0.2.0\"")]))
        "both enabled and carrying plannedFor"),
    check "documents: a plan deferring a channel with no target release is refused"
      (mentions (ReleasePlan.parse "p" (planOf
        [planRow "github-release" true none, planRow "installer" true none,
         planRow "npm" false none, planRow "homebrew" false (some "\"0.2.0\"")]))
        "cannot decay into abandonment"),
    check "documents: a plan deferring a channel to an empty release is refused"
      (mentions (ReleasePlan.parse "p" (planOf
        [planRow "github-release" true none, planRow "installer" true none,
         planRow "npm" false (some "\"\""), planRow "homebrew" false (some "\"0.2.0\"")]))
        "not a release version"),
    -- A deferral has to name a release, not a mood. Both are non-empty
    -- strings; only one of them is a commitment anything can be checked
    -- against.
    check "documents: a plan deferring a channel to a non-version is refused"
      (mentions (ReleasePlan.parse "p" (planOf
        [planRow "github-release" true none, planRow "installer" true none,
         planRow "npm" false (some "\"banana\""), planRow "homebrew" false (some "\"0.2.0\"")]))
        "not a release version"),
    -- The GitHub Release is not a toggle: every other channel serves the same
    -- bytes, so switching it off describes no release rather than a smaller one.
    check "documents: a plan disabling the GitHub Release is refused"
      (mentions (ReleasePlan.parse "p" (planOf
        [planRow "github-release" false (some "\"9.9.9\""), planRow "installer" true none,
         planRow "npm" false (some "\"0.2.0\""), planRow "homebrew" false (some "\"0.2.0\"")]))
        "source of truth"),
    check "documents: a plan whose plannedFor is not a string is refused"
      (mentions (ReleasePlan.parse "p" (planOf
        [planRow "github-release" true none, planRow "installer" true none,
         planRow "npm" false (some "2"), planRow "homebrew" false (some "\"0.2.0\"")]))
        "is not a string"),
    check "documents: a plan missing a channel row is refused"
      (mentions (ReleasePlan.parse "p" (planOf defaultPlanRows.dropLast)) "has no row for the 'homebrew' channel"),
    check "documents: a missing row says why absence is not disablement"
      (mentions (ReleasePlan.parse "p" (planOf defaultPlanRows.dropLast)) "rather than merely absent"),
    check "documents: a plan with two rows for one channel is refused"
      (mentions (ReleasePlan.parse "p" (planOf (defaultPlanRows ++ [planRow "npm" true none])))
        "2 rows for the 'npm' channel"),
    check "documents: a duplicate row says why order must not decide"
      (mentions (ReleasePlan.parse "p" (planOf (defaultPlanRows ++ [planRow "npm" true none])))
        "depends on lookup order"),
    check "documents: a plan naming an unknown channel is refused"
      (mentions (ReleasePlan.parse "p" (planOf (defaultPlanRows ++ [planRow "flatpak" true none])))
        "not a distribution channel"),
    check "documents: a plan row with no enabled field is refused"
      (mentions (ReleasePlan.parse "p" "{\"channels\": [{\"channel\": \"npm\"}]}")
        "has no 'enabled' field"),
    check "documents: a plan row whose enabled is not a boolean is refused"
      (mentions (ReleasePlan.parse "p" "{\"channels\": [{\"channel\": \"npm\", \"enabled\": \"yes\"}]}")
        "is not a boolean"),
    -- Identity.
    check "documents: an identity missing a field is refused"
      (mentions (Identity.parse "i" "{\"repository\": \"a/b\"}") "has no 'npmPackage' field"),
    check "documents: an identity with an empty field is refused"
      (mentions (Identity.parse "i" "{\"repository\": \"\"}") "is empty"),
    -- Build metadata: the complete record, then every way to hollow it out.
    check "documents: a complete build-metadata record parses"
      (BuildMetadata.parse "b" completeBuildMetadata).toOption.isSome
      (errorOf (BuildMetadata.parse "b" completeBuildMetadata)),
    check "documents: absent optional fields default to empty rather than failing"
      ((BuildMetadata.parse "b" completeBuildMetadata).toOption.map (·.runnerOs) == some ""),
    check "documents: a non-object build-metadata record is refused"
      (mentions (BuildMetadata.parse "b" "[]") "is not a JSON object"),
    check "documents: a malformed build-metadata record is refused"
      (mentions (BuildMetadata.parse "b" "{") "is not valid JSON"),
    check "documents: a build-metadata record with a bad digest is refused"
      (mentions (BuildMetadata.parse "b"
        (objectOf (buildMetadataFields.map fun (k, v) => if k == "sha256" then (k, "\"abc\"") else (k, v))))
        "is not a SHA-256 digest"),
    check "documents: a build-metadata record with a bad commit is refused"
      (mentions (BuildMetadata.parse "b"
        (objectOf (buildMetadataFields.map fun (k, v) => if k == "commit" then (k, "\"abc\"") else (k, v))))
        "not a full git object id"),
    check "documents: a build-metadata record with an unknown tier is refused"
      (mentions (BuildMetadata.parse "b"
        (objectOf (buildMetadataFields.map fun (k, v) => if k == "tier" then (k, "\"gold\"") else (k, v))))
        "not a support tier"),
    -- Pairing a target with the evidence it was built. The three fields are
    -- independently plausible and only agree by accident otherwise, which is
    -- why the constructor is private and this is the only way in.
    check "documents: a target agreeing with its build record pairs"
      (publishedOf (sampleTarget "linux-x64" .supported) digest64).toOption.isSome
      (errorOf (publishedOf (sampleTarget "linux-x64" .supported) digest64)),
    checkEq "documents: a published target composes its asset name"
      ((publishedOf (sampleTarget "linux-x64" .supported) digest64).toOption.map (·.asset))
      (some ("tl" ++ "-" ++ "linux-x64")),
    check "documents: a build record from another leg is refused"
      (mentions (publishedOf (sampleTarget "darwin-arm64" .supported) digest64)
        "records target 'linux-x64'"),
    check "documents: a crossed build record says the legs were mixed up"
      (mentions (publishedOf (sampleTarget "darwin-arm64" .supported) digest64)
        "crossed between legs"),
    check "documents: a build record disagreeing about the tier is refused"
      (mentions (publishedOf (sampleTarget "linux-x64" .bestEffort) digest64)
        "records tier 'supported'"),
    check "documents: a tier disagreement says what the tier decides"
      (mentions (publishedOf (sampleTarget "linux-x64" .bestEffort) digest64)
        "whether a missing artifact blocks the release"),
    check "documents: an artifact hashing to something else is refused"
      (mentions (publishedOf (sampleTarget "linux-x64" .supported)
        (String.ofList (List.replicate 64 'c'))) "but its build leg recorded"),
    check "documents: a digest disagreement says nothing is signed"
      (mentions (publishedOf (sampleTarget "linux-x64" .supported)
        (String.ofList (List.replicate 64 'c'))) "Nothing is signed"),
    -- What became of a target. `absent` carries no evidence because there is
    -- none, and the two cases must not be distinguishable only by convention.
    checkEq "documents: a published outcome carries its target"
      ((TargetOutcome.published <$> (publishedOf (sampleTarget "linux-x64" .supported) digest64))
        |>.toOption.map (·.target.name)) (some "linux-x64"),
    check "documents: a published outcome carries its evidence"
      (((TargetOutcome.published <$> (publishedOf (sampleTarget "linux-x64" .supported) digest64))
        |>.toOption.bind (·.published?)).isSome),
    checkEq "documents: an absent outcome names its target"
      (TargetOutcome.absent (sampleTarget "darwin-x64" .bestEffort)).target.name "darwin-x64",
    check "documents: an absent outcome carries no evidence"
      ((TargetOutcome.absent (sampleTarget "darwin-x64" .bestEffort)).published?.isNone),
    -- The per-target asset names, composed in one place each.
    checkEq "documents: the build-metadata asset is named after its target"
      (sampleTarget "linux-x64" .supported).buildMetadataAsset "build-metadata-linux-x64.json",
    checkEq "documents: the link-audit asset is named after its target"
      (sampleTarget "linux-x64" .supported).linkAuditAsset "link-audit-linux-x64.txt",
    -- The deferral deadline. A deferral to a release that has shipped is a
    -- channel that was forgotten rather than postponed.
    checkEq "documents: the committed plan has no expired deferral at 0.1.0"
      (staleAt "0.1.0") (some []),
    checkEq "documents: a deferral to the release being cut has expired"
      (staleAt "0.2.0") (some ["npm", "homebrew"]),
    checkEq "documents: a deferral overtaken by a later release has expired"
      (staleAt "0.3.0") (some ["npm", "homebrew"]),
    -- The row the triple-only comparison got wrong: 0.2.0 is still ahead of
    -- 0.2.0-rc.1, so cutting the release candidate must not abort.
    checkEq "documents: a deferral to 0.2.0 survives cutting 0.2.0-rc.1"
      (staleAt "0.2.0-rc.1") (some []),
    check "documents: an expired deferral is told both versions and the two fixes"
      (match Version.parse "p" "0.2.0", Version.parse "c" "0.3.0" with
       | .ok planned, .ok current =>
           let message := ReleasePlan.staleDeferralMessage .npm planned current
           contains message "'npm'" && contains message "0.2.0" && contains message "0.3.0"
             && contains message "enable the channel" && contains message "plannedFor"
       | _, _ => false)]
  -- The optional build-metadata fields. Absent is a record that did not say;
  -- present-but-not-a-string is a record this generator cannot understand, and
  -- reading the second as the first is the conflation the whole module removes.
  for name in optionalBuildFields do
    let malformed := objectOf (buildMetadataFields ++ [(name, "2")])
    let present := objectOf (buildMetadataFields ++ [(name, "\"recorded\"")])
    outs := outs ++ [
      check s!"documents: build metadata whose optional '{name}' is not a string is refused"
        (mentions (BuildMetadata.parse "b" malformed) "is not a string"),
      check s!"documents: a malformed optional '{name}' names its own path"
        (mentions (BuildMetadata.parse "b" malformed) s!"b at {name}"),
      check s!"documents: a present optional '{name}' is accepted"
        (BuildMetadata.parse "b" present).toOption.isSome
        (errorOf (BuildMetadata.parse "b" present))]
  outs := outs ++ [
    checkEq "documents: a present optional field is read, not merely tolerated"
      ((BuildMetadata.parse "b"
        (objectOf (buildMetadataFields ++ [("runnerOs", "\"Linux\"")]))).toOption.map (·.runnerOs))
      (some "Linux")]
  -- One row per required field, absent and then blank. The shell tested all
  -- nine with `not build.get(field)`, which cannot tell those two apart — so a
  -- record blanked in either way produced one indistinguishable message.
  for (name, _) in buildMetadataFields do
    let without := objectOf (buildMetadataFields.filter fun (key, _) => key != name)
    let blanked := objectOf (buildMetadataFields.map fun (key, value) =>
      if key == name then (key, "\"\"") else (key, value))
    outs := outs ++ [
      check s!"documents: build metadata without '{name}' is refused"
        (mentions (BuildMetadata.parse "b" without) s!"has no '{name}' field"),
      check s!"documents: build metadata with a blank '{name}' is refused"
        (mentions (BuildMetadata.parse "b" blanked) "is empty"),
      check s!"documents: a blank '{name}' is refused differently from an absent one"
        (errorOf (BuildMetadata.parse "b" without) != errorOf (BuildMetadata.parse "b" blanked))]
  return outs

/-- Deletion guard for every non-private release contract theorem, on the same
    reasoning as `pinnedVerdictLogicTheorems` in Tests/VerifyTests.lean: they
    carry no landmark by design, because landmarks guard the *product's* proved
    claims and this is release administration. Private proof helpers are not
    separate contracts: the public theorem statements contain the properties
    they help prove, and may retain or replace that scaffolding freely. Naming
    every public contract here makes retiring one a compile error rather than a
    silent deletion. -/
private def pinnedReleaseVerdictTheorems : Unit :=
  let _ := @Release.Check.allHeld_iff_noFailures
  let _ := @Release.metadataAccepts_iff
  let _ := @Release.metadataFailures_isEmpty_iff
  let _ := @Release.manifestAccepts_iff
  let _ := @Release.manifestFailures_isEmpty_iff
  let _ := @Release.descriptionCoherent_iff
  let _ := @Release.descriptionProblems_isEmpty_iff
  let _ := @Release.Homebrew.formulaCovers_iff
  let _ := @Release.Homebrew.coverageBlockers_isEmpty_iff
  let _ := @Release.Homebrew.tapDisposition_identical_iff
  let _ := @Release.Homebrew.tapDisposition_absent_iff
  let _ := @Release.Policy.gateRuns_iff
  let _ := @Release.Policy.runAccepts_iff
  let _ := @Release.Policy.runFailures_isEmpty_iff
  let _ := @Release.Policy.publicationCommand_iff
  let _ := @Release.Policy.contributedEffects_eq
  let _ := @Release.Policy.effectsOf_ne_nil
  let _ := @Release.identityAccepts_iff
  let _ := @Release.auditPermits_iff
  let _ := @Release.auditBlockers_isEmpty_iff
  let _ := @Release.auditBlockers_partition
  let _ := @Release.versionProblems_isEmpty_iff
  let _ := @Release.channelDecisions_eq
  let _ := @Release.channelDecisions_lookup
  let _ := @Release.Write.OutputPath.components_ne_nil
  let _ := @Release.Write.decodeRow_encodeRow
  let _ := @Release.Write.decodeRow_landed_iff
  let _ := @Release.Write.accept_isOk_iff_landed
  let _ := @Release.Write.WriteOutcome.destination_replaced_iff_landed
  let _ := @Release.Write.WriteOutcome.staging_occupied_iff_retained
  ()

/-! ## The publication decision, end to end

`renderChannelOutputs` decides whether an immutable publication job runs, so
the four lines it emits are pinned exactly, for every combination of enabled
channels the plan can express. The theorems above characterise the decision;
these check that the rendering carries it unchanged to the workflow. -/

private def planTextOf (npm brew : Bool) : String :=
  let row (c : String) (on : Bool) (planned : Option String) :=
    let base := s!"\"channel\": \"{c}\", \"enabled\": {if on then "true" else "false"}"
    match planned with
    | none => "{" ++ base ++ "}"
    | some p => "{" ++ base ++ s!", \"plannedFor\": \"{p}\"" ++ "}"
  "{\"channels\": [" ++ String.intercalate ","
    [row "github-release" true none, row "installer" true none,
     row "npm" npm (if npm then none else some "0.2.0"),
     row "homebrew" brew (if brew then none else some "0.2.0")] ++ "]}"

private def channelOutputTests : List Outcome :=
  let expected (npm brew : Bool) : String :=
    "github-release=true\ninstaller=true\n" ++
    s!"npm={if npm then "true" else "false"}\nhomebrew={if brew then "true" else "false"}\n"
  ([(false, false), (true, false), (false, true), (true, true)].map fun (npm, brew) =>
    match ReleasePlan.parse "p" (planTextOf npm brew) with
    | .error message =>
        check s!"plan output: the plan with npm={npm} homebrew={brew} parses" false message
    | .ok plan =>
        checkEq s!"plan output: npm={npm} homebrew={brew} renders exactly four decided lines"
          (renderChannelOutputs plan) (expected npm brew)) ++
  [ -- Every channel appears, including the enabled ones. A workflow reading an
    -- output that was never emitted gets the empty string, which compares
    -- unequal to 'true' — so an omitted line disables a channel silently.
    check "plan output: every channel is named, not only the disabled ones"
      (match ReleasePlan.parse "p" (planTextOf false false) with
       | .ok plan => Channel.all.all fun c => ((renderChannelOutputs plan).splitOn s!"{c.wire}=").length == 2
       | .error _ => false)]

/-! ## The pin commands, end to end

`renderPin` and `parsePin` are covered above as functions. These drive the two
subcommands through real files, because the parts between the function and the
process — reading a path that is not there, writing one that cannot be written,
and the exit status each produces — are where a release step actually meets
this tool, and none of them is exercised by testing the pure core. -/

private def pinCommandTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let identityPath := (base / "identity.json").toString
  let pinPath := (base / "identity.pin").toString
  let realIdentity ← IO.FS.readFile "release/identity.json"
  IO.FS.writeFile identityPath realIdentity
  let run := runCommand
  let writePin (identity : String) (name : String) (dir : String) :=
    run "write-pin" ["--identity", identity, "--output", name, "--output-dir", dir]
  let (writeStatus, writeOut, _) ← writePin identityPath "identity.pin" base.toString
  let written ← IO.FS.readFile pinPath
  let (checkStatus, checkOut, _) ← run "check-pin" [identityPath, pinPath]
  -- Drift, which is the whole reason check-pin exists.
  IO.FS.writeFile pinPath "https://example.invalid\n^x$\n"
  let (driftStatus, _, driftErr) ← run "check-pin" [identityPath, pinPath]
  let (missingIdentity, _, missingIdentityErr) ←
    writePin (base / "absent.json").toString "identity.pin" base.toString
  let (missingPin, _, missingPinErr) ← run "check-pin" [identityPath, (base / "absent.pin").toString]
  -- An identity anchored at the head but not the tail: the generator must
  -- refuse rather than write a pin the verifier would reject. The tail is the
  -- half that was historically dropped, and a tag name may contain '/', so
  -- trailing content past the pinned identity is reachable.
  let badIdentityPath := (base / "bad.json").toString
  IO.FS.writeFile badIdentityPath
    "{\"repository\":\"a/b\",\"npmPackage\":\"@a/b\",\"releaseWorkflow\":\"w\",\"certificateOidcIssuer\":\"https://i\",\"certificateIdentityRegexp\":\"^https://github.com/x\"}"
  let unwrittenPath := (base / "never.pin").toString
  let (badStatus, _, badErr) ← writePin badIdentityPath "never.pin" base.toString
  let neverWritten := !(← System.FilePath.pathExists unwrittenPath)
  -- The same malformed identity through check-pin. Without its own refusal
  -- there, an unusable release/identity.json is reported as a drifted pin —
  -- which sends the operator to `write-pin`, which refuses, with nothing
  -- connecting the two messages.
  let (badCheckStatus, _, badCheckErr) ← run "check-pin" [badIdentityPath, pinPath]
  -- Writing into a directory that does not exist: a refusal, not a backtrace.
  let (unwritableStatus, _, unwritableErr) ←
    writePin identityPath "p.pin" (base / "no-such-dir").toString
  -- The two boundary refusals, at the usage layer rather than the filesystem:
  -- a name that would leave the granted directory never reaches the mechanism.
  let (escapingStatus, _, escapingErr) ← writePin identityPath "../escaped.pin" base.toString
  let (absoluteStatus, _, absoluteErr) ←
    writePin identityPath (base / "absolute.pin").toString base.toString
  let escapedAbsent := !(← System.FilePath.pathExists (base.parent.getD base / "escaped.pin"))
  IO.FS.removeDirAll base
  return [
    checkEq "pin command: write-pin succeeds against the committed identity" writeStatus 0,
    check "pin command: write-pin says where it wrote"
      (contains writeOut "identity.pin" && contains writeOut base.toString) writeOut,
    checkEq "pin command: what it wrote is what renderPin produces"
      written (okOr "<refused>" (Identity.parse "i" realIdentity >>= renderPin)),
    checkEq "pin command: check-pin accepts the pin write-pin just wrote" checkStatus 0,
    check "pin command: check-pin says the two agree" (contains checkOut "matches") checkOut,
    checkEq "pin command: check-pin refuses a drifted pin" driftStatus 1,
    check "pin command: a drifted pin is told how to regenerate"
      (contains driftErr "write-pin") driftErr,
    check "pin command: a drifted pin says what a stale one means"
      (contains driftErr "wrong identity") driftErr,
    checkEq "pin command: a missing identity file is a refusal" missingIdentity 1,
    check "pin command: a missing identity file names the path"
      (contains missingIdentityErr "could not read") missingIdentityErr,
    checkEq "pin command: a missing pin file is a refusal" missingPin 1,
    check "pin command: a missing pin file names the path"
      (contains missingPinErr "could not read") missingPinErr,
    checkEq "pin command: an unanchored expression is refused" badStatus 1,
    check "pin command: the unanchored refusal says which anchor is missing"
      (contains badErr "not anchored at $") badErr,
    check "pin command: a refused pin is not written at all" neverWritten
      "write-pin created a file it had already decided to refuse",
    checkEq "pin command: check-pin refuses an identity it cannot render a pin from"
      badCheckStatus 1,
    check "pin command: an unusable identity is reported as such, not as drift"
      (contains badCheckErr "not anchored at $" && !contains badCheckErr "wrong identity")
      badCheckErr,
    checkEq "pin command: an output directory that does not exist is a refusal, not an exception"
      unwritableStatus 1,
    check "pin command: and it names the phase that could not open it"
      (contains unwritableErr "opening the output directory" && contains unwritableErr "ENOENT")
      unwritableErr,
    -- The granted directory is the whole of where this may write, so a name
    -- that climbs out of it is refused before anything is opened.
    checkEq "pin command: an output name climbing out of the directory is a usage error"
      escapingStatus 2,
    check "pin command: and the refusal says why '..' is not a component"
      (contains escapingErr "'..' is not an output component") escapingErr,
    check "pin command: nothing was written outside the granted directory" escapedAbsent
      "write-pin created a file above the directory it was given",
    checkEq "pin command: an absolute output name is a usage error" absoluteStatus 2,
    check "pin command: and the refusal says --output-dir is what decides where"
      (contains absoluteErr "absolute path") absoluteErr]

/-! ## The native writer, through a public command

`Release.Write`'s fault matrix is the mechanism's oracle: it enumerates every
phase against injected rows. These rows are the other half — the real primitive
against a real directory, for the phases a filesystem can actually be arranged
to produce. What each one pins is what ADR-0028 says the write leaves behind:
the destination's bytes, and whether the staging sibling is still there.

`write-pin` is the vehicle because its input is one small committed file, so a
row here is about the write rather than about assembling a document. -/

private def writeCommandTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let identityPath := (base / "identity.json").toString
  IO.FS.writeFile identityPath (← IO.FS.readFile "release/identity.json")
  let expected := okOr "<refused>"
    (Identity.parse "i" (← IO.FS.readFile identityPath) >>= renderPin)
  let writeInto (dir : String) (name : String) :=
    runCommand "write-pin" ["--identity", identityPath, "--output", name, "--output-dir", dir]
  let present (path : System.FilePath) : IO Bool := do
    -- `pathExists` follows links, so a dangling one reads as absent. These rows
    -- are about what is *at* the path, which is what the exclusive create meets.
    match ← (IO.FS.Handle.mk path IO.FS.Mode.read).toBaseIO with
    | .ok _ => return true
    | .error _ => return (← path.isDir) || (← (IO.Process.output
        { cmd := "test", args := #["-L", path.toString] }).map (·.exitCode == 0))
  -- The ordinary case, and the one thing every other row is a deviation from.
  let plain := base / "plain"
  IO.FS.createDir plain
  let (plainStatus, plainOut, plainErr) ← writeInto plain.toString "identity.pin"
  let plainWritten ← IO.FS.readFile (plain / "identity.pin")
  let plainNoStaging := !(← present (plain / "identity.pin.tmp"))
  -- A nested name: every component but the last is descended into, no-follow.
  let nested := base / "nested"
  IO.FS.createDirAll (nested / "inner")
  let (nestedStatus, _, nestedErr) ← writeInto nested.toString "inner/identity.pin"
  let nestedWritten ← IO.FS.readFile (nested / "inner" / "identity.pin")
  -- Replacement: the destination already holds something, and ends up holding
  -- the new bytes rather than a concatenation or a truncation.
  let replaced := base / "replaced"
  IO.FS.createDir replaced
  IO.FS.writeFile (replaced / "identity.pin") "an older pin that is longer than the new one\n"
  let (replacedStatus, _, replacedErr) ← writeInto replaced.toString "identity.pin"
  let replacedWritten ← IO.FS.readFile (replaced / "identity.pin")
  -- A directory in the name that does not exist. Nothing here creates
  -- directories: a name whose parent is missing is a refusal, not a mkdir.
  let (missingDirStatus, _, missingDirErr) ← writeInto plain.toString "absent/identity.pin"
  -- A regular file where a directory component was expected.
  let notDir := base / "notdir"
  IO.FS.createDir notDir
  IO.FS.writeFile (notDir / "inner") "a file, not a directory\n"
  let (notDirStatus, _, notDirErr) ← writeInto notDir.toString "inner/identity.pin"
  -- A symbolic link as a directory component. Refused rather than followed:
  -- following it would put release evidence outside the granted directory,
  -- which is the one thing the anchored write exists to prevent.
  let linked := base / "linked"
  IO.FS.createDirAll (linked / "real")
  let elsewhere := base / "elsewhere"
  IO.FS.createDir elsewhere
  let _ ← IO.Process.output
    { cmd := "ln", args := #["-s", elsewhere.toString, (linked / "inner").toString] }
  let (linkedStatus, _, linkedErr) ← writeInto linked.toString "inner/identity.pin"
  let linkTargetEmpty := !(← present (elsewhere / "identity.pin"))
  -- Something already at the staging path. It is created exclusively, so the
  -- write refuses before a byte is written and leaves what was there for
  -- whoever has to explain it.
  let occupied := base / "occupied"
  IO.FS.createDir occupied
  IO.FS.writeFile (occupied / "identity.pin.tmp") "an earlier run left this behind\n"
  let (occupiedStatus, _, occupiedErr) ← writeInto occupied.toString "identity.pin"
  let occupiedUntouched :=
    (← IO.FS.readFile (occupied / "identity.pin.tmp")) == "an earlier run left this behind\n"
  let occupiedNotWritten := !(← present (occupied / "identity.pin"))
  -- A *dangling* symbolic link at the staging path. This is the one an
  -- existence check cannot see, and the reason the create is exclusive rather
  -- than preceded by a look.
  let dangling := base / "dangling"
  IO.FS.createDir dangling
  let _ ← IO.Process.output
    { cmd := "ln", args := #["-s", (dangling / "nothing").toString,
      (dangling / "identity.pin.tmp").toString] }
  let (danglingStatus, _, danglingErr) ← writeInto dangling.toString "identity.pin"
  let danglingTargetAbsent := !(← present (dangling / "nothing"))
  -- And a staging link that points at something real, which a write through
  -- would have overwritten.
  let aimed := base / "aimed"
  IO.FS.createDir aimed
  IO.FS.writeFile (aimed / "target") "the file a followed link would have eaten\n"
  let _ ← IO.Process.output
    { cmd := "ln", args := #["-s", (aimed / "target").toString,
      (aimed / "identity.pin.tmp").toString] }
  let (aimedStatus, _, aimedErr) ← writeInto aimed.toString "identity.pin"
  let aimedTargetIntact :=
    (← IO.FS.readFile (aimed / "target")) == "the file a followed link would have eaten\n"
  -- A destination that is a directory: the staging file is written in full and
  -- the rename fails. This is the arm that has to clean up after itself — a
  -- stray `<name>.tmp` beside a signed asset set is a file nothing describes.
  let blocked := base / "blocked"
  IO.FS.createDir blocked
  IO.FS.createDir (blocked / "identity.pin")
  let (blockedStatus, _, blockedErr) ← writeInto blocked.toString "identity.pin"
  let blockedCleanedUp := !(← present (blocked / "identity.pin.tmp"))
  IO.FS.removeDirAll base
  return [
    check "write command: an ordinary write succeeds" (plainStatus == 0) plainErr,
    checkEq "write command: the destination holds exactly the bytes" plainWritten expected,
    check "write command: and no staging file survives it" plainNoStaging
      "a staging sibling was left beside a completed write",
    check "write command: it says the name and the directory it wrote into"
      (contains plainOut "identity.pin" && contains plainOut plain.toString) plainOut,
    check "write command: a nested output name is written beneath the directory"
      (nestedStatus == 0) nestedErr,
    checkEq "write command: and holds the bytes" nestedWritten expected,
    check "write command: an existing destination is replaced" (replacedStatus == 0) replacedErr,
    checkEq "write command: and holds only the new bytes" replacedWritten expected,
    -- Every refusal below names its phase, because the phase is what says which
    -- thing to look at.
    checkEq "write command: a missing directory in the name is a refusal" missingDirStatus 1,
    check "write command: and names the walk phase and ENOENT"
      (contains missingDirErr "opening a directory beneath" && contains missingDirErr "ENOENT")
      missingDirErr,
    checkEq "write command: a regular file where a directory belongs is a refusal" notDirStatus 1,
    check "write command: and names it as not a directory"
      (contains notDirErr "ENOTDIR") notDirErr,
    checkEq "write command: a symlinked directory component is a refusal" linkedStatus 1,
    check "write command: and says links are refused rather than followed"
      (contains linkedErr "refused rather than followed") linkedErr,
    check "write command: nothing was written through the link" linkTargetEmpty
      "the write followed a symbolic link out of the granted directory",
    checkEq "write command: an occupied staging path is a refusal" occupiedStatus 1,
    check "write command: and names the create phase and EEXIST"
      (contains occupiedErr "creating the staging file" && contains occupiedErr "EEXIST")
      occupiedErr,
    check "write command: it writes through nothing it did not create" occupiedUntouched
      "the command wrote through a file that was already at the staging path",
    check "write command: and produces no destination when it refuses to stage"
      occupiedNotWritten "a file appeared despite the refusal",
    -- The refusal must not remove what it did not create: an occupied staging
    -- path is evidence of an earlier run, and this call is not the one that
    -- gets to decide it is rubbish.
    check "write command: a refused create leaves the occupant for someone to explain"
      (contains occupiedErr "Nothing was left behind") occupiedErr,
    checkEq "write command: a dangling link at the staging path is a refusal" danglingStatus 1,
    check "write command: and it is EEXIST rather than a followed create"
      (contains danglingErr "EEXIST") danglingErr,
    check "write command: nothing was created at the dangling link's target"
      danglingTargetAbsent "the exclusive create followed a dangling symbolic link",
    checkEq "write command: a staging link aimed at a real file is a refusal" aimedStatus 1,
    check "write command: and its target is untouched" aimedTargetIntact
      "the write followed a symbolic link at the staging path",
    check "write command: an aimed staging link names EEXIST too"
      (contains aimedErr "EEXIST") aimedErr,
    checkEq "write command: a destination that is a directory is a refusal" blockedStatus 1,
    check "write command: and names the rename phase"
      (contains blockedErr "renaming the staging file") blockedErr,
    -- The cleanup half: this invocation created the sibling, so this invocation
    -- removes it.
    check "write command: a failed rename removes the sibling it created" blockedCleanedUp
      "a staging sibling survived a write that refused after creating it",
    check "write command: and the refusal says so" (contains blockedErr "was removed") blockedErr,
    check "write command: every refusal says the destination is unchanged"
      ([missingDirErr, notDirErr, linkedErr, occupiedErr, danglingErr, aimedErr,
        blockedErr].all fun message => contains message "still holds what it held")
      "a refusal did not say what happened to the destination"]

/-! ## The plan commands, end to end

`plan-channels` decides whether an immutable publication job runs;
`plan-deferrals` decides whether a release is cut at all. Both are driven
through real files here, because reading a path that is not there and the exit
status each refusal produces are where a release step actually meets this tool,
and neither is exercised by testing the pure core. -/

private def planCommandTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let planPath := (base / "plan.json").toString
  let stalePath := (base / "stale.json").toString
  let brokenPath := (base / "broken.json").toString
  let realPlan ← IO.FS.readFile "release/plan.json"
  IO.FS.writeFile planPath realPlan
  IO.FS.writeFile stalePath (planOf defaultPlanRows)
  IO.FS.writeFile brokenPath "{\"channels\": 3}"
  let (channelsStatus, channelsOut, _) ← runCommand "plan-channels" [planPath]
  let (channelsMissing, _, channelsMissingErr) ←
    runCommand "plan-channels" [(base / "absent.json").toString]
  let (channelsBroken, _, channelsBrokenErr) ← runCommand "plan-channels" [brokenPath]
  let (channelsUsage, _, _) ← runCommand "plan-channels" [planPath, "extra"]
  -- The committed plan defers npm and Homebrew to 0.2.0, so 0.1.0 is ahead of
  -- nothing and 0.2.0 has caught up with both.
  let (aheadStatus, aheadOut, _) ← runCommand "plan-deferrals" [planPath, "v0.1.0"]
  let (bareStatus, _, _) ← runCommand "plan-deferrals" [planPath, "0.1.0"]
  let (expiredStatus, _, expiredErr) ← runCommand "plan-deferrals" [stalePath, "v0.2.0"]
  -- Cutting the release candidate: 0.2.0 is still ahead of 0.2.0-rc.1, which
  -- is the comparison a triple-only ordering got wrong.
  let (candidateStatus, _, candidateErr) ← runCommand "plan-deferrals" [stalePath, "v0.2.0-rc.1"]
  let (badVersion, _, badVersionErr) ← runCommand "plan-deferrals" [planPath, "banana"]
  let (badTag, _, badTagErr) ← runCommand "plan-deferrals" [planPath, "vbanana"]
  let (missingPlan, _, missingPlanErr) ←
    runCommand "plan-deferrals" [(base / "absent.json").toString, "v0.1.0"]
  let (brokenPlan, _, brokenPlanErr) ← runCommand "plan-deferrals" [brokenPath, "v0.1.0"]
  let (deferralsUsage, _, deferralsUsageErr) ← runCommand "plan-deferrals" [planPath]
  IO.FS.removeDirAll base
  return [
    checkEq "plan command: plan-channels succeeds against the committed plan" channelsStatus 0,
    checkEq "plan command: plan-channels emits the decided lines on stdout"
      channelsOut (okOr "<refused>" ((ReleasePlan.parse "p" realPlan).map renderChannelOutputs)),
    checkEq "plan command: a missing plan file is a refusal" channelsMissing 1,
    check "plan command: a missing plan file names the path"
      (contains channelsMissingErr "could not read") channelsMissingErr,
    checkEq "plan command: a malformed plan is a refusal" channelsBroken 1,
    check "plan command: a malformed plan says what is wrong with it"
      (contains channelsBrokenErr "is not an array") channelsBrokenErr,
    checkEq "plan command: plan-channels with a spare argument is a usage error" channelsUsage 2,
    checkEq "plan command: plan-deferrals accepts deferrals still ahead of the tag" aheadStatus 0,
    check "plan command: plan-deferrals says what it checked"
      (contains aheadOut "ahead of 0.1.0") aheadOut,
    checkEq "plan command: a bare version is accepted as well as a tag" bareStatus 0,
    checkEq "plan command: a deferral the release has caught up with is a refusal"
      expiredStatus 1,
    check "plan command: an expired deferral names every channel that expired"
      (contains expiredErr "'npm'" && contains expiredErr "'homebrew'") expiredErr,
    check "plan command: an expired deferral says how to fix it"
      (contains expiredErr "enable the channel") expiredErr,
    check "plan command: a deferral to 0.2.0 survives cutting 0.2.0-rc.1"
      (candidateStatus == 0) candidateErr,
    checkEq "plan command: a version that is not one is a refusal" badVersion 1,
    check "plan command: a bad version says what shape was expected"
      (contains badVersionErr "not a release version") badVersionErr,
    checkEq "plan command: a tag whose version is malformed is a refusal" badTag 1,
    check "plan command: a malformed tag is refused for its version, not its 'v'"
      (contains badTagErr "not a release version" || contains badTagErr "not a number") badTagErr,
    checkEq "plan command: plan-deferrals on a missing plan is a refusal" missingPlan 1,
    check "plan command: a missing plan names the path"
      (contains missingPlanErr "could not read") missingPlanErr,
    checkEq "plan command: plan-deferrals on a malformed plan is a refusal" brokenPlan 1,
    check "plan command: a malformed plan is refused before the version is judged"
      (contains brokenPlanErr "is not an array") brokenPlanErr,
    checkEq "plan command: plan-deferrals with one argument is a usage error" deferralsUsage 2,
    check "plan command: the usage error names both arguments"
      (contains deferralsUsageErr "<plan.json> <version-or-tag>") deferralsUsageErr]

/-! ## The SBOM

The exact bytes are pinned as a committed fixture rather than as a literal
here, so what a reviewer judges is an SPDX document rather than an escaped
string, and `Tests/fixtures/sbom-golden.spdx.json` is what the tool itself
renders from the two committed inputs beside it — an unnoticed change to what a
release describes is then a failing row rather than a difference in a signed
asset nobody reads.

The refusals get the weight: a document that understates what ships still reads
as evidence, so every input that cannot be understood is refused rather than
carried.
-/

private def rev40 (c : Char) : String := String.ofList (List.replicate 40 c)

/-- A manifest row. `url` is raw JSON rather than a string so that a row whose
    url is a number is reachable — reading that as an absent url is the
    absent/malformed conflation this whole tool exists to remove. -/
private def manifestRow (name rev : String) (url : Option String := none)
    (kind : Option String := some "\"git\"") : String :=
  "{" ++ String.intercalate ", " (
    (match kind with | none => [] | some raw => ["\"type\": " ++ raw]) ++
    ["\"name\": \"" ++ name ++ "\"", "\"rev\": \"" ++ rev ++ "\""] ++
    (match url with | none => [] | some raw => ["\"url\": " ++ raw])) ++ "}"

/-- A manifest, which names the Lake package it belongs to. -/
private def manifestOf (rows : List String) (package : String := "\"tl\"") : String :=
  "{\"name\": " ++ package ++ ", \"packages\": [" ++ String.intercalate "," rows ++ "]}"

/-- The toolchain pin's shape, since a bare word is no longer one. -/
private def pinnedToolchain : String := "leanprover/lean4:v4.33.0"

private def oneDependency : String := manifestOf [manifestRow "batteries" (rev40 '1')]

private def sbomInputsOf (version toolchain manifest : String) : SbomInputs :=
  { version, toolchainDocument := "lean-toolchain", toolchainText := toolchain
    manifestDocument := "lake-manifest.json", manifestText := manifest }

/-- The whole pipeline, for a row that only varies the manifest. -/
private def sbomOfManifest (manifest : String) : Except String Sbom :=
  sbomOfInputs (sbomInputsOf "1.2.3" "leanprover/lean4:v4.33.0\n" manifest)

private def renderedOf (version toolchain manifest : String) : Except String String :=
  renderSbomOfInputs (sbomInputsOf version toolchain manifest)

/-- The `(name, <field>)` pairs of a document's `packages` array, read with
    Lean's own JSON parser rather than through the code under test: a
    cross-check that used the parser under test would agree with a broken one.

    Pairs, and read out of one object at a time, because two independent
    substring searches over the rendered text would also pass on a document
    that paired one dependency's name with another's revision. -/
private def packagePairs (field : String) (text : String) : Option (List (String × String)) :=
  match Json.parse text with
  | .error _ => none
  | .ok root =>
    match root.getObjVal? "packages" with
    | .error _ => none
    | .ok packages =>
      match packages.getArr? with
      | .error _ => none
      | .ok rows =>
        rows.foldl (init := some []) fun acc row =>
          match acc, (row.getObjVal? "name").bind Json.getStr?,
              (row.getObjVal? field).bind Json.getStr? with
          | some collected, .ok name, .ok value => some (collected ++ [(name, value)])
          | _, _, _ => none

/-- What `lake-manifest.json` pins, and what the rendered document says. The
    manifest calls it `rev` and SPDX calls it `versionInfo`; comparing the two
    lists is the whole check. -/
private def manifestPairs : String → Option (List (String × String)) := packagePairs "rev"

private def documentPairs : String → Option (List (String × String)) :=
  packagePairs "versionInfo"

private def sbomTests : List Outcome :=
  let dependencies (manifest : String) : Option (List String) :=
    (sbomOfManifest manifest).toOption.map fun sbom => sbom.dependencies.map (·.downloadLocation)
  [ -- The identifier mapping. Package names are in the SPDX character class
    -- today; the mapping is explicit because a name that is not would
    -- otherwise produce an identifier SPDX cannot carry.
    checkEq "sbom: an ordinary package name maps to its identifier"
      (spdxIdentifier "batteries") "SPDXRef-Package-batteries",
    checkEq "sbom: a dot survives the identifier mapping"
      (spdxIdentifier "a.b") "SPDXRef-Package-a.b",
    checkEq "sbom: characters outside the identifier class become dashes"
      (spdxIdentifier "quote/4 v_1") "SPDXRef-Package-quote-4-v-1",
    -- The version. It is the one argument an operator types.
    check "sbom: a tag is refused where the bare version belongs"
      (mentions (renderedOf "v1.2.3" pinnedToolchain oneDependency) "carries a leading 'v'"),
    check "sbom: the tag refusal says what the document would otherwise be called"
      (mentions (renderedOf "v1.2.3" pinnedToolchain oneDependency) "'vv1.2.3'"),
    check "sbom: a version that is not one is refused"
      (mentions (renderedOf "1.2" pinnedToolchain oneDependency) "not a release version"),
    check "sbom: a leading zero is refused"
      (mentions (renderedOf "01.2.3" pinnedToolchain oneDependency) "leading zero"),
    check "sbom: build metadata is refused"
      (mentions (renderedOf "1.2.3+b" pinnedToolchain oneDependency) "build metadata"),
    check "sbom: a prerelease is accepted, and names itself"
      (match renderedOf "1.2.3-rc.1" pinnedToolchain oneDependency with
       | .ok document =>
           contains document "\"name\": \"tl-1.2.3-rc.1\""
             && contains document "/spdx/v1.2.3-rc.1\""
       | .error _ => false),
    -- The toolchain. It is what carries GMP and libuv into the binary, so a
    -- document without it understates exactly what the licensing section of
    -- ADR-0006 is about.
    check "sbom: an empty toolchain file is refused"
      (mentions (renderedOf "1.2.3" "" oneDependency) "is empty"),
    check "sbom: a whitespace-only toolchain file is refused"
      (mentions (renderedOf "1.2.3" "  \n" oneDependency) "is empty"),
    check "sbom: an empty toolchain says what it would understate"
      (mentions (renderedOf "1.2.3" "" oneDependency) "understate what ships"),
    -- A pin, not a channel. A bare name resolves to whatever it points at
    -- today, which is the opposite of what this field records.
    check "sbom: a toolchain that is not a pin is refused"
      (mentions (renderedOf "1.2.3" "definitely-not-an-elan-pin" oneDependency)
        "is not a toolchain pin"),
    check "sbom: a bare channel name is refused"
      (mentions (renderedOf "1.2.3" "stable" oneDependency) "is not a toolchain pin"),
    check "sbom: a toolchain with no channel is refused"
      (mentions (renderedOf "1.2.3" "leanprover/lean4" oneDependency) "is not a toolchain pin"),
    check "sbom: a toolchain refusal shows the shape elan reads"
      (mentions (renderedOf "1.2.3" "stable" oneDependency) "<owner>/<repository>:<channel>"),
    check "sbom: a toolchain carrying a space is refused"
      (mentions (renderedOf "1.2.3" "leanprover/lean4:v4.33.0 and more" oneDependency)
        "would not accept"),
    -- Whitespace this file's own trimming does not remove, because it trims
    -- ASCII: a non-breaking space would otherwise ride into the compiler
    -- version, looking exactly like the ordinary space it is not.
    check "sbom: a toolchain padded with a non-breaking space is refused"
      (mentions (renderedOf "1.2.3" (pinnedToolchain ++ String.singleton (Char.ofNat 0xa0))
        oneDependency) "would not accept"),
    check "sbom: an invisible character is described as one"
      (mentions (renderedOf "1.2.3" (pinnedToolchain ++ String.singleton (Char.ofNat 0xa0))
        oneDependency) "looks like one"),
    check "sbom: a two-line toolchain file is refused rather than embedded"
      (mentions (renderedOf "1.2.3" "leanprover/lean4:v4.33.0\nsomething else\n" oneDependency)
        "more than one line"),
    check "sbom: a carriage return in the toolchain is refused"
      (mentions (renderedOf "1.2.3" "a\r\nb\n" oneDependency) "more than one line"),
    checkEq "sbom: the toolchain is recorded without its trailing newline"
      ((sbomOfInputs (sbomInputsOf "1.2.3" "leanprover/lean4:v4.33.0\n" oneDependency)).toOption.bind
        (fun sbom => (sbom.dependencies.head?).map (·.versionInfo)))
      (some "leanprover/lean4:v4.33.0"),
    -- The manifest: every way it can fail to be one.
    check "sbom: a malformed manifest is refused"
      (mentions (sbomOfManifest "{ not json") "is not valid JSON"),
    -- The manifest is an argument rather than something this command finds, so
    -- being handed another checkout's is a mistake it can actually make.
    check "sbom: a manifest belonging to another Lake package is refused"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" (rev40 '1')] "\"elsewhere\""))
        "describes the Lake package 'elsewhere'"),
    check "sbom: another project's manifest says what would be published"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" (rev40 '1')] "\"elsewhere\""))
        "a dependency set it was not built from"),
    check "sbom: a manifest that names no package is refused"
      (mentions (sbomOfManifest "{\"packages\": []}") "has no 'name' field"),
    -- Each row is described as a git package pinned to a commit, so a row of
    -- another kind is refused rather than rendered as one.
    check "sbom: a dependency Lake did not resolve from git is refused"
      (mentions (sbomOfManifest (manifestOf
        [manifestRow "x" (rev40 '1') none (some "\"path\"")])) "is 'path'"),
    check "sbom: a non-git dependency says why it cannot be described"
      (mentions (sbomOfManifest (manifestOf
        [manifestRow "x" (rev40 '1') none (some "\"path\"")]))
        "not something it can describe"),
    check "sbom: a row that does not say what kind it is is refused"
      (mentions (sbomOfManifest (manifestOf
        [manifestRow "x" (rev40 '1') none none])) "has no 'type' field"),
    check "sbom: a manifest with no packages key is refused"
      (mentions (sbomOfManifest "{\"name\": \"tl\"}") "has no 'packages' field"),
    check "sbom: a manifest whose packages are not an array is refused"
      (mentions (sbomOfManifest "{\"name\": \"tl\", \"packages\": 3}") "is not an array"),
    check "sbom: a manifest row that is not an object is refused"
      (mentions (sbomOfManifest "{\"name\": \"tl\", \"packages\": [7]}") "is not a JSON object"),
    check "sbom: a row with no name is refused"
      (mentions (sbomOfManifest (manifestOf ["{\"type\": \"git\", \"rev\": \"" ++ rev40 '1' ++ "\"}"]))
        "has no 'name' field"),
    check "sbom: a row with a blank name is refused"
      (mentions (sbomOfManifest (manifestOf [manifestRow "" (rev40 '1')])) "is empty"),
    check "sbom: a row whose name is not a string is refused"
      (mentions (sbomOfManifest "{\"name\": \"tl\", \"packages\": [{\"name\": 4, \"rev\": \"x\"}]}")
        "is not a string"),
    check "sbom: a row with no revision is refused"
      (mentions (sbomOfManifest "{\"name\": \"tl\", \"packages\": [{\"type\": \"git\", \"name\": \"x\"}]}")
        "has no 'rev' field"),
    check "sbom: a row with a blank revision is refused"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" ""])) "is empty"),
    -- A pin is the whole point of the row: a branch name names something that
    -- moves, and the SBOM would describe a build nobody can reconstruct.
    check "sbom: a branch name where a pinned commit belongs is refused"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" "main"]))
        "not a full git object id"),
    check "sbom: an unpinned revision is told what a pin is"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" "main"])) "ADR-0009"),
    check "sbom: an unpinned revision names the dependency it belongs to"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" "main"])) "the 'x' dependency"),
    check "sbom: an uppercase revision is refused rather than folded"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" (rev40 'A')])) "lowercase"),
    -- The url: absent, declined, given, and malformed are four different
    -- things, and only the last is an error.
    checkEq "sbom: a row with no url declines to name a download location"
      ((dependencies (manifestOf [manifestRow "x" (rev40 '1')])).bind (·.getLast?))
      (some "NOASSERTION"),
    checkEq "sbom: a url is composed with the pinned revision"
      ((dependencies (manifestOf
        [manifestRow "x" (rev40 '1') (some "\"https://e.invalid/x\"")])).bind (·.getLast?))
      (some ("git+https://e.invalid/x@" ++ rev40 '1')),
    -- A manifest that already declines to name a url must not acquire one
    -- reading `git+NOASSERTION@<rev>`.
    checkEq "sbom: an explicit NOASSERTION url is carried, not composed"
      ((dependencies (manifestOf
        [manifestRow "x" (rev40 '1') (some "\"NOASSERTION\"")])).bind (·.getLast?))
      (some "NOASSERTION"),
    check "sbom: a url that is not a string is refused, not read as absent"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" (rev40 '1') (some "5")]))
        "is not a string"),
    check "sbom: a malformed url names its own path"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" (rev40 '1') (some "5")]))
        "packages.[0].url"),
    check "sbom: an empty url is refused"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" (rev40 '1') (some "\"\"")]))
        "is empty"),
    -- A url is composed into `git+<url>@<rev>`, which a reader resolves. Text
    -- that merely occupies the field is worse than the sentinel that declines
    -- it, because it reads as a location.
    check "sbom: a url that could not be fetched from is refused"
      (mentions (sbomOfManifest (manifestOf
        [manifestRow "x" (rev40 '1') (some "\"not a URI\"")])) "not a location"),
    check "sbom: a url with no scheme is refused"
      (mentions (sbomOfManifest (manifestOf
        [manifestRow "x" (rev40 '1') (some "\"example.invalid/x\"")])) "not a location"),
    check "sbom: an unfetchable url says what it would have become"
      (mentions (sbomOfManifest (manifestOf
        [manifestRow "x" (rev40 '1') (some "\"not a URI\"")])) "git+<url>@<rev>"),
    check "sbom: an empty url says how to decline instead"
      (mentions (sbomOfManifest (manifestOf [manifestRow "x" (rev40 '1') (some "\"\"")]))
        "NOASSERTION"),
    -- A name the renderer cannot encode. The document is pure ASCII by
    -- construction, and a character needing a surrogate pair is refused there
    -- rather than mis-encoded into a signed asset.
    check "sbom: a package name outside the BMP is refused rather than mis-encoded"
      (mentions (renderSbomOfInputs (sbomInputsOf "1.2.3" pinnedToolchain
        (manifestOf [manifestRow (String.singleton (Char.ofNat 0x1f600)) (rev40 '1')])))
        "Basic Multilingual Plane"),
    -- An empty inventory. A generator that silently found nothing would emit a
    -- confident empty document that still reads as evidence.
    check "sbom: a manifest listing no packages is refused"
      (mentions (sbomOfManifest (manifestOf [])) "lists no packages"),
    check "sbom: an empty inventory says why it is not a smaller release"
      (mentions (sbomOfManifest (manifestOf [])) "nothing ships"),
    -- Identifier collisions. SPDX identifiers are unique within a document,
    -- and the name is mapped into a restricted class on the way in, so two
    -- distinct names can arrive at one identifier.
    check "sbom: a repeated dependency name is refused"
      (mentions (sbomOfManifest (manifestOf
        [manifestRow "x" (rev40 '1'), manifestRow "x" (rev40 '2')])) "describes both 'x' and 'x'"),
    check "sbom: two names that collide after mapping are refused"
      (mentions (sbomOfManifest (manifestOf
        [manifestRow "a/b" (rev40 '1'), manifestRow "a-b" (rev40 '2')]))
        "describes both 'a/b' and 'a-b'"),
    check "sbom: a collision says why the document would describe neither"
      (mentions (sbomOfManifest (manifestOf
        [manifestRow "a/b" (rev40 '1'), manifestRow "a-b" (rev40 '2')]))
        "Identifiers are unique within a document"),
    -- …including a collision with one of the four packages this document
    -- always carries, which no per-row check would catch, and separately with
    -- the subject itself, which is not in the dependency list at all.
    check "sbom: a dependency colliding with a fixed package is refused"
      (mentions (sbomOfManifest (manifestOf [manifestRow "gmp" (rev40 '1')]))
        "SPDXRef-Package-gmp"),
    check "sbom: a dependency colliding with the document's own subject is refused"
      (mentions (sbomOfManifest (manifestOf [manifestRow "tl" (rev40 '1')]))
        "SPDXRef-Package-tl"),
    -- The shape of the document itself.
    checkEq "sbom: the document carries the four fixed packages plus every dependency"
      ((sbomOfManifest (manifestOf
        [manifestRow "a" (rev40 '1'), manifestRow "b" (rev40 '2')])).toOption.map
        (·.packages.length)) (some 6),
    checkEq "sbom: the document describes tl and depends on everything else"
      ((sbomOfManifest oneDependency).toOption.map
        (fun sbom => (sbom.subject.name, sbom.relationships.length)))
      (some ("tl", 5)),
    check "sbom: the version reaches the subject, the name and the namespace"
      (match renderedOf "1.2.3" "leanprover/lean4:v4.33.0" oneDependency with
       | .ok document =>
           contains document "\"name\": \"tl-1.2.3\""
             && contains document "\"documentNamespace\": \"https://github.com/DmitryKorolev/tl/spdx/v1.2.3\""
             && contains document "\"versionInfo\": \"1.2.3\""
       | .error _ => false),
    -- The document is a function of the release and of nothing else: no
    -- timestamp, no generated id. Two correct SBOMs for one release must not
    -- differ, because both are hashed into SHA256SUMS and signed.
    check "sbom: the creation time is fixed rather than stamped"
      (match renderedOf "1.2.3" pinnedToolchain oneDependency with
       | .ok document => contains document "\"created\": \"1970-01-01T00:00:00Z\""
       | .error _ => false),
    check "sbom: the tool that wrote it is named"
      (match renderedOf "1.2.3" pinnedToolchain oneDependency with
       | .ok document => contains document "\"Tool: tlrelease sbom\""
       | .error _ => false),
    -- Whitespace around the toolchain is not content: two checkouts whose
    -- lean-toolchain differs only in a trailing newline describe one release.
    checkEq "sbom: the toolchain's surrounding whitespace does not reach the bytes"
      (okOr "<padded>" (renderedOf "1.2.3" ("  " ++ pinnedToolchain ++ "  \n") oneDependency))
      (okOr "<bare>" (renderedOf "1.2.3" pinnedToolchain oneDependency)),
    check "sbom: a different release renders different bytes"
      (match renderedOf "1.2.3" pinnedToolchain oneDependency, renderedOf "1.2.4" pinnedToolchain oneDependency with
       | .ok earlier, .ok later => earlier != later
       | _, _ => false),
    -- The licensing boundary ADR-0006 is about has to be in the document by
    -- name, or it does not discharge what it is produced for.
    check "sbom: the statically linked components ADR-0006 is about are named"
      (match renderedOf "1.2.3" "leanprover/lean4:v4.33.0" oneDependency with
       | .ok document =>
           contains document "\"gmp\"" && contains document "\"libuv\""
             && contains document "LGPL-3.0-or-later" && contains document "\"lean4\""
       | .error _ => false)]

/-! ## The SBOM against the repository's own inputs and its committed golden -/

private def sbomDocumentTests : IO (List Outcome) := do
  let goldenToolchain ← IO.FS.readFile "Tests/fixtures/sbom-lean-toolchain"
  let goldenManifest ← IO.FS.readFile "Tests/fixtures/sbom-lake-manifest.json"
  let golden ← IO.FS.readFile "Tests/fixtures/sbom-golden.spdx.json"
  let realToolchain ← IO.FS.readFile "lean-toolchain"
  let realManifest ← IO.FS.readFile "lake-manifest.json"
  let real := renderSbomOfInputs
    { version := "1.2.3", toolchainDocument := "lean-toolchain", toolchainText := realToolchain
      manifestDocument := "lake-manifest.json", manifestText := realManifest }
  let pairs := manifestPairs realManifest
  let mut outs := [
    -- The golden document. Regenerated by the tool itself, so a change to what
    -- a release describes is a failing row rather than a quiet difference in a
    -- signed asset.
    checkEq "sbom: the committed golden is exactly what the tool renders"
      (okOr "<refused>" (renderSbomOfInputs
        { version := "9.9.9", toolchainDocument := "Tests/fixtures/sbom-lean-toolchain"
          toolchainText := goldenToolchain
          manifestDocument := "Tests/fixtures/sbom-lake-manifest.json"
          manifestText := goldenManifest })) golden,
    -- The repository's own inputs, which is the document a release actually
    -- publishes. A model that no longer describes them is a model of nothing.
    check "sbom: the repository's own inputs produce a document" real.toOption.isSome
      (errorOf real),
    check "sbom: the committed manifest reads independently of the parser under test"
      pairs.isSome "lake-manifest.json could not be read as name/rev pairs",
    checkEq "sbom: the document carries every lake dependency and nothing else"
      ((okOr "" real).splitOn "\"SPDXID\": \"SPDXRef-Package-").length
      ((pairs.getD []).length + 5)]
  -- Each dependency at the exact revision the manifest pins — a branch or a
  -- range here would describe a build nobody can reconstruct. Compared as
  -- pairs read out of the rendered document, so a name attached to another
  -- dependency's revision fails rather than satisfying two separate searches.
  let described := (documentPairs (okOr "" real)).getD []
  for (name, revision) in pairs.getD [] do
    outs := outs ++ [
      check s!"sbom: '{name}' is described at the revision lake-manifest.json pins"
        (described.contains (name, revision))
        s!"the rendered document has no package pairing '{name}' with {revision}; it carries {described}"]
  outs := outs ++ [
    check "sbom: the toolchain the repository pins is the one recorded"
      (contains (okOr "" real) s!"\"versionInfo\": \"{realToolchain.trimAscii.toString}\"")
      realToolchain]
  return outs

/-! ## The SBOM command, end to end

The pure core above cannot reach the parts a release step actually meets: a
path that is not there, a destination that cannot be written, whether a refused
generation leaves a file behind, and the exit status each produces. -/

private def sbomCommandTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let sbom (version toolchain manifest name : String) :=
    runCommand "sbom" ["--version", version, "--toolchain", toolchain,
      "--lake-manifest", manifest, "--output", name, "--output-dir", base.toString]
  let never := "never.spdx.json"
  let (status, out, _) ← sbom "1.2.3" "lean-toolchain" "lake-manifest.json" "first.spdx.json"
  let (againStatus, _, _) ← sbom "1.2.3" "lean-toolchain" "lake-manifest.json" "second.spdx.json"
  let (otherStatus, _, _) ← sbom "1.2.4" "lean-toolchain" "lake-manifest.json" "other.spdx.json"
  let written ← IO.FS.readFile (base / "first.spdx.json")
  let writtenAgain ← IO.FS.readFile (base / "second.spdx.json")
  let writtenOther ← IO.FS.readFile (base / "other.spdx.json")
  -- Against the committed fixtures, through the command rather than the pure
  -- core: this is the path the release workflow runs.
  let (goldenStatus, _, _) ← sbom "9.9.9" "Tests/fixtures/sbom-lean-toolchain"
    "Tests/fixtures/sbom-lake-manifest.json" "golden.spdx.json"
  let goldenWritten ← IO.FS.readFile (base / "golden.spdx.json")
  let golden ← IO.FS.readFile "Tests/fixtures/sbom-golden.spdx.json"
  let (missingToolchain, _, missingToolchainErr) ←
    sbom "1.2.3" (base / "absent").toString "lake-manifest.json" never
  let (missingManifest, _, missingManifestErr) ←
    sbom "1.2.3" "lean-toolchain" (base / "absent.json").toString never
  -- A refusal must not leave a document behind: a partial SBOM would be hashed
  -- into SHA256SUMS and signed like a complete one.
  let brokenManifest := (base / "broken.json").toString
  IO.FS.writeFile brokenManifest (manifestOf [])
  let (emptyInventory, _, emptyInventoryErr) ← sbom "1.2.3" "lean-toolchain" brokenManifest never
  let (badVersion, _, badVersionErr) ← sbom "v1.2.3" "lean-toolchain" "lake-manifest.json" never
  -- A name the renderer cannot encode: the refusal comes from rendering rather
  -- than from parsing, which is the one command branch the pure rows above
  -- cannot reach.
  let astralManifest := (base / "astral.json").toString
  IO.FS.writeFile astralManifest
    (manifestOf [manifestRow (String.singleton (Char.ofNat 0x1f600)) (rev40 '1')])
  let (unrenderable, _, unrenderableErr) ← sbom "1.2.3" "lean-toolchain" astralManifest never
  -- Checked after every refusal above, not after the first: each of them was
  -- given the same destination, so this says none of them wrote anything.
  let nothingWritten := !(← System.FilePath.pathExists (base / never))
  -- One write refusal through this command too. The mechanism's phases are
  -- enumerated against `write-pin` and against injected rows; what this row
  -- says is that this command reports them rather than exiting zero.
  let (unwritable, _, unwritableErr) ← runCommand "sbom"
    ["--version", "1.2.3", "--toolchain", "lean-toolchain",
     "--lake-manifest", "lake-manifest.json", "--output", "s.json",
     "--output-dir", (base / "no-such-dir").toString]
  -- The default: no --output-dir means the working directory, stated rather
  -- than discovered. Driven through the built binary in a scratch directory,
  -- because "where this process was started" is not observable in-process.
  let cwd ← IO.currentDir
  let scratch := base / "scratch"
  IO.FS.createDir scratch
  let executable := cwd / ".lake" / "build" / "bin" / "tlrelease"
  let defaulted ← (IO.Process.output {
    cmd := executable.toString, cwd := some scratch
    args := #["sbom", "--version", "1.2.3",
      "--toolchain", (cwd / "lean-toolchain").toString,
      "--lake-manifest", (cwd / "lake-manifest.json").toString,
      "--output", "defaulted.spdx.json"] }).toBaseIO
  let landed ← System.FilePath.pathExists (scratch / "defaulted.spdx.json")
  let (missingOutput, _, missingOutputErr) ← runCommand "sbom"
    ["--version", "1.2.3", "--toolchain", "lean-toolchain",
     "--lake-manifest", "lake-manifest.json"]
  let (emptyDirectory, _, emptyDirectoryErr) ← runCommand "sbom"
    ["--version", "1.2.3", "--toolchain", "lean-toolchain",
     "--lake-manifest", "lake-manifest.json",
     "--output", "x.spdx.json", "--output-dir", ""]
  IO.FS.removeDirAll base
  return [
    checkEq "sbom command: the repository's inputs produce an SBOM" status 0,
    check "sbom command: it says where it wrote and how much it describes"
      (contains out "wrote" && contains out "packages for tl 1.2.3") out,
    -- Byte-stability is not a nicety: the document is hashed into SHA256SUMS
    -- and signed, so two generations for one release have to agree.
    checkEq "sbom command: two runs over the same inputs are byte-identical"
      (againStatus, writtenAgain) (0, written),
    check "sbom command: a different release produces a different document"
      (otherStatus == 0 && writtenOther != written) "the two releases rendered the same bytes",
    checkEq "sbom command: the committed golden is what the command writes"
      (goldenStatus, goldenWritten) (0, golden),
    checkEq "sbom command: a missing toolchain file is a refusal" missingToolchain 1,
    check "sbom command: a missing input names the path and what it would cost"
      (contains missingToolchainErr "could not read"
        && contains missingToolchainErr "understate what ships") missingToolchainErr,
    checkEq "sbom command: a missing manifest is a refusal" missingManifest 1,
    check "sbom command: a missing manifest names the path"
      (contains missingManifestErr "could not read") missingManifestErr,
    checkEq "sbom command: an empty inventory is a refusal" emptyInventory 1,
    check "sbom command: an empty inventory says an empty SBOM is not a smaller release"
      (contains emptyInventoryErr "nothing ships") emptyInventoryErr,
    check "sbom command: a refused generation writes no document at all" nothingWritten
      "the command created a file it had already decided to refuse",
    checkEq "sbom command: a name the renderer cannot encode is a refusal" unrenderable 1,
    check "sbom command: an unencodable name is refused for the reason it is"
      (contains unrenderableErr "Basic Multilingual Plane") unrenderableErr,
    -- A malformed version is a refusal, not a usage error: the invocation was
    -- well formed and a decision was made.
    checkEq "sbom command: a tag where the version belongs is a refusal" badVersion 1,
    check "sbom command: the tag refusal says to pass the bare version"
      (contains badVersionErr "bare version") badVersionErr,
    checkEq "sbom command: an output directory that is not there is a refusal, not an exception"
      unwritable 1,
    check "sbom command: and the refusal names the phase"
      (contains unwritableErr "opening the output directory") unwritableErr,
    -- Through the real process, so a failure to run it is a failure here rather
    -- than a row that quietly stops meaning anything.
    check "sbom command: without --output-dir the built binary writes where it was started"
      (match defaulted with
       | .ok result => result.exitCode == 0 && landed
       | .error _ => false)
      (match defaulted with
       | .ok result => s!"status {result.exitCode}: {result.stderr}"
       | .error error => s!"could not run {executable}: {error}"),
    checkEq "sbom command: no --output at all is a usage error" missingOutput 2,
    check "sbom command: and it names the option that was not given"
      (contains missingOutputErr "--output is required") missingOutputErr,
    -- The empty string is what a workflow expression that resolved to nothing
    -- looks like on the command line. It is refused as a directory rather
    -- than silently meaning the working one.
    checkEq "sbom command: an empty --output-dir is a usage error" emptyDirectory 2,
    check "sbom command: and it says the empty string is not a value"
      (contains emptyDirectoryErr "--output-dir") emptyDirectoryErr]

/-! ## Checks: the verdict and the report are one list

`Check.allHeld_iff_noFailures` proves the two readings agree. These rows are
about what each one *says* — order, which texts are emitted, and that an empty
list passes, which is the shape a check list that stopped being built would
take. -/

private def heldCheck : Check := { held := true, failure := "should not be said" }
private def failedCheck : Check := { held := false, failure := "first" }
private def secondFailed : Check := { held := false, failure := "second" }

private def checkTests : List Outcome :=
  [checkEq "check: every check holding is a pass" (Check.allHeld [heldCheck, heldCheck]) true,
   checkEq "check: a passing list reports nothing"
     (Check.failures [heldCheck, heldCheck]) [],
   checkEq "check: one failing check fails the list"
     (Check.allHeld [heldCheck, failedCheck, heldCheck]) false,
   checkEq "check: only the failing checks are reported"
     (Check.failures [heldCheck, failedCheck, heldCheck]) ["first"],
   checkEq "check: failures are reported in list order"
     (Check.failures [failedCheck, heldCheck, secondFailed]) ["first", "second"],
   -- An empty list passes, which is correct and is also the shape a check list
   -- that stopped being built would take. Every caller that can produce one
   -- refuses on emptiness separately; this row records that this layer does
   -- not, so nobody reads a pass here as evidence anything was looked at.
   checkEq "check: an empty list passes, and says nothing" (Check.allHeld []) true,
   checkEq "check: an empty list reports nothing" (Check.failures []) []]

/-! ## Named options

Three ways an option list fails silently, each closed at the parser. -/

private def sampleSpecs : List OptionSpec :=
  [{ name := "alpha", takesValue := true }, { name := "beta", takesValue := false }]

private def parsedOptions (args : List String) : Except String Options :=
  parseOptions sampleSpecs args

private def optionValue (args : List String) (name : String) : String :=
  match parsedOptions args with
  | .error message => s!"<refused: {message}>"
  | .ok options => (options.value? name).getD "<absent>"

private def optionTests : List Outcome :=
  [checkEq "options: a declared option carries its value"
     (optionValue ["--alpha", "one"] "alpha") "one",
   checkEq "options: an undeclared option is absent rather than empty"
     (optionValue ["--beta"] "alpha") "<absent>",
   check "options: a valueless option records that it was given"
     (match parsedOptions ["--beta"] with
      | .ok options => options.given "beta" && !options.given "alpha"
      | .error _ => false) "the flag was not recorded",
   -- The three silent failures.
   check "options: an option nobody declared is refused"
     (mentions (parsedOptions ["--comit", "x"]) "is not an option this command takes")
     (errorOf (parsedOptions ["--comit", "x"])),
   check "options: the refusal lists the options that do exist"
     (mentions (parsedOptions ["--comit", "x"]) "--alpha")
     (errorOf (parsedOptions ["--comit", "x"])),
   check "options: an option given twice is refused"
     (mentions (parsedOptions ["--alpha", "one", "--alpha", "two"]) "more than once")
     (errorOf (parsedOptions ["--alpha", "one", "--alpha", "two"])),
   check "options: an option with no value at all is refused"
     (mentions (parsedOptions ["--alpha"]) "was given none")
     (errorOf (parsedOptions ["--alpha"])),
   -- The one that would otherwise be silent: `--alpha --beta` binds alpha to
   -- the literal text "--beta", and a free-text field would carry it.
   check "options: a value that is another option is refused rather than bound"
     (mentions (parsedOptions ["--alpha", "--beta"]) "which is another option")
     (errorOf (parsedOptions ["--alpha", "--beta"])),
   -- Positionals and the separator.
   check "options: a bare word is positional"
     (match parsedOptions ["stray"] with
      | .ok options => options.positional == ["stray"]
      | .error _ => false) "the word was not collected",
   check "options: everything after -- is positional, options included"
     (match parsedOptions ["--", "--alpha", "one"] with
      | .ok options => options.positional == ["--alpha", "one"]
      | .error _ => false) "the separator did not hold",
   -- The accessors.
   check "options: a required option that was not given is a usage message"
     (mentions (parsedOptions [] >>= (·.required "alpha")) "--alpha is required")
     (errorOf (parsedOptions [] >>= (·.required "alpha"))),
   -- An option given as the empty string is what a workflow expression that
   -- resolved to nothing looks like on the command line. It gets past a
   -- presence check and produces a record its own reader refuses, written by a
   -- step that exited zero.
   check "options: an option given as the empty string is refused"
     (mentions (parsedOptions ["--alpha", ""] >>= (·.required "alpha")) "is not a value")
     (errorOf (parsedOptions ["--alpha", ""] >>= (·.required "alpha"))),
   check "options: the empty-value refusal is different from the absent-value one"
     (errorOf (parsedOptions ["--alpha", ""] >>= (·.required "alpha"))
       != errorOf (parsedOptions [] >>= (·.required "alpha"))) "one message for two conditions",
   checkEq "options: a descriptive option defaults to the empty string"
     (match parsedOptions [] with
      | .ok options => options.describing "alpha"
      | .error _ => "<refused>") ""]

/-! ## Running another program

The seam the whole port turns on: a status that is a value, and three outcomes
because "it is not there" and "it did not finish" are not answers. -/

private def absentProgram : String := "definitely-not-a-program-on-this-path"

private def outcomeLabel : RunOutcome → String
  | .completed output => s!"completed {output.exitCode}"
  | .unavailable _ _ => "unavailable"
  | .timedOut _ _ => "timedOut"

private def processTests : IO (List Outcome) := do
  let absent ← Release.run absentProgram #[]
  let failing ← Release.run "sh" #["-c", "printf answer; printf trouble >&2; exit 3"]
  let hung ← Release.run "sh" #["-c", "sleep 30"] 300
  let fine ← succeeded "sh" #["-c", "printf hello"]
  let nonZero ← succeeded "sh" #["-c", "printf why >&2; exit 7"]
  let missing ← succeeded absentProgram #[]
  return [
    -- A program that is not there is not a program that failed.
    checkEq "process: a command that is not on PATH is unavailable"
      (outcomeLabel absent) "unavailable",
    check "process: an unavailable command says it cannot be skipped"
      (match absent.failureMessage with
       | some message => contains message "cannot be skipped"
       | none => false) "no failure message",
    -- The status is a value, and the streams stay apart.
    checkEq "process: a non-zero status is carried, not discarded"
      (outcomeLabel failing) "completed 3",
    checkEq "process: stdout and stderr are captured separately"
      (match failing with
       | .completed output => (output.stdout, output.stderr)
       | _ => ("<not completed>", "")) ("answer", "trouble"),
    check "process: a completed run has no failure message"
      failing.failureMessage.isNone "a completed run reported a failure message",
    -- A hang is bounded, and the bound is honoured rather than reported early.
    checkEq "process: a program that does not finish times out" (outcomeLabel hung) "timedOut",
    check "process: a timeout says the tool established nothing"
      (match hung.failureMessage with
       | some message => contains message "established nothing"
       | none => false) "no failure message",
    -- `succeeded` collapses all three failures and cannot be reached otherwise.
    checkEq "process: succeeded returns the output of a zero-status run"
      (match fine with | .ok output => output.stdout | .error message => message) "hello",
    check "process: succeeded refuses a non-zero status and quotes the diagnosis"
      (mentions nonZero "exited 7" && mentions nonZero "why") (errorOf nonZero),
    check "process: succeeded refuses a command that is not there"
      (mentions missing "could not be run") (errorOf missing)]

/-! ## Digests

The tool is not trusted for its name. Both refusals below are driven through
`resolveFrom`, so they are reachable without removing anything from the machine
the tests run on. -/

private def brokenCandidates : List Candidate :=
  -- `cat` is present everywhere and answers with the file's own bytes, which is
  -- not the digest of them. This is the shape of a `shasum` whose `-a 256` is
  -- ignored: present, exiting zero, and answering with the wrong function.
  [{ command := "cat", leadingArgs := #[] }]

private def failingCandidates : List Candidate :=
  [{ command := "sh", leadingArgs := #["-c", "exit 1"] }]

private def absentCandidates : List Candidate :=
  [{ command := absentProgram, leadingArgs := #[] }]

private def digestTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let file := (base / "content").toString
  IO.FS.writeFile file "abc"
  let subdirectory := (base / "sub").toString
  IO.FS.createDirAll subdirectory
  let link := (base / "link").toString
  let _ ← Release.run "ln" #["-s", file, link]
  let fifo := (base / "pipe").toString
  let _ ← Release.run "mkfifo" #[fifo]
  let absent ← Digester.resolveFrom absentCandidates
  let broken ← Digester.resolveFrom brokenCandidates
  let failing ← Digester.resolveFrom failingCandidates
  let real ← Digester.resolve
  let digested ← match real with
    | .error message => pure (.error message : Except String Sha256)
    | .ok digester => digester.digest file
  let ofDirectory ← match real with
    | .error message => pure (.error message : Except String Sha256)
    | .ok digester => digester.digest subdirectory
  let ofLink ← match real with
    | .error message => pure (.error message : Except String Sha256)
    | .ok digester => digester.digest link
  let ofFifo ← match real with
    | .error message => pure (.error message : Except String Sha256)
    | .ok digester => digester.digest fifo
  let ofMissing ← match real with
    | .error message => pure (.error message : Except String Sha256)
    | .ok digester => digester.digest ((base / "no-such-file").toString)
  IO.FS.removeDirAll base
  return [
    check "digest: no digest tool at all is a refusal that names the remedy"
      (mentions absent "no working SHA-256 tool" && mentions absent "coreutils")
      (errorOf absent),
    -- The reason the probe exists: a tool present, exiting zero, and computing
    -- something other than SHA-256 would fill a signed manifest with digests of
    -- the wrong function and nothing downstream would notice.
    check "digest: a tool that answers with the wrong function is refused"
      (mentions broken "does not compute SHA-256") (errorOf broken),
    check "digest: the wrong-function refusal names the standard it checked against"
      (mentions broken "FIPS 180-4") (errorOf broken),
    check "digest: a tool that is present and fails is refused"
      (mentions failing "exited 1") (errorOf failing),
    -- The real tool, cross-checked against the same published vector.
    checkEq "digest: the resolved tool computes the FIPS 180-4 vector for 'abc'"
      (match digested with | .ok sha => sha.hex | .error message => message)
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    -- Everything that is not an ordinary file.
    check "digest: a directory is refused" (mentions ofDirectory "is a directory")
      (errorOf ofDirectory),
    check "digest: a symbolic link is refused rather than followed"
      (mentions ofLink "symbolic link") (errorOf ofLink),
    check "digest: the symlink refusal says what a consumer would receive"
      (mentions ofLink "what a consumer receives is the link") (errorOf ofLink),
    check "digest: a named pipe is refused rather than read"
      (mentions ofFifo "neither an ordinary file nor a directory") (errorOf ofFifo),
    check "digest: a path that is not there is refused"
      (mentions ofMissing "could not be read") (errorOf ofMissing)]

/-! ## The manifest verdict

Pure, over an explicit evidence value, which is what `manifestAccepts_iff` is
stated about. Every branch is reachable here without a filesystem. -/

private def digest64c : String := String.ofList (List.replicate 64 'c')

/-- The verdict rows, built inside `Except` so that a fixture which stopped
    parsing becomes one failing row saying so, rather than a group that quietly
    stops asserting anything. `Sha256` has a private constructor, so there is no
    default to fall back to — which is the property it exists to have. -/
private def manifestVerdictRows : Except String (List Outcome) := do
  let shaA ← Sha256.parse "a" digest64
  let shaC ← Sha256.parse "c" digest64c
  let assets : List Asset :=
    [{ name := "LICENSE", sha256 := shaA, kind := .notice },
     { name := "tl.spdx.json", sha256 := shaC, kind := .sbom }]
  let matching : DirectoryEvidence :=
    { names := ["LICENSE", "tl.spdx.json"],
      digests := [("LICENSE", shaA), ("tl.spdx.json", shaC)] }
  let verdictOf (evidence : DirectoryEvidence) : Bool :=
    manifestAccepts "dist" "release-manifest.json" assets evidence
  let reportOf (evidence : DirectoryEvidence) : List String :=
    manifestFailures "dist" "release-manifest.json" assets evidence
  let missing : DirectoryEvidence := { names := ["LICENSE"], digests := [("LICENSE", shaA)] }
  let tampered : DirectoryEvidence :=
    { matching with digests := [("LICENSE", shaC), ("tl.spdx.json", shaC)] }
  let extra : DirectoryEvidence :=
    { matching with names := matching.names ++ ["unexpected-asset"] }
  let allowed : DirectoryEvidence :=
    { matching with
      names := matching.names
        ++ ["SHA256SUMS", "release-manifest.json", "LICENSE.sigstore.json",
            "tl.spdx.json.sigstore.json"] }
  let uncollected : DirectoryEvidence := { matching with digests := [("LICENSE", shaA)] }
  return [
    check "manifest: a directory holding exactly what is described matches"
      (verdictOf matching) s!"{reportOf matching}",
    checkEq "manifest: a match reports nothing at all" (reportOf matching) [],
    -- The three ways a directory stops matching.
    check "manifest: a described asset that is not present is refused"
      (!verdictOf missing) "an absent asset was accepted",
    check "manifest: the absent-asset message says which side it is missing from"
      ((reportOf missing).any (contains · "is described by the manifest but is not in dist"))
      s!"{reportOf missing}",
    check "manifest: an asset whose bytes differ is refused"
      (!verdictOf tampered) "a modified asset was accepted",
    check "manifest: the mismatch message names both digests"
      ((reportOf tampered).any fun failure => contains failure digest64c && contains failure digest64)
      s!"{reportOf tampered}",
    check "manifest: an asset nothing describes is refused"
      (!verdictOf extra) "an undescribed asset was accepted",
    check "manifest: the extra-asset message says why a surplus is not harmless"
      ((reportOf extra).any (contains · "nothing accounts for")) s!"{reportOf extra}",
    -- The three things a manifest structurally cannot describe.
    check "manifest: the sums file, the manifest, and bundles for described assets may be undescribed"
      (verdictOf allowed) s!"{reportOf allowed}",
    -- A described-and-present asset with no digest collected is this program
    -- failing to look, which must not be reported as the directory being wrong.
    check "manifest: a described asset present but unhashed is refused"
      (!verdictOf uncollected) "an unhashed asset was accepted",
    check "manifest: the unhashed message blames the collector, not the directory"
      ((reportOf uncollected).any (contains · "failing to look")) s!"{reportOf uncollected}",
    -- A bundle is admitted by asset, not by suffix. Written as "anything ending
    -- .sigstore.json", the one category this check cannot inspect became a
    -- category anyone could add a member to — and SHA256SUMS excludes the same
    -- suffix, so such a file would be accounted for by neither.
    check "manifest: a bundle named for a described asset may be undescribed"
      (allowedUndescribed "release-manifest.json" assets "LICENSE.sigstore.json")
      "a legitimate bundle was refused",
    check "manifest: a bundle named for nothing in the release is not allowed"
      (!allowedUndescribed "release-manifest.json" assets "anything-at-all.sigstore.json")
      "an unattached bundle was allowed",
    check "manifest: an unattached bundle in the directory is refused"
      (!verdictOf { matching with
        names := matching.names ++ ["anything-at-all.sigstore.json"] })
      "an unattached bundle was accepted"]

private def manifestVerdictTests : List Outcome :=
  (match manifestVerdictRows with
   | .ok rows => rows
   | .error message =>
       [check "manifest: the verdict fixtures parse" false message]) ++
  -- Classification, which needs no digests.
  [checkEq "manifest: a notice is classified as one"
     (classifyAsset [] "THIRD-PARTY-LICENSES").wire "notice",
   checkEq "manifest: an SBOM is classified by its suffix"
     (classifyAsset [] "tl-0.1.0.spdx.json").wire "sbom",
   checkEq "manifest: a file shaped like a binary but not in the target list is other"
     (classifyAsset [] "tl-imaginary-platform").wire "other",
   checkEq "manifest: a binary is classified against the target list"
     (classifyAsset [sampleTarget "linux-x64" .supported] "tl-linux-x64").wire "binary",
   checkEq "manifest: a build record is classified against the target list"
     (classifyAsset [sampleTarget "linux-x64" .supported] "build-metadata-linux-x64.json").wire
     "build-metadata",
   checkEq "manifest: a link audit is classified against the target list"
     (classifyAsset [sampleTarget "linux-x64" .supported] "link-audit-linux-x64.txt").wire
     "link-audit",
   -- Generation omits exactly what verification allows to be undescribed.
   -- Written twice these could drift, and a release would refuse itself.
   checkEq "manifest: what generation omits is exactly what verification allows"
     (describableNames "release-manifest.json"
       ["LICENSE", "SHA256SUMS", "release-manifest.json", "tl-linux-x64.sigstore.json"])
     ["LICENSE"]]

/-! ## The build-record verdict

Seven facts, each varied one at a time from a record that agrees. -/

private def metadataText (overrides : List (String × String)) : String :=
  objectOf (buildMetadataFields.map fun (key, value) =>
    (key, (overrides.lookup key).getD value))

private def recordVerdict (run : RunContext) (target : Target)
    (digestText : String) (overrides : List (String × String)) : Except String Bool := do
  let facts ← factsOf run
  let build ← BuildMetadata.parse "b" (metadataText overrides)
  let digest ← Sha256.parse "d" digestText
  return metadataAccepts facts target digest build

private def recordReport (run : RunContext) (target : Target)
    (digestText : String) (overrides : List (String × String)) : List String :=
  match factsOf run, BuildMetadata.parse "b" (metadataText overrides),
        Sha256.parse "d" digestText with
  | .ok facts, .ok build, .ok digest => metadataFailures facts target digest build
  | _, _, _ => ["<a fixture stopped parsing>"]

private def linuxTarget : Target := sampleTarget "linux-x64" .supported

private def inRun : RunContext := .inWorkflow sampleWorkflowRef "42"

private def accepted (overrides : List (String × String)) : Bool :=
  (recordVerdict inRun linuxTarget digest64 overrides).toOption == some true

private def metadataVerdictTests : List Outcome :=
  [check "record: a record agreeing on all seven facts is accepted" (accepted [])
     s!"{recordReport inRun linuxTarget digest64 []}",
   checkEq "record: an accepted record reports nothing"
     (recordReport inRun linuxTarget digest64 []) [],
   -- Each of the seven, one at a time.
   check "record: a record naming another target is refused"
     (!accepted [("target", "\"darwin-x64\"")]) "a crossed record was accepted",
   check "record: a record recording another tier is refused"
     (!accepted [("tier", "\"best-effort\"")]) "a drifted tier was accepted",
   check "record: a record whose digest is not the artifact's is refused"
     ((recordVerdict inRun linuxTarget digest64c []).toOption == some false)
     "bytes that were not the ones built were accepted",
   check "record: a record from another commit is refused"
     (!accepted [("commit", s!"\"{String.ofList (List.replicate 40 'd')}\"")])
     "another commit was accepted",
   check "record: a record from another toolchain is refused"
     (!accepted [("toolchain", "\"leanprover/lean4:v0.0.0\"")]) "another toolchain was accepted",
   check "record: a record built against another dependency set is refused"
     (!accepted [("lakeManifestSha256", s!"\"{digest64c}\"")]) "another dependency set was accepted",
   -- The one the shell compared leg-to-leg only. Four artifacts carried in from
   -- an earlier run of this same workflow agree with each other perfectly.
   check "record: a record from another run of this workflow is refused"
     (!accepted [("runId", "\"41\"")]) "a record from another run was accepted",
   check "record: a record from another workflow is refused"
     (!accepted [("workflowRef", "\"owner/repo/.github/workflows/ci.yml@refs/heads/main\"")])
     "a record from another workflow was accepted",
   check "record: the wrong-run message says that legs agreeing with each other proves nothing"
     ((recordReport inRun linuxTarget digest64 [("runId", "\"41\"")]).any
       (contains · "agreeing with each other establishes nothing"))
     s!"{recordReport inRun linuxTarget digest64 [("runId", "\"41\"")]}",
   -- Outside a workflow there is no run to disagree with, and that is a stated
   -- choice rather than an absent value silently disabling the comparison.
   check "record: outside a workflow the run identity is not compared"
     ((recordVerdict .outsideWorkflow linuxTarget digest64 [("runId", "\"99\"")]).toOption
       == some true) "a rehearsal refused a record it has nothing to compare against",
   check "record: outside a workflow the other six facts are still compared"
     ((recordVerdict .outsideWorkflow linuxTarget digest64
        [("commit", s!"\"{String.ofList (List.replicate 40 'd')}\"")]).toOption == some false)
     "a rehearsal accepted a record from another commit",
   -- A field this build does not know is refused rather than dropped: the
   -- manifest embeds a record by re-rendering what was parsed, so an unknown
   -- field would survive in one published document and vanish from the other.
   check "record: a field this build does not know is refused, not ignored"
     (mentions (BuildMetadata.parse "b"
       (objectOf (buildMetadataFields ++ [("surprise", "\"x\"")])))
       "a field this build does not know")
     (errorOf (BuildMetadata.parse "b"
       (objectOf (buildMetadataFields ++ [("surprise", "\"x\"")])))),
   check "record: the unknown-field refusal lists the fields there are"
     (mentions (BuildMetadata.parse "b"
       (objectOf (buildMetadataFields ++ [("surprise", "\"x\"")]))) "lakeManifestSha256")
     "the refusal did not say which fields exist",
   -- Every disagreement is reported, not the first: a directory with two
   -- problems must not take two runs of a four-binary pipeline to diagnose.
   check "record: every disagreeing fact is reported at once"
     ((recordReport inRun linuxTarget digest64
        [("commit", s!"\"{String.ofList (List.replicate 40 'd')}\""),
         ("toolchain", "\"leanprover/lean4:v0.0.0\"")]).length == 2)
     s!"{recordReport inRun linuxTarget digest64 [("commit", "\"d…\""), ("toolchain", "\"x\"")]}"]

/-! ## Assembling a release

`Manifest.of` is where the tier policy, the evidence-covers-the-target-list
rule, and the cross-leg run agreement live. Built inside `Except` for the same
reason as the verdict rows: a fixture that stopped parsing must fail rather than
stop asserting. -/

private def sampleIdentity : Identity :=
  { repository := "Owner/tl", npmPackage := "@scope/tl", releaseWorkflow := "w",
    certificateOidcIssuer := "i", certificateIdentityRegexp := "e" }

private def twoTargets : Except String Targets :=
  Targets.parse "t" (targetsOf
    [targetRow "linux-x64" "supported", targetRow "linux-arm64" "best-effort"])

private def evidenceFor (name : String) (tier : String) (digestText : String)
    (overrides : List (String × String)) (linkAudit : Bool) :
    Except String TargetEvidence := do
  let build ← BuildMetadata.parse "b" (metadataText
    ([("target", "\"" ++ name ++ "\""), ("tier", "\"" ++ tier ++ "\"")] ++ overrides))
  let digest ← Sha256.parse "d" digestText
  let tierValue ← Tier.parse "tier" tier
  return { target := sampleTarget name tierValue, found := .present digest (some build) linkAudit }

private def absentFor (name : String) (tier : String) : Except String TargetEvidence := do
  let tierValue ← Tier.parse "tier" tier
  return { target := sampleTarget name tierValue, found := .absent }

private def assembledUnder (run : RunContext) (version : String)
    (evidence : List (Except String TargetEvidence))
    (directory : List (String × Sha256)) : Except String Manifest := do
  let parsedVersion ← Version.parse "v" version
  let facts ← factsOf run
  let targets ← twoTargets
  let rows ← evidence.mapM id
  let inputs : ManifestInputs :=
    { version := parsedVersion
      facts := facts
      identity := sampleIdentity
      targets := targets
      evidence := rows
      directory := directory }
  Manifest.of inputs

private def assembledFrom (version : String) (evidence : List (Except String TargetEvidence))
    (directory : List (String × Sha256)) : Except String Manifest :=
  assembledUnder inRun version evidence directory

private def assemblyRows : Except String (List Outcome) := do
  let shaA ← Sha256.parse "a" digest64
  let shaC ← Sha256.parse "c" digest64c
  -- Asset names composed through `Target.asset` rather than spelled out: the
  -- prefix followed by a target name reads as a tracker id to the task-ID
  -- lint, which cannot tell the two apart, and there is exactly one place that
  -- knows how an asset name is spelled.
  let linuxAsset := (sampleTarget "linux-x64" .supported).asset
  let armAsset := (sampleTarget "linux-arm64" .bestEffort).asset
  let directory : List (String × Sha256) :=
    [(linuxAsset, shaA), (armAsset, shaA), ("LICENSE", shaC)]
  let bothPresent : List (Except String TargetEvidence) :=
    [evidenceFor "linux-x64" "supported" digest64 [] true,
     evidenceFor "linux-arm64" "best-effort" digest64 [] true]
  let complete := assembledFrom "1.2.3" bothPresent directory
  let oneAbsent := assembledFrom "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] true, absentFor "linux-arm64" "best-effort"]
    [(linuxAsset, shaA), ("LICENSE", shaC)]
  let missingRequired := assembledFrom "1.2.3"
    [absentFor "linux-x64" "supported", evidenceFor "linux-arm64" "best-effort" digest64 [] true]
    directory
  let noAudit := assembledFrom "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] false,
     evidenceFor "linux-arm64" "best-effort" digest64 [] true] directory
  let noRecord := assembledFrom "1.2.3"
    [(do let row ← evidenceFor "linux-x64" "supported" digest64 [] true
         return { row with found := .present shaA none true }),
     evidenceFor "linux-arm64" "best-effort" digest64 [] true] directory
  -- Driven outside a workflow deliberately: inside one, each leg is already
  -- held to the ambient run, so a leg from another run is caught per-record and
  -- the cross-leg rule never gets a turn. Outside one there is no ambient run,
  -- and this is the only thing left that says the legs belong together.
  let twoRuns := assembledUnder .outsideWorkflow "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] true,
     evidenceFor "linux-arm64" "best-effort" digest64 [("runId", "\"99\"")] true] directory
  let twoRunsInWorkflow := assembledFrom "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] true,
     evidenceFor "linux-arm64" "best-effort" digest64 [("runId", "\"99\"")] true] directory
  let shortEvidence := assembledFrom "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] true] directory
  let foreignEvidence := assembledFrom "1.2.3"
    (bothPresent ++ [evidenceFor "windows-x64" "supported" digest64 [] true]) directory
  let emptyDirectory := assembledFrom "1.2.3" bothPresent []
  let repeated := assembledFrom "1.2.3" bothPresent (directory ++ [("LICENSE", shaA)])
  let prerelease := assembledFrom "1.2.3-rc.1" bothPresent directory
  let emptyTargets : Except String Manifest := do
    let parsedVersion ← Version.parse "v" "1.2.3"
    let facts ← factsOf inRun
    let inputs : ManifestInputs :=
      { version := parsedVersion
        facts := facts
        identity := sampleIdentity
        targets := ⟨[]⟩
        evidence := []
        directory := directory }
    Manifest.of inputs
  let orphanRecord := assembledFrom "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] true, absentFor "linux-arm64" "best-effort"]
    [(linuxAsset, shaA), ("LICENSE", shaC),
     ((sampleTarget "linux-arm64" .bestEffort).buildMetadataAsset, shaC)]
  let orphanAudit := assembledFrom "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] true, absentFor "linux-arm64" "best-effort"]
    [(linuxAsset, shaA), ("LICENSE", shaC),
     ((sampleTarget "linux-arm64" .bestEffort).linkAuditAsset, shaC)]
  -- The evidence row claims best-effort for a target the list calls Supported.
  -- Its absence must still block the release.
  let demoted := assembledFrom "1.2.3"
    [(do let row ← absentFor "linux-x64" "best-effort"
         return row), evidenceFor "linux-arm64" "best-effort" digest64 [] true]
    directory
  let crossedWorkflows := assembledUnder .outsideWorkflow "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] true,
     evidenceFor "linux-arm64" "best-effort" digest64
       [("workflowRef", "\"owner/repo/.github/workflows/ci.yml@refs/heads/main\"")] true]
    directory
  return [
    check "assembly: a complete candidate set is described"
      complete.toOption.isSome (errorOf complete),
    checkEq "assembly: every target is described, published or not"
      (complete.toOption.map (·.outcomes.length)) (some 2),
    checkEq "assembly: the assets are sorted by name, whatever order they arrived in"
      (complete.toOption.map fun manifest => manifest.assets.map (·.name))
      (some ["LICENSE", armAsset, linuxAsset]),
    -- A missing Best-effort target is recorded as unpublished rather than
    -- omitted: a consumer can tell "we did not build this" from "we do not know
    -- about this".
    check "assembly: a missing Best-effort target still produces a manifest"
      oneAbsent.toOption.isSome (errorOf oneAbsent),
    checkEq "assembly: the absent Best-effort target is recorded, not dropped"
      (oneAbsent.toOption.map fun manifest => manifest.outcomes.length) (some 2),
    checkEq "assembly: an absent target is not listed among the npm packages"
      (oneAbsent.toOption.map fun manifest => manifest.npmPackages)
      (some ["@scope/tl", "@scope/tl-bin-linux-x64"]),
    -- A missing Supported target stops the release.
    check "assembly: a missing Supported target is refused"
      (mentions missingRequired "release-blocking") (errorOf missingRequired),
    -- Both companion files are mandatory, not "compared when present". Written
    -- the other way, deleting the evidence satisfied the check that exists to
    -- prove the signed bytes were smoke-tested.
    check "assembly: a published binary with no link audit is refused"
      (mentions noAudit "link-audit-linux-x64.txt") (errorOf noAudit),
    check "assembly: a published binary with no build record is refused"
      (mentions noRecord "is a refusal rather than a check that gets skipped")
      (errorOf noRecord),
    -- The cross-leg property, which is about the set rather than one record.
    check "assembly: outside a workflow, legs recording different runs are refused"
      (mentions twoRuns "not produced by one run") (errorOf twoRuns),
    check "assembly: inside a workflow, a leg from another run is caught per record"
      (mentions twoRunsInWorkflow "carried in") (errorOf twoRunsInWorkflow),
    -- What an unreadable target list used to do: an empty list skipped every
    -- comparison, and the result was signed.
    check "assembly: a target with no evidence collected for it is refused"
      (mentions shortEvidence "no evidence was collected") (errorOf shortEvidence),
    check "assembly: evidence for a target the list does not carry is refused"
      (mentions foreignEvidence "does not list") (errorOf foreignEvidence),
    check "assembly: a release directory with nothing in it is refused"
      (mentions emptyDirectory "holds no assets") (errorOf emptyDirectory),
    check "assembly: a name collected twice is refused"
      (mentions repeated "collected twice") (errorOf repeated),
    -- An empty target list makes every loop below it vacuous, so a manifest
    -- would be rendered and signed having compared nothing. `Targets.parse`
    -- refuses one; this refuses it again, because a check whose failure mode is
    -- "passes silently on empty input" is worth stating at both ends.
    check "assembly: an empty target list is refused rather than compared vacuously"
      (mentions emptyTargets "every per-leg comparison below would pass")
      (errorOf emptyTargets),
    -- A record or an audit whose binary never arrived would be hashed,
    -- described and signed while nothing compared it to anything.
    check "assembly: a build record for a binary that did not arrive is refused"
      (mentions orphanRecord "did not deliver it") (errorOf orphanRecord),
    check "assembly: a link audit for a binary that did not arrive is refused"
      (mentions orphanAudit "did not deliver it") (errorOf orphanAudit),
    -- The tier decides whether an absence blocks the release, so it comes from
    -- the parsed target list and never from the evidence handed in. Demoting a
    -- Supported target would turn a release-blocking absence into a row saying
    -- "not built" — a partial release describing itself as complete.
    check "assembly: the tier comes from the target list, not from the evidence row"
      (mentions demoted "release-blocking") (errorOf demoted),
    -- Outside a workflow there is no ambient identity, so leg-to-leg agreement
    -- is the only thing left saying the legs belong together — and run ids are
    -- per workflow, so comparing the id alone would admit a binary built by
    -- another workflow that reached the same number.
    check "assembly: outside a workflow, legs naming different workflows are refused"
      (mentions crossedWorkflows "not produced by one run") (errorOf crossedWorkflows),
    -- The two channel decisions read off the parsed version rather than by
    -- searching a string for a hyphen, which is how a prerelease reached the
    -- `latest` tag once already.
    checkEq "assembly: a release publishes to the latest dist-tag"
      (complete.toOption.map (·.npmDistTag)) (some "latest"),
    checkEq "assembly: a prerelease publishes to the next dist-tag"
      (prerelease.toOption.map (·.npmDistTag)) (some "next"),
    checkEq "assembly: a release pushes the tap"
      (complete.toOption.map (·.homebrewPush)) (some true),
    checkEq "assembly: a prerelease does not push the tap"
      (prerelease.toOption.map (·.homebrewPush)) (some false),
    checkEq "assembly: the tap is derived from the identity owner"
      (complete.toOption.map (·.homebrewTap)) (some "Owner/homebrew-tap")]

private def assemblyTests : List Outcome :=
  match assemblyRows with
  | .ok rows => rows
  | .error message => [check "assembly: the fixtures parse" false message]

/-- The document a fixed release assembles to, byte for byte.

    A golden file rather than a set of field assertions, because the manifest is
    hashed into `SHA256SUMS` and signed: what has to hold is that the bytes are a
    function of the release and of nothing else — not that some fields are
    present. Field assertions would go on passing through a key rename, an
    ordering change, or an indentation change, each of which makes two correct
    generations of one release disagree.

    Regenerate deliberately with `--write-golden` on the test binary if the
    document is meant to change, and read the diff: a change here is a change to
    something signed. -/
private def goldenManifestPath : String := "Tests/fixtures/release-manifest-golden.json"

private def goldenManifestDocument : Except String String := do
  let shaA ← Sha256.parse "a" digest64
  let shaC ← Sha256.parse "c" digest64c
  let linuxAsset := (sampleTarget "linux-x64" .supported).asset
  let armAsset := (sampleTarget "linux-arm64" .bestEffort).asset
  let manifest ← assembledFrom "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] true,
     evidenceFor "linux-arm64" "best-effort" digest64 [] true]
    [(linuxAsset, shaA), (armAsset, shaA), ("LICENSE", shaC)]
  renderManifest manifest

/-- The directory a real signing job produces, assembled the way the workflow
    assembles it.

    This exists because two release-blocking defects got past unit tests that
    each passed on a hand-built directory: `manifest-verify` refused the very
    set `manifest` had just described, because the bundles for `SHA256SUMS` and
    the manifest itself are named for the two files a manifest structurally
    cannot describe. Nothing that tests one command at a time can see that —
    only the sequence can. So the sequence is the test: describe, list the
    assets the way the workflow's `find` does, write the sums, sign every one of
    them and the sums file, and only then verify. -/
private def lifecycleTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let dist := base / "dist"
  IO.FS.createDirAll dist
  let write (name : String) (contents : String) : IO Unit :=
    IO.FS.writeFile (dist / name).toString contents
  let commit := String.ofList (List.replicate 40 '7')
  let workflowRef := "o/r/.github/workflows/release.yml@refs/tags/v1.2.3"
  let targets ← IO.FS.readFile "release/targets.json"
  let names : List String := match Targets.parse "t" targets with
    | .ok parsed => parsed.targets.map (fun target => target.name)
    | .error _ => []
  for name in names do
    write ("tl-" ++ name) s!"binary for {name}\n"
    write ("link-audit-" ++ name ++ ".txt") s!"audit for {name}\n"
  write "LICENSE" "license\n"
  write "THIRD-PARTY-LICENSES" "notice\n"
  write "REBUILDING.md" "docs\n"
  write "tl.spdx.json" "{}\n"
  let manifestName := "release-manifest.json"
  let manifestPath := (dist / manifestName).toString
  -- Each leg's record, written by the command a leg runs.
  let mut legStatuses : List UInt32 := []
  for name in names do
    let tier := match Targets.parse "t" targets with
      | .ok parsed => match parsed.find? name with
        | some target => target.tier.wire
        | none => "supported"
      | .error _ => "supported"
    let (status, _, _) ← runCommand "build-metadata"
      ["--target", name, "--binary", (dist / ("tl-" ++ name)).toString,
       "--commit", commit, "--tier", tier, "--runner", "ubuntu-latest",
       "--toolchain", "lean-toolchain", "--lake-manifest", "lake-manifest.json",
       "--workflow-ref", workflowRef, "--run-id", "42",
       "--output-dir", dist.toString, "--output", ("build-metadata-" ++ name ++ ".json")]
    legStatuses := legStatuses ++ [status]
  let (describeStatus, _, describeErr) ← runCommand "manifest"
    ["--dist", dist.toString, "--tag", "v1.2.3", "--commit", commit,
     "--toolchain", "lean-toolchain", "--lake-manifest", "lake-manifest.json",
     "--targets", "release/targets.json", "--identity", "release/identity.json",
     "--workflow-ref", workflowRef, "--run-id", "42",
     "--output-dir", dist.toString, "--output", manifestName]
  -- What the workflow's `find` collects: every regular file except the sums
  -- file and the bundles. The manifest is in this list, which is why its own
  -- bundle exists.
  let entries ← System.FilePath.readDir dist
  let assetNames := (entries.toList.map (·.fileName)).filter fun name =>
    name != "SHA256SUMS" && !name.endsWith ".sigstore.json"
  write "SHA256SUMS" "sums\n"
  write "SHA256SUMS.sigstore.json" "bundle\n"
  for name in assetNames do
    write (name ++ ".sigstore.json") "bundle\n"
  let (verifyStatus, _, verifyErr) ← runCommand "manifest-verify"
    ["--dist", dist.toString, "--manifest", manifestPath]
  -- And a bundle for nothing at all is still refused: the tightening that made
  -- the two above legitimate must not have re-admitted the whole suffix.
  write "not-an-asset.sigstore.json" "bundle\n"
  let (rogueStatus, _, _) ← runCommand "manifest-verify"
    ["--dist", dist.toString, "--manifest", manifestPath]
  IO.FS.removeDirAll base
  return [
    check "lifecycle: every build leg records what it built"
      (legStatuses.all (· == 0)) s!"leg statuses were {legStatuses}",
    check "lifecycle: the sign job describes the release" (describeStatus == 0) describeErr,
    check "lifecycle: the manifest is listed among the assets the workflow signs"
      (assetNames.contains manifestName)
      "the manifest is a regular file in dist, so the workflow signs it and its bundle exists",
    -- The one the unit tests could not see.
    check "lifecycle: the signed directory verifies against its own manifest"
      (verifyStatus == 0) verifyErr,
    checkEq "lifecycle: a bundle named for nothing in the release is still refused"
      rogueStatus 1]

private def goldenManifestTests : IO (List Outcome) := do
  let golden ← IO.FS.readFile goldenManifestPath
  let rendered := okOr "<the golden fixtures stopped assembling>" goldenManifestDocument
  return [
    checkEq "manifest: a fixed release renders to the committed golden bytes" rendered golden,
    -- The property the golden exists for, stated separately so a golden that
    -- was regenerated from a broken generator still fails this.
    check "manifest: the rendered document is pure ASCII with a trailing newline"
      (rendered.endsWith "\n" && rendered.toList.all (fun c => c.toNat < 0x80))
      "the signed document carries bytes whose length depends on an encoding choice"]

/-! ## Reading a manifest back, whole

The manifest is the one description three channels publish from, so the reader
takes all of it and holds it to agreeing with itself before any of them acts.
Every row below takes a manifest this pipeline really assembles, changes one
statement the document makes twice, and requires the reader to refuse.

Driven through `ManifestDescription.parse` — the function `manifest-verify` and
every channel command calls — rather than through the check list directly. The
check list is characterised by `descriptionCoherent_iff`; what these establish
is that the parser consults it, and that each structural refusal reaches the
right message. -/

private def jsonEntries (value : Json) : List (String × Json) :=
  match value with
  | .obj fields => fields.toArray.toList.map fun entry => (entry.1, entry.2)
  | _ => []

private def fieldOf (value : Json) (name : String) : Json :=
  (((jsonEntries value).find? (·.1 == name)).map (·.2)).getD .null

private def withField (value : Json) (name : String) (replacement : Json) : Json :=
  Json.mkObj ((jsonEntries value).map fun (key, held) =>
    if key == name then (key, replacement) else (key, held))

private def withoutField (value : Json) (name : String) : Json :=
  Json.mkObj ((jsonEntries value).filter fun (key, _) => key != name)

/-- Edit one field of a nested object in place. -/
private def withIn (value : Json) (name : String) (edit : Json → Json) : Json :=
  withField value name (edit (fieldOf value name))

/-- Edit the rows of an array field. -/
private def withRows (value : Json) (edit : List Json → List Json) : Json :=
  match value with
  | .arr items => .arr (edit items.toList).toArray
  | other => other

/-- Edit the first row of an array field, which is the published `linux-x64`
    target in every fixture below. -/
private def withFirstRow (value : Json) (edit : Json → Json) : Json :=
  withRows value fun rows =>
    match rows with
    | head :: rest => edit head :: rest
    | [] => []

/-- A manifest this pipeline really assembles, as a value to mutate. -/
private def describedManifest : Except String Json := do
  let shaA ← Sha256.parse "a" digest64
  let shaC ← Sha256.parse "c" digest64c
  let linuxAsset := (sampleTarget "linux-x64" .supported).asset
  let armAsset := (sampleTarget "linux-arm64" .bestEffort).asset
  let manifest ← assembledFrom "1.2.3"
    [evidenceFor "linux-x64" "supported" digest64 [] true,
     evidenceFor "linux-arm64" "best-effort" digest64 [] true]
    [(linuxAsset, shaA), (armAsset, shaA), ("LICENSE", shaC)]
  return manifest.toJson

private def describedPrerelease : Except String Json := do
  let shaA ← Sha256.parse "a" digest64
  let shaC ← Sha256.parse "c" digest64c
  let linuxAsset := (sampleTarget "linux-x64" .supported).asset
  let armAsset := (sampleTarget "linux-arm64" .bestEffort).asset
  let manifest ← assembledFrom "1.2.3-rc.1"
    [evidenceFor "linux-x64" "supported" digest64 [] true,
     evidenceFor "linux-arm64" "best-effort" digest64 [] true]
    [(linuxAsset, shaA), (armAsset, shaA), ("LICENSE", shaC)]
  return manifest.toJson

/-- A mutated fixture, as the document itself. -/
private def parseEditedJson (base : Except String Json) (edit : Json → Json) :
    Except String Json := do
  return edit (← base)

private def parseEdited (base : Except String Json) (edit : Json → Json) :
    Except String ManifestDescription := do
  ManifestDescription.parse "release-manifest.json" (← render (← parseEditedJson base edit))

private def parseMutated (edit : Json → Json) : Except String ManifestDescription :=
  parseEdited describedManifest edit

/-- A mutation is refused, and the refusal says which disagreement it is. -/
private def refuses (what : String) (needle : String) (edit : Json → Json) : Outcome :=
  let result := parseMutated edit
  check s!"description: {what}"
    (result.toOption.isNone && mentions result needle)
    (match result with
     | .ok _ => "the mutated manifest was accepted"
     | .error message => s!"refused, but not for '{needle}': {message}")

private def describedOk : Except String ManifestDescription := parseMutated id

/-- A manifest whose schema version is not a whole number.

    Reached by editing the rendered text: this project's renderer refuses to
    emit a fractional number at all, and the reader still has to refuse one —
    the document it is given was not necessarily written by this build. -/
private def fractionalSchema : Except String ManifestDescription := do
  let text ← render (← describedManifest)
  ManifestDescription.parse "release-manifest.json"
    (String.intercalate "\"schemaVersion\": 1.5"
      (text.splitOn "\"schemaVersion\": 1"))

private def readBack (project : ManifestDescription → α) : Option α :=
  describedOk.toOption.map project

private def descriptionTests : List Outcome :=
  let armRow := (sampleTarget "linux-arm64" .bestEffort).asset
  [ -- The document a real assembly produces reads back, in every section.
    check "description: an assembled manifest reads back whole"
      describedOk.toOption.isSome (errorOf describedOk),
    checkEq "description: the version is parsed, not carried as text"
      (readBack fun d => d.version.render) (some "1.2.3"),
    checkEq "description: the tag reads back" (readBack (·.tag)) (some "v1.2.3"),
    checkEq "description: every target row is read, published or not"
      (readBack fun d => d.targets.length) (some 2),
    checkEq "description: the published targets are read in document order"
      (readBack (·.publishedTargets)) (some ["linux-x64", "linux-arm64"]),
    checkEq "description: each published row carries its own embedded build record"
      (readBack fun d => d.targets.filterMap fun row =>
        match row.outcome with
        | .published _ _ build => some build.target
        | .absent => none)
      (some ["linux-x64", "linux-arm64"]),
    checkEq "description: the signing pins are read back rather than trusted elsewhere"
      (readBack fun d =>
        (d.signing.certificateOidcIssuer, d.signing.certificateIdentityRegexp, d.signing.workflow))
      (some (sampleIdentity.certificateOidcIssuer, sampleIdentity.certificateIdentityRegexp,
        sampleIdentity.releaseWorkflow)),
    checkEq "description: the npm dist-tag is read back" (readBack fun d => d.npm.distTag)
      (some "latest"),
    checkEq "description: the npm package list is read back" (readBack fun d => d.npm.packages)
      (some ["@scope/tl", "@scope/tl-bin-linux-x64", "@scope/tl-bin-linux-arm64"]),
    checkEq "description: the Homebrew section is read back"
      (readBack fun d => (d.homebrew.tap, d.homebrew.push, d.homebrew.pinnedTargets))
      (some ("Owner/homebrew-tap", true, ["linux-x64", "linux-arm64"])),
    -- A prerelease reads back with both of its channel decisions inverted, and
    -- is accepted: the coherence rows compare the document against the version
    -- it states, so they must not accept only stable releases.
    check "description: a prerelease manifest is accepted, with its own channel decisions"
      (match parseEdited describedPrerelease id with
       | .ok d => d.npm.distTag == "next" && d.homebrew.push == false
           && d.version.isPrerelease
       | .error _ => false)
      (errorOf (parseEdited describedPrerelease id)),
    -- A target that did not build is a row, not an omission, and it publishes
    -- nothing anywhere: this is the shape a Best-effort leg failure produces.
    check "description: an unpublished target row reads back as publishing nothing"
      (match parseMutated (fun root =>
          withIn (withIn (withIn root "targets" (withRows · fun rows => rows.take 1))
            "homebrew" (fun brew => withIn brew "pinnedTargets" (withRows · fun rows => rows.take 1)))
            "npm" (fun npm => withIn npm "packages" (withRows · fun rows => rows.take 2))) with
       | .ok d => d.publishedTargets == ["linux-x64"]
       | .error _ => false)
      "dropping the second target row should leave a coherent one-target release",
    -- The whole-document statements.
    refuses "a schema version this build does not read is refused" "schema version"
      (withField · "schemaVersion" (Json.num 2)),
    refuses "a manifest for another product is refused" "describes the product"
      (withField · "product" (Json.str "not-tl")),
    refuses "a tag that is not the version's tag is refused" "records the tag"
      (withField · "tag" (Json.str "v9.9.9")),
    refuses "a manifest with no target rows is refused" "lists no targets"
      (withIn · "targets" (withRows · fun _ => [])),
    refuses "a target listed twice is refused" "lists the target"
      (withIn · "targets" (withRows · fun rows =>
        match rows with
        | head :: rest => head :: head :: rest
        | [] => [])),
    refuses "a manifest with no assets is refused" "describes no assets"
      (withIn · "assets" (withRows · fun _ => [])),
    refuses "an asset described twice is refused" "describes"
      (withIn · "assets" (withRows · fun rows =>
        match rows with
        | head :: rest => head :: head :: rest
        | [] => [])),
    -- The two channel decisions. Both are read off the version, and a document
    -- that states a different one is refused rather than obeyed: an npm version
    -- cannot be withdrawn and a tap carries one formula.
    refuses "a stable release tagged 'next' on npm is refused" "npm dist-tag"
      (withIn · "npm" (withField · "distTag" (Json.str "next"))),
    refuses "an npm package list that omits a published target is refused"
      "does not follow from the targets"
      (withIn · "npm" (withIn · "packages" (withRows · fun rows => rows.take 2))),
    refuses "an npm package list with an extra package is refused"
      "does not follow from the targets"
      (withIn · "npm" (withIn · "packages" (withRows · fun rows =>
        rows ++ [Json.str "@scope/tl-bin-solaris-sparc"]))),
    refuses "a stable release that would not push the tap is refused" "records homebrew push"
      (withIn · "homebrew" (withField · "push" (Json.bool false))),
    refuses "a Homebrew pin list that disagrees with the published targets is refused"
      "pins the Homebrew targets"
      (withIn · "homebrew" (withIn · "pinnedTargets" (withRows · fun rows => rows.take 1))),
    -- The per-row statements, one wrong thing at a time.
    refuses "a target row naming an asset it does not compose is refused" "names the asset"
      (withIn · "targets" (withFirstRow · (withField · "asset" (Json.str "tl-something-else")))),
    -- The asset table's digest for the published binary, moved away from the
    -- target row's. The two sections describe the same file, and a channel
    -- pinning the digest from one of them would serve bytes the other refuses.
    refuses "a target row whose digest the asset table does not carry is refused"
      "the asset table does not agree"
      (withIn · "assets" (withRows · fun rows => rows.map fun row =>
        if fieldOf row "name" == Json.str (sampleTarget "linux-x64" .supported).asset then
          withField row "sha256" (Json.str digest64c)
        else row)),
    refuses "a build record embedded under the wrong target is refused"
      "embeds a build record for" (withIn · "targets" (withFirstRow ·
        (withIn · "build" (withField · "target" (Json.str "linux-arm64"))))),
    refuses "a build record disagreeing about the tier is refused" "records tier"
      (withIn · "targets" (withFirstRow ·
        (withIn · "build" (withField · "tier" (Json.str "best-effort"))))),
    refuses "a build record disagreeing about the bytes is refused"
      "not the bytes that leg built" (withIn · "targets" (withFirstRow ·
        (withIn · "build" (withField · "sha256" (Json.str digest64c))))),
    refuses "a leg that built another commit is refused" "did not all build the same source"
      (withIn · "targets" (withFirstRow ·
        (withIn · "build" (withField · "commit" (Json.str (String.ofList (List.replicate 40 '9'))))))),
    refuses "a leg that built with another toolchain is refused" "the pinned toolchain"
      (withIn · "targets" (withFirstRow ·
        (withIn · "build" (withField · "toolchain" (Json.str "leanprover/lean4:v4.0.0"))))),
    refuses "a leg that built against another dependency set is refused" "dependency set"
      (withIn · "targets" (withFirstRow ·
        (withIn · "build" (withField · "lakeManifestSha256" (Json.str digest64c))))),
    -- The unpublished row's shape. Both halves matter: a row that says it
    -- published nothing while naming an asset is a contradiction a consumer
    -- would resolve by whichever half it read, and a row missing the keys makes
    -- the two shapes different shapes.
    refuses "a row saying it published nothing while naming an asset is refused"
      "disagree about whether this release serves"
      (withIn · "targets" (withRows · fun rows =>
        match rows with
        | head :: rest => withField head "published" (Json.bool false) :: rest
        | [] => [])),
    refuses "an unpublished row missing its null keys is refused"
      "keeps every key with a null value"
      (withIn · "targets" (withRows · fun rows =>
        match rows with
        | head :: rest =>
            withoutField (withoutField (withoutField
              (withField head "published" (Json.bool false)) "asset") "sha256") "build" :: rest
        | [] => [])),
    -- Structure, before agreement. Each of these is a document someone can fix,
    -- reported where it is.
    refuses "a schema version that is not a number is refused" "is not a number"
      (withField · "schemaVersion" (Json.str "1")),
    -- Written as text rather than as a mutation, because this project's own
    -- renderer refuses to emit a fractional number: the reader still has to
    -- refuse one, since the document it reads was not necessarily written by
    -- this build.
    check "description: a fractional schema version is refused"
      (mentions fractionalSchema "not a whole number") (errorOf fractionalSchema),
    refuses "a negative schema version is refused" "is negative"
      (withField · "schemaVersion" (Json.num ⟨-1, 0⟩)),
    refuses "a manifest with no signing section is refused" "has no 'signing' field"
      (withoutField · "signing"),
    refuses "a manifest with no npm section is refused" "has no 'npm' field"
      (withoutField · "npm"),
    refuses "a manifest with no homebrew section is refused" "has no 'homebrew' field"
      (withoutField · "homebrew"),
    refuses "a signing section missing a pin is refused" "has no 'workflow' field"
      (withIn · "signing" (withoutField · "workflow")),
    refuses "a version that is not a version is refused" "is not a number"
      (withField · "version" (Json.str "one.two.three")),
    refuses "an abbreviated commit is refused" "full git object id"
      (withField · "commit" (Json.str "0123456")),
    refuses "a lake-manifest digest of the wrong length is refused" "is not a SHA-256 digest"
      (withField · "lakeManifestSha256" (Json.str "abc")),
    refuses "an empty package name is refused" "is empty"
      (withIn · "npm" (withIn · "packages" (withRows · fun rows => rows ++ [Json.str ""]))),
    refuses "a published flag that is not a boolean is refused" "is not a boolean"
      (withIn · "targets" (withFirstRow · (withField · "published" (Json.str "true")))),
    refuses "a pinned-target list that is not an array is refused" "is not an array"
      (withIn · "homebrew" (withField · "pinnedTargets" (Json.str "linux-x64"))),
    refuses "an asset row with no digest is refused" "has no 'sha256' field"
      (withIn · "assets" (withFirstRow · (withoutField · "sha256"))),
    -- The report is every disagreement at once. Fixing a signed artifact set
    -- one refusal per run is not a thing anyone should be asked to do, and it
    -- is also how the second problem gets discovered after the first is
    -- "fixed" by regenerating.
    check "description: every disagreement is reported, not just the first"
      (let result := parseMutated fun root =>
        withField (withField root "product" (Json.str "not-tl")) "tag" (Json.str "v9.9.9")
       mentions result "describes the product" && mentions result "records the tag")
      (errorOf (parseMutated fun root =>
        withField (withField root "product" (Json.str "not-tl")) "tag" (Json.str "v9.9.9"))),
    -- The arm's own fixture is real: if `assembledFrom` stopped producing a
    -- second target the rows above would be checking a one-target release and
    -- the per-row mutations would still pass.
    check "description: the fixture really describes two targets and three assets"
      (readBack (fun d => (d.targets.length, d.assets.length)) == some (2, 3))
      s!"the fixture changed shape: {readBack fun d => (d.targets.length, d.assets.length)}",
    check "description: the fixture's second target is the Best-effort one"
      (readBack (fun d => d.assets.any (·.name == armRow)) == some true)
      "the arm asset is missing from the fixture"]

/-! ## The Homebrew formula

The formula is rendered, not filled in, so what these establish is that the
rendering is a function of the release: the tracked copy is this renderer's own
output at the placeholder release, a Best-effort target that did not build loses
its block and its pin while the spec stays resolvable, a Supported target that
did not build is refused, and every value that reaches Ruby source is one Ruby
reads as data. -/

private def zeroDigest : String := Homebrew.placeholderDigestHex

private def brewTarget (name tier os cpu : String) : Except String Target :=
  parseTarget { document := "t" } (Json.mkObj
    [("target", Json.str name), ("tier", Json.str tier),
     ("os", Json.str os), ("cpu", Json.str cpu)])

private def brewSpec (versionText : String) (pinned : List (String × String × String × String)) :
    Except String Homebrew.Spec := do
  let version ← Version.parse "v" versionText
  let digest ← Sha256.parse "d" digest64
  let sums ← Sha256.parse "s" digest64c
  let pins ← pinned.mapM fun (name, tier, os, cpu) => do
    let target ← brewTarget name tier os cpu
    return ({ target, digest } : Homebrew.Pin)
  return {
    version, sumsDigest := sums, pins
    repository := "Owner/tl"
    tap := "Owner/homebrew-tap"
    issuer := "https://token.actions.githubusercontent.com"
    certificateIdentity := "^https://github\\.com/Owner/tl/x$" }

private def allFour : List (String × String × String × String) :=
  [("linux-x64", "supported", "linux", "x64"),
   ("linux-arm64", "supported", "linux", "arm64"),
   ("darwin-arm64", "supported", "darwin", "arm64"),
   ("darwin-x64", "best-effort", "darwin", "x64")]

private def renderedFormula (versionText : String)
    (pinned : List (String × String × String × String)) : Except String String := do
  Homebrew.render (← brewSpec versionText pinned)

private def formulaText (versionText : String)
    (pinned : List (String × String × String × String)) : String :=
  okOr "<the formula did not render>" (renderedFormula versionText pinned)

/-- Both formula commands, driven the way a release job drives them. -/
private def homebrewCommandTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let dist := base / "dist"
  IO.FS.createDirAll dist
  let manifestText := okOr "<the fixture stopped assembling>" (do
    render (← describedManifest))
  let manifestPath := (dist / "release-manifest.json").toString
  IO.FS.writeFile manifestPath manifestText
  IO.FS.writeFile (dist / "SHA256SUMS").toString "sums\n"
  let sumsDigest := okOr "<no digester>" (← do
    match ← Digester.resolve with
    | .error message => pure (.error message)
    | .ok digester =>
        pure ((← digester.digest (dist / "SHA256SUMS").toString).map (·.hex)))
  let (renderStatus, renderOut, renderErr) ← runCommand "homebrew-render"
    ["--dist", dist.toString, "--manifest", manifestPath,
     "--output", "tl.rb", "--output-dir", base.toString]
  let renderedPath := (base / "tl.rb")
  let rendered ← if ← renderedPath.pathExists then IO.FS.readFile renderedPath else pure ""
  -- A manifest that publishes nothing for a Supported target, and is otherwise
  -- coherent: the three sections that follow from the published set are edited
  -- with it. This is what proves the coverage refusal is reachable — the
  -- assembler refuses to *build* such a release, so without this the rule would
  -- only ever be exercised through a value no command can receive.
  let missingSupported := okOr "<the fixture stopped assembling>" (do
    render (← parseEditedJson describedManifest fun root =>
      withIn (withIn (withIn root "targets" (withFirstRow · fun row =>
          withField (withField (withField (withField row "published" (Json.bool false))
            "asset" Json.null) "sha256" Json.null) "build" Json.null))
        "homebrew" (fun brew => withIn brew "pinnedTargets" (withRows · fun rows => rows.drop 1)))
        "npm" (fun npm => withIn npm "packages" (withRows · fun rows =>
          rows.take 1 ++ rows.drop 2))))
  let partialPath := (dist / "partial.json").toString
  IO.FS.writeFile partialPath missingSupported
  let (partialStatus, _, partialErr) ← runCommand "homebrew-render"
    ["--dist", dist.toString, "--manifest", partialPath,
     "--output", "partial.rb", "--output-dir", base.toString]
  let partialWritten ← (base / "partial.rb").pathExists
  let (absentManifest, _, absentErr) ← runCommand "homebrew-render"
    ["--dist", dist.toString, "--manifest", (dist / "nothing.json").toString,
     "--output", "tl.rb", "--output-dir", base.toString]
  let bareDist := base / "bare"
  IO.FS.createDirAll bareDist
  IO.FS.writeFile (bareDist / "release-manifest.json").toString manifestText
  let (noSums, _, noSumsErr) ← runCommand "homebrew-render"
    ["--dist", bareDist.toString, "--manifest", (bareDist / "release-manifest.json").toString,
     "--output", "tl.rb", "--output-dir", base.toString]
  let (renderUsage, _, _) ← runCommand "homebrew-render"
    ["--dist", dist.toString, "--manifest", manifestPath]
  let (placeholderStatus, _, placeholderErr) ← runCommand "homebrew-placeholder"
    ["--identity", "release/identity.json", "--targets", "release/targets.json",
     "--output", "placeholder.rb", "--output-dir", base.toString]
  let placeholder ← if ← (base / "placeholder.rb").pathExists then
      IO.FS.readFile (base / "placeholder.rb") else pure ""
  let (noIdentity, _, noIdentityErr) ← runCommand "homebrew-placeholder"
    ["--identity", (dist / "nothing.json").toString, "--targets", "release/targets.json",
     "--output", "x.rb", "--output-dir", base.toString]
  let brokenTargets := (dist / "targets.json").toString
  IO.FS.writeFile brokenTargets "{\"targets\": []}"
  let (emptyTargets, _, emptyTargetsErr) ← runCommand "homebrew-placeholder"
    ["--identity", "release/identity.json", "--targets", brokenTargets,
     "--output", "y.rb", "--output-dir", base.toString]
  let (placeholderUsage, _, _) ← runCommand "homebrew-placeholder"
    ["--identity", "release/identity.json", "--targets", "release/targets.json"]
  let tracked ← IO.FS.readFile "Formula/tl.rb"
  IO.FS.removeDirAll base
  return [
    check "homebrew-render: a verified release renders a formula" (renderStatus == 0) renderErr,
    check "homebrew-render: it says where it wrote and what it pinned"
      (contains renderOut "v1.2.3" && contains renderOut "pinning 2") renderOut,
    check "homebrew-render: the formula pins the release's own tag"
      (contains rendered "/download/v1.2.3/SHA256SUMS") rendered,
    -- The fallback digest comes from the directory, because the sums file is
    -- the one asset the manifest structurally cannot describe.
    check "homebrew-render: the fallback url pins the digest of the directory's SHA256SUMS"
      (contains rendered s!"  sha256 \"{sumsDigest}\"") s!"expected {sumsDigest} in the formula",
    check "homebrew-render: the published targets are the ones pinned"
      (contains rendered "PINNED_TARGETS = %w[linux-arm64 linux-x64]") rendered,
    -- The coverage rule, reached through the command rather than the function.
    checkEq "homebrew-render: a release missing a Supported target is refused" partialStatus 1,
    check "homebrew-render: the refusal names the target and says why it matters"
      (contains partialErr "linux-x64" && contains partialErr "raises on *load*") partialErr,
    check "homebrew-render: a refused release writes no formula at all"
      (!partialWritten) "a partial formula was left behind for someone to publish",
    checkEq "homebrew-render: a manifest that is not there is refused" absentManifest 1,
    check "homebrew-render: that refusal names the path it could not read"
      (contains absentErr "nothing.json") absentErr,
    checkEq "homebrew-render: a directory with no SHA256SUMS is refused" noSums 1,
    check "homebrew-render: that refusal names the file the fallback url needs"
      (contains noSumsErr "SHA256SUMS") noSumsErr,
    checkEq "homebrew-render: a missing --output is a usage error, not a refusal" renderUsage 2,
    check "homebrew-placeholder: the tracked formula renders" (placeholderStatus == 0)
      placeholderErr,
    check "homebrew-placeholder: what it writes is what is tracked" (placeholder == tracked)
      "the placeholder command and the tracked formula disagree",
    checkEq "homebrew-placeholder: an identity file that is not there is refused" noIdentity 1,
    check "homebrew-placeholder: that refusal names the path" (contains noIdentityErr "nothing.json")
      noIdentityErr,
    checkEq "homebrew-placeholder: an empty target list is refused" emptyTargets 1,
    check "homebrew-placeholder: that refusal says a release with no targets is not smaller"
      (contains emptyTargetsErr "lists no targets") emptyTargetsErr,
    checkEq "homebrew-placeholder: a missing --output is a usage error" placeholderUsage 2]

/-! ### Updating the tap

Driven against a real git remote — a bare repository on disk, cloned the way the
release job clones the tap — because the property is that publication happens
once. A stub git could be made to say anything about a diff; what has to hold is
that a second run of a job that already pushed produces no second commit. -/

private def gitRun (cwd : String) (args : List String) : IO UInt32 := do
  match ← Release.run "git" ((["-C", cwd] ++ args).toArray) with
  | .completed output => return output.exitCode
  | _ => return 127

private def commitCount (checkout : String) : IO String := do
  match ← Release.succeeded "git" #["-C", checkout, "rev-list", "--count", "HEAD"] with
  | .ok output => return output.stdout.trimAscii.toString
  | .error message => return message

private def tapPublishTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let manifestText := okOr "<the fixture stopped assembling>" (do render (← describedManifest))
  let prereleaseText := okOr "<the fixture stopped assembling>" (do render (← describedPrerelease))
  let dist := base / "dist"
  IO.FS.createDirAll dist
  let manifestPath := (dist / "release-manifest.json").toString
  IO.FS.writeFile manifestPath manifestText
  let prereleasePath := (dist / "prerelease.json").toString
  IO.FS.writeFile prereleasePath prereleaseText
  IO.FS.writeFile (dist / "SHA256SUMS").toString "sums\n"
  -- What this release renders, computed the way the command does, so the rows
  -- below compare the tap against the release rather than against a file the
  -- test happened to write.
  let sumsDigest ← (do
    match ← Digester.resolve with
    | .error message => pure (.error message)
    | .ok digester => pure (← digester.digest (dist / "SHA256SUMS").toString))
  let expected := okOr "<the fixture stopped rendering>" (do
    let description ← ManifestDescription.parse "m" manifestText
    Homebrew.renderCovering description.distributedTargets
      (Homebrew.specOf description (← sumsDigest)))
  -- The tap, as a bare repository the release job pushes to. Named for the tap
  -- the fixture manifest describes, because that is what the origin check reads.
  let owner := base / "Owner"
  IO.FS.createDirAll owner
  let remotePath := (owner / "homebrew-tap.git").toString
  let _ ← gitRun base.toString ["init", "--bare", "--initial-branch=main", "--", remotePath]
  let checkout := (base / "tap").toString
  let _ ← gitRun base.toString ["clone", "--quiet", "--", remotePath, checkout]
  IO.FS.createDirAll (checkout ++ "/Formula")
  IO.FS.writeFile (checkout ++ "/README.md") "tap\n"
  let _ ← gitRun checkout ["add", "-A"]
  let _ ← gitRun checkout
    ["-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-qm", "init"]
  let _ ← gitRun checkout ["push", "--quiet", "origin", "HEAD:main"]
  let before ← commitCount checkout
  -- A prerelease first: the tap must be left exactly as it is.
  let (preStatus, preOut, preErr) ← runCommand "homebrew-publish"
    ["--dist", dist.toString, "--manifest", prereleasePath, "--tap", checkout]
  let afterPrerelease ← commitCount checkout
  let (dryStatus, dryOut, dryErr) ← runCommand "homebrew-publish"
    ["--dist", dist.toString, "--manifest", manifestPath, "--tap", checkout, "--dry-run"]
  let afterDry ← commitCount checkout
  let (firstStatus, firstOut, firstErr) ← runCommand "homebrew-publish"
    ["--dist", dist.toString, "--manifest", manifestPath, "--tap", checkout]
  let afterFirst ← commitCount checkout
  let published ← if ← System.FilePath.pathExists (checkout ++ "/Formula/tl.rb") then
      IO.FS.readFile (checkout ++ "/Formula/tl.rb") else pure ""
  -- The bare repository received it, which is what "pushed" has to mean.
  let remoteHas ← Release.succeeded "git" #["-C", remotePath, "show", "main:Formula/tl.rb"]
  -- Twice. A job that failed after pushing and is retried must reach the
  -- comparison and stop, not add a second commit saying the same thing.
  let (againStatus, againOut, _) ← runCommand "homebrew-publish"
    ["--dist", dist.toString, "--manifest", manifestPath, "--tap", checkout]
  let afterAgain ← commitCount checkout
  -- A tap holding some other formula is replaced by this release's.
  IO.FS.writeFile (checkout ++ "/Formula/tl.rb") "class Tl < Formula\n  # someone else\nend\n"
  let _ ← gitRun checkout ["add", "-A"]
  let _ ← gitRun checkout
    ["-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-qm", "drift"]
  let (changedStatus, changedOut, _) ← runCommand "homebrew-publish"
    ["--dist", dist.toString, "--manifest", manifestPath, "--tap", checkout]
  let afterChanged ← commitCount checkout
  let restored ← IO.FS.readFile (checkout ++ "/Formula/tl.rb")
  -- A checkout of the wrong repository.
  let wrongRemote := (base / "elsewhere.git").toString
  let _ ← gitRun base.toString ["init", "--bare", "--initial-branch=main", "--", wrongRemote]
  let wrongCheckout := (base / "wrong").toString
  let _ ← gitRun base.toString ["clone", "--quiet", "--", wrongRemote, wrongCheckout]
  IO.FS.createDirAll (wrongCheckout ++ "/Formula")
  let (wrongStatus, _, wrongErr) ← runCommand "homebrew-publish"
    ["--dist", dist.toString, "--manifest", manifestPath, "--tap", wrongCheckout]
  -- A tap with no Formula directory: a shape this command updates rather than
  -- decides.
  let bareCheckout := (base / "noformula").toString
  let _ ← gitRun base.toString ["clone", "--quiet", "--", remotePath, bareCheckout]
  IO.FS.removeDirAll (bareCheckout ++ "/Formula")
  let (noDirStatus, _, noDirErr) ← runCommand "homebrew-publish"
    ["--dist", dist.toString, "--manifest", manifestPath, "--tap", bareCheckout]
  let (absentSums, _, absentSumsErr) ← runCommand "homebrew-publish"
    ["--dist", (base / "nowhere").toString, "--manifest", manifestPath, "--tap", checkout]
  let (notARepo, _, notARepoErr) ← runCommand "homebrew-publish"
    ["--dist", dist.toString, "--manifest", manifestPath, "--tap", base.toString]
  let (publishUsage, _, _) ← runCommand "homebrew-publish"
    ["--dist", dist.toString, "--manifest", manifestPath]
  IO.FS.removeDirAll base
  return [
    check "homebrew-publish: a prerelease is an outcome, not a failure" (preStatus == 0) preErr,
    check "homebrew-publish: it says the tap keeps the formula it has"
      (contains preOut "prerelease" && contains preOut "carries one formula") preOut,
    checkEq "homebrew-publish: a prerelease adds no commit" afterPrerelease before,
    check "homebrew-publish: a dry run reports what it would do" (dryStatus == 0) dryErr,
    check "homebrew-publish: the dry run names the state it found"
      (contains dryOut "no formula for tl yet" && contains dryOut "--dry-run") dryOut,
    checkEq "homebrew-publish: a dry run adds no commit" afterDry before,
    check "homebrew-publish: a stable release updates the tap" (firstStatus == 0) firstErr,
    check "homebrew-publish: it says what it pushed and where"
      (contains firstOut "v1.2.3" && contains firstOut "Owner/homebrew-tap") firstOut,
    -- The bytes pushed are what this release renders, not a file the caller
    -- named: passing the tracked placeholder used to publish `version 0.0.0`
    -- and five all-zero digests while reporting the release's own tag.
    checkEq "homebrew-publish: the tap carries the formula this release renders"
      published expected,
    check "homebrew-publish: the remote received it, which is what pushing means"
      (remoteHas.toOption.map (·.stdout) == some expected)
      s!"the bare repository does not hold the formula: {errorOf remoteHas}",
    checkEq "homebrew-publish: publishing added exactly one commit"
      (before, afterFirst) ("1", "2"),
    -- Idempotence, which is what makes a retried release job safe.
    check "homebrew-publish: an identical formula is a no-op" (againStatus == 0) againOut,
    check "homebrew-publish: it says the tap already carries this formula"
      (contains againOut "already carries") againOut,
    checkEq "homebrew-publish: the no-op adds no second commit" afterAgain afterFirst,
    check "homebrew-publish: a changed formula is pushed" (changedStatus == 0) changedOut,
    check "homebrew-publish: it says the tap carried a different formula"
      (contains changedOut "different formula") changedOut,
    checkEq "homebrew-publish: the replacement is this release's formula" restored expected,
    -- One more than the drift commit the fixture made, not one more than the
    -- publication: the tap moved, and this replaced it.
    checkEq "homebrew-publish: the change is one further commit" afterChanged "4",
    -- The destination check, and the refusal that must not quote the remote.
    checkEq "homebrew-publish: a checkout of another repository is refused" wrongStatus 1,
    check "homebrew-publish: the refusal names the tap the manifest describes"
      (contains wrongErr "Owner/homebrew-tap") wrongErr,
    check "homebrew-publish: the refusal does not repeat the remote url, which carries a credential"
      (!contains wrongErr "elsewhere.git") wrongErr,
    checkEq "homebrew-publish: a tap with no Formula directory is refused" noDirStatus 1,
    check "homebrew-publish: that refusal says a tap keeps its formulae under Formula/"
      (contains noDirErr "under Formula/") noDirErr,
    checkEq "homebrew-publish: a directory with no SHA256SUMS is refused" absentSums 1,
    check "homebrew-publish: that refusal names the file the fallback url needs"
      (contains absentSumsErr "SHA256SUMS") absentSumsErr,
    checkEq "homebrew-publish: a directory that is not a git checkout is refused" notARepo 1,
    check "homebrew-publish: that refusal carries git's own diagnosis"
      (contains notARepoErr "git") notARepoErr,
    checkEq "homebrew-publish: a missing --tap is a usage error" publishUsage 2]

/-- Every url a remote may be written as, and the ones that are not this tap. -/
private def tapRemoteTests : List Outcome :=
  let tap := "Owner/homebrew-tap"
  let accepts (url : String) := Homebrew.tapRemoteAccepts tap url
  [ check "tap remote: the https url the release workflow uses is accepted"
      (accepts "https://github.com/Owner/homebrew-tap.git") "",
    check "tap remote: the same url with a credential is accepted"
      (accepts "https://x-access-token:secret@github.com/Owner/homebrew-tap.git") "",
    check "tap remote: an https url without the .git suffix is accepted"
      (accepts "https://github.com/Owner/homebrew-tap") "",
    check "tap remote: a trailing slash is accepted"
      (accepts "https://github.com/Owner/homebrew-tap/") "",
    check "tap remote: the ssh spelling is accepted"
      (accepts "git@github.com:Owner/homebrew-tap.git") "",
    check "tap remote: a local path is accepted, which is what makes this testable"
      (accepts "/tmp/fixture/Owner/homebrew-tap.git") "",
    check "tap remote: surrounding whitespace is trimmed, as git's own output has"
      (accepts "  https://github.com/Owner/homebrew-tap.git\n") "",
    check "tap remote: another repository of the same owner is refused"
      (!accepts "https://github.com/Owner/tl.git") "",
    check "tap remote: another owner's tap of the same name is refused"
      (!accepts "https://github.com/Someone/homebrew-tap.git") "",
    check "tap remote: a repository whose name merely ends with the tap's is refused"
      (!accepts "https://github.com/Owner/not-homebrew-tap.git") "",
    check "tap remote: a repository whose owner merely ends with this one is refused"
      (!accepts "https://github.com/NotOwner/homebrew-tap.git") "",
    check "tap remote: the empty url is refused" (!accepts "") "",
    check "tap remote: a url that only contains the tap deeper in its path is refused"
      (!accepts "https://github.com/Owner/homebrew-tap/subdir") ""]

/-- The digest a fixture pins for the `index`-th target: sixty-three zeroes and
    a distinct final digit, so a url pinned under the wrong block is visible in
    the file rather than only in a comparison. -/
private def fixtureDigestHex (index : Nat) : String :=
  String.ofList (List.replicate 63 '0') ++ toString (index % 10)

private def fixtureSumsHex : String := String.ofList (List.replicate 63 '0') ++ "9"

/-- A fixture release at this version, publishing every target but the dropped
    ones. Built from this repository's real identity and target list, so the
    formulae real Homebrew audits have this project's platforms in them. -/
private def fixtureSpec (identity : Identity) (targets : Targets) (versionText : String)
    (drop : List String) : Except String Homebrew.Spec := do
  let version ← Version.parse "v" versionText
  let sums ← Sha256.parse "s" fixtureSumsHex
  let pins ← (targets.targets.zipIdx.filter fun (target, _) =>
      !drop.contains target.name).mapM fun (target, index) => do
    let digest ← Sha256.parse "d" (fixtureDigestHex (index + 1))
    return ({ target, digest } : Homebrew.Pin)
  return {
    version, sumsDigest := sums, pins
    repository := identity.repository
    tap := identity.homebrewTap
    issuer := identity.certificateOidcIssuer
    certificateIdentity := identity.certificateIdentityRegexp }

/-- The three shapes CI hands to real Homebrew, beside the tracked placeholder.

    They are committed rather than generated in the macOS job because that job
    has no Lean toolchain: the drift rows below are what make the committed
    bytes this renderer's own output, and `brew` is then judging the thing a
    release publishes rather than a file someone wrote. -/
private def formulaFixtures : List (String × String × List String) :=
  [("full", "1.2.3", []),
   ("dropped", "1.2.3", ["darwin-x64"]),
   ("prerelease", "1.2.3-rc.1", [])]

/-- The tracked copies, and what this renderer says they should be. -/
private def formulaDriftTests : IO (List Outcome) := do
  let scratch ← IO.FS.createTempDir
  let tracked ← IO.FS.readFile "Formula/tl.rb"
  let identityText ← IO.FS.readFile "release/identity.json"
  let targetsText ← IO.FS.readFile "release/targets.json"
  let rendered : Except String String := do
    let identity ← Identity.parse "release/identity.json" identityText
    let targets ← Targets.parse "release/targets.json" targetsText
    let spec ← Homebrew.placeholderSpec identity targets
    Homebrew.renderCovering targets.targets spec
  let mut fixtureRows : List Outcome := []
  for (name, versionText, drop) in formulaFixtures do
    let path := s!"Tests/fixtures/homebrew/{name}.rb"
    let committed ← if ← System.FilePath.pathExists path then IO.FS.readFile path else pure ""
    let expected : Except String String := do
      let identity ← Identity.parse "release/identity.json" identityText
      let targets ← Targets.parse "release/targets.json" targetsText
      Homebrew.renderCovering targets.targets (← fixtureSpec identity targets versionText drop)
    fixtureRows := fixtureRows ++ [
      check s!"formula: the committed {name} fixture is exactly what this renderer produces"
        (expected.toOption == some committed)
        (match expected with
         | .error message => s!"the {name} fixture did not render: {message}"
         | .ok text =>
             s!"{path} is stale — real Homebrew audits it in CI, so it has to be this renderer's own output. What it should contain has been written to {(scratch / s!"{name}.rb").toString}; copy that over it. Rendered {text.length} bytes against {committed.length} committed")]
    -- Written whether or not the row holds, because a failing row whose remedy
    -- is "reproduce 190 lines by hand" is a row people edit the fixture to
    -- satisfy. These are the only formulae in the repository with no command
    -- that regenerates them: they describe a release, and no release exists.
    match expected with
    | .ok text => IO.FS.writeFile (scratch / s!"{name}.rb").toString text
    | .error _ => pure ()
  return fixtureRows ++ [
    -- The whole point of rendering rather than substituting: the tracked file
    -- is an output, so editing it by hand fails here instead of quietly
    -- publishing a formula nothing generated.
    check "formula: the tracked Formula/tl.rb is exactly what this renderer produces"
      (rendered.toOption == some tracked)
      (match rendered with
       | .error message => s!"the placeholder did not render: {message}"
       | .ok text =>
           s!"regenerate it with `tlrelease homebrew-placeholder --identity release/identity.json --targets release/targets.json --output tl.rb --output-dir Formula`; rendered {text.length} bytes against {tracked.length} tracked"),
    -- And it is still a placeholder. A filled-in copy committed by accident
    -- would pin a stale release, and this is the property that says so
    -- independently of the byte comparison above.
    check "formula: the tracked copy pins nothing installable"
      ((tracked.splitOn zeroDigest).length == 6)
      s!"expected five placeholder digests (four targets and the fallback), found {(tracked.splitOn zeroDigest).length - 1}"]

private def homebrewTests : List Outcome :=
  let full := formulaText "1.2.3" allFour
  let dropped := formulaText "1.2.3" (allFour.filter fun (name, _, _, _) => name != "darwin-x64")
  let pre := formulaText "1.2.3-rc.1" allFour
  let noMac := formulaText "1.2.3" (allFour.filter fun (_, _, os, _) => os != "darwin")
  let missingSupported : Except String String := do
    let spec ← brewSpec "1.2.3" (allFour.filter fun (name, _, _, _) => name != "linux-arm64")
    let targets ← allFour.mapM fun (name, tier, os, cpu) => brewTarget name tier os cpu
    Homebrew.renderCovering targets spec
  let droppedBestEffort : Except String String := do
    let spec ← brewSpec "1.2.3" (allFour.filter fun (name, _, _, _) => name != "darwin-x64")
    let targets ← allFour.mapM fun (name, tier, os, cpu) => brewTarget name tier os cpu
    Homebrew.renderCovering targets spec
  let withField (edit : Homebrew.Spec → Homebrew.Spec) : Except String String := do
    Homebrew.render (edit (← brewSpec "1.2.3" allFour))
  let unknownOs : Except String String := do
    Homebrew.render (← brewSpec "1.2.3" [("plan9-x64", "supported", "plan9", "x64")])
  let unknownCpu : Except String String := do
    Homebrew.render (← brewSpec "1.2.3" [("linux-riscv", "supported", "linux", "riscv")])
  let nothingPinned : Except String String := do
    let spec ← brewSpec "1.2.3" []
    let targets ← [("darwin-x64", "best-effort", "darwin", "x64")].mapM
      fun (name, tier, os, cpu) => brewTarget name tier os cpu
    Homebrew.renderCovering targets spec
  [ -- Every pinned target gets its own block, under its own digest.
    check "formula: a complete release renders" (renderedFormula "1.2.3" allFour).toOption.isSome
      (errorOf (renderedFormula "1.2.3" allFour)),
    check "formula: every pinned target has a url"
      (allFour.all fun (name, _, _, _) => contains full s!"ASSET_PREFIX}{name}\"")
      full,
    checkEq "formula: every pinned target's url carries a digest"
      ((full.splitOn "      sha256 \"").length - 1) 4,
    checkEq "formula: the fallback url carries one too, so five digests in all"
      ((full.splitOn "sha256 \"").length - 1) 5,
    check "formula: the fallback url pins the sums file's own digest"
      (contains full s!"  sha256 \"{digest64c}\"") full,
    check "formula: each platform digest lands under its own url"
      (contains full ("ASSET_PREFIX}linux-x64\"\n      sha256 \"" ++ digest64 ++ "\"")) full,
    check "formula: the pinned targets are listed for install to consult"
      (contains full "PINNED_TARGETS = %w[darwin-arm64 darwin-x64 linux-arm64 linux-x64]") full,
    -- Sorted, and sorted independently of the order the release listed them:
    -- the tap compares formula text, so a reordering would read as a change.
    checkEq "formula: the pinned-target list does not depend on manifest order"
      (okOr "<a>" (renderedFormula "1.2.3" allFour))
      (okOr "<b>" (renderedFormula "1.2.3" allFour.reverse)),
    check "formula: the identity pins are rendered into the formula"
      (contains full "OIDC_ISSUER = \"https://token.actions.githubusercontent.com\""
        && contains full "CERTIFICATE_IDENTITY = '^https://github\\.com/Owner/tl/x$'") full,
    check "formula: the signature check survives rendering"
      (contains full "verify-blob" && contains full "--certificate-identity-regexp") full,
    -- The stable/prerelease split. Homebrew scans a version out of the fallback
    -- url and `brew audit` calls an explicit one redundant — except on a
    -- prerelease, where the scanner drops the suffix and the scanned value is
    -- the wrong release.
    check "formula: a stable release carries no explicit version line"
      (!contains full "\n  version \"") full,
    check "formula: a prerelease carries an explicit version line"
      (contains pre "\n  version \"1.2.3-rc.1\"") pre,
    check "formula: every prerelease url names the prerelease tag"
      (contains pre "/download/v1.2.3-rc.1/" && !contains pre "/download/v1.2.3/") pre,
    -- A Best-effort target that did not build: block dropped, pin dropped, and
    -- the fallback url still there — without it Homebrew raises on *load* for
    -- every brew command touching the tap.
    check "formula: a dropped Best-effort target renders" droppedBestEffort.toOption.isSome
      (errorOf droppedBestEffort),
    check "formula: the dropped target has no url"
      (!contains dropped "ASSET_PREFIX}darwin-x64\"") dropped,
    check "formula: the dropped target is absent from the pin list, so install refuses there"
      (contains dropped "PINNED_TARGETS = %w[darwin-arm64 linux-arm64 linux-x64]") dropped,
    check "formula: the dropped-block formula keeps its fallback url, so the spec resolves"
      (contains dropped "/download/v1.2.3/SHA256SUMS") dropped,
    checkEq "formula: the dropped-block formula pins three targets plus the fallback"
      ((dropped.splitOn "sha256 \"").length - 1) 4,
    -- A whole platform with nothing pinned writes no block at all. An empty
    -- `on_macos do end` is legal Ruby that tells a reader macOS was considered
    -- and found empty, which is the wrong impression.
    check "formula: an operating system with no pinned target gets no empty block"
      (!contains noMac "on_macos" && contains noMac "on_linux") noMac,
    -- The one decision with a theorem: a Supported target with no url would
    -- make Homebrew raise on load for that whole platform.
    check "formula: a release missing a Supported target renders nothing"
      (missingSupported.toOption.isNone) "a partial formula was rendered",
    check "formula: the refusal names the target and its tier"
      (mentions missingSupported "linux-arm64" && mentions missingSupported "Supported")
      (errorOf missingSupported),
    -- Every value that reaches Ruby source. The old generator needed a SemVer
    -- guard because its version was a string; the version is a parsed `Version`
    -- here, and these are the values that still arrive from a JSON document.
    check "formula: a repository that would close the Ruby string is refused"
      (mentions (withField fun spec => { spec with repository := "o\"; system \"id\"; x=\"" })
        "end the string literal")
      (errorOf (withField fun spec => { spec with repository := "o\"" })),
    check "formula: a repository carrying a Ruby interpolation is refused"
      (mentions (withField fun spec => { spec with repository := "o/#{`id`}" })
        "begin an interpolation")
      (errorOf (withField fun spec => { spec with repository := "o/#{`id`}" })),
    check "formula: an issuer with a backslash is refused"
      (mentions (withField fun spec => { spec with issuer := "https://x\\ny" }) "backslash")
      (errorOf (withField fun spec => { spec with issuer := "https://x\\ny" })),
    check "formula: an identity expression with a single quote is refused"
      (mentions (withField fun spec => { spec with certificateIdentity := "^a'; system('id'); b$" })
        "single quote")
      (errorOf (withField fun spec => { spec with certificateIdentity := "^a'$" })),
    check "formula: an identity expression ending in a backslash is refused"
      (mentions (withField fun spec => { spec with certificateIdentity := "^a\\" })
        "escaping the closing quote")
      (errorOf (withField fun spec => { spec with certificateIdentity := "^a\\" })),
    check "formula: a non-ASCII pin is refused rather than written into executable source"
      (mentions (withField fun spec => { spec with issuer := "https://café.example" })
        "outside printable ASCII")
      (errorOf (withField fun spec => { spec with issuer := "https://café.example" })),
    -- A platform this renderer cannot place would be dropped by the per-block
    -- lookup, which looks exactly like a target the release did not build.
    check "formula: a target whose operating system has no Homebrew block is refused"
      (mentions unknownOs "on_macos") (errorOf unknownOs),
    check "formula: a target whose processor has no Homebrew block is refused"
      (mentions unknownCpu "on_arm") (errorOf unknownCpu),
    -- The renderer is a function of the spec, which is what makes the tap
    -- comparison "is this the formula this release renders".
    checkEq "formula: rendering the same spec twice produces the same bytes"
      (okOr "<a>" (renderedFormula "1.2.3" allFour))
      (okOr "<b>" (renderedFormula "1.2.3" allFour)),
    check "formula: the rendered formula ends in a newline"
      (full.endsWith "\n") "a Ruby file that does not end in a newline",
    -- A release whose targets are all Best-effort and all failed. Every
    -- per-target row holds by having nothing release-blocking to satisfy, so
    -- without its own row this renders a formula that loads everywhere and
    -- installs nowhere.
    check "formula: a release that pins nothing at all is refused" nothingPinned.toOption.isNone
      "a formula with no url, no block and an empty pin list was rendered",
    check "formula: that refusal says the tap update would publish nothing"
      (mentions nothingPinned "publishes nothing") (errorOf nothingPinned)]

/-! ## The typed release policy registry

The registry is data, so what these establish is that the projections of it are
the ones the shell performs — and that the three decisions over it (may a gate
be skipped, did the run pass, what does a surface contribute) are the ones the
theorems characterise, driven to every crossing. -/

private def sampleGate (name : String) (requires : List Policy.ToolRequirement) : Policy.Gate :=
  { name, requires, profiles := [.ci], onTag := .always
    invocation := .tool "true" [], summary := "" }

private def presentOnly (tools : List String) : String → Bool := fun tool => tools.contains tool

private def policyTests : List Outcome :=
  let ciNames := Policy.gateNames .ci false
  let releaseNames := Policy.gateNames .release false
  let releaseTagNames := Policy.gateNames .release true
  let needsBoth := sampleGate "two tools"
    [{ tool := "actionlint", lost := "actionlint is not on PATH" },
     { tool := "shellcheck", lost := "actionlint is present but shellcheck is not" }]
  let needsNone := sampleGate "no tools" []
  let missingOf (present : List String) (gate : Policy.Gate) : Option String :=
    (Policy.firstMissing (presentOnly present) gate).map (·.lost)
  let rows (outcomes : List Policy.GateOutcome) : List (Policy.Gate × Policy.GateOutcome) :=
    outcomes.map fun outcome => (needsNone, outcome)
  let accepts (strict : Bool) (outcomes : List Policy.GateOutcome) : Bool :=
    Policy.runAccepts strict (rows outcomes)
  let reportSays (strict : Bool) (outcome : Policy.GateOutcome) (needle : String) : Bool :=
    (Policy.runFailures strict (rows [outcome])).any fun failure => contains failure needle
  let saysAny (problems : List String) (needle : String) : Bool :=
    problems.any fun problem => contains problem needle
  let planWithChannels (npm brew : Bool) : Option ReleasePlan :=
    (ReleasePlan.parse "p" (planTextOf npm brew)).toOption
  [ -- Profiles, and the one difference between them.
    checkEq "policy: the release profile is the ci profile without the deferred channels"
      (ciNames.filter fun name => !name.startsWith "npm " && name != "the rendered formulae parse")
      releaseNames,
    check "policy: the deferred-channel gates are in ci and not in release"
      (["npm package selftest", "npm publisher selftest", "npm bootstrap selftest",
        "the rendered formulae parse"].all fun name =>
          ciNames.contains name && !releaseNames.contains name)
      s!"{ciNames}",
    -- The tag run omits the working-tree gate rather than skipping it.
    checkEq "policy: a tag run omits the build-stamp gate"
      (releaseNames.filter (· != "the checked-in build stamp is the development stamp"))
      releaseTagNames,
    check "policy: nothing else changes on a tag run"
      (releaseTagNames.length + 1 == releaseNames.length)
      s!"{releaseNames.length} against {releaseTagNames.length}",
    check "policy: every gate is in at least one profile"
      (Policy.gates.all fun gate => !gate.profiles.isEmpty) "a gate no profile runs",
    check "policy: every gate name is distinct"
      ((Policy.gates.map (·.name)).eraseDups.length == Policy.gates.length)
      s!"{Policy.gates.map (·.name)}",
    checkEq "policy: a profile name parses" (Policy.Profile.parse "p" "release").toOption
      (some .release),
    check "policy: an unknown profile is refused with both spellings"
      (mentions (Policy.Profile.parse "--profile" "everything") "'ci'"
        && mentions (Policy.Profile.parse "--profile" "everything") "'release'")
      (errorOf (Policy.Profile.parse "--profile" "everything")),
    -- Whether a gate runs, across every crossing of its requirements.
    check "policy: a gate with no requirements always runs"
      (Policy.gateRuns (presentOnly []) needsNone) "",
    check "policy: a gate whose tools are all present runs"
      (Policy.gateRuns (presentOnly ["actionlint", "shellcheck"]) needsBoth) "",
    check "policy: a gate missing its first tool does not run"
      (!Policy.gateRuns (presentOnly ["shellcheck"]) needsBoth) "",
    check "policy: a gate missing its second tool does not run"
      (!Policy.gateRuns (presentOnly ["actionlint"]) needsBoth) "",
    -- …and the first missing requirement decides, so a two-tool gate reports
    -- each absence in its own terms rather than in one.
    checkEq "policy: the first missing requirement is what the report names"
      (missingOf ["shellcheck"] needsBoth) (some "actionlint is not on PATH"),
    checkEq "policy: a later missing requirement gets its own wording"
      (missingOf ["actionlint"] needsBoth)
      (some "actionlint is present but shellcheck is not"),
    checkEq "policy: nothing is missing when everything is present"
      (missingOf ["actionlint", "shellcheck"] needsBoth) none,
    -- Whether the run passed, across outcome × strict.
    check "policy: a run of passing gates passes" (accepts false [.passed, .passed]) "",
    check "policy: a failed gate fails the run, whatever follows it"
      (!accepts false [.failed "why", .passed]) "",
    check "policy: a failed gate fails a strict run too"
      (!accepts true [.failed "why"]) "",
    check "policy: a skipped gate is tolerated without --strict"
      (accepts false [.passed, .skipped { tool := "ruby", lost := "ruby is not on PATH" }]) "",
    check "policy: a skipped gate fails under --strict"
      (!accepts true [.skipped { tool := "ruby", lost := "ruby is not on PATH" }]) "",
    check "policy: the strict refusal says a missing tool is a broken job, not a smaller release"
      (reportSays true (.skipped { tool := "ruby", lost := "ruby is not on PATH" }) "broken job") "",
    check "policy: the strict refusal also names what the absence costs"
      (reportSays true (.skipped { tool := "ruby", lost := "ruby is not on PATH" })
        "ruby is not on PATH") "",
    check "policy: a failed gate's report carries what the gate said"
      (reportSays false (.failed "it refused") "it refused") "",
    check "policy: a failed gate's report names the gate"
      (reportSays false (.failed "it refused") "no tools") "",
    checkEq "policy: a passing run reports nothing" (Policy.runFailures true (rows [.passed])) [],
    -- Surface effects. The installer is the row worth reading twice.
    check "policy: the three publication channels publish"
      (Policy.publicationChannels.all fun channel =>
        (Policy.effectsOf channel).contains .publicationCommand) "",
    check "policy: the installer contributes no publication effect"
      (!(Policy.effectsOf .installer).contains .publicationCommand
        && !(Policy.effectsOf .installer).contains .workflowJob) "",
    check "policy: the installer contributes presence and documentation instead"
      ((Policy.effectsOf .installer).contains .presence
        && (Policy.effectsOf .installer).contains .documentation) "",
    check "policy: an enabled surface contributes exactly its own effects"
      (match planWithChannels true false with
       | some plan => Policy.contributedEffects plan .npm == Policy.effectsOf .npm
       | none => false) "",
    check "policy: a deferred surface contributes none of them"
      (match planWithChannels false false with
       | some plan => (Policy.contributedEffects plan .npm).isEmpty
           && (Policy.contributedEffects plan .homebrew).isEmpty
       | none => false) "",
    check "policy: the surfaces this release does publish still contribute"
      (match planWithChannels false false with
       | some plan => !(Policy.contributedEffects plan .githubRelease).isEmpty
           && !(Policy.contributedEffects plan .installer).isEmpty
       | none => false) "",
    -- The parity oracle's own arithmetic.
    checkEq "policy parity: identical lists agree" (Policy.parityProblems .ci ["a", "b"] ["a", "b"])
      [],
    check "policy parity: a gate the shell runs and the registry lacks is reported"
      (saysAny (Policy.parityProblems .ci ["a"] ["a", "b"]) "the ci profile runs 'b'") "",
    check "policy parity: a gate the registry invents is reported"
      (saysAny (Policy.parityProblems .release ["a", "b"] ["a"]) "the typed registry puts 'b'") "",
    check "policy parity: the same gates in a different order are reported"
      (saysAny (Policy.parityProblems .ci ["b", "a"] ["a", "b"]) "different order") "",
    -- The one result an oracle must never accept.
    check "policy parity: an empty observed list is refused rather than satisfied"
      (saysAny (Policy.parityProblems .ci [] []) "nothing to compare") "",
    -- The grouping, whose two mistakes both make the comparison pass.
    checkEq "policy parity: a grouped listing with its channel listing is well formed"
      (Policy.groupingProblems ["a", Policy.shellChannelGroupGate] true) [],
    checkEq "policy parity: an ungrouped listing with no channel listing is well formed"
      (Policy.groupingProblems ["a", "b"] false) [],
    check "policy parity: a grouped listing with no channel listing is refused"
      (saysAny (Policy.groupingProblems ["a", Policy.shellChannelGroupGate] false) "would pass") "",
    check "policy parity: a channel listing for an ungrouped profile is refused"
      (saysAny (Policy.groupingProblems ["a", "b"] true) "nothing would expand into it") "",
    checkEq "policy parity: the grouping gate expands into the channel gates"
      (Policy.flattenShellNames ["a", Policy.shellChannelGroupGate, "z"] ["x", "y"])
      ["a", "x", "y", "z"]]

/-- The runner, over a world that answers whatever a row needs it to.

    Every crossing the shell wrote out four times by hand — tool present or
    absent, strict or not, the command passing or refusing — driven without
    installing or uninstalling anything, which is the point of the seam. -/
private def policyRunnerTests : IO (List Outcome) := do
  let asked ← IO.mkRef (0 : Nat)
  let runnerWith (tools : List String) (failing : List String) : Policy.Runner :=
    { present := fun tool => do
        asked.modify (· + 1)
        return tools.contains tool
      invoke := fun invocation => do
        if failing.contains invocation.command then
          return .error s!"'{invocation.command}' refused"
        return .ok () }
  -- The runner reports each gate as it goes, which is what an operator reads
  -- and what a test must not print a hundred lines of.
  let outcomesOf (tools failing : List String) (profile : Policy.Profile) (tagRun : Bool) :
      IO (List (Policy.Gate × Policy.GateOutcome)) := do
    let sink ← IO.mkRef { : IO.FS.Stream.Buffer }
    IO.withStdout (IO.FS.Stream.ofBuffer sink) <|
      IO.withStderr (IO.FS.Stream.ofBuffer sink) <|
        Policy.runGates (runnerWith tools failing) profile tagRun
  let everyTool := ((Policy.gates.flatMap (·.requires)).map (·.tool)).eraseDups
  asked.set 0
  let allPresent ← outcomesOf everyTool [] .ci false
  let asksPerRun ← asked.get
  let noTools ← outcomesOf [] [] .ci false
  let oneFailing ← outcomesOf everyTool ["./scripts/check-task-ids.sh"] .release false
  -- The real runner, over a gate whose command is not there. The process layer
  -- calls that `unavailable`; a gate that reached execution must report it as a
  -- failure rather than as a skip, because a skip is a claim about this machine
  -- and this one is a claim about the gate.
  let absentCommand : Policy.Gate :=
    { name := "a command that is not there", profiles := [.ci], onTag := .always
      requires := [], invocation := .tool "tl-no-such-program-exists" [], summary := "" }
  let absentOutcome ← Policy.defaultRunner.invoke absentCommand.invocation
  let shellPresent ← Policy.onPath "sh"
  let nonsensePresent ← Policy.onPath "tl-no-such-program-exists"
  let relativePresent ← Policy.onPath "./scripts/check-task-ids.sh"
  let relativeAbsent ← Policy.onPath "./scripts/there-is-no-such-script.sh"
  let outcomeNames (rows : List (Policy.Gate × Policy.GateOutcome)) (which : String) :=
    (rows.filter fun (_, outcome) =>
      match outcome, which with
      | .passed, "passed" => true
      | .failed _, "failed" => true
      | .skipped _, "skipped" => true
      | _, _ => false).map (·.1.name)
  return [
    -- Every gate runs when every tool is there, and none of them is skipped.
    checkEq "policy runner: with every tool present, every gate runs"
      (outcomeNames allPresent "passed") (Policy.gateNames .ci false),
    checkEq "policy runner: and none is skipped" (outcomeNames allPresent "skipped") [],
    -- Each distinct tool is asked about once, however many gates declare it.
    checkEq "policy runner: each distinct tool is asked about exactly once"
      asksPerRun everyTool.length,
    check "policy runner: more than one gate declares a shared tool, so that means something"
      ((Policy.gates.filter fun gate =>
        gate.requires.any (·.tool == "shellcheck")).length > 1) "",
    -- With no tools at all, exactly the gates that declare one are skipped.
    checkEq "policy runner: with no tools, every gate that needs one is skipped"
      (outcomeNames noTools "skipped")
      ((Policy.gatesIn .ci false).filter (!·.requires.isEmpty) |>.map (·.name)),
    checkEq "policy runner: and the rest still run"
      (outcomeNames noTools "passed")
      ((Policy.gatesIn .ci false).filter (·.requires.isEmpty) |>.map (·.name)),
    -- A skipped run passes without --strict and fails with it. Same rows.
    check "policy runner: a run with skips passes without --strict"
      (Policy.runAccepts false noTools) "",
    check "policy runner: the same run fails under --strict"
      (!Policy.runAccepts true noTools) "",
    -- A refusing gate fails the run, and the report carries what it said.
    checkEq "policy runner: a gate whose command refuses is a failure"
      (outcomeNames oneFailing "failed") ["task-id lint selftest", "task-id leakage"],
    check "policy runner: the report carries what the gate said"
      ((Policy.runFailures false oneFailing).any fun failure => contains failure "refused") "",
    check "policy runner: one failing gate does not stop the rest running"
      ((outcomeNames oneFailing "passed").length + 2 == (Policy.gateNames .release false).length)
      s!"{outcomeNames oneFailing "passed"}",
    -- The real world half: what `onPath` answers, and what a command that is
    -- not there does when a gate reaches it anyway.
    check "policy runner: a command on PATH is found" shellPresent "sh was not found on PATH",
    check "policy runner: a command that does not exist is not found" (!nonsensePresent) "",
    check "policy runner: a relative path is checked as a path, not searched for on PATH"
      relativePresent "./scripts/check-task-ids.sh was not found",
    check "policy runner: a relative path that is not there is not found" (!relativeAbsent) "",
    check "policy runner: a gate whose command cannot be run fails rather than skipping"
      (absentOutcome.toOption.isNone) "an absent command was reported as success",
    check "policy runner: and the refusal says the tool is not there"
      (mentions absentOutcome "could not be run") (errorOf absentOutcome)]

/-- The oracle against the shell scripts themselves.

    Run here rather than only in CI, because the property is that the registry
    tracks the shell *on this commit*: a gate added to one of them is a failing
    test on the change that added it, not a failing job afterwards. -/
private def policyParityTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  let listing (name : String) (args : List String) : IO (Except String String) := do
    match ← Release.succeeded "sh" ((["-c", "\"$@\"", "sh"] ++ args).toArray) with
    | .error message => return .error s!"{name}: {message}"
    | .ok output =>
        let path := (base / name).toString
        IO.FS.writeFile path output.stdout
        return .ok path
  let ci ← listing "ci.txt" ["./scripts/check-release-policy.sh", "--profile", "ci", "--list-names"]
  let rel ← listing "release.txt"
    ["./scripts/check-release-policy.sh", "--profile", "release", "--list-names"]
  let relTag ← listing "release-tag.txt"
    ["./scripts/check-release-policy.sh", "--profile", "release", "--tag", "v9.9.9", "--list-names"]
  let chan ← listing "channel.txt" ["./scripts/check-channel-policy.sh", "--list-names"]
  let run (args : List String) : IO (UInt32 × String × String) := runCommand "policy-parity" args
  let mut outs : List Outcome := []
  match ci, rel, relTag, chan with
  | .ok ciPath, .ok relPath, .ok relTagPath, .ok chanPath =>
      let (ciStatus, ciOut, ciErr) ← run ["--profile", "ci", "--observed", ciPath,
        "--channel", chanPath]
      let (relStatus, _, relErr) ← run ["--profile", "release", "--observed", relPath]
      let (tagStatus, _, tagErr) ← run ["--profile", "release", "--observed", relTagPath, "--tag"]
      -- The mutation that used to pass: the ci listing carries the grouping
      -- gate, which flattens to nothing without a channel listing and leaves
      -- exactly the release profile's gates behind.
      let (crossed, _, crossedErr) ← run ["--profile", "release", "--observed", ciPath]
      let (tagDrift, _, tagDriftErr) ← run ["--profile", "release", "--observed", relPath, "--tag"]
      let emptyPath := (base / "empty.txt").toString
      IO.FS.writeFile emptyPath "\n\n"
      let (emptyStatus, _, emptyErr) ← run ["--profile", "ci", "--observed", emptyPath]
      let (absent, _, absentErr) ← run ["--profile", "ci", "--observed", (base / "no.txt").toString]
      let (usage, _, _) ← run ["--profile", "ci"]
      let (badProfile, _, badProfileErr) ← run ["--profile", "everything", "--observed", ciPath]
      outs := [
        check "policy parity: the ci profile matches the shell policy on this commit"
          (ciStatus == 0) ciErr,
        check "policy parity: it says how many gates it compared"
          (contains ciOut "13 gate(s)") ciOut,
        check "policy parity: the release profile matches" (relStatus == 0) relErr,
        check "policy parity: a tag run matches" (tagStatus == 0) tagErr,
        checkEq "policy parity: the ci listing does not satisfy the release profile" crossed 1,
        check "policy parity: that refusal names the grouping gate"
          (contains crossedErr "deferred-channel gates") crossedErr,
        checkEq "policy parity: a non-tag listing does not satisfy a tag run" tagDrift 1,
        check "policy parity: that refusal names the gate a tag run omits"
          (contains tagDriftErr "build stamp") tagDriftErr,
        checkEq "policy parity: an empty listing is refused" emptyStatus 1,
        check "policy parity: that refusal says the comparison would have nothing to compare"
          (contains emptyErr "nothing to compare") emptyErr,
        checkEq "policy parity: a listing that is not there is refused" absent 1,
        check "policy parity: that refusal names the path" (contains absentErr "no.txt") absentErr,
        checkEq "policy parity: a missing --observed is a usage error" usage 2,
        checkEq "policy parity: an unknown profile is a usage error" badProfile 2,
        check "policy parity: that usage error names the profiles"
          (contains badProfileErr "'release'") badProfileErr]
  | _, _, _, _ =>
      outs := [check "policy parity: the shell policy scripts list their gates" false
        s!"{ci} {rel} {relTag} {chan}"]
  -- `policy-list` is the same projection the oracle compares, driven through
  -- the command a workflow would run.
  let (listStatus, listOut, listErr) ← runCommand "policy-list" ["--profile", "release"]
  let (listUsage, _, _) ← runCommand "policy-list" []
  IO.FS.removeDirAll base
  return outs ++ [
    check "policy-list: it names the gates of a profile" (listStatus == 0) listErr,
    -- The names, then the one summary line every command ends with. Compared
    -- as "the names come first, in order" rather than as the whole stream, so
    -- this stays a report a human reads and `policy-parity` keeps reading the
    -- shell's machine-readable listing instead.
    checkEq "policy-list: one name per line, in registry order"
      (((listOut.splitOn "\n").filter (!·.isEmpty)).dropLast) (Policy.gateNames .release false),
    check "policy-list: the last line is the command's own summary"
      ((((listOut.splitOn "\n").filter (!·.isEmpty)).getLastD "").startsWith "tlrelease policy-list:")
      listOut,
    checkEq "policy-list: no profile is a usage error" listUsage 2]

/-! ## The canonical signing identity

The policy is `parseSan`, and the expression is its projection into the one
syntax cosign speaks. Both are exercised: the structural accept/reject table
runs against the committed configuration, and the rendered bytes are pinned so
a change to what cosign is given cannot be silent. -/

private def pinnedIdentity : Identity :=
  { repository := "Owner/tl", npmPackage := "@scope/tl"
    releaseWorkflow := ".github/workflows/release.yml"
    certificateOidcIssuer := "https://token.actions.githubusercontent.com"
    certificateIdentityRegexp := "" }

private def sanFor (repository workflow ref : String) : String :=
  "https://github.com/" ++ repository ++ "/" ++ workflow ++ "@" ++ ref

private def acceptsSan (san : String) : Bool := identityAccepts pinnedIdentity san

private def certificateTests : IO (List Outcome) := do
  let realIdentityText ← IO.FS.readFile "release/identity.json"
  let realIdentity := Identity.parse "release/identity.json" realIdentityText
  let renderedReal := realIdentity >>= renderIdentityExpression
  let rendered := renderIdentityExpression pinnedIdentity
  let liveFailures := match realIdentity, renderedReal with
    | .ok identity, .ok expression => Check.failures (identityChecks identity expression)
    | _, _ => ["release/identity.json stopped parsing or rendering"]
  return [
    -- The committed mirror is exactly what this build renders. This is the
    -- property that makes the expression stop being configuration: it cannot
    -- be widened by editing it, because editing it makes this fail.
    checkEq "identity: the committed expression is the canonical rendering" liveFailures [],
    checkEq "identity: the pinned expression renders to exactly these bytes"
      (okOr "<refused>" rendered)
      ("^https://github\\.com/Owner/tl/\\.github/workflows/release\\.yml@refs/tags/"
        ++ "v(0|[1-9][0-9]*)\\.(0|[1-9][0-9]*)\\.(0|[1-9][0-9]*)(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?$"),
    -- Anchors and escapes, each as its own row, because each admits a
    -- different wrong certificate when it is missing.
    check "identity: the expression is anchored at both ends"
      ((okOr "" rendered).startsWith "^" && (okOr "" rendered).endsWith "$")
      (okOr "<refused>" rendered),
    check "identity: every dot in a literal is escaped"
      (!(okOr "" rendered |>.splitOn "github.com").length.blt 2 |> not)
      "an unescaped dot would also match github<any>com",
    -- What the policy accepts.
    check "identity: this repository's release workflow on a SemVer tag is accepted"
      (acceptsSan (sanFor "Owner/tl" ".github/workflows/release.yml" "refs/tags/v1.2.3"))
      "the pin rejects the thing it exists to accept",
    check "identity: a prerelease tag is accepted"
      (acceptsSan (sanFor "Owner/tl" ".github/workflows/release.yml" "refs/tags/v1.2.3-rc.1"))
      "a prerelease was rejected",
    -- What it rejects, one wrong thing at a time.
    check "identity: another repository is rejected"
      (!acceptsSan (sanFor "someone/tl" ".github/workflows/release.yml" "refs/tags/v1.2.3"))
      "another repository was accepted",
    check "identity: another workflow in this repository is rejected"
      (!acceptsSan (sanFor "Owner/tl" ".github/workflows/ci.yml" "refs/tags/v1.2.3"))
      "another workflow was accepted",
    check "identity: a branch ref is rejected"
      (!acceptsSan (sanFor "Owner/tl" ".github/workflows/release.yml" "refs/heads/main"))
      "a branch ref was accepted — it moves, so it would sign every later commit",
    check "identity: a tag with a leading zero is rejected"
      (!acceptsSan (sanFor "Owner/tl" ".github/workflows/release.yml" "refs/tags/v01.2.3"))
      "a tag the signing grammar refuses was accepted",
    check "identity: a tag carrying build metadata is rejected"
      (!acceptsSan (sanFor "Owner/tl" ".github/workflows/release.yml" "refs/tags/v1.2.3+b"))
      "a tag nothing could be signed from was accepted",
    -- The two an unanchored expression would admit, and the reason both
    -- anchors are there.
    check "identity: an identity that merely contains this one is rejected"
      (!acceptsSan ("https://evil.example/https://github.com/Owner/tl/.github/workflows/release.yml@refs/tags/v1.2.3"))
      "a containing identity was accepted",
    check "identity: an identity that merely begins with this one is rejected"
      (!acceptsSan (sanFor "Owner/tl-fork" ".github/workflows/release.yml" "refs/tags/v1.2.3"))
      "a prefixing identity was accepted",
    check "identity: a tag name extending past the version is rejected"
      (!acceptsSan (sanFor "Owner/tl" ".github/workflows/release.yml" "refs/tags/v1.2.3/extra"))
      "a tag name may contain '/', and one did",
    -- Malformed input reaches a refusal that says which part was wrong.
    check "identity: a SAN with no scheme prefix is refused with a reason"
      (mentions (parseSan "github.com/Owner/tl/x@refs/tags/v1.2.3") "does not begin with")
      (errorOf (parseSan "github.com/Owner/tl/x@refs/tags/v1.2.3")),
    check "identity: a SAN naming no ref is refused with a reason"
      (mentions (parseSan "https://github.com/Owner/tl/x") "names no ref")
      (errorOf (parseSan "https://github.com/Owner/tl/x")),
    check "identity: a SAN naming no workflow file is refused with a reason"
      (mentions (parseSan "https://github.com/Owner/tl@refs/tags/v1.2.3") "no workflow file")
      (errorOf (parseSan "https://github.com/Owner/tl@refs/tags/v1.2.3")),
    -- A configuration this generator will not render, rather than one it
    -- renders wrongly.
    check "identity: a repository carrying a regex metacharacter is refused"
      (mentions (renderIdentityExpression { pinnedIdentity with repository := "Own|er/tl" })
        "will not render")
      (errorOf (renderIdentityExpression { pinnedIdentity with repository := "Own|er/tl" })),
    check "identity: an empty workflow path is refused"
      (mentions (renderIdentityExpression { pinnedIdentity with releaseWorkflow := "" })
        "is empty")
      (errorOf (renderIdentityExpression { pinnedIdentity with releaseWorkflow := "" })),
    -- A mirror that disagrees is a refusal that shows both, because the
    -- difference is the thing to look at.
    check "identity: a widened mirror is refused, and both readings are shown"
      (match rendered with
       | .ok expression =>
           (Check.failures (identityExpressionChecks
             { pinnedIdentity with certificateIdentityRegexp := "^.*$" } expression)).length == 1
       | .error _ => false) "a mirror that says something else was accepted"]

/-! ## Release prerequisites

The three distinctions the module is built around, each as rows: missing is not
unchecked, not-applicable is not satisfied, and a property is not a proxy for
it. The aggregation carries theorems; these exercise the classification and the
predicates the theorems are stated over. -/

private def rowWith (outcome : AuditOutcome) : Row :=
  { kind := .tagRuleset, summary := "a row", outcome }

private def rulesetWith (enforcement : String) (included excluded : List String)
    (ruleTypes : List String) : TagRuleset :=
  { identifier := "1", enforcement,
    conditions := { included, excluded }, ruleTypes }

private def planWith (npm homebrew : Bool) : Except String ReleasePlan :=
  ReleasePlan.parse "p" (planOf
    [planRow "github-release" true none, planRow "installer" true none,
     planRow "npm" npm (if npm then none else some "\"0.2.0\""),
     planRow "homebrew" homebrew (if homebrew then none else some "\"0.2.0\"")])

private def kindsFor (npm homebrew : Bool) : List String :=
  match planWith npm homebrew with
  | .ok plan => (applicableKinds plan).map fun kind =>
      match kind.channel with
      | none => "always"
      | some channel => channel.wire
  | .error message => [message]

private def prerequisiteTests : List Outcome :=
  let verified := rowWith .verified
  let carried := rowWith (.carried "recorded, never checked")
  let missing := rowWith (.missing "create it")
  let unchecked := rowWith (.operationalError "the API would not answer")
  [-- The verdict, over the four outcomes.
   check "prereqs: verified and carried rows permit a release"
     (auditPermits [verified, carried]) "a clean audit refused",
   check "prereqs: a missing row stops the release"
     (!auditPermits [verified, missing]) "a missing prerequisite was permitted",
   -- The one that matters most: an audit that could not run has established
   -- nothing, and reading its silence as consent is the failure this prevents.
   check "prereqs: an unchecked row stops the release too"
     (!auditPermits [verified, unchecked]) "an unasked question was read as consent",
   check "prereqs: a clean audit reports no blockers"
     (auditBlockers [verified, carried]).isEmpty "a clean audit reported a blocker",
   -- Missing and unchecked stay apart, including mixed.
   checkEq "prereqs: missing and unchecked are counted separately"
     ((auditMissing [verified, missing, unchecked]).length,
      (auditUnchecked [verified, missing, unchecked]).length) (1, 1),
   checkEq "prereqs: a missing row is not counted as unchecked"
     (auditUnchecked [missing]).length 0,
   checkEq "prereqs: an unchecked row is not counted as missing"
     (auditMissing [unchecked]).length 0,
   -- Applicability from the plan: a deferred channel produces no rows at all,
   -- which is neither missing nor unchecked.
   checkEq "prereqs: a GitHub-only release needs no npm or Homebrew prerequisites"
     (kindsFor false false) ["always", "always", "always", "always", "always"],
   checkEq "prereqs: enabling npm adds exactly its two prerequisites"
     ((kindsFor true false).filter (· == "npm")).length 2,
   checkEq "prereqs: enabling Homebrew adds exactly its two prerequisites"
     ((kindsFor false true).filter (· == "homebrew")).length 2,
   -- The tag ruleset predicate, which has been a proxy in three review rounds.
   check "prereqs: a ruleset covering every v* tag qualifies"
     (restrictsTagCreation (rulesetWith "active" ["refs/tags/v*"] [] ["creation"]))
     "a qualifying ruleset was rejected",
   check "prereqs: ~ALL covers every v* tag"
     (restrictsTagCreation (rulesetWith "active" ["~ALL"] [] ["creation"]))
     "the catch-all pattern was rejected",
   -- The defect the round-3 finding names: one tag, or one release line, is not
   -- every v* tag.
   check "prereqs: a ruleset naming one tag does not qualify"
     (!restrictsTagCreation (rulesetWith "active" ["refs/tags/v1.0.0"] [] ["creation"]))
     "a ruleset over one tag read as one over every v* tag",
   check "prereqs: a ruleset naming one release line does not qualify"
     (!restrictsTagCreation (rulesetWith "active" ["refs/tags/v1.*"] [] ["creation"]))
     "a ruleset over one release line read as one over every v* tag",
   -- An exclude list can hole any include pattern, and deciding which holes
   -- matter is interpretation a gate should refuse to perform.
   check "prereqs: any exclude list disqualifies"
     (!restrictsTagCreation (rulesetWith "active" ["~ALL"] ["refs/tags/v0.*"] ["creation"]))
     "an excluded release line still read as complete coverage",
   check "prereqs: evaluate mode does not qualify"
     (!restrictsTagCreation (rulesetWith "evaluate" ["~ALL"] [] ["creation"]))
     "a ruleset that only reports read as one that restricts",
   check "prereqs: a ruleset with no creation rule does not qualify"
     (!restrictsTagCreation (rulesetWith "active" ["~ALL"] [] ["update", "deletion"]))
     "a ruleset restricting updates read as one restricting creation",
   -- The deployment policy: a branch entry is the half that lets a push reach
   -- the signing job, and filtering it out before looking made an environment
   -- admitting both report as tag-only.
   check "prereqs: a tag-only v* policy qualifies"
     (policyAdmitsOnlyReleaseTags [{ entryType := "tag", name := "v*" }])
     "a correct policy was rejected",
   check "prereqs: a policy admitting a branch as well does not qualify"
     (!policyAdmitsOnlyReleaseTags
       [{ entryType := "tag", name := "v*" }, { entryType := "branch", name := "main" }])
     "a branch entry was invisible behind a tag entry",
   check "prereqs: an empty policy restricts nothing"
     (!policyAdmitsOnlyReleaseTags []) "a policy naming nothing read as a restriction",
   -- The reviewer rule: a rule with nobody in it approves itself, and is a
   -- different configuration from no rule at all.
   checkEq "prereqs: a required-reviewers rule with nobody in it is distinguishable"
     ((environmentProtectionOf (Json.mkObj [("protection_rules",
        Json.arr #[Json.mkObj [("type", Json.str "required_reviewers"),
                               ("reviewers", Json.arr #[])]])])).requiredReviewers)
     (some 0),
   checkEq "prereqs: an environment with only a wait timer has no reviewer rule"
     ((environmentProtectionOf (Json.mkObj [("protection_rules",
        Json.arr #[Json.mkObj [("type", Json.str "wait_timer")]])])).requiredReviewers)
     none]

/-! ## One version, and the embedded copies

Both were shell gates in check-release-policy.sh until they moved into the
release tool. That script runs in a job with no Lean toolchain by design, so
these run here — against the real repository files, which is what makes them a
drift guard rather than a test of a fixture. -/

private def consistencyTests : IO (List Outcome) := do
  let targetsText ← IO.FS.readFile "release/targets.json"
  let commandsText ← IO.FS.readFile "Tl/Cli/Commands.lean"
  let lakefileText ← IO.FS.readFile "lakefile.lean"
  let releaseTestsText ← IO.FS.readFile "Tests/ReleaseTests.lean"
  let libraryText ← IO.FS.readFile "scripts/lib/release-common.sh"
  let identityText ← IO.FS.readFile "release/identity.json"
  let manifestPaths : List String := match Targets.parse "release/targets.json" targetsText with
    | .ok targets =>
        "npm/tl/package.json"
          :: targets.targets.map (fun target => "npm/platform/" ++ target.name ++ "/package.json")
    | .error _ => []
  let mut manifests : Array (String × String) := #[]
  for path in manifestPaths do
    let text ← IO.FS.readFile path
    manifests := manifests.push (path, text)
  let sources : VersionSources :=
    { commandsPath := "Tl/Cli/Commands.lean", commandsText
      lakefilePath := "lakefile.lean", lakefileText
      releaseTestsPath := "Tests/ReleaseTests.lean", releaseTestsText
      identityPath := "release/identity.json", identityText
      manifests := manifests.toList }
  let product := productVersionOf sources
  let copies := versionCopies sources
  let problems := match product, copies with
    | .ok product, .ok copies => versionProblems product copies none
    | .error message, _ => [message]
    | _, .error message => [message]
  let taggedProblems := match product, copies with
    | .ok product, .ok copies => versionProblems product copies (some "v9.9.9")
    | _, _ => ["<a source stopped parsing>"]
  -- Every guarded copy, against the real library.
  let mut copyRows : List Outcome := []
  for copy in guardedCopies do
    let consumerText ← IO.FS.readFile copy.consumer
    copyRows := copyRows ++ [
      check s!"copies: {copy.consumer} still carries {copy.blockName} unchanged"
        (match copyCheck copy consumerText libraryText with
         | .ok check => check.held
         | .error _ => false)
        (match copyCheck copy consumerText libraryText with
         | .ok check => check.failure
         | .error message => message)]
  -- Drift is detected, not merely absent. A gate that passes over a library it
  -- could not read would pass here too, so one row breaks a copy on purpose.
  let driftRow ← match guardedCopies.find? (·.mode == .classification) with
    | none => pure (check "copies: a classification row exists to break" false "none found")
    | some copy => do
        let consumerText ← IO.FS.readFile copy.consumer
        -- The consumer, not the library: the mutation has to land inside the
        -- marked block, which is what the comparison reads.
        let mutated := consumerText.replace "Darwin) install_os=darwin" "Darwin) install_os=linux"
        pure (check "copies: a copy that classifies differently is caught"
          (mutated != consumerText &&
            (match copyCheck copy mutated libraryText with
             | .ok check => !check.held
             | .error _ => false))
          "a mutated classification was not detected, so this guard proves nothing")
  let nameProblems := match packageNameChecks sources with
    | .ok checks => Check.failures checks
    | .error message => [message]
  return [
    checkEq "version: every copy of the release version agrees" problems [],
    -- The published package name is a second identity, and the first port of
    -- this gate dropped it.
    checkEq "version: the launcher is published under the pinned package name"
      nameProblems [],
    check "version: a launcher under another name is refused"
      (match packageNameChecks
          { sources with manifests :=
              ("npm/tl/package.json", "{\"name\": \"@other/tl\", \"version\": \"0.1.0\"}")
                :: sources.manifests.drop 1 } with
       | .ok checks => !(Check.failures checks).isEmpty
       | .error _ => false) "a launcher published under another name was accepted",
    -- The gate must also be able to fail: a comparison that accepted anything
    -- would satisfy the row above without establishing it.
    check "version: a tag naming another version is refused"
      (!taggedProblems.isEmpty) "a tag disagreeing with the checkout was accepted",
    check "version: exactly one productVersion definition is required"
      (mentions (oneLiteral "f" "it" "def productVersion : String := \"a\"\ndef productVersion : String := \"b\"" "def productVersion : String := \"" "\"") "Exactly one is expected")
      "two definitions were resolved rather than refused",
    check "version: a missing definition is refused with a different message"
      (mentions (oneLiteral "f" "it" "nothing here" "def productVersion : String := \"" "\"") "has no")
      "an absent definition was not distinguished from a duplicated one",
    driftRow] ++ copyRows

/-! ## The prerequisite audit, driven over a stubbed GitHub

The pure predicates are covered above. These drive `collectRows` and the ruleset
loop themselves, over a client that answers from a table — which is what makes
the 404, malformed-response, unreachable and truncated-page branches reachable
without a repository in a particular state. -/

private def stubClient (answers : List (String × ApiResult)) : GithubClient :=
  fun path => pure ((answers.lookup path).getD (.failed s!"the stub was not asked about {path}"))

private def jsonOf (text : String) : Json :=
  match Json.parse text with | .ok value => value | .error _ => Json.null

private def repoPath : String := "repos/Owner/tl"
private def envPath : String := "repos/Owner/tl/environments/release"
private def policyPath : String := "repos/Owner/tl/environments/release/deployment-branch-policies"
private def rulesetsPath : String := "repos/Owner/tl/rulesets"

private def healthyAnswers : List (String × ApiResult) :=
  [(repoPath, .body (jsonOf "{\"visibility\": \"public\"}")),
   (envPath, .body (jsonOf
     "{\"protection_rules\": [{\"type\": \"required_reviewers\", \"reviewers\": [{\"a\": 1}]}]}")),
   (policyPath, .body (jsonOf
     "{\"total_count\": 1, \"branch_policies\": [{\"type\": \"tag\", \"name\": \"v*\"}]}")),
   (rulesetsPath, .body (jsonOf "[{\"target\": \"tag\", \"id\": 7}]")),
   ("repos/Owner/tl/rulesets/7", .body (jsonOf
     "{\"enforcement\": \"active\", \"conditions\": {\"ref_name\": {\"include\": [\"~ALL\"], \"exclude\": []}}, \"rules\": [{\"type\": \"creation\"}]}"))]

private def reachable : IO (Except String Unit) := pure (.ok ())

private def auditWith (answers : List (String × ApiResult)) (npm homebrew : Bool)
    (reach : IO (Except String Unit) := reachable) : IO (List Row) := do
  match planWith npm homebrew with
  | .error _ => return []
  | .ok plan => collectRows (stubClient answers) reach sampleIdentity plan

private def outcomeNames (rows : List Row) : List String :=
  rows.map fun row =>
    match row.outcome with
    | .verified => "ok" | .carried _ => "carried"
    | .missing _ => "MISSING" | .operationalError _ => "unchecked"

private def prerequisiteIoTests : IO (List Outcome) := do
  let healthy ← auditWith healthyAnswers false false
  let privateRepo ← auditWith
    (healthyAnswers.map fun (p, r) =>
      if p == repoPath then (p, .body (jsonOf "{\"visibility\": \"private\"}")) else (p, r))
    false false
  let noEnvironment ← auditWith
    (healthyAnswers.map fun (p, r) => if p == envPath then (p, .notFound) else (p, r)) false false
  let unreadableEnvironment ← auditWith
    (healthyAnswers.map fun (p, r) =>
      if p == envPath then (p, .failed "HTTP 502") else (p, r)) false false
  let emptyReviewers ← auditWith
    (healthyAnswers.map fun (p, r) =>
      if p == envPath then (p, .body (jsonOf
        "{\"protection_rules\": [{\"type\": \"required_reviewers\", \"reviewers\": []}]}"))
      else (p, r)) false false
  let truncatedPolicy ← auditWith
    (healthyAnswers.map fun (p, r) =>
      if p == policyPath then (p, .body (jsonOf
        "{\"total_count\": 31, \"branch_policies\": [{\"type\": \"tag\", \"name\": \"v*\"}]}"))
      else (p, r)) false false
  let unreadableRuleset ← auditWith
    (healthyAnswers.map fun (p, r) =>
      if p == "repos/Owner/tl/rulesets/7" then (p, .failed "HTTP 500") else (p, r)) false false
  let narrowRuleset ← auditWith
    (healthyAnswers.map fun (p, r) =>
      if p == "repos/Owner/tl/rulesets/7" then (p, .body (jsonOf
        "{\"enforcement\": \"active\", \"conditions\": {\"ref_name\": {\"include\": [\"refs/tags/v1.0.0\"], \"exclude\": []}}, \"rules\": [{\"type\": \"creation\"}]}"))
      else (p, r)) false false
  let malformed ← auditWith
    (healthyAnswers.map fun (p, r) =>
      if p == repoPath then (p, .body (jsonOf "{\"visibility\": 7}")) else (p, r)) false false
  let unauthenticated ← auditWith healthyAnswers false false
    (pure (.error "gh is not authenticated ('gh auth login')"))
  let withChannels ← auditWith
    (healthyAnswers ++ [("repos/Owner/homebrew-tap", .body (jsonOf "{}"))]) true true
  return [
    -- A repository in the state the pipeline needs.
    checkEq "audit: a healthy configuration produces five verified rows"
      (outcomeNames healthy) ["ok", "ok", "ok", "ok", "ok"],
    check "audit: a healthy configuration permits the release" (auditPermits healthy) "refused",
    -- Each row, one wrong thing at a time.
    check "audit: a private repository stops the release"
      ((auditMissing privateRepo).length == 1 && !auditPermits privateRepo) "accepted",
    -- 404 is an answer; anything else is not.
    check "audit: a 404 on the environment is missing"
      ((auditMissing noEnvironment).length > 0) "a 404 was not read as absent",
    check "audit: any other API failure is unchecked, not missing"
      ((auditUnchecked unreadableEnvironment).length > 0
        && (auditMissing unreadableEnvironment).length == 0)
      "an unreachable endpoint was reported as an absent environment",
    check "audit: a reviewer rule with nobody in it is missing, not verified"
      (!auditPermits emptyReviewers) "an empty reviewer list approved itself",
    -- The page-is-not-a-list defect.
    check "audit: a deployment policy longer than one page is unchecked"
      ((auditUnchecked truncatedPolicy).length == 1 && !auditPermits truncatedPolicy)
      "one page of a longer policy list was read as the whole list",
    -- An unreadable ruleset is not an absent one.
    check "audit: a ruleset the API could not read is unchecked"
      ((auditUnchecked unreadableRuleset).length == 1) "an unreadable ruleset read as absent",
    check "audit: a ruleset covering one tag is missing, not verified"
      ((auditMissing narrowRuleset).length == 1) "a ruleset over one tag read as full coverage",
    -- A response this audit does not understand is not a finding about the thing.
    check "audit: a malformed field is unchecked, not missing"
      ((auditUnchecked malformed).length == 1) "an unreadable response read as a finding",
    -- gh itself unavailable: every applicable row, one stated reason, and no
    -- row claiming the thing is absent.
    check "audit: an unauthenticated gh makes every row unchecked"
      (unauthenticated.length == 5 && (auditMissing unauthenticated).isEmpty
        && !auditPermits unauthenticated) "gh being unavailable was not reported as unchecked",
    -- Applicability, end to end rather than over the kind list alone.
    checkEq "audit: a GitHub-only release collects five rows" healthy.length 5,
    checkEq "audit: enabling both channels collects four more" withChannels.length 9,
    check "audit: the deferred channels are named, not silently dropped"
      (match planWith false false with
       | .ok plan => (deferredNotes plan).length == 2
       | .error _ => false) "a deferred channel produced no note"]

/-! ### The client, and what it makes of an answer

`collectRows` above is driven over a table of `ApiResult`s. What produces those
in a release is `githubApiWith`, and its decision — a page of JSON is an answer,
a 404 is an answer, anything else is not — was reachable only with a real `gh`
against a real repository. These rows drive it against scripts that answer the
way each of those cases does, so the classification that decides which remedy an
operator is shown is exercised rather than assumed. -/

private def writeStub (path : System.FilePath) (body : String) : IO String := do
  IO.FS.writeFile path ("#!/bin/sh\n" ++ body)
  -- 0o755. The script is executed, so a stub that is merely written would make
  -- every row below report `unavailable` and none of them would be about what
  -- they name.
  let _ ← IO.Process.run { cmd := "chmod", args := #["755", path.toString] }
  return path.toString

private def resultLabel : ApiResult → String
  | .body _ => "body"
  | .notFound => "notFound"
  | .failed _ => "failed"

private def resultDetail : ApiResult → String
  | .body json => json.compress
  | .notFound => ""
  | .failed detail => detail

private def clientTests : IO (List Outcome) := do
  let base ← IO.FS.createTempDir
  -- Each stub answers the way one real `gh` outcome does. The first echoes the
  -- path it was given, which is the only way to observe what was actually
  -- requested.
  let echo ← writeStub (base / "gh-echo") "printf '\"%s\"' \"$2\"\n"
  let notFound ← writeStub (base / "gh-404")
    "echo 'gh: Not Found (HTTP 404)' >&2\nexit 1\n"
  let garbage ← writeStub (base / "gh-garbage") "printf 'not json at all'\n"
  let broken ← writeStub (base / "gh-500")
    "echo 'gh: Internal Server Error (HTTP 500)' >&2\nexit 1\n"
  let slow ← writeStub (base / "gh-slow") "sleep 30\n"
  let plain ← githubApiWith echo "repos/Owner/tl"
  let queried ← githubApiWith echo "repos/Owner/tl/rulesets?includes_parents=false"
  let missing ← githubApiWith notFound "repos/Owner/tl"
  let unparseable ← githubApiWith garbage "repos/Owner/tl"
  let serverError ← githubApiWith broken "repos/Owner/tl"
  let timedOut ← githubApiWith slow "repos/Owner/tl" 300
  let absent ← githubApiWith (base / "gh-absent").toString "repos/Owner/tl"
  IO.FS.removeDirAll base
  return [
    checkEq "client: a page of JSON is an answer" (resultLabel plain) "body",
    -- Not a page: GitHub defaults these endpoints to thirty rows, and one that
    -- asked for the default would read a policy on page two as absent.
    check "client: every request asks for a whole page"
      (((resultDetail plain).splitOn "per_page=100").length > 1) (resultDetail plain),
    check "client: a path that already carries a query keeps it"
      (((resultDetail queried).splitOn "includes_parents=false&per_page=100").length > 1)
      (resultDetail queried),
    -- A 404 is an answer about the thing being asked for; everything else is
    -- the absence of one, and the two have opposite remedies.
    checkEq "client: a 404 is an answer, and it is missing" (resultLabel missing) "notFound",
    checkEq "client: a server error is not an answer" (resultLabel serverError) "failed",
    check "client: the server's own diagnosis reaches the operator"
      (((resultDetail serverError).splitOn "HTTP 500").length > 1) (resultDetail serverError),
    -- Exit zero with a body that is not JSON is the shape that would otherwise
    -- reach a predicate as an empty document and satisfy nothing quietly.
    checkEq "client: a success that is not JSON is not evidence"
      (resultLabel unparseable) "failed",
    check "client: and it says so, naming the request"
      (((resultDetail unparseable).splitOn "is not JSON").length > 1 &&
        ((resultDetail unparseable).splitOn "repos/Owner/tl").length > 1)
      (resultDetail unparseable),
    checkEq "client: a client that does not finish is not an answer"
      (resultLabel timedOut) "failed",
    check "client: a timeout says the tool established nothing"
      (((resultDetail timedOut).splitOn "established nothing").length > 1)
      (resultDetail timedOut),
    checkEq "client: a client that is not there is not an answer"
      (resultLabel absent) "failed",
    check "client: and it cannot be read as a clean audit"
      (((resultDetail absent).splitOn "cannot be skipped").length > 1) (resultDetail absent)]

/-! ### What the audit prints, and what it decides

`auditReport` is the whole of it: the lines an operator reads and the verdict
the workflow branches on, from the rows. Pure, so both are reachable here rather
than only through a run against a configured repository — which is what left the
four row renderings, the deferred notes and the two-count refusal uncovered. -/

private def row (kind : PrerequisiteKind) (summary : String) (outcome : AuditOutcome) : Row :=
  { kind, summary, outcome }

private def reportOf (rows : List Row) (npm := false) (homebrew := false) :
    List String × Except String String :=
  match planWith npm homebrew with
  | .ok plan => auditReport "Owner/tl" plan rows
  | .error message => ([message], .error message)

private def reportTestsForAudit : List Outcome :=
  let clean := reportOf [row .repositoryPublic "the repository is public" .verified,
    row .releaseReviewers "the release environment requires a reviewer"
      (.carried "reviewer lists are not readable without admin")]
  -- Two missing and one unchecked, not one each: with equal counts a report
  -- that swapped them would read the same, and the two have opposite remedies.
  let stopped := reportOf [row .repositoryPublic "the repository is public" .verified,
    row .tagRuleset "a ruleset protects every v* tag" (.missing "create the ruleset"),
    row .npmPackages "the five npm packages exist" (.missing "publish the bootstrap version"),
    row .releaseEnvironment "the release environment exists"
      (.operationalError "HTTP 502 from the environments endpoint")]
  let published := reportOf [] (npm := true) (homebrew := true)
  [ -- One line per row, in order, whatever the outcome: an audit that printed
    -- only its failures leaves a reader unable to tell a clean sweep from a run
    -- that checked two things.
    checkEq "report: every row is rendered, in the order it was collected"
      (clean.1.length) 4,
    check "report: a verified row reads as ok"
      (clean.1.any fun line => (line.splitOn "  ok        the repository is public").length > 1)
      s!"{clean.1}",
    check "report: a carried row names the assumption under it"
      (clean.1.any fun line =>
        ((line.splitOn "  carried").length > 1) &&
          ((line.splitOn "not readable without admin").length > 1))
      s!"{clean.1}",
    check "report: a missing row shouts, and carries its remedy"
      (stopped.1.any fun line =>
        ((line.splitOn "  MISSING").length > 1) && ((line.splitOn "create the ruleset").length > 1))
      s!"{stopped.1}",
    check "report: an unchecked row is distinguishable from a missing one"
      (stopped.1.any fun line =>
        ((line.splitOn "  unchecked").length > 1) && ((line.splitOn "HTTP 502").length > 1))
      s!"{stopped.1}",
    -- A deferred channel is reported, and reported as deferred: not as a row,
    -- and not by silence.
    check "report: a deferred channel is named above the rows"
      (clean.1.take 2 |>.all fun line => (line.splitOn "  deferred").length > 1)
      s!"{clean.1}",
    check "report: an enabled channel contributes no deferral note"
      (published.1.isEmpty) s!"{published.1}",
    -- The verdict, both ways.
    check "report: verified and carried rows permit the release, and it says how many"
      (match clean.2 with
       | .ok established =>
         ((established.splitOn "2 prerequisite(s) for Owner/tl hold").length > 1)
       | .error _ => false) s!"{clean.2.toOption}",
    check "report: a blocked audit refuses"
      (match stopped.2 with | .ok _ => false | .error _ => true) "a blocked audit permitted the release",
    -- The two counts separately: they have opposite remedies, and the mixed
    -- case is the one an operator most needs named.
    check "report: the refusal counts missing and unchecked apart"
      (match stopped.2 with
       | .ok _ => false
       | .error message => ((message.splitOn "3 prerequisite(s) stop this release").length > 1) &&
           ((message.splitOn "2 missing, 1 unchecked").length > 1))
      (match stopped.2 with | .ok m => m | .error m => m),
    check "report: the refusal says why silence is not consent"
      (match stopped.2 with
       | .ok _ => false
       | .error message => (message.splitOn "reading its silence as consent").length > 1)
      (match stopped.2 with | .ok m => m | .error m => m)]

/-! ## The v0.1 dependency boundary

The lexical arm of ADR-0026's boundary. Its whole job is to notice a command
invocation on the release path, so the rows that matter are the ones separating
an invocation from a mention: these scripts explain themselves at length, and
every one of the six forbidden names appears in that prose. A scan answered by
rewording a comment would teach exactly the wrong lesson, and one that missed an
invocation is a gate reporting a clean release path it never read. -/

private def boundaryCommands' (line : String) : List String := commandWords (codeOf line)

/-- The forbidden commands one text reaches. The scan also reports the lines it
    could not read, and the rows below that care about those read them from the
    same value rather than from a second call. -/
private def invocationsIn (kind : SourceKind) (text : String) : List Invocation :=
  (scanLines kind text).invocations

private def boundaryTests : List Outcome :=
  let jobs :=
    "on:\n  push:\n\njobs:\n  gates:\n    steps:\n      - run: ./scripts/check-task-ids.sh\n" ++
    "  publish-npm:\n    steps:\n      - run: npm publish --provenance\n" ++
    "  publish-release:\n    steps:\n      - run: gh release create\n"
  let running := workflowRunningText jobs
  [ -- Comments, in the four shapes these files actually contain.
    check "boundary: a commented invocation is prose, not a finding"
      ((boundaryCommands' "  # npm publish is deferred").isEmpty),
    check "boundary: a trailing comment does not hide the invocation before it"
      ((boundaryCommands' "npm publish # deferred").contains "npm"),
    check "boundary: a `#` inside a word is not a comment"
      ((boundaryCommands' "echo ${name#prefix} npm").contains "echo"),
    check "boundary: a quoted `#` is text"
      ((boundaryCommands' "printf '# %s' npm").contains "printf"),
    -- Command position. Each row is one way a real script writes an invocation.
    check "boundary: a bare invocation is found" ((boundaryCommands' "npm publish").contains "npm"),
    check "boundary: an argument is not an invocation"
      (!(boundaryCommands' "echo npm").contains "npm"),
    check "boundary: a probe for the tool counts as reaching for it"
      ((boundaryCommands' "if command -v npm >/dev/null 2>&1; then").contains "npm"),
    check "boundary: an invocation after a pipe is found"
      ((boundaryCommands' "curl -sSf https://example.invalid | node -").contains "node"),
    check "boundary: an invocation inside a substitution is found"
      ((boundaryCommands' "version=$(python3 -c 'print(1)')").contains "python3"),
    check "boundary: an assignment prefix does not consume the command"
      ((boundaryCommands' "NODE_ENV=production npm run build").contains "npm"),
    check "boundary: a quoted command name is still a command name"
      ((boundaryCommands' "'ruby' -c Formula/tl.rb").contains "ruby"),
    -- The spellings that are the same command. Each was a live evasion: an
    -- absolute path defeats the PATH-shim arm too, a shebang chooses the
    -- interpreter for a whole file, and a CRLF line ending glues a carriage
    -- return to the only token on its line.
    check "boundary: an absolute path is the command it ends in"
      ((boundaryCommands' "/usr/bin/python3 -c 'print(1)'").any
        (fun word => commandName word == "python3")),
    check "boundary: an interpreter reached through env is still that interpreter"
      ((invocationsIn .shell "/usr/bin/env python3 -c 'print(1)'").any (·.command.basename == "python3")),
    check "boundary: a shebang is not a comment"
      ((invocationsIn .shell "#!/usr/bin/env ruby\nputs 1\n").any (·.command.basename == "ruby")),
    check "boundary: a CRLF line ending does not hide the command on it"
      ((invocationsIn .shell "npm\r\necho hi\r\n").any (·.command.basename == "npm")),
    check "boundary: a script whose name ends in a command name is not that command"
      (!(invocationsIn .shell "./scripts/npm-pack.sh --selftest").any (·.command.basename == "npm")),
    check "boundary: a longer word that starts with a forbidden one is not it"
      (!(boundaryCommands' "npm-pack --selftest").contains "npm"),
    check "boundary: a script named after the tool is not the tool"
      (!(invocationsIn .shell "./scripts/npm-pack.sh --selftest").any (·.command.basename == "npm")),
    -- What a finding carries. The line is what makes the message actionable;
    -- the number is what makes it findable.
    checkEq "boundary: a finding carries its line number, its line and how it got there"
      (invocationsIn .shell "set -eu\necho hi\nbrew install tl")
      [{ line := 3, command := { written := "brew", basename := "brew" },
         site := .commandPosition, text := "brew install tl" }],
    checkEq "boundary: an interpreter is reported as written and as identified"
      (invocationsIn .shell "#! /usr/bin/python3\nprint(1)\n")
      [{ line := 1, command := { written := "/usr/bin/python3", basename := "python3" },
         site := .shebang, text := "#! /usr/bin/python3" }],
    -- References, as the scripts really write them.
    check "boundary: a plain reference is followed"
      ((referencedScripts "./scripts/check-task-ids.sh --selftest").contains "scripts/check-task-ids.sh"),
    check "boundary: a reference through a variable resolves to the same file"
      ((referencedScripts "RC_LIB_SELF=\"$repo_root/scripts/lib/release-common.sh\"").contains
        "scripts/lib/release-common.sh"),
    check "boundary: a root script is followed without a directory to name it"
      ((referencedScripts "sh install.sh --selftest").contains "install.sh"),
    check "boundary: a glob is not a file this can read"
      ((referencedScripts "git ls-files -- '*.sh'").isEmpty),
    check "boundary: a path inside a throwaway fixture is not a first-party script"
      ((referencedScripts "cp x \"$tmp/fixture.sh\"").isEmpty),
    check "boundary: one file named twice is followed once"
      ((referencedScripts "./scripts/a.sh\n./scripts/a.sh").length == 1),
    -- Workflow jobs, excluded by name.
    checkEq "boundary: a job opener is two spaces, a name and a colon"
      (jobOpener? "  publish-npm:") (some "publish-npm"),
    check "boundary: a step key inside a job does not open one"
      (jobOpener? "    steps:").isNone,
    check "boundary: the top-level jobs key does not open one" (jobOpener? "jobs:").isNone,
    -- A workflow step written on one line puts its command after a YAML key.
    -- Read as plain shell the key takes the command position and the command
    -- becomes an argument, which is how fifteen steps of the real release
    -- workflow were invisible to this scan.
    check "boundary: a single-line run: step is read as the shell it runs"
      ((invocationsIn .workflow "      - run: brew install coreutils").any
        (·.command.basename == "brew")),
    check "boundary: a step's title is prose, not a command line"
      ((invocationsIn .workflow "      - name: npm publish the packages").isEmpty),
    check "boundary: a run: block's lines are read too"
      ((invocationsIn .workflow "      - run: |\n          npm publish\n").any
        (·.command.basename == "npm")),
    -- YAML removes a block scalar's common indentation, so a `#!` written ten
    -- spaces in is at the first byte of the script the step writes. Read as a
    -- workflow comment it would be prose, and the helper it heads would run
    -- under an interpreter the release path may not have.
    check "boundary: a shebang indented inside a block scalar is still a shebang"
      ((invocationsIn .workflow "          #!/usr/bin/env python3").any
        (·.command.basename == "python3")),
    check "boundary: and in a shell file the same line is not one, because the kernel would not honour it"
      ((invocationsIn .shell "          #!/usr/bin/env python3").isEmpty),
    -- Both directions over one fixture: the npm step is there to be found, and
    -- what removes it is the deferred-job filter. Asserting only the second
    -- would hold just as well if the filter were the identity.
    check "boundary: a deferred channel's publish job is there to be found"
      ((invocationsIn .workflow jobs).any (·.command.basename == "npm")) jobs,
    check "boundary: and it is not read"
      (!(invocationsIn .workflow running).any (·.command.basename == "npm"))
      running,
    check "boundary: the job after a deferred one is still read"
      (((running.splitOn "publish-release").length > 1) &&
        ((running.splitOn "gh release create").length > 1))
      running,
    -- The verdict is not reachable from fabricated evidence any more:
    -- `ScannedFile` has a private constructor, so every row about what the gate
    -- decides is a row about a real tree, in `boundaryFixtureTests` below.
    -- The inventories themselves.
    check "boundary: no entry point is also excluded as deferred"
      (entryPoints.all fun entry => !(deferredPaths.map (·.path)).contains entry.path),
    check "boundary: each entry point, deferred path and deferred job is named once"
      (((entryPoints.map (·.path)).eraseDups.length == entryPoints.length) &&
        ((deferredPaths.map (·.path)).eraseDups.length == deferredPaths.length) &&
        ((deferredJobs.map (·.job)).eraseDups.length == deferredJobs.length)),
    check "boundary: every deferred exclusion names the channel that owns it"
      (deferredPaths.all fun deferred => !deferred.channels.isEmpty && !deferred.why.isEmpty),
    -- The exclusions are only sound while the plan defers those channels, and
    -- this is the pair that says so: nothing is stale for the release being cut,
    -- and enabling a channel makes its own exclusions stale.
    check "boundary: no exclusion is stale for the release this repository cuts"
      (match ReleasePlan.parse "p" (planOf
          [planRow "github-release" true none, planRow "installer" true none,
           planRow "npm" false (some "\"0.2.0\""),
           planRow "homebrew" false (some "\"0.2.0\"")]) with
       | .ok plan => (staleExclusions plan).isEmpty
       | .error _ => false),
    check "boundary: enabling a channel makes its exclusions stale, by name"
      (match planWith true false with
       | .ok plan =>
         let stale := staleExclusions plan
         stale.any (fun line => (line.splitOn "npm-pack.sh").length > 1)
           && stale.any (fun line => (line.splitOn "publish-npm").length > 1)
           && !stale.any (fun line => (line.splitOn "publish-homebrew").length > 1)
       | .error _ => false) ]

/-! ### The boundary against real trees

Every mutation an adversarial review found is a fixture here, driven through the
public `dependency-boundary` command over a planted checkout. That is the whole
point of the group: the first version of this file tested the verdict on
evidence it built by hand, and the two defects that reached `main` — an empty
entry point, and an interpreter spelled as an absolute path — were both invisible
to rows shaped that way while being one command away from visible. -/

/-! ### The spellings of one command

A corpus rather than scattered rows, because the defect this closes was not a
missing check — it was two parsers that disagreed about what a command word is.
`#!/usr/bin/env python3` was read as an invocation and `#! /usr/bin/python3` as
a command named `#!` taking a path, and both spellings execute Python on every
platform this project ships to.

Each row is asserted twice, and the pair is the point. The parser row says what
the scan makes of the text; the command row plants the same text in a checkout
and runs the public `dependency-boundary` over it. A parser row alone can hold
while the command never reaches that code — which is how the spaced shebang
survived a group of rows that already covered shebangs — and a command row alone
cannot say *why* a verdict came out the way it did.

Three of the rows are the documented blind spots, asserted as clean on purpose.
A command name held in a variable, a name inside the string another shell runs,
and a script whose name ends in a command name are not findings here: the first
two are what `scripts/check-release-runtimes.sh` exists to catch by running the
path, and pinning them keeps a later "improvement" from turning this arm into
one that refuses the release path this repository already has. -/

/-- What the scan must make of one spelling. -/
private inductive Spelling where
  /-- The text reaches a forbidden command, by this route. -/
  | reaches (site : InvocationSite) (command : String)
  /-- The text was read, and reaches nothing forbidden. -/
  | clean
  /-- The text is shaped like something this scan reads and is not, so it
      refuses rather than reporting nothing. -/
  | unreadable
  deriving DecidableEq, Repr

private structure SpellingRow where
  label : String
  /-- A whole helper script, not a line: a `#!` is only a shebang at the start
      of one, and the rows about heredocs need the lines around it. -/
  helper : String
  expect : Spelling

private def spellingCorpus : List SpellingRow :=
  [{ label := "a bare command", helper := "#!/bin/sh\nnpm publish\n"
     expect := .reaches .commandPosition "npm" },
   { label := "a relative path", helper := "#!/bin/sh\n./tool/node --version\n"
     expect := .reaches .commandPosition "node" },
   { label := "an absolute path", helper := "#!/bin/sh\n/usr/bin/python3 -c 'print(1)'\n"
     expect := .reaches .commandPosition "python3" },
   { label := "an interpreter reached through env"
     helper := "#!/bin/sh\n/usr/bin/env python3 helper.py\n"
     expect := .reaches .commandPosition "python3" },
   { label := "exec, which replaces the shell with the command"
     helper := "#!/bin/sh\nexec npm publish\n"
     expect := .reaches .commandPosition "npm" },
   { label := "a probe for the tool", helper := "#!/bin/sh\ncommand -v ruby >/dev/null 2>&1\n"
     expect := .reaches .commandPosition "ruby" },
   { label := "an assignment prefix", helper := "#!/bin/sh\nNODE_ENV=production npm run build\n"
     expect := .reaches .commandPosition "npm" },
   { label := "a quoted command name", helper := "#!/bin/sh\n'ruby' -c Formula/tl.rb\n"
     expect := .reaches .commandPosition "ruby" },
   { label := "a shebang written against the marker"
     helper := "#!/usr/bin/env ruby\nputs 1\n"
     expect := .reaches .shebang "ruby" },
   { label := "a shebang written with a space after the marker"
     helper := "#! /usr/bin/python3\nprint(1)\n"
     expect := .reaches .shebang "python3" },
   { label := "a shebang with whitespace on both sides of env"
     helper := "#!  /usr/bin/env  node\nconsole.log(1)\n"
     expect := .reaches .shebang "node" },
   { label := "a spaced shebang on a CRLF line"
     helper := "#! /usr/bin/python3\r\nprint(1)\r\n"
     expect := .reaches .shebang "python3" },
   { label := "a command on a CRLF line", helper := "#!/bin/sh\r\nnpm\r\necho hi\r\n"
     expect := .reaches .commandPosition "npm" },
   { label := "a heredoc's shebang, which is the script it writes"
     helper := "#!/bin/sh\ncat > helper.py <<EOF\n#!/usr/bin/env python3\nEOF\n"
     expect := .reaches .shebang "python3" },
   { label := "a shebang that names no interpreter", helper := "#!\necho hi\n"
     expect := .unreadable },
   { label := "a shebang naming a variable the kernel will not expand"
     helper := "#!$INTERPRETER\necho hi\n"
     expect := .unreadable },
   { label := "a shebang whose interpreter is literal and whose argument is not"
     helper := "#!/usr/bin/env $INTERPRETER\necho hi\n"
     expect := .unreadable },
   { label := "a shebang with an interpreter flag, which is literal"
     helper := "#!/usr/bin/env -S ruby -w\nputs 1\n"
     expect := .reaches .shebang "ruby" },
   { label := "a commented invocation", helper := "#!/bin/sh\n# npm publish is deferred\n"
     expect := .clean },
   { label := "an argument that is not a command", helper := "#!/bin/sh\necho npm\n"
     expect := .clean },
   { label := "a tool whose name ends in a command name"
     helper := "#!/bin/sh\n./tool/npm-pack --selftest\n"
     expect := .clean },
   { label := "a command name held in a variable, resolved through PATH (the runtime arm's)"
     helper := "#!/bin/sh\ntool=npm\n\"$tool\" publish\n"
     expect := .clean },
   { label := "a command inside the string another shell runs (the runtime arm's)"
     helper := "#!/bin/sh\nsh -c \"npm publish\"\n"
     expect := .clean },
   -- The composition neither arm covered: a shim cannot shadow an absolute
   -- path, and a lexer cannot see the command position a variable holds. What
   -- is left visible is the path, wherever it is written.
   { label := "an interpreter path escaped into a different word"
     helper := "#!/bin/sh\n/usr/bin/pyt\\hon3 -c 'print(1)'\n"
     expect := .reaches .commandPosition "python3" },
   { label := "an interpreter path assigned to a variable"
     helper := "#!/bin/sh\ntool=/usr/bin/python3\n\"$tool\" -c 'print(1)'\n"
     expect := .reaches .writtenAsPath "python3" },
   -- The directory is a variable and the tail is literal, so the word is still
   -- in command position and still ends in the interpreter's name: caught as an
   -- invocation rather than as a path, which is the stronger of the two.
   { label := "an interpreter path built from a directory held in a variable"
     helper := "#!/bin/sh\ndir=/usr/bin\n\"$dir/python3\" -c 'print(1)'\n"
     expect := .reaches .commandPosition "python3" },
   { label := "an interpreter path passed as an argument, not run"
     helper := "#!/bin/sh\ncp /usr/bin/ruby \"$dest\"\n"
     expect := .reaches .writtenAsPath "ruby" },
   -- The residual, pinned as uncovered rather than left to be assumed covered:
   -- a name that is a literal word to nobody and resolves through PATH for
   -- nobody. A runtime without the interpreter installed is what closes it.
   { label := "an interpreter name read out of a file (neither arm's, and tracked as such)"
     helper := "#!/bin/sh\ntool=$(cat toolname)\n\"$tool\" -c 'print(1)'\n"
     expect := .clean }]

/-- What the scan made of one helper, in the terms a row states. -/
private def spellingObserved (helper : String) : Spelling :=
  let scan := scanLines .shell helper
  match scan.unsupported, scan.invocations with
  | _ :: _, _ => .unreadable
  | [], invocation :: _ => .reaches invocation.site invocation.command.basename
  | [], [] => .clean

/-- The refusal a row expects to find in the command's output. Deliberately the
    *finding* form and not the bare command name: the refusal's closing sentence
    names all six commands, so a row searching for `npm` would pass whatever the
    scan had done. -/
private def spellingNeedle : Spelling → String
  | .reaches .commandPosition command => s!"invokes {command}"
  | .reaches .shebang command => s!"runs under {command}"
  | .reaches .writtenAsPath command => s!"names the path of {command}"
  | .unreadable => "could not read a line"
  | .clean => "invoke none of"

/-- One file inside a planted checkout. -/
private def writeIn (root : System.FilePath) (path : String) (text : String) : IO Unit := do
  let full := root / path
  if let some parent := full.parent then IO.FS.createDirAll parent
  IO.FS.writeFile full text

private def cleanWorkflow : String := "jobs:\n  gates:\n    steps:\n      - run: true\n"

/-- A minimal checkout with all four entry points, so a refusal is the one the
    row plants rather than a missing file. Shared by the fixture rows and the
    spelling corpus: both run the real command over a real tree, and a second
    way to build one is a second thing to keep in step with `entryPoints`. -/
private def plantCheckout (base : System.FilePath) (name installer extra : String)
    (workflow : String := cleanWorkflow) : IO System.FilePath := do
  let root := base / name
  writeIn root "install.sh" installer
  writeIn root "scripts/verify-release-artifacts.sh" "#!/bin/sh\nsha256sum \"$1\"\n"
  writeIn root "scripts/check-release-policy.sh" ("#!/bin/sh\n" ++ extra)
  writeIn root ".github/workflows/release.yml" workflow
  return root

/-- Every spelling, through both the parser and the public command. -/
private def boundarySpellingTests : IO (List Outcome) := do
  let plan := "release/plan.json"
  let base ← IO.FS.createTempDir
  let mut outcomes : List Outcome := []
  for (row, index) in spellingCorpus.zipIdx 1 do
    let root ← plantCheckout base s!"spelling-{index}"
      "#!/bin/sh\n./scripts/helper.sh\n" "echo policy\n"
    writeIn root "scripts/helper.sh" row.helper
    let (status, out, err) ← dispatchCaptured
      ["dependency-boundary", "--root", root.toString, "--plan", plan]
    let wanted : UInt32 := if row.expect == .clean then 0 else 1
    outcomes := outcomes ++
      [checkEq s!"boundary spelling: {row.label} — the parser"
         (spellingObserved row.helper) row.expect,
       check s!"boundary spelling: {row.label} — the command"
         (status == wanted && ((out ++ err).splitOn (spellingNeedle row.expect)).length > 1)
         s!"exit {status}: {out}{err}"]
  IO.FS.removeDirAll base
  return outcomes

private def boundaryCommandTests : IO (List Outcome) := do
  let plan := "release/plan.json"
  let (realStatus, realOut, realErr) ←
    dispatchCaptured ["dependency-boundary", "--root", ".", "--plan", plan]
  let base ← IO.FS.createTempDir
  let write := writeIn
  let plant (name installer extra : String) (workflow : String := cleanWorkflow) :
      IO System.FilePath := plantCheckout base name installer extra workflow
  let cleanRoot ← plant "clean" "#!/bin/sh\necho install\n" "echo policy\n"
  let violatingRoot ← plant "violating" "#!/bin/sh\npython3 -c 'print(1)'\n" "echo policy\n"
  let deferredRoot ← plant "deferred" "#!/bin/sh\necho install\n"
    "./scripts/npm-pack.sh --selftest\n"
  write deferredRoot "scripts/npm-pack.sh" "#!/bin/sh\nnpm pack\n"
  let danglingRoot ← plant "dangling" "#!/bin/sh\necho install\n"
    "./scripts/absent-helper.sh\n"
  -- A single-line step in a job that runs, and the same command in one that
  -- does not: the workflow entry point is scanned per job, by name.
  let workflowRoot ← plant "workflow" "#!/bin/sh\necho install\n" "echo policy\n"
    ("jobs:\n  gates:\n    steps:\n      - run: brew install coreutils\n" ++
      "  publish-npm:\n    steps:\n      - run: npm publish\n")
  -- The interpreter of a helper a step writes, indented as YAML indents it.
  let scalarRoot ← plant "block-scalar" "#!/bin/sh\necho install\n" "echo policy\n"
    ("jobs:\n  gates:\n    steps:\n      - run: |\n          cat > helper.py <<'PY'\n" ++
      "          #!/usr/bin/env python3\n          PY\n          ./helper.py\n")
  -- The mutants, one per defect a review found. Named for what they do, so a
  -- failure here says which bypass came back.
  let emptyRoot ← plant "empty-entry-point" "" "echo policy\n"
  let absoluteRoot ← plant "absolute-interpreter"
    "#!/bin/sh\n/usr/bin/python3 -c 'print(1)'\n" "echo policy\n"
  let shebangRoot ← plant "absolute-shebang" "#!/bin/sh\n./scripts/helper.sh\n" "echo policy\n"
  write shebangRoot "scripts/helper.sh" "#!/usr/bin/env ruby\nputs 1\n"
  let chainRoot ← plant "beyond-the-bound" "#!/bin/sh\n./scripts/c1.sh\n" "echo policy\n"
  for index in [:closureBound + 5] do
    write chainRoot s!"scripts/c{index + 1}.sh" s!"#!/bin/sh\n./scripts/c{index + 2}.sh\n"
  write chainRoot s!"scripts/c{closureBound + 6}.sh" "#!/bin/sh\nnpm publish\n"
  let run (root : System.FilePath) : IO (UInt32 × String × String) :=
    dispatchCaptured ["dependency-boundary", "--root", root.toString, "--plan", plan]
  let (cleanStatus, cleanOut, _) ← run cleanRoot
  let (violatingStatus, _, violatingErr) ← run violatingRoot
  let (deferredStatus, deferredOut, deferredErr) ← run deferredRoot
  let (danglingStatus, _, danglingErr) ← run danglingRoot
  let (workflowStatus, _, workflowErr) ← run workflowRoot
  let (scalarStatus, _, scalarErr) ← run scalarRoot
  let (emptyStatus, _, emptyErr) ← run emptyRoot
  let (absoluteStatus, _, absoluteErr) ← run absoluteRoot
  let (shebangStatus, _, shebangErr) ← run shebangRoot
  let (chainStatus, _, chainErr) ← run chainRoot
  -- The plan the exclusions are read against, rather than the repository's own:
  -- a channel this release publishes through must make its exclusions a
  -- refusal, and that transition has no other test that runs the real command.
  let enabledPlan := (base / "plan-npm-enabled.json").toString
  IO.FS.writeFile enabledPlan (planOf
    [planRow "github-release" true none, planRow "installer" true none,
     planRow "npm" true none, planRow "homebrew" false (some "\"0.2.0\"")])
  let (enabledStatus, _, enabledErr) ←
    dispatchCaptured ["dependency-boundary", "--root", cleanRoot.toString,
      "--plan", enabledPlan]
  IO.FS.removeDirAll base
  return [
    -- The real tree. This row is the boundary itself, not a fixture of it.
    check "boundary: this checkout's v0.1 release path is clean" (realStatus == 0)
      s!"{realOut}{realErr}",
    check "boundary: the clean verdict names every entry point it read"
      (["install.sh", "scripts/verify-release-artifacts.sh", "scripts/check-release-policy.sh",
        ".github/workflows/release.yml"].all fun path => (realOut.splitOn path).length > 1)
      realOut,
    check "boundary: the clean verdict names the shared library it followed into"
      ((realOut.splitOn "scripts/lib/release-common.sh").length > 1) realOut,
    check "boundary: a fixture with no interpreter on the path passes" (cleanStatus == 0) cleanOut,
    check "boundary: an invocation in an entry point refuses" (violatingStatus == 1) violatingErr,
    check "boundary: the refusal names the file and the interpreter"
      (((violatingErr.splitOn "install.sh:2").length > 1) &&
        ((violatingErr.splitOn "python3").length > 1)) violatingErr,
    -- The exclusion is by name, and it is what keeps the deferred channels'
    -- own machinery from failing a boundary it is not part of.
    check "boundary: a deferred channel's script is not entered" (deferredStatus == 0)
      s!"{deferredOut}{deferredErr}",
    check "boundary: the deferred script is absent from what was read"
      ((deferredOut.splitOn "npm-pack").length == 1) deferredOut,
    -- A reference to a file that is not there means either the reference or
    -- the inventory is wrong, and both readings end in a file nobody scanned.
    check "boundary: a referenced script that is missing refuses" (danglingStatus == 1) danglingErr,
    check "boundary: the refusal names the file it could not read"
      ((danglingErr.splitOn "absent-helper.sh").length > 1) danglingErr,
    check "boundary: a one-line run: step in a job that runs is a refusal"
      (workflowStatus == 1) workflowErr,
    check "boundary: the refusal names the workflow, the line and the command"
      (((workflowErr.splitOn "release.yml:4").length > 1) &&
        ((workflowErr.splitOn "invokes brew").length > 1)) workflowErr,
    -- Against `invokes npm`, not against `npm`: the refusal's closing sentence
    -- names all six commands, so a bare search would pass whatever happened.
    check "boundary: the same command in a deferred channel's job is not one"
      ((workflowErr.splitOn "invokes npm").length == 1) workflowErr,
    -- The helper a step writes runs under whatever its first line names, and
    -- YAML's indentation is not part of that line.
    check "boundary: an interpreter a workflow step writes into a helper is a refusal"
      (scalarStatus == 1) scalarErr,
    check "boundary: and the refusal says the helper runs under it"
      ((scalarErr.splitOn "runs under python3").length > 1) scalarErr,
    -- An entry point with nothing in it produces no findings for the same
    -- reason a clean one does. This is the row that fabricated evidence could
    -- not supply, and the defect it describes reached main.
    check "boundary: an empty entry point is not a clean release path"
      (emptyStatus == 1) emptyErr,
    check "boundary: and the refusal names the file that held nothing"
      (((emptyErr.splitOn "read nothing").length > 1) &&
        ((emptyErr.splitOn "install.sh").length > 1)) emptyErr,
    -- An absolute path is the spelling neither arm would otherwise catch: a
    -- PATH shim cannot shadow /usr/bin/python3 either.
    check "boundary: an interpreter spelled as an absolute path is the same interpreter"
      (absoluteStatus == 1) absoluteErr,
    check "boundary: and the refusal names it by its program name"
      ((absoluteErr.splitOn "invokes python3").length > 1) absoluteErr,
    check "boundary: a shebang chooses an interpreter, so it is read as one"
      (shebangStatus == 1) shebangErr,
    check "boundary: and the shebang refusal names the script and the interpreter"
      (((shebangErr.splitOn "helper.sh:1").length > 1) &&
        ((shebangErr.splitOn "runs under ruby").length > 1)) shebangErr,
    -- Running out of the bound is a refusal, not a shorter verdict over the
    -- prefix it managed to read.
    check "boundary: a closure that outgrows its bound refuses"
      (chainStatus == 1) chainErr,
    check "boundary: and it says what it did not reach, and how to answer that"
      (((chainErr.splitOn "still queued").length > 1) &&
        ((chainErr.splitOn "closureBound").length > 1)) chainErr,
    -- The exclusions are only sound while the plan defers those channels.
    check "boundary: a channel this release publishes through cannot stay excluded"
      (enabledStatus == 1) enabledErr,
    check "boundary: and the refusal names the file and the edit that clears it"
      (((enabledErr.splitOn "npm-pack.sh").length > 1) &&
        ((enabledErr.splitOn "deferredPaths").length > 1)) enabledErr]

/-! ## The release-evidence write, as a model

Nothing here writes a file. The mechanism is a parameter (`Write.Mechanism`), so
the phase matrix below reaches failures a filesystem cannot be asked for on
demand — an `EIO` mid-write, a directory sync that failed *after* a successful
rename, a cleanup that could not remove what it created. The native writer
arrives against these same expectations: for every phase, the typed outcome, the
destination and the staging path this model predicts are what a real fault test
then compares the directory against. -/

private def writeWhat : String := "--output-dir"

private def componentText : Except String Write.Component → String
  | .ok component => component.text
  | .error _ => "<refused>"

private def pathRender : Except String Write.OutputPath → String
  | .ok path => path.render
  | .error _ => "<refused>"

private def pathComponents : Except String Write.OutputPath → List String
  | .ok path => path.components.map (·.text)
  | .error _ => ["<refused>"]

private def errorOfExcept : Except String α → String
  | .error message => message
  | .ok _ => "<no error>"

private def says (result : Except String α) (needle : String) : Bool :=
  ((errorOfExcept result).splitOn needle).length > 1

private def writePathTests : List Outcome :=
  [ -- The shapes a writing command actually uses.
    checkEq "write path: a single-component name parses"
      (pathComponents (Write.OutputPath.parse writeWhat "release-manifest.json"))
      ["release-manifest.json"],
    checkEq "write path: a nested name parses into its components"
      (pathComponents (Write.OutputPath.parse writeWhat "dist/tl.spdx.json"))
      ["dist", "tl.spdx.json"],
    checkEq "write path: rendering is the name it was given back"
      (pathRender (Write.OutputPath.parse writeWhat "dist/tl.spdx.json")) "dist/tl.spdx.json",
    checkEq "write path: the leaf is the file, not the first directory"
      (match Write.OutputPath.parse writeWhat "dist/inner/tl.spdx.json" with
       | .ok path => path.leaf.text
       | .error _ => "<refused>") "tl.spdx.json",
    checkEq "write path: a one-component name is its own leaf"
      (match Write.OutputPath.parse writeWhat "identity.pin" with
       | .ok path => path.leaf.text
       | .error _ => "<refused>") "identity.pin",
    checkEq "write path: the staging sibling is the leaf plus .tmp"
      (match Write.OutputPath.parse writeWhat "dist/tl.spdx.json" with
       | .ok path => path.stagingName
       | .error _ => "<refused>") "tl.spdx.json.tmp",
    checkEq "write path: the staging location retains every parent component"
      (match Write.OutputPath.parse writeWhat "dist/tl.spdx.json" with
       | .ok path => path.stagingRender
       | .error _ => "<refused>") "dist/tl.spdx.json.tmp",
    -- Every refusal the boundary owes, each naming its own rule rather than
    -- reporting "invalid": which rule was broken is what says how to fix it.
    check "write path: an absolute name is refused"
      (says (Write.OutputPath.parse writeWhat "/etc/passwd") "is an absolute path"),
    check "write path: and the refusal says --output-dir is what decides where"
      (says (Write.OutputPath.parse writeWhat "/etc/passwd") "--output-dir"),
    check "write path: a name climbing out of the granted directory is refused"
      (says (Write.OutputPath.parse writeWhat "../outside.json") "'..' is not an output component"),
    check "write path: .. in the middle is refused too"
      (says (Write.OutputPath.parse writeWhat "dist/../../outside.json") "'..' is not an output component"),
    check "write path: a '.' component is refused rather than skipped"
      (says (Write.OutputPath.parse writeWhat "./tl.spdx.json") "'.' is not an output component"),
    check "write path: an empty name is refused"
      (says (Write.OutputPath.parse writeWhat "") "empty component"),
    check "write path: a doubled separator is an empty component"
      (says (Write.OutputPath.parse writeWhat "dist//tl.json") "empty component"),
    check "write path: a trailing separator names no file"
      (says (Write.OutputPath.parse writeWhat "dist/") "empty component"),
    check "write path: an embedded NUL is refused"
      (says (Write.OutputPath.parse writeWhat "dist\x00/../../etc/passwd") "NUL byte"),
    check "write path: and the refusal says why a NUL is not cosmetic"
      (says (Write.OutputPath.parse writeWhat "dist\x00x") "stops reading a path at the first NUL"),
    -- One component is one component: a separator inside one means a path was
    -- built as a string somewhere it should have been built as a list.
    checkEq "write path: an ordinary component parses"
      (componentText (Write.Component.parse writeWhat "dist")) "dist",
    check "write path: a component holding a separator is refused"
      (says (Write.Component.parse writeWhat "dist/tl.json") "contains '/'"),
    check "write path: an empty component is refused"
      (says (Write.Component.parse writeWhat "") "empty component"),
    check "write path: a '.' component is refused"
      (says (Write.Component.parse writeWhat ".") "not an output component"),
    check "write path: a '..' component is refused"
      (says (Write.Component.parse writeWhat "..") "not an output component"),
    check "write path: a component holding a NUL is refused"
      (says (Write.Component.parse writeWhat "tl\x00.json") "NUL byte"),
    -- A name that merely starts with a dot is a file, not a traversal.
    checkEq "write path: a dotfile is an ordinary component"
      (componentText (Write.Component.parse writeWhat ".hidden")) ".hidden",
    checkEq "write path: a name beginning with .. but longer is ordinary"
      (componentText (Write.Component.parse writeWhat "..hidden")) "..hidden",
    -- The base is the operator's anchor and is deliberately not held to the
    -- component rules: it may be absolute, and it may be a symbolic link.
    checkEq "write base: an absolute directory is accepted"
      (match Write.OutputDirectory.parse writeWhat "/var/folders/tmp.d" with
       | .ok base => base.path
       | .error _ => "<refused>") "/var/folders/tmp.d",
    checkEq "write base: a relative directory is accepted"
      (match Write.OutputDirectory.parse writeWhat "dist" with
       | .ok base => base.path
       | .error _ => "<refused>") "dist",
    check "write base: the empty string is refused"
      (says (Write.OutputDirectory.parse writeWhat "") "names no directory"),
    check "write base: an embedded NUL is refused"
      (says (Write.OutputDirectory.parse writeWhat "di\x00st") "NUL byte"),
    checkEq "write base: the default is the working directory, stated"
      Write.OutputDirectory.working.path "."]

/-! ### The row the native side reports

The codes are a contract with C, so the matrix runs both ways over both
enumerations: everything the model can name encodes and decodes back, and every
code a row could carry either decodes to something this list holds or is
refused. A phase added to the inductive without a code, or with a code nothing
knows, fails here rather than at a release. -/

private def sampleErrno : Write.Errno := .eacces

private def failureRow (operation : Write.Operation) (errno : Write.Errno) :
    Write.WriteOutcome :=
  .failedBeforeCommit { operation, errno } .notCreated

private def decodedIs (result : Except String Write.WriteOutcome)
    (outcome : Write.WriteOutcome) : Bool :=
  match result with
  | .ok decoded => decoded == outcome
  | .error _ => false

private def roundTrips (outcome : Write.WriteOutcome) : Bool :=
  decodedIs (Write.decodeRow (Write.encodeRow outcome)) outcome

private def outcomeOf : Except String Write.WriteOutcome → String
  | .ok outcome => reprStr outcome
  | .error message => s!"<refused: {message}>"

private def writeCodecTests : List Outcome :=
  -- Every phase, as the failure a fault test injects for it.
  (Write.Operation.all.map fun operation =>
    check s!"write row: a failure in {operation.describe} survives the row"
      (roundTrips (failureRow operation sampleErrno))
      (outcomeOf (Write.decodeRow (Write.encodeRow (failureRow operation sampleErrno))))) ++
  -- Every named errno, on the phase most likely to report it.
  (Write.Errno.named.map fun errno =>
    check s!"write row: {errno.name} survives the row"
      (roundTrips (failureRow .createStaging errno))
      (outcomeOf (Write.decodeRow (Write.encodeRow (failureRow .createStaging errno))))) ++
  [ -- An unrecognised errno keeps its number rather than being folded into a
    -- name that reads like a diagnosis.
    check "write row: an unmapped errno survives with its raw number"
      (roundTrips (failureRow .writeBytes (.other 79))),
    checkEq "write row: and it is reported as a number, not a guessed name"
      (Write.Errno.name (.other 79)) "errno 79",
    -- Both sync strengths, both directory-sync outcomes, all three cleanup
    -- dispositions: the whole observation space, not a sample of it.
    check "write row: a full-barrier commit survives"
      (roundTrips (.committed .fullBarrier .synced)),
    check "write row: an ordinary-fsync commit survives"
      (roundTrips (.committed .ordinaryFsync .synced)),
    check "write row: a commit whose directory sync failed survives"
      (roundTrips (.committed .fullBarrier
        (.unsynced { operation := .syncDirectory, errno := .eio }))),
    check "write row: a failure that created nothing survives"
      (roundTrips (.failedBeforeCommit { operation := .createStaging, errno := .eexist }
        .notCreated)),
    check "write row: a failure whose staging file was removed survives"
      (roundTrips (.failedBeforeCommit { operation := .rename, errno := .eisdir } .removed)),
    check "write row: a failure whose staging file could not be removed survives"
      (roundTrips (.failedBeforeCommit { operation := .writeBytes, errno := .enospc }
        (.retained { operation := .removeStaging, errno := .eacces }))),
    -- The codes, both directions. Every code a row could carry decodes to a
    -- phase this build lists, and every listed phase has a code that decodes.
    check "write row: every phase code decodes back to its own phase"
      (Write.Operation.all.all fun operation =>
        Write.Operation.ofCode operation.code == some operation),
    check "write row: every code a row could carry is a phase this build lists"
      ((List.range 40).all fun code =>
        match Write.Operation.ofCode code with
        | none => true
        | some operation => Write.Operation.all.contains operation),
    check "write row: no phase encodes as zero, which is how a row says no error"
      (Write.Operation.all.all fun operation => operation.code != 0),
    check "write row: every named errno decodes back to itself"
      (Write.Errno.named.all fun errno => Write.Errno.ofCode errno.code errno.raw == some errno),
    check "write row: every errno code a row could carry is one this build lists"
      ((List.range 40).all fun code =>
        match Write.Errno.ofCode code 0 with
        | none => true
        | some errno => Write.Errno.named.contains errno),
    check "write row: no named errno encodes as zero"
      (Write.Errno.named.all fun errno => errno.code != 0),
    check "write row: every phase says what it was doing, and what to do about it"
      (Write.Operation.all.all fun operation =>
        !operation.describe.isEmpty && !operation.remedy.isEmpty),
    check "write row: every named errno has a name to print"
      (Write.Errno.named.all fun errno => !errno.name.isEmpty)]

/-! ### Rows this build refuses

A row the decoder half-understood would be a write reported as successful over
a file that was never replaced, so every shape that is not exactly one outcome's
encoding is a refusal. -/

private def refusedRow (why : String) (row : List Nat) : Outcome :=
  check s!"write row: {why} is refused" (Write.decodeRow row).toOption.isNone
    (outcomeOf (Write.decodeRow row))

private def writeMalformedTests : List Outcome :=
  [ refusedRow "an empty row" [],
    refusedRow "a row of eight fields" [0, 0, 0, 0, 0, 0, 0, 0],
    refusedRow "a row of ten fields" [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    refusedRow "an outcome tag this build does not know" [2, 0, 0, 0, 0, 0, 0, 0, 0],
    refusedRow "a sync strength this build does not know" [0, 2, 0, 0, 0, 0, 0, 0, 0],
    -- A commit that also carries an error is two claims about one write.
    refusedRow "a synced commit carrying an error" [0, 0, 0, 5, 1, 0, 0, 0, 0],
    refusedRow "an unsynced commit carrying no error" [0, 0, 1, 0, 0, 0, 0, 0, 0],
    refusedRow "a commit carrying a second error" [0, 0, 0, 0, 0, 0, 11, 1, 0],
    -- A write that did not commit never reached a sync, so a strength here
    -- means the two sides disagree about what happened.
    refusedRow "a failure reporting a sync strength" [1, 1, 0, 5, 3, 0, 0, 0, 0],
    refusedRow "a failure carrying no error" [1, 0, 0, 0, 0, 0, 0, 0, 0],
    refusedRow "a cleanup disposition this build does not know" [1, 0, 3, 5, 3, 0, 0, 0, 0],
    refusedRow "a retained cleanup carrying no error" [1, 0, 2, 5, 3, 0, 0, 0, 0],
    refusedRow "a removed cleanup carrying an error" [1, 0, 1, 5, 3, 0, 11, 1, 0],
    refusedRow "a created-nothing cleanup carrying an error" [1, 0, 0, 5, 3, 0, 11, 1, 0],
    -- One value, one encoding. A named errno with a raw number beside it is a
    -- second spelling of the same error, and admitting it would mean two rows
    -- decode to one outcome.
    refusedRow "a named errno carrying a raw number" [1, 0, 0, 5, 3, 13, 0, 0, 0],
    refusedRow "an errno code this build does not know" [1, 0, 0, 5, 44, 0, 0, 0, 0],
    refusedRow "a phase code this build does not know" [1, 0, 0, 44, 3, 0, 0, 0, 0],
    -- The refusal has to say it is a defect in the tool rather than something
    -- the caller did, because there is no invocation that fixes it.
    check "write row: a refusal says the two sides of the contract were changed apart"
      (says (Write.decodeRow [7, 0, 0, 0, 0, 0, 0, 0, 0]) "defect in the release tool"),
    -- The array form the FFI boundary actually hands over.
    check "write row: the array form decodes the same way"
      (decodedIs (Write.decode #[0, 0, 0, 0, 0, 0, 0, 0, 0]) (.committed .fullBarrier .synced)),
    check "write row: a short array is refused like a short row"
      (Write.decode #[0, 0, 0]).toOption.isNone]

/-! ### What the directory looks like afterwards

The prediction a fault test compares the real directory against. Pinned per
phase rather than only proved, because the theorems say the prediction is
consistent and these rows say what it actually is. -/

private def writeEffectTests : List Outcome :=
  (Write.Operation.all.flatMap fun operation =>
    let outcome : Write.WriteOutcome := failureRow operation sampleErrno
    [ checkEq s!"write effect: a failure in {operation.describe} leaves the destination alone"
        outcome.destination Write.Destination.untouched,
      checkEq s!"write effect: a failure in {operation.describe} is not a landed write"
        outcome.landed false]) ++
  [ checkEq "write effect: a commit replaces the destination"
      (Write.WriteOutcome.committed .fullBarrier .synced).destination Write.Destination.replaced,
    checkEq "write effect: a commit whose directory sync failed still replaced it"
      (Write.WriteOutcome.committed .ordinaryFsync
        (.unsynced { operation := .syncDirectory, errno := .eio })).destination
      Write.Destination.replaced,
    checkEq "write effect: a commit leaves no staging file"
      (Write.WriteOutcome.committed .fullBarrier .synced).staging Write.Staging.absent,
    checkEq "write effect: a failure that created nothing leaves no staging file"
      (Write.WriteOutcome.failedBeforeCommit { operation := .createStaging, errno := .eexist }
        .notCreated).staging Write.Staging.absent,
    checkEq "write effect: a failure whose cleanup removed the sibling leaves none"
      (Write.WriteOutcome.failedBeforeCommit { operation := .rename, errno := .eisdir }
        .removed).staging Write.Staging.absent,
    -- The one a rerun has to know about: the next attempt creates that sibling
    -- exclusively, so a leftover fails the next write too.
    checkEq "write effect: a failure whose cleanup could not remove it leaves one"
      (Write.WriteOutcome.failedBeforeCommit { operation := .writeBytes, errno := .enospc }
        (.retained { operation := .removeStaging, errno := .eacces })).staging
      Write.Staging.occupied]

/-! ### What a command tells the operator -/

private def acceptOf (outcome : Write.WriteOutcome) : Except String (Option String) :=
  Write.accept "dist/tl.spdx.json" "dist/tl.spdx.json.tmp" outcome

private def acceptedSilently (result : Except String (Option String)) : Bool :=
  match result with
  | .ok none => true
  | _ => false

private def disclosureOf (outcome : Write.WriteOutcome) : String :=
  match acceptOf outcome with
  | .ok (some disclosure) => disclosure
  | .ok none => "<nothing disclosed>"
  | .error message => s!"<refused: {message}>"

private def writeAcceptTests : List Outcome :=
  [ check "write accept: a clean commit is accepted and discloses nothing"
      (acceptedSilently (acceptOf (.committed .fullBarrier .synced))),
    -- The ADR's decision, and the one this model exists to make expressible:
    -- the rename happened, so every later open in this run reads the new bytes.
    -- Refusing here would send an operator to repair a correct file.
    check "write accept: an unflushed directory entry is a disclosure, not a refusal"
      (acceptOf (.committed .fullBarrier
        (.unsynced { operation := .syncDirectory, errno := .eio }))).toOption.isSome,
    check "write accept: and the disclosure says the file was replaced"
      ((((disclosureOf (.committed .fullBarrier
        (.unsynced { operation := .syncDirectory, errno := .eio }))).splitOn "was replaced").length > 1)),
    check "write accept: and it names the phase that did not complete"
      ((((disclosureOf (.committed .fullBarrier
        (.unsynced { operation := .syncDirectory, errno := .eio }))).splitOn "EIO").length > 1)),
    check "write accept: an ordinary fsync is accepted, not downgraded to a refusal"
      (acceptedSilently (acceptOf (.committed .ordinaryFsync .synced))),
    checkEq "write accept: the two strengths are distinguishable in a report"
      (Write.SyncStrength.describe .fullBarrier != Write.SyncStrength.describe .ordinaryFsync) true,
    -- A write that did not commit refuses, and the refusal has to carry the
    -- three things an operator acts on: what failed, that the destination is
    -- unchanged, and what is left at the staging path.
    check "write accept: a failure before the commit refuses"
      (acceptOf (failureRow .rename .eisdir)).toOption.isNone,
    check "write accept: the refusal names the phase"
      (says (acceptOf (failureRow .rename .eisdir)) "renaming the staging file"),
    check "write accept: the refusal names the errno"
      (says (acceptOf (failureRow .rename .eisdir)) "EISDIR"),
    check "write accept: the refusal says the destination is unchanged"
      (says (acceptOf (failureRow .rename .eisdir)) "still holds what it held"),
    check "write accept: the refusal names the destination"
      (says (acceptOf (failureRow .rename .eisdir)) "dist/tl.spdx.json"),
    check "write accept: a failure that created nothing says nothing was left behind"
      (says (acceptOf (failureRow .openBase .enoent)) "Nothing was left behind"),
    check "write accept: a removed staging file is reported as removed"
      (says (acceptOf (.failedBeforeCommit { operation := .rename, errno := .eisdir } .removed))
        "was removed"),
    -- The one an operator must act on before rerunning.
    check "write accept: a retained staging file is named"
      (says (acceptOf (.failedBeforeCommit { operation := .writeBytes, errno := .enospc }
        (.retained { operation := .removeStaging, errno := .eacces }))) "tl.spdx.json.tmp"),
    check "write accept: and the refusal says why it matters"
      (says (acceptOf (.failedBeforeCommit { operation := .writeBytes, errno := .enospc }
        (.retained { operation := .removeStaging, errno := .eacces }))) "is still there"),
    -- Every phase's refusal teaches: it says what to do next, not only what
    -- broke. A message that only restates its own name is a defect.
    check "write accept: every phase's refusal carries a remedy"
      (Write.Operation.all.all fun operation =>
        says (acceptOf (failureRow operation sampleErrno)) operation.remedy),
    -- The errno narrows the phase's remedy where it determines one.
    check "write accept: a permission refusal says the permissions refuse this user"
      (says (acceptOf (failureRow .walkDirectory .eacces)) "refuse this user"),
    check "write accept: an out-of-space refusal says so"
      (says (acceptOf (failureRow .writeBytes .enospc)) "out of space or over quota"),
    check "write accept: a symlinked component says links are refused, not followed"
      (says (acceptOf (failureRow .walkDirectory .eloop)) "refused rather than followed"),
    check "write accept: an ownership refusal says the directory belongs to another user"
      (says (acceptOf (failureRow .ownBase .notOwned)) "belongs to another user")]

/-! ### The seam

`through` is what a writing command will call, with the native mechanism in
place of these. Each row hands it a phase's row directly, which is how the
matrix reaches faults a filesystem cannot be asked for. -/

private def fixedMechanism (row : Array UInt32) : Write.Mechanism :=
  fun _ _ _ => pure row

private def throwingMechanism : Write.Mechanism :=
  fun _ _ _ => throw (IO.userError "the mechanism itself failed")

private def rowOf (outcome : Write.WriteOutcome) : Array UInt32 :=
  ((Write.encodeRow outcome).map (fun code => UInt32.ofNat code)).toArray

private def writeSeamTests : IO (List Outcome) := do
  match Write.OutputPath.parse writeWhat "dist/tl.spdx.json" with
  | .error message =>
      -- Not a skip: the seam rows below all write through this name, so a
      -- checkout where it stopped parsing must fail rather than fall silent.
      return [check "write seam: the sample output name parses" false message]
  | .ok samplePath =>
  let runThrough (mechanism : Write.Mechanism) : IO (Except String (Option String)) :=
    Write.through mechanism Write.OutputDirectory.working samplePath (String.toUTF8 "bytes")
  let clean ← runThrough (fixedMechanism (rowOf (.committed .fullBarrier .synced)))
  let unsynced ← runThrough (fixedMechanism (rowOf (.committed .ordinaryFsync
    (.unsynced { operation := .syncDirectory, errno := .eio }))))
  let malformed ← runThrough (fixedMechanism #[9, 9, 9])
  let thrown ← runThrough throwingMechanism
  let located ←
    match Write.OutputDirectory.parse writeWhat "/tmp/release-output" with
    | .error message => pure (.error message)
    | .ok base =>
        Write.through
          (fixedMechanism (rowOf (.failedBeforeCommit
            { operation := .writeBytes, errno := .enospc }
            (.retained { operation := .removeStaging, errno := .eacces }))))
          base samplePath (String.toUTF8 "bytes")
  let mut phaseRows : List Outcome := []
  for operation in Write.Operation.all do
    let outcome := failureRow operation sampleErrno
    let refused ← runThrough (fixedMechanism (rowOf outcome))
    phaseRows := phaseRows ++ [
      check s!"write seam: an injected failure in {operation.describe} refuses"
        refused.toOption.isNone (toString refused.toOption.isSome),
      check s!"write seam: and it names the phase it was injected at"
        (says refused operation.describe) (errorOfExcept refused)]
  return phaseRows ++ [
    check "write seam: a clean commit passes through with nothing to disclose"
      (acceptedSilently clean) (errorOfExcept clean),
    check "write seam: a commit with an unflushed directory entry passes through"
      clean.toOption.isSome (errorOfExcept unsynced),
    check "write seam: and it carries the disclosure"
      (match unsynced with | .ok (some _) => true | _ => false) (errorOfExcept unsynced),
    -- A row this build cannot read is a defect in the tool, and it must refuse
    -- rather than fall back to reporting a write that may not have happened.
    check "write seam: a row this build cannot read refuses"
      malformed.toOption.isNone (errorOfExcept malformed),
    check "write seam: and says it is a defect rather than a bad invocation"
      (says malformed "defect in the release tool"),
    -- The mechanism itself failing is not the same thing, and says so.
    check "write seam: a mechanism that fails outright refuses"
      thrown.toOption.isNone (errorOfExcept thrown),
    check "write seam: and the refusal names the file it was writing"
      (says thrown "dist/tl.spdx.json"),
    check "write seam: and the directory it was writing into"
      (says thrown "in ."),
    check "write seam: a retained staging refusal names its exact location under the base"
      (says located "/tmp/release-output/dist/tl.spdx.json.tmp")
      (errorOfExcept located)]

def releaseToolTests : IO (List Outcome) := do
  let (helpStatus, helpOut, helpErr) ← dispatchCaptured ["--help"]
  let (shortStatus, shortOut, _) ← dispatchCaptured ["-h"]
  let (wordStatus, wordOut, _) ← dispatchCaptured ["help"]
  let (emptyStatus, emptyOut, emptyErr) ← dispatchCaptured []
  let (unknownStatus, unknownOut, unknownErr) ← dispatchCaptured ["publish-everything"]
  let mut outs := [
    -- Asking for help is not an error, and it goes to stdout.
    checkEq "tlrelease: --help succeeds" helpStatus 0,
    check "tlrelease: --help writes the usage to stdout" (contains helpOut "usage: tlrelease")
      helpOut,
    check "tlrelease: --help writes nothing to stderr" helpErr.isEmpty helpErr,
    checkEq "tlrelease: -h is the same as --help" (shortStatus, shortOut) (helpStatus, helpOut),
    checkEq "tlrelease: the help subcommand is the same as --help"
      (wordStatus, wordOut) (helpStatus, helpOut),
    -- The two refusals. A release step invoking this with no command, or with
    -- a command this build does not have, must not be able to read the result
    -- as success — that is the entire failure this executable exists to stop.
    checkEq "tlrelease: no command is a usage error" emptyStatus 2,
    check "tlrelease: no command says so on stderr"
      (contains emptyErr "no command given") emptyErr,
    check "tlrelease: no command writes nothing to stdout" emptyOut.isEmpty emptyOut,
    checkEq "tlrelease: an unknown command is a usage error" unknownStatus 2,
    check "tlrelease: an unknown command names the command it did not recognise"
      (contains unknownErr "publish-everything") unknownErr,
    check "tlrelease: an unknown command says how to list the real ones"
      (contains unknownErr "--help") unknownErr,
    check "tlrelease: an unknown command writes nothing to stdout" unknownOut.isEmpty unknownOut,
    -- Distinguishing "did nothing" from "succeeded" is the whole point, so a
    -- refusal must never share an exit status with success.
    check "tlrelease: no refusal exits zero"
      (emptyStatus != 0 && unknownStatus != 0) s!"empty={emptyStatus} unknown={unknownStatus}"]
  -- `help` is generated from the same table `dispatch` reads, so a command
  -- that exists but is undocumented — or documented but unreachable — is not
  -- representable. These rows check that the table is actually the source of
  -- both, which is only observable once it is non-empty.
  for command in commands do
    let (status, _, stderr) ← dispatchCaptured [command.name]
    outs := outs ++ [
      check s!"tlrelease: '{command.name}' is listed in the usage"
        (contains helpOut command.name) helpOut,
      -- Against stderr, which is where dispatch writes it. The first version
      -- of this row searched stdout for a message that only ever goes to
      -- stderr, so it held for every input and could not fail — a vacuous row
      -- guarding the one property the command table exists to give.
      check s!"tlrelease: '{command.name}' reaches its own handler, not the unknown-command path"
        (!contains stderr "unknown command")
        s!"dispatching '{command.name}' reported it as unknown; stderr was: {stderr}",
      -- Invoked with no arguments every command must refuse, and refuse as a
      -- usage error rather than by claiming to have done something.
      checkEq s!"tlrelease: '{command.name}' with no arguments is a usage error" status 2]
  outs := outs ++ [
    check "tlrelease: every command has a distinct name"
      ((commands.map (·.name)).eraseDups.length == commands.length)
      s!"duplicate command names: {commands.map (·.name)}"]
  return jsonTests ++ modelTests ++ checkTests ++ optionTests ++ boundaryTests ++ reportTestsForAudit ++ descriptionTests ++ homebrewTests ++ tapRemoteTests ++ policyTests ++ manifestVerdictTests
    ++ metadataVerdictTests ++ assemblyTests ++ prerequisiteTests ++ channelOutputTests ++ sbomTests ++ outs
    ++ (← documentTests) ++ (← pinCommandTests) ++ (← writeCommandTests) ++ (← planCommandTests)
    ++ writePathTests ++ writeCodecTests ++ writeMalformedTests ++ writeEffectTests
    ++ writeAcceptTests ++ (← writeSeamTests)
    ++ (← sbomDocumentTests) ++ (← sbomCommandTests) ++ (← processTests) ++ (← digestTests) ++ (← goldenManifestTests) ++ (← formulaDriftTests) ++ (← homebrewCommandTests) ++ (← tapPublishTests) ++ (← policyParityTests) ++ (← policyRunnerTests) ++ (← certificateTests) ++ (← consistencyTests) ++ (← prerequisiteIoTests) ++ (← clientTests) ++ (← lifecycleTests) ++ (← boundarySpellingTests) ++ (← boundaryCommandTests)

end Tl.Tests
