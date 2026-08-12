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

private def targetRow (name : String) (tier : String) : String :=
  "{\"target\": \"" ++ name ++ "\", \"tier\": \"" ++ tier ++ "\", \"os\": \"linux\", \"cpu\": \"x64\"}"

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

/-- Deletion guard for the release tool's verdict-logic theorems, on the same
    reasoning as `pinnedVerdictLogicTheorems` in Tests/VerifyTests.lean: they
    carry no landmark by design, because landmarks guard the *product's* proved
    claims and this is release administration. Naming them here makes retiring
    one a compile error rather than a silent deletion. -/
private def pinnedReleaseVerdictTheorems : Unit :=
  let _ := @Release.channelDecisions_eq
  let _ := @Release.channelDecisions_lookup
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
  let (writeStatus, writeOut, _) ← run "write-pin" [identityPath, pinPath]
  let written ← IO.FS.readFile pinPath
  let (checkStatus, checkOut, _) ← run "check-pin" [identityPath, pinPath]
  -- Drift, which is the whole reason check-pin exists.
  IO.FS.writeFile pinPath "https://example.invalid\n^x$\n"
  let (driftStatus, _, driftErr) ← run "check-pin" [identityPath, pinPath]
  let (missingIdentity, _, missingIdentityErr) ←
    run "write-pin" [(base / "absent.json").toString, pinPath]
  let (missingPin, _, missingPinErr) ← run "check-pin" [identityPath, (base / "absent.pin").toString]
  -- An identity anchored at the head but not the tail: the generator must
  -- refuse rather than write a pin the verifier would reject. The tail is the
  -- half that was historically dropped, and a tag name may contain '/', so
  -- trailing content past the pinned identity is reachable.
  let badIdentityPath := (base / "bad.json").toString
  IO.FS.writeFile badIdentityPath
    "{\"repository\":\"a/b\",\"npmPackage\":\"@a/b\",\"releaseWorkflow\":\"w\",\"certificateOidcIssuer\":\"https://i\",\"certificateIdentityRegexp\":\"^https://github.com/x\"}"
  let unwrittenPath := (base / "never.pin").toString
  let (badStatus, _, badErr) ← run "write-pin" [badIdentityPath, unwrittenPath]
  let neverWritten := !(← System.FilePath.pathExists unwrittenPath)
  -- The same malformed identity through check-pin. Without its own refusal
  -- there, an unusable release/identity.json is reported as a drifted pin —
  -- which sends the operator to `write-pin`, which refuses, with nothing
  -- connecting the two messages.
  let (badCheckStatus, _, badCheckErr) ← run "check-pin" [badIdentityPath, pinPath]
  -- Writing into a directory that does not exist: a refusal, not a backtrace.
  let (unwritableStatus, _, unwritableErr) ←
    run "write-pin" [identityPath, (base / "no-such-dir" / "p.pin").toString]
  IO.FS.removeDirAll base
  return [
    checkEq "pin command: write-pin succeeds against the committed identity" writeStatus 0,
    check "pin command: write-pin says where it wrote" (contains writeOut pinPath) writeOut,
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
    checkEq "pin command: an unwritable destination is a refusal, not an exception"
      unwritableStatus 1,
    check "pin command: an unwritable destination names the path"
      (contains unwritableErr "could not write") unwritableErr]

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
  let first := (base / "first.spdx.json").toString
  let second := (base / "second.spdx.json").toString
  let other := (base / "other.spdx.json").toString
  let never := (base / "never.spdx.json").toString
  let (status, out, _) ← runCommand "sbom" ["1.2.3", "lean-toolchain", "lake-manifest.json", first]
  let (againStatus, _, _) ←
    runCommand "sbom" ["1.2.3", "lean-toolchain", "lake-manifest.json", second]
  let (otherStatus, _, _) ←
    runCommand "sbom" ["1.2.4", "lean-toolchain", "lake-manifest.json", other]
  let written ← IO.FS.readFile first
  let writtenAgain ← IO.FS.readFile second
  let writtenOther ← IO.FS.readFile other
  -- Against the committed fixtures, through the command rather than the pure
  -- core: this is the path the release workflow runs.
  let goldenOut := (base / "golden.spdx.json").toString
  let (goldenStatus, _, _) ← runCommand "sbom"
    ["9.9.9", "Tests/fixtures/sbom-lean-toolchain", "Tests/fixtures/sbom-lake-manifest.json",
     goldenOut]
  let goldenWritten ← IO.FS.readFile goldenOut
  let golden ← IO.FS.readFile "Tests/fixtures/sbom-golden.spdx.json"
  let (missingToolchain, _, missingToolchainErr) ←
    runCommand "sbom" ["1.2.3", (base / "absent").toString, "lake-manifest.json", never]
  let (missingManifest, _, missingManifestErr) ←
    runCommand "sbom" ["1.2.3", "lean-toolchain", (base / "absent.json").toString, never]
  -- A refusal must not leave a document behind: a partial SBOM would be hashed
  -- into SHA256SUMS and signed like a complete one.
  let brokenManifest := (base / "broken.json").toString
  IO.FS.writeFile brokenManifest (manifestOf [])
  let (emptyInventory, _, emptyInventoryErr) ←
    runCommand "sbom" ["1.2.3", "lean-toolchain", brokenManifest, never]
  let (badVersion, _, badVersionErr) ←
    runCommand "sbom" ["v1.2.3", "lean-toolchain", "lake-manifest.json", never]
  -- A name the renderer cannot encode: the refusal comes from rendering rather
  -- than from parsing, which is the one command branch the pure rows above
  -- cannot reach.
  let astralManifest := (base / "astral.json").toString
  IO.FS.writeFile astralManifest
    (manifestOf [manifestRow (String.singleton (Char.ofNat 0x1f600)) (rev40 '1')])
  let (unrenderable, _, unrenderableErr) ←
    runCommand "sbom" ["1.2.3", "lean-toolchain", astralManifest, never]
  -- Checked after every refusal above, not after the first: each of them was
  -- given the same destination, so this says none of them wrote anything.
  let nothingWritten := !(← System.FilePath.pathExists never)
  -- A destination that is an existing directory. The temporary file is written
  -- and the rename over it fails, which is the arm that has to clean up after
  -- itself — a stray `<output>.tmp` beside a signed asset set is a file nothing
  -- describes.
  let occupied := (base / "occupied").toString
  IO.FS.createDir occupied
  let (occupiedStatus, _, occupiedErr) ←
    runCommand "sbom" ["1.2.3", "lean-toolchain", "lake-manifest.json", occupied]
  let noTemporary := !(← System.FilePath.pathExists (occupied ++ ".tmp"))
  -- Something already at the staging path. Writing through it would follow
  -- whatever it is — a link elsewhere, or another run's half-written file — so
  -- it is refused, and what was there is left for whoever has to explain it.
  let staged := (base / "staged.spdx.json").toString
  IO.FS.writeFile (staged ++ ".tmp") "an earlier run left this behind\n"
  let (stagedStatus, _, stagedErr) ←
    runCommand "sbom" ["1.2.3", "lean-toolchain", "lake-manifest.json", staged]
  let stagedUntouched := (← IO.FS.readFile (staged ++ ".tmp")) == "an earlier run left this behind\n"
  let stagedNotWritten := !(← System.FilePath.pathExists staged)
  let (unwritable, _, unwritableErr) ← runCommand "sbom"
    ["1.2.3", "lean-toolchain", "lake-manifest.json", (base / "no-such-dir" / "s.json").toString]
  let (fewArguments, _, fewArgumentsErr) ←
    runCommand "sbom" ["1.2.3", "lean-toolchain", "lake-manifest.json"]
  let (manyArguments, _, _) ← runCommand "sbom"
    ["1.2.3", "lean-toolchain", "lake-manifest.json", never, "extra"]
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
    checkEq "sbom command: a destination that is a directory is a refusal" occupiedStatus 1,
    check "sbom command: a destination that is a directory names the path"
      (contains occupiedErr "could not write") occupiedErr,
    check "sbom command: a failed rename leaves no temporary file behind" noTemporary
      "an <output>.tmp survived a write the command refused to complete",
    checkEq "sbom command: an occupied staging path is a refusal" stagedStatus 1,
    check "sbom command: an occupied staging path says what to look at"
      (contains stagedErr "already exists") stagedErr,
    check "sbom command: it writes through nothing it did not create" stagedUntouched
      "the command wrote through a file that was already at the staging path",
    check "sbom command: and produces no document when it refuses to stage"
      stagedNotWritten "a document appeared despite the refusal",
    -- A malformed version is a refusal, not a usage error: the invocation was
    -- well formed and a decision was made.
    checkEq "sbom command: a tag where the version belongs is a refusal" badVersion 1,
    check "sbom command: the tag refusal says to pass the bare version"
      (contains badVersionErr "bare version") badVersionErr,
    checkEq "sbom command: an unwritable destination is a refusal, not an exception"
      unwritable 1,
    check "sbom command: an unwritable destination names the path"
      (contains unwritableErr "could not write") unwritableErr,
    checkEq "sbom command: three arguments is a usage error" fewArguments 2,
    check "sbom command: the usage error names every argument"
      (contains fewArgumentsErr "<version> <lean-toolchain> <lake-manifest.json> <output.spdx.json>")
      fewArgumentsErr,
    checkEq "sbom command: a spare argument is a usage error" manyArguments 2]

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
  return jsonTests ++ modelTests ++ checkTests ++ optionTests ++ manifestVerdictTests
    ++ metadataVerdictTests ++ assemblyTests ++ channelOutputTests ++ sbomTests ++ outs
    ++ (← documentTests) ++ (← pinCommandTests) ++ (← planCommandTests)
    ++ (← sbomDocumentTests) ++ (← sbomCommandTests) ++ (← processTests) ++ (← digestTests) ++ (← goldenManifestTests) ++ (← certificateTests)

end Tl.Tests
