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
    PublishedTarget.of target digest build
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
  return jsonTests ++ modelTests ++ channelOutputTests ++ outs ++ (← documentTests)
    ++ (← pinCommandTests) ++ (← planCommandTests)

end Tl.Tests
