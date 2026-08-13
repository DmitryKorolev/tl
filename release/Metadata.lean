/-
What one build leg recorded, and whether it agrees with the release being cut.

Two halves of one boundary. A build leg is the only place a released binary
exists next to the source it was compiled from, and the job that signs gets its
binaries from an artifact store — so without a record travelling with each
binary, `sign` signs whatever arrived. `build-metadata` writes that record on
the leg; `metadataChecks` is what the manifest generator holds the record to
when the binaries come back together.

The evidence travels rather than the capability, deliberately. Attesting per
leg would mean granting `id-token: write` to four more jobs which all share one
`job_workflow_ref`, so each could then mint a certificate every verifier
accepts. A signed JSON record proves less and costs nothing.

Two defects this replaces, both recorded against the shell and Python it came
from:

- Nine required fields were tested with `not build.get(field)`, which cannot
  tell an absent field from `""`, `0` or `false`. `BuildMetadata.parse` in
  `release/Model.lean` already fixes that half; what remains here is that the
  *comparison* was nine separate `if`s in a function an empty target list could
  skip entirely.
- The run identity was compared leg-to-leg only — every leg agreeing with every
  other leg, and none of them with the run actually doing the signing. Four
  artifacts carried in from an earlier run of the same workflow agree with each
  other perfectly. And the workflow-ref half was guarded by
  `if workflow_ref and …`, so an unset environment variable did not weaken the
  check, it removed it.

The second is why `RunContext` is a closed sum rather than two strings that
might be empty. There is no value of it that means "do not compare"; there is
one that means "this run is not part of a workflow", which a caller has to
choose, spell out, and be seen to have spelled out.
-/
import release.Command
import release.Digest
import release.Json
import release.Model

namespace Release

open Lean (Json)

/-! ## Writing a leg's record -/

/-- What a leg records about the artifact it just built.

    The four descriptive fields at the end are for a human reading a published
    release months later; no verdict reads them, and inventing a check for them
    would be a check nothing could fail. They are carried through
    `BuildMetadata` as plain strings and are the only fields here allowed to be
    empty. -/
def BuildMetadata.toJson (build : BuildMetadata) : Json :=
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

/-- The record's bytes: the same deterministic rendering every document in this
    tool uses, so a leg's record is a function of what it built. -/
def renderBuildMetadata (build : BuildMetadata) : Except String String :=
  render build.toJson

/-- Assemble a leg's record from values that have each been checked.

    Every argument is already a parsed type or is one of the four descriptive
    strings, so this cannot fail and there is nothing here to get wrong. The
    checking happens in the command below, at the boundary.

    Which of these fields a rebuild is expected to reproduce is decided by
    ADR-0006's reproducibility boundary (*What reproduces, and what cannot*):
    `target`, `sha256`, `commit`, `tier`, `toolchain` and `lakeManifestSha256`
    are functions of the payload; the rest identify the run that produced it and
    are excluded by name there. A field added here is one or the other, and
    saying which — in that list — is part of adding it, because a rebuilder
    comparing against an unclassified field has no way to tell a real mismatch
    from a different run. -/
structure BuildMetadataInputs where
  target : String
  digest : Sha256
  commit : Commit
  tier : Tier
  runner : String
  toolchain : String
  lakeManifestSha256 : Sha256
  workflowRef : String
  runId : String
  runnerOs : String
  runnerArch : String
  containerImage : String
  runAttempt : String

def BuildMetadataInputs.record (inputs : BuildMetadataInputs) : BuildMetadata := {
  target := inputs.target
  sha256 := inputs.digest
  commit := inputs.commit
  tier := inputs.tier
  runner := inputs.runner
  toolchain := inputs.toolchain
  lakeManifestSha256 := inputs.lakeManifestSha256
  workflowRef := inputs.workflowRef
  runId := inputs.runId
  runnerOs := inputs.runnerOs
  runnerArch := inputs.runnerArch
  containerImage := inputs.containerImage
  runAttempt := inputs.runAttempt }

/-! ## The command a build leg runs -/

private def buildMetadataOptions : List OptionSpec :=
  [{ name := "target", takesValue := true },
   { name := "binary", takesValue := true },
   { name := "commit", takesValue := true },
   { name := "tier", takesValue := true },
   { name := "runner", takesValue := true },
   { name := "toolchain", takesValue := true },
   { name := "lake-manifest", takesValue := true },
   { name := "workflow-ref", takesValue := true },
   { name := "run-id", takesValue := true },
   { name := "output", takesValue := true },
   { name := "runner-os", takesValue := true },
   { name := "runner-arch", takesValue := true },
   { name := "container-image", takesValue := true },
   { name := "run-attempt", takesValue := true }]

private def buildMetadataUsage : String :=
  "usage: tlrelease build-metadata --target <name> --binary <path> --commit <sha> --tier <supported|best-effort> --runner <label> --toolchain <lean-toolchain> --lake-manifest <lake-manifest.json> --workflow-ref <ref> --run-id <id> --output <path> [--runner-os <s>] [--runner-arch <s>] [--container-image <s>] [--run-attempt <s>]"

/-- Everything the command was told, with the option names resolved.

    A structure rather than a fourteen-value tuple: the project rule is that
    four-plus component returns consumed by more than one caller get a name, and
    the reason bites here — half of these are strings that describe the machine
    and half are strings that get parsed into evidence, and a tuple would let
    them be swapped without a type error. -/
private structure BuildMetadataArgs where
  target : String
  binary : String
  commit : String
  tier : String
  runner : String
  toolchainPath : String
  lakeManifestPath : String
  workflowRef : String
  runId : String
  output : String
  runnerOs : String
  runnerArch : String
  containerImage : String
  runAttempt : String

private def buildMetadataArgs (options : Options) : Except String BuildMetadataArgs := do
  return {
    target := ← options.required "target"
    binary := ← options.required "binary"
    commit := ← options.required "commit"
    tier := ← options.required "tier"
    runner := ← options.required "runner"
    toolchainPath := ← options.required "toolchain"
    lakeManifestPath := ← options.required "lake-manifest"
    workflowRef := ← options.required "workflow-ref"
    runId := ← options.required "run-id"
    output := ← options.required "output"
    -- The four the release page shows a human and no verdict reads. Absent is
    -- the empty string here and only here; `describing` is named so that using
    -- it where a decision is made reads wrong.
    runnerOs := options.describing "runner-os"
    runnerArch := options.describing "runner-arch"
    containerImage := options.describing "container-image"
    runAttempt := options.describing "run-attempt" }

/-- The tier is passed in rather than read from `release/targets.json`, and
    that is the point of it.

    Reading it here would make the manifest generator's later comparison a
    comparison of `targets.json` with itself. The value comes from the build
    matrix, which states the tier a second time and uses it for real —
    `continue-on-error` is derived from it, so a leg the matrix calls
    best-effort genuinely does not block the release. Recording the matrix's
    belief is what lets the sign job catch a matrix that has drifted from the
    target list, which is a live possibility because the two are edited in
    different files. -/
private def buildMetadataDecision (args : BuildMetadataArgs) : Decision String := do
  let commit ← ofExcept (Commit.parse "--commit" args.commit)
  let tier ← ofExcept (Tier.parse "--tier" args.tier)
  let toolchain ← readParsed args.toolchainPath parseToolchain
  let digester ← ofIO Digester.resolve
  -- One tool resolution, and each file hashed once. The Python hashed the
  -- binary twice per leg.
  let digest ← ofIO (digester.digest args.binary)
  let lakeManifestSha256 ← ofIO (digester.digest args.lakeManifestPath)
  let record := BuildMetadataInputs.record {
    target := args.target, digest, commit, tier, runner := args.runner, toolchain,
    lakeManifestSha256, workflowRef := args.workflowRef, runId := args.runId,
    runnerOs := args.runnerOs, runnerArch := args.runnerArch,
    containerImage := args.containerImage, runAttempt := args.runAttempt }
  let document ← ofExcept (renderBuildMetadata record)
  ofIO (writeFileAtomically args.output document)
  return s!"wrote {args.output} — {args.target} ({tier.wire}) is {digest.hex}"

private def buildMetadataCommand : Command := {
  name := "build-metadata"
  arguments := "--target <name> --binary <path> --commit <sha> --tier <tier> …"
  summary := "Record what this build leg built, for the sign job to hold the artifact to."
  run := runWithOptions "tlrelease build-metadata" buildMetadataOptions buildMetadataUsage
    buildMetadataArgs buildMetadataDecision }

def metadataCommands : List Command := [buildMetadataCommand]

end Release
