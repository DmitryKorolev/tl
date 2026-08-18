/-
One version, said in eight places, and a gate that they agree.

The release version appears in the binary's own self-report, the Lake package,
a pinned test literal, five npm manifests, and — at release time — the tag. Any
two of them disagreeing produces a release that is internally inconsistent in a
way no single file reveals: `tl version` says one thing, `npm install` resolves
another, and the artifacts are named for a third.

There is no regular-expression engine here and none is needed. The two Lean
definitions are extracted by scanning lines for a fixed prefix and a fixed
suffix, and the manifests are read with `release/Json.lean`, which already
parses and renders JSON with typed access. What the Python this replaces did
was `json.load` plus two line-anchored literal extractions; naming that a
parsing problem overstated it.

The one thing worth carrying over verbatim is *exactly one match*. The release
workflow used `sed -n 's/…/p'`, which prints every match — so two definitions
produced a two-line version string that flowed into `$GITHUB_OUTPUT` and then
into later `run:` blocks. A second definition is refused here rather than
silently resolved by file order.
-/
import release.Command
import release.Model

namespace Release

open Lean (Json)

/-! ## Extracting a literal from source -/

/-- Everything between `before` and the next `after`, once per line that has
    both.

    Scanning rather than matching: the values wanted are string literals with
    fixed surroundings, and a pattern language would be a dependency and a
    second syntax to get right. The line is the unit because both definitions
    are one-liners and a definition spread over two lines is a shape this gate
    should refuse rather than accommodate. -/
def literalsBetween (text : String) (before : String) (after : String) : List String :=
  (text.splitOn "\n").filterMap fun line =>
    match line.splitOn before with
    | _ :: rest :: _ =>
        match rest.splitOn after with
        | value :: _ :: _ => some value
        | _ => none
    | _ => none

/-- Exactly one, or a refusal naming which way it went wrong.

    Absence and duplication are separate messages because they have separate
    fixes: one means the definition moved or changed shape and this gate has to
    move with it, the other means which version ships depends on file order. -/
def oneLiteral (document : String) (what : String) (text : String)
    (before : String) (after : String) : Except String String :=
  match literalsBetween text before after with
  | [value] => .ok value
  | [] =>
      .error s!"{document} has no {what}. Either the definition moved or changed shape; update the pattern this gate scans for, because the release workflow reads the same value and would otherwise ship an empty version."
  | found =>
      .error s!"{document} has {found.length} definitions of {what} ({String.intercalate ", " found}). Exactly one is expected: with two, which version ships depends on file order."

/-! ## Where the version is written -/

/-- One place the version appears, and what it says there. -/
structure VersionCopy where
  label : String
  value : String
  deriving Repr

/-- Every file this gate reads, as text, with the path it came from.

    A structure rather than positional arguments: the caller is I/O and this is
    the whole of what the comparison needs, so the two can be kept apart and
    every branch below is reachable from a test without a filesystem. -/
structure VersionSources where
  commandsPath : String
  commandsText : String
  lakefilePath : String
  lakefileText : String
  releaseTestsPath : String
  releaseTestsText : String
  identityPath : String
  identityText : String
  /-- The launcher manifest first: its `name` is the published package, and is
      held to `release/identity.json`. -/
  manifests : List (String × String)
  deriving Inhabited

/-- The canonical version: what the binary reports about itself.

    Canonical because it is the one a user can observe. Every other copy is
    held to it rather than to a value in a configuration file, so "which one is
    right" is not a question the gate has to answer. -/
def productVersionOf (sources : VersionSources) : Except String String :=
  oneLiteral sources.commandsPath "`def productVersion`" sources.commandsText
    "def productVersion : String := \"" "\""

/-- Every other copy, each labelled with where it lives. -/
def versionCopies (sources : VersionSources) : Except String (List VersionCopy) := do
  let lakefile ← oneLiteral sources.lakefilePath "the package `version :=` line"
    sources.lakefileText "  version := v!\"" "\""
  let pinned ← oneLiteral sources.releaseTestsPath
    "the pinned `tl version` product-version literal" sources.releaseTestsText
    "checkEq \"tl version: product version\" (jStr out.data \"version\") (some \"" "\")"
  let fromManifests ← sources.manifests.mapM fun (path, text) => do
    let cursor : Cursor := { document := path }
    let root ← parseDocument cursor text
    let value ← nonEmptyStringField cursor root "version"
    return { label := path, value }
  return { label := s!"{sources.lakefilePath} package version", value := lakefile }
    :: { label := s!"{sources.releaseTestsPath} pinned `tl version` payload", value := pinned }
    :: fromManifests

/-- The published package name, and what the launcher manifest calls itself.

    A separate comparison from the version because it is a different identity:
    `release/identity.json` is what every consumer is pinned to, and a launcher
    published under another name is a package nobody installs. The gate this
    replaces checked it and the first port dropped it. -/
def packageNameChecks (sources : VersionSources) : Except String (List Check) := do
  let cursor : Cursor := { document := sources.identityPath }
  let identity ← parseDocument cursor sources.identityText
  let pinned ← nonEmptyStringField cursor identity "npmPackage"
  match sources.manifests with
  | [] =>
      .error s!"no npm manifests were read, so the published package name was compared against nothing. That is this gate failing to look rather than the name being right."
  | (launcherPath, launcherText) :: _ =>
      let launcherCursor : Cursor := { document := launcherPath }
      let launcher ← parseDocument launcherCursor launcherText
      let name ← nonEmptyStringField launcherCursor launcher "name"
      return [{ held := name == pinned,
                failure := s!"{launcherPath} calls itself '{name}', and {sources.identityPath} pins the published package as '{pinned}'. Every consumer — VERIFYING.md, the installer, the prose documents — is pinned to that name, so a launcher published under another one is a package nobody installs." }]

/-! ## The verdict -/

/-- What every copy is held to, as checks so the verdict and the report cannot
    drift apart. -/
def versionChecks (product : String) (copies : List VersionCopy)
    (tag : Option String) : List Check :=
  let semver : Check :=
    { held := (Version.parse "productVersion" product).toOption.isSome,
      failure := s!"productVersion '{product}' is not a release version. The pinned signing identity accepts only a SemVer tag, so nothing built from this version could be signed with an identity any verifier accepts." }
  let agreement := copies.map fun copy =>
    { held := copy.value == product,
      failure := s!"{copy.label} is '{copy.value}', but the binary reports '{product}'. Bring every copy to '{product}' in one change — the binary's self-report is canonical because it is the one a user can observe." : Check }
  let tagged := match tag with
    | none => []
    | some tag =>
        [{ held := tag == "v" ++ product,
           failure := s!"the tag is '{tag}', and this checkout builds '{product}'. A release named for one version and reporting another is one nobody can reason about; move the tag, or bring the version to it." : Check }]
  semver :: agreement ++ tagged

/-- Whether every copy agrees. -/
def versionConsistent (product : String) (copies : List VersionCopy)
    (tag : Option String) : Bool :=
  Check.allHeld (versionChecks product copies tag)

/-- Why they do not, or nothing at all. -/
def versionProblems (product : String) (copies : List VersionCopy)
    (tag : Option String) : List String :=
  Check.failures (versionChecks product copies tag)

/-- **The version is consistent exactly when nothing is reported.**

    The bridge `Check.allHeld_iff_noFailures` gives over an arbitrary check
    list, restated here about the pair of functions the command calls so the
    guarantee is on the functions rather than one composition away. -/
theorem versionProblems_isEmpty_iff (product : String) (copies : List VersionCopy)
    (tag : Option String) :
    versionProblems product copies tag = [] ↔ versionConsistent product copies tag = true :=
  (Check.allHeld_iff_noFailures (versionChecks product copies tag)).symm

/-! ## Reading a marked block out of a shipped adapter

`install.sh` is piped straight into a shell and has no checkout to source from;
the npm launcher ships inside a published package and has none either. Both
therefore carry the `uname` mapping inline, bounded by explicit markers.

What that mapping is held to lives in `release/Platform.lean`, which is the
authority and is cross-checked against `release/targets.json`. The two readers
below are what let it be compared against the shell that will actually run:
`embeddedBlock` bounds the text, and `caseClassification` reduces it to which
pattern selects which target — because the wording around the arms differs
legitimately between the two adapters (their messages name different tools)
while a disagreement about which system is which ships the wrong binary.

This is line scanning, not parsing. The blocks are delimited by explicit
markers this repository's own shell obeys and shellcheck enforces. -/

/-- A line with its surroundings stripped and the library namespace removed.

    `rc__` before `rc_`, or the longer prefix would be left with a stray
    underscore. Replacement is textual rather than word-boundary-aware, which is
    narrower than what it replaces: a token containing `rc_` other than as a
    prefix would also be rewritten. No identifier in the compared functions is
    one, and the alternative is a pattern language this gate does not need. -/
def normalizeShellLine (line : String) : String :=
  let trimmed := line.trimAscii.toString
  ((trimmed.replace "rc__" "").replace "rc_" "")

/-- Body lines worth comparing: no comments, no blanks, and neither the
    function header nor its closing brace — the embedded copy is a bare
    function and so is the library's, so what is compared is what they do. -/
def comparableLines (body : String) : List String :=
  (body.splitOn "\n").filterMap fun line =>
    let stripped := line.trimAscii.toString
    if stripped.isEmpty || stripped.startsWith "#" then none
    else
      let normalized := normalizeShellLine line
      if normalized == "}" || (normalized.splitOn "() {").length == 2 then none
      else some normalized

/-- The lines between a block's BEGIN and END markers. -/
def embeddedBlock (document : String) (text : String) (name : String) :
    Except String String :=
  let begin := s!"# EMBEDDED-COPY-BEGIN {name}"
  let finish := s!"# EMBEDDED-COPY-END {name}"
  match text.splitOn begin with
  | _ :: after :: _ =>
      match after.splitOn finish with
      | body :: _ :: _ => .ok body
      | _ =>
          .error s!"{document} opens an embedded-copy block for '{name}' and never closes it. The END marker is what bounds the comparison, so without it this guard would compare the rest of the file."
  | _ =>
      .error s!"{document} has no '# EMBEDDED-COPY-BEGIN {name}' block. Either the copy was deleted — then delete its row from this gate too, deliberately — or the markers were lost, which retires the guard silently."

/-- Characters a shell case *pattern* is made of: globs and alternation and
    nothing else.

    Narrow deliberately. Message text is full of parentheses — a refusal naming
    `'$(uname -s)'` closes one on almost every line — so a looser "everything
    before the first `)`" rule reads those as case arms and reports the two
    files as disagreeing about wording rather than about classification. -/
private def patternChar (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
    || c == '_' || c == '*' || c == '?' || c == '.' || c == '|' || c == ' '
    || c == '\t' || c == '-'

/-- A case arm's pattern, if this line opens one. -/
private def armPattern (line : String) : Option (String × String) :=
  match line.splitOn ")" with
  | head :: rest :: more =>
      if !head.isEmpty && head.toList.all patternChar then
        some (head.trimAscii.toString,
          (String.intercalate ")" (rest :: more)).trimAscii.toString)
      else none
  | _ => none

/-- Every `NAME=value` assignment on a line, in order.

    A line can carry more than one — `os=darwin; os=linux` is two statements,
    and reading only the first is how a copy that ends up selecting the wrong
    target reads as one that selects the right one. Split on `;` first, so each
    statement is considered on its own. -/
private def assignedValues (line : String) : List String :=
  (line.splitOn ";").filterMap fun statement =>
    match statement.splitOn "=" with
    | name :: rest :: _ =>
        let identifier := name.trimAscii.toString
        if identifier.isEmpty || !identifier.toList.all (fun c =>
            ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_')
        then none
        else
          let value := ((rest.trimAscii.toString).splitOn " ").headD ""
          -- The value, not the whole assignment. The variable names differ
          -- legitimately and by design: the library namespaces its own with
          -- `rc_`, install.sh uses `install_os`, and the npm launcher uses
          -- `os`. What has to agree is which target each pattern selects.
          if value.isEmpty then none else some value
    | _ => none

/-- Which patterns map to which targets, for every arm of the mapping.

    *Every* assignment in an arm, in order, not the first one. The shell runs
    them all and the last one wins, so keeping only the first reads

        Darwin)
          os=darwin
          os=linux
          ;;

    as an arm that selects darwin, while the shell selects linux — a copy that
    installs the Linux binary on macOS, with a green gate. Comparing the whole
    sequence needs no model of which assignment survives: two files that run
    different statements are different, whichever one wins.

    Arms that only refuse assign nothing and are kept with an empty list, so a
    copy that dropped an arm entirely is drift even when the arms that remain
    agree. -/
def caseClassification (body : String) : List (String × List String) :=
  let rec walk (lines : List String) (current : Option String)
      (acc : List (String × List String)) : List (String × List String) :=
    match lines with
    | [] => acc.reverse
    | line :: rest =>
        if line.startsWith "case " || line.startsWith "esac" || line.startsWith ";;" then
          walk rest current acc
        else
          match armPattern line with
          | some (pattern, tail) =>
              walk rest (some pattern) ((pattern, (assignedValues tail)) :: acc)
          | none =>
              match current with
              | none => walk rest current acc
              | some pattern =>
                  match assignedValues line with
                  | [] => walk rest current acc
                  | values =>
                      -- Appended to the arm being read, which is the head of the
                      -- accumulator: `acc` is built by prepending.
                      let updated := match acc with
                        | (name, existing) :: older =>
                            if name == pattern then (name, existing ++ values) :: older else acc
                        | [] => acc
                      walk rest current updated
  walk (comparableLines body) none []

/-! ## The commands -/

private def versionOptions : List OptionSpec :=
  [{ name := "targets", takesValue := true },
   { name := "tag", takesValue := true }]

private structure VersionArgs where
  targetsPath : String
  tag : Option String

private def versionArgs (options : Options) : Except String VersionArgs := do
  return { targetsPath := ← options.required "targets"
           tag := options.value? "tag" }

/-- Read every file the comparison needs.

    The npm manifest list is derived from `release/targets.json` rather than
    written out, so a target added there is a manifest this gate expects — the
    alternative is a sixth manifest nobody compares. -/
private def readSources (targetsPath : String) : Decision VersionSources := do
  let targets ← readParsed targetsPath Targets.parse
  let commandsText ← ofIO (readTextFile "Tl/Cli/Commands.lean")
  let identityText ← ofIO (readTextFile "release/identity.json")
  let lakefileText ← ofIO (readTextFile "lakefile.lean")
  let releaseTestsText ← ofIO (readTextFile "Tests/ReleaseTests.lean")
  let manifestPaths := "npm/tl/package.json"
    :: targets.targets.map fun target => s!"npm/platform/{target.name}/package.json"
  let manifests ← manifestPaths.mapM fun path => do
    let text ← ofIO (readTextFile path)
    return (path, text)
  return { commandsPath := "Tl/Cli/Commands.lean", commandsText
           lakefilePath := "lakefile.lean", lakefileText
           releaseTestsPath := "Tests/ReleaseTests.lean", releaseTestsText
           identityPath := "release/identity.json", identityText
           manifests }

private def versionDecision (args : VersionArgs) : Decision String := do
  let sources ← readSources args.targetsPath
  let product ← ofExcept (productVersionOf sources)
  let copies ← ofExcept (versionCopies sources)
  let names ← ofExcept (packageNameChecks sources)
  match versionProblems product copies args.tag ++ Check.failures names with
  | [] =>
      return s!"one version everywhere: {product}, across {copies.length + 1} places"
  | problems =>
      decline (s!"the release version is not one version.\n"
        ++ String.join (problems.map fun problem => s!"  {problem}\n")
        ++ "A release named for one version, reporting another and resolving to a third is one nobody can reason about.")

private def versionCommand : Command :=
  optionCommand "version-consistency" "--targets <targets.json> [--tag <vX.Y.Z>]"
    "Refuse unless every copy of the release version agrees with the binary's own."
    ["--targets", "release/targets.json"]
    versionOptions versionArgs versionDecision

def consistencyCommands : List Command := [versionCommand]

end Release
