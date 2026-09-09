/-
The build provenance compiled into the binary and reported by `tl version`
(ADR-0006, "Tool versioning").

The stamp is read as a claim: `clean` means *this binary corresponds exactly to
that commit*. Everything here therefore fails closed — a step that cannot
establish what it is asserting refuses rather than assuming the favourable
answer. The shell this replaces had learned that discipline the hard way and
carried the scars in its comments: a digest taken through a pipeline reported
the *last* stage's status, so a digest tool that could not read the file left
the caller holding an empty digest and a zero exit; an `exit 2` inside a command
substitution ended only the subshell; a bare `git status --porcelain` was
silenced by a repository's own `status.showUntrackedFiles=no`, hiding exactly
the files that decide whether the tree is clean.

Two things this deliberately does not claim. The stamp is a pure function of
`lean-toolchain`, `lake-manifest.json` and the git state, so an independent
rebuilder gets the same *stamp* from the same commit; whether the compiled
binary comes out bit-identical depends on the Lean and system toolchains, which
nothing here touches and ADR-0006 carries as an open item. And a stamp is
evidence about a checkout, not about a build environment.

The output is a file under `Tl/`, which is the one direction release
administration writes into the product. It reads nothing from it: `release/`
imports no `Tl` module, so `lake build tlrelease` does not depend on the file
this command writes — which is what makes it possible for the gates job to
build this tool before the stamp step runs.
-/
import release.Manifest

namespace Release

namespace Stamp

/-- Where the stamp lands, relative to the checkout. Named once, because the
    dirtiness probe has to exclude exactly the path the writer writes: without
    the exclusion a second stamp in one checkout calls the tree dirty on account
    of the first. -/
def outputComponents : List String := ["Tl", "Build", "Stamp.lean"]

def outputRelative : String := String.intercalate "/" outputComponents

/-! ## What may be embedded

Every value below lands inside a Lean string literal. They are machine-produced
— a git object id, two hex digests, a toolchain line — so anything outside the
expected shape means the input is not what this command thinks it is. -/

/-- The characters a stamped value may carry.

    Deliberately a whitelist. A value with a quote or a backslash would close
    the string literal it is spliced into and make the rest of the file code;
    the more likely failure is duller — a value that is not the thing it was
    read as at all — and a whitelist catches both without having to enumerate
    what is dangerous. -/
def embeddableChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')
    || c == '.' || c == '/' || c == ':' || c == '_' || c == '-'

/-- Whether a value may be spliced into the generated file. Empty is refused:
    an empty toolchain or digest is what an unreadable file produces, and it
    would be embedded as a value that reads like a deliberate one. -/
def embeddable (value : String) : Bool :=
  match value.toList with
  | [] => false
  | chars => chars.all embeddableChar

/-- **A value is embedded exactly when it is non-empty and every character of
    it is one the whitelist admits.**

    The direction that decides the write is left to right: `true` splices the
    value into Lean source that every build of the product then compiles, so an
    acceptance that drifted into admitting a quote would be admitting the rest
    of the file as code. Right to left is what keeps the guard from refusing
    ordinary toolchain lines and object ids. -/
theorem embeddable_iff (value : String) :
    embeddable value = true ↔
      value.toList ≠ [] ∧ ∀ c ∈ value.toList, embeddableChar c = true := by
  rw [embeddable]
  cases chars : value.toList with
  | nil =>
      constructor
      · intro impossible; exact Bool.noConfusion impossible
      · intro ⟨nonEmpty, _⟩; exact absurd rfl nonEmpty
  | cons head tail =>
      rw [List.all_eq_true]
      constructor
      · intro every; exact ⟨List.cons_ne_nil head tail, every⟩
      · intro ⟨_, every⟩; exact every

/-! ## What the stamp says -/

/-- Everything the generated file is a function of. -/
structure Provenance where
  /-- The full source commit, or `""` for a development stamp. -/
  commit : String
  /-- Whether the working tree carried uncommitted changes when the commit was
      taken. Meaningless — and always `false` — for a development stamp. -/
  dirty : Bool
  /-- The `lean-toolchain` pin in effect. -/
  toolchain : String
  /-- The SHA-256 of `lake-manifest.json`: the identity of the resolved
      dependency set. ADR-0009 pins are immutable commits, so one digest fixes
      every dependency revision at once. -/
  manifestDigest : String
  deriving Repr

/-- Why this provenance may not be written, or nothing. -/
def unstampable (provenance : Provenance) : List String :=
  (if embeddable provenance.toolchain then []
    else [s!"the toolchain value '{provenance.toolchain}' is not one this command will embed"])
  ++ (if embeddable provenance.manifestDigest then []
    else [s!"the lake-manifest digest '{provenance.manifestDigest}' is not one this command will embed"])
  ++ (if provenance.commit.isEmpty || embeddable provenance.commit then []
    else [s!"the commit '{provenance.commit}' is not one this command will embed"])

/-- The generated file, as the bytes to write.

    Deterministic: the same provenance renders the same text on every run,
    which is what lets CI regenerate it and compare rather than trust. -/
def render (provenance : Provenance) : String :=
  let quote := "\""
  String.intercalate "\n"
    ["/-",
     "`Tl.Build.Stamp` — the build provenance baked into this binary.",
     "",
     "GENERATED FILE — do not edit by hand. Regenerate with",
     "",
     "    tlrelease stamp --root .              # development stamp (this copy)",
     "    tlrelease stamp --root . --commit     # stamp the current git HEAD",
     "",
     "The checked-in copy is deliberately the *development* stamp: `commit` is empty,",
     "so a plain `lake build` produces a binary that reports itself as an",
     "unidentified local build rather than claiming a source commit it may not match.",
     "`lake exe tltest` regenerates this file from a copy of the repository's inputs",
     "and compares the committed bytes with the result, so a stamped copy cannot reach",
     "main. The release workflow stamps a clean checkout of the tagged commit before",
     "building, which is what puts a real commit here.",
     "",
     "`toolchain` and `manifestDigest` are the pins in effect for *this* checkout and",
     "are the same in the development and stamped copies; `Tests/ReleaseTests.lean`",
     "fails when either drifts from `lean-toolchain` / `lake-manifest.json` on disk.",
     "-/",
     "",
     "namespace Tl.Build",
     "",
     "/-- The full source commit the binary was built from, or `\"\"` when no commit",
     "    was stamped (a development build). -/",
     s!"def stampCommit : String := {quote}{provenance.commit}{quote}",
     "",
     "/-- Whether the working tree carried uncommitted changes when `stampCommit`",
     "    was taken. Meaningless — and always `false` — when `stampCommit` is `\"\"`. -/",
     s!"def stampDirty : Bool := {if provenance.dirty then "true" else "false"}",
     "",
     "/-- The `lean-toolchain` pin the binary was compiled with. -/",
     s!"def stampToolchain : String := {quote}{provenance.toolchain}{quote}",
     "",
     "/-- The SHA-256 of `lake-manifest.json`, lowercase hex: the identity of the",
     "    resolved dependency set (ADR-0009 pins are immutable commits, so this",
     "    digest fixes every dependency revision at once). -/",
     "def stampManifestDigest : String :=",
     s!"  {quote}{provenance.manifestDigest}{quote}",
     "",
     "end Tl.Build",
     ""]

/-! ## Reading the checkout -/

private def gitIn (root : String) (args : List String) : Decision String := do
  match ← ofIO (do return .ok (← Release.succeeded "git" ((["-C", root] ++ args).toArray))) with
  | .ok output => return output.stdout.trimAscii.toString
  | .error message => decline message

/-- The commit at `HEAD`, and whether the tree beneath `root` is clean.

    `--show-toplevel` is compared against the root the operator named, because
    `git rev-parse` walks up to the nearest ancestor repository: a source tree
    merely sitting *inside* an unrelated checkout would otherwise be stamped
    with that checkout's commit — a `clean` claim naming a commit that does not
    contain this source at all. -/
private def gitProvenance (root : String) : Decision (String × Bool) := do
  let commit ← gitIn root ["rev-parse", "HEAD"]
  let toplevel ← gitIn root ["rev-parse", "--show-toplevel"]
  let resolved ← ofIO (do
    try
      return .ok (← IO.FS.realPath root).toString
    catch error => return .error s!"could not resolve {root}: {error}")
  let resolvedToplevel ← ofIO (do
    try
      return .ok (← IO.FS.realPath toplevel).toString
    catch error => return .error s!"could not resolve {toplevel}: {error}")
  if resolvedToplevel != resolved then
    decline s!"--commit found a git repository at '{toplevel}', not at {root}. The source there is not what that repository tracks, so a stamp naming its commit would claim a provenance this checkout does not have. Clone or unpack the source as its own checkout, or stamp without --commit."
  -- Untracked files count: they change what gets compiled. The config is
  -- pinned because a repository or user setting of
  -- `status.showUntrackedFiles=no` hides exactly the files this decision is
  -- about, and the command's own output is excluded because it is overwritten
  -- a moment later and so cannot affect the build. List every untracked file:
  -- Git 2.17's normal mode can report the output's parent directory even when
  -- the excluded output is the only file inside it.
  let status ← gitIn root
    ["-c", "status.showUntrackedFiles=all", "status", "--porcelain",
     "--", ".", s!":(exclude){outputRelative}"]
  return (commit, !status.isEmpty)

private def stampOptions : List OptionSpec :=
  [{ name := "root", takesValue := true },
   { name := "commit", takesValue := false }]

private structure StampArgs where
  root : String
  rootDirectory : Write.OutputDirectory
  withCommit : Bool

private def stampArgs (options : Options) : Except String StampArgs := do
  let root ← options.required "root"
  return { root, rootDirectory := ← Write.OutputDirectory.parse "--root" root
           withCommit := options.given "commit" }

private def stampDecision (args : StampArgs) : Decision String := do
  let toolchainPath := args.root ++ "/lean-toolchain"
  let manifestPath := args.root ++ "/lake-manifest.json"
  let toolchainText ← ofIO (readTextFile toolchainPath)
  let toolchain := toolchainText.trimAscii.toString
  let digester ← ofIO Digester.resolve
  let manifestDigest ← ofIO (digester.digest manifestPath)
  let (commit, dirty) ← if args.withCommit then gitProvenance args.root else pure ("", false)
  let provenance : Provenance :=
    { commit, dirty, toolchain, manifestDigest := manifestDigest.hex }
  match unstampable provenance with
  | [] => pure ()
  | problems =>
      decline ("a value read from this checkout is not one this command will embed. Every one of them is spliced into a Lean string literal that the whole product then compiles, so a value outside the expected shape means the file it came from is not what it was read as.\n"
        ++ String.join (problems.map fun problem => s!"  {problem}\n"))
  let path ← ofExcept (Write.OutputPath.parse "the build stamp" outputRelative)
  let disclosure ← ofIO (writeEvidence args.rootDirectory path (render provenance))
  return disclosing
    s!"wrote {args.root}/{outputRelative} (commit={if commit.isEmpty then "<development>" else commit} dirty={dirty} toolchain={toolchain})"
    disclosure

private def stampCommand : Command :=
  optionCommand "stamp" "--root <dir> [--commit]"
    "Regenerate the build provenance the binary reports, from the checkout it is built out of."
    ["--root", ".", "--commit"]
    stampOptions stampArgs stampDecision

def stampCommands : List Command := [stampCommand]

end Stamp

export Stamp (stampCommands)

end Release
