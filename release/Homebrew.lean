/-
The Homebrew channel: one rendered formula, and one idempotent tap update.

`Formula/tl.rb` is Ruby because a Homebrew formula is a Ruby DSL, and it stays
Ruby (ADR-0028). What it stops being is a *template*: the shell generator that
preceded this read `SHA256SUMS`, re-derived the platform set from it, carried its
own copy of the tier policy, and then edited the tracked file with a sequence of
single-substitution regular expressions — each of which had a failure mode of
"could not find the placeholder", and each of whose meaning depended on whether
an earlier one had already rewritten the line it was looking at.

Here the formula is *rendered* from a typed description of the release, and the
description is the signed manifest. That removes three things at once. The
platform set is the manifest's published-target list rather than a fourth
derivation of it; the version is a `Version` rather than a string that reaches
Ruby source, which is what the generator's SemVer guard existed to make safe; and
the tracked `Formula/tl.rb` becomes a rendered artifact compared byte-for-byte
against this renderer at the placeholder release, so an edit to it is a failing
test rather than a formula that pins a stale release.

What is still decided rather than rendered gets a theorem. A formula missing a
url for a Supported target is the failure that matters, and it is not visible in
the output: Homebrew raises `formula requires at least a URL` when the formula is
*loaded* — for every `brew` command touching the tap, not only `brew install
tl` — so one silently dropped Supported target takes the tap down for that whole
platform. `formulaCovers_iff` is what keeps the coverage rule from being one row
that can be deleted.
-/
import release.Manifest

namespace Release

namespace Homebrew

/-! ## Which Homebrew block a target belongs in

Homebrew selects a spec with nested `on_macos`/`on_linux` and `on_arm`/`on_intel`
blocks, so a target's `os` and `cpu` decide where its url is written. The map is
closed in both directions: a target this renderer does not know how to place is a
refusal, because the alternative is a formula that silently serves nothing on
that platform while looking complete. -/

/-- The outer block for an operating system. -/
def osBlock : String → Option String
  | "darwin" => some "on_macos"
  | "linux" => some "on_linux"
  | _ => none

/-- The inner block for a processor. -/
def cpuBlock : String → Option String
  | "arm64" => some "on_arm"
  | "x64" => some "on_intel"
  | _ => none

/-- The order the blocks are written in, which is the order the tracked formula
    has always had. Fixed rather than derived from the target list so that two
    releases publishing the same targets in a different file order render the
    same formula — the tap compares formula text, and a reordered but equivalent
    formula would read as a change to push. -/
def osOrder : List String := ["darwin", "linux"]

def cpuOrder : List String := ["arm64", "x64"]

/-! ## What the formula pins -/

/-- One platform block: the target it serves and the digest it pins. -/
structure Pin where
  target : Target
  digest : Sha256
  deriving Repr

/-- Everything the formula is rendered from.

    A value rather than a set of arguments so that rendering does no I/O and no
    lookups: whoever builds this has already decided which targets are pinned,
    and the renderer cannot quietly drop one. -/
structure Spec where
  version : Version
  repository : String
  tap : String
  issuer : String
  certificateIdentity : String
  /-- The digest of the release's own `SHA256SUMS`, which the fallback url
      points at. It is the one asset a manifest structurally cannot describe —
      the sums file lists the manifest — so it is hashed from the verified
      directory rather than read out of the document. -/
  sumsDigest : Sha256
  pins : List Pin

/-- The targets this formula pins a binary for, sorted, as `install` reads them.

    Sorted rather than left in manifest order: this list is the formula's own
    statement of what it serves, and a reader comparing two releases should see
    a list that changed because the release changed. -/
def Spec.pinnedTargets (spec : Spec) : List String :=
  (spec.pins.map (·.target.name)).mergeSort (· ≤ ·)

/-! ## The coverage decision

The one thing here whose wrong answer is silent. A Best-effort target that did
not build has its block dropped, which is the documented behaviour: the fallback
url keeps the spec resolvable and `install` refuses on that platform with a
message naming the tier. A *Supported* target that did not build must never
reach that path — it is release-blocking under ADR-0006, and a formula that
dropped it would install nothing on a platform this release claims to serve. -/

/-- One row: this target is pinned, unless it is one whose absence the release
    tolerates. -/
def coverageCheck (pinned : List String) (target : Target) : Check :=
  { held := !target.tier.releaseBlocking || pinned.contains target.name,
    failure := s!"the formula would pin no binary for '{target.name}', which release/targets.json calls Supported — release-blocking under ADR-0006. A formula cannot pin a digest for an asset the release did not publish, and dropping the block would leave `brew install tl` with nothing to install on that platform. Build the missing target and re-run; do not publish a partial formula." }

/-- One row per target in the distributed set.

    The set comes from the manifest's own target rows rather than from a
    checkout's `release/targets.json`: the question is whether *this release*
    published every target it says is release-blocking, and a checkout read at
    publication time is a different release's answer. -/
def coverageChecks (targets : List Target) (pinned : List String) : List Check :=
  targets.map (coverageCheck pinned)

/-- Whether a formula pinning these targets may be rendered. -/
def formulaCovers (targets : List Target) (pinned : List String) : Bool :=
  Check.allHeld (coverageChecks targets pinned)

/-- `!b || c` is how "only if `b`" is written as a `Bool`. Stated once so the
    row above can be read as the implication it means. -/
private theorem notOr_eq_true_iff (b c : Bool) :
    (!b || c) = true ↔ (b = true → c = true) :=
  match b, c with
  | false, _ => ⟨fun _ absurdity => Bool.noConfusion absurdity, fun _ => rfl⟩
  | true, false => ⟨fun held => Bool.noConfusion held, fun implication => implication rfl⟩
  | true, true => ⟨fun _ _ => rfl, fun _ => rfl⟩

private theorem coverageCheck_held_iff (pinned : List String) (target : Target) :
    (coverageCheck pinned target).held = true ↔
      (target.tier.releaseBlocking = true → pinned.contains target.name = true) :=
  notOr_eq_true_iff _ _

/-- **A formula may be rendered exactly when every Supported target is pinned.**

    Left to right is what keeps the rule from becoming a row someone deletes:
    dropping it makes the verdict strictly more accepting, so a release missing a
    Supported binary would satisfy the left side and fail the right, and this
    implication would stop compiling.

    Right to left is what a verdict that refuses everything cannot satisfy, and
    the case it protects is the real one — a Best-effort target that did not
    build must still render, or a single failed Intel-macOS leg would block every
    release. -/
theorem formulaCovers_iff (targets : List Target) (pinned : List String) :
    formulaCovers targets pinned = true ↔
      ∀ target ∈ targets,
        target.tier.releaseBlocking = true → pinned.contains target.name = true := by
  rw [formulaCovers, Check.allHeld, coverageChecks, List.all_eq_true]
  constructor
  · intro held target member
    exact (coverageCheck_held_iff pinned target).mp
      (held _ (List.mem_map.mpr ⟨target, member, rfl⟩))
  · intro every check member
    have ⟨target, isMember, isCheck⟩ := List.mem_map.mp member
    rw [← isCheck]
    exact (coverageCheck_held_iff pinned target).mpr (every target isMember)

/-- Why it may not be, or nothing at all. -/
def coverageBlockers (targets : List Target) (pinned : List String) : List String :=
  Check.failures (coverageChecks targets pinned)

/-- **The report is empty exactly when every Supported target is pinned.**

    `formulaCovers_iff` characterises the verdict; the command branches on the
    report, so this is the form the guarantee has to take to be about the code
    that runs. -/
theorem coverageBlockers_isEmpty_iff (targets : List Target) (pinned : List String) :
    coverageBlockers targets pinned = [] ↔
      ∀ target ∈ targets,
        target.tier.releaseBlocking = true → pinned.contains target.name = true :=
  Iff.trans (Check.allHeld_iff_noFailures (coverageChecks targets pinned)).symm
    (formulaCovers_iff targets pinned)

/-! ## Rendering

Every value that reaches Ruby source is either a type whose parser already
restricts it — a `Version` renders digits, dots and an alphanumeric suffix; a
`Sha256` is 64 lowercase hex characters — or is checked here against the
characters Ruby would read as syntax. The shell generator needed a SemVer
guard because its version was a string; this needs one for the two identity
pins, which come from a JSON document and reach a string literal a `brew
install` executes. -/

/-- A value that may be written inside a double-quoted Ruby string.

    Quote, backslash and `#` are the three characters that end the literal or
    start an interpolation. Refused rather than escaped: everything passing
    through here is a repository name or an issuer url, none of which has any
    business containing one, and a value that does is a document to fix rather
    than a string to encode. -/
private def rubySafe (what value : String) : Except String String :=
  if value.any fun c => c == '"' || c == '\\' || c == '#' then
    .error s!"{what} is '{value}', which carries a quote, a backslash or a '#'. It is written into Ruby source that every `brew install` from the tap executes, where those characters end the string literal or begin an interpolation. Fix the value in release/identity.json rather than escaping it here."
  else if value.any fun c => c.toNat < 0x20 || c.toNat > 0x7e then
    .error s!"{what} carries a character outside printable ASCII. A formula is source code a user's Homebrew executes; a value that cannot be read on the page does not belong in one."
  else .ok value

/-- A value that may be written inside a single-quoted Ruby string.

    The certificate expression is written single-quoted precisely because it is
    full of backslashes, which a single-quoted Ruby literal takes verbatim. The
    two characters that are still syntax there are the quote itself and a
    trailing backslash. -/
private def rubySafeRaw (what value : String) : Except String String :=
  if value.any (· == '\'') then
    .error s!"{what} carries a single quote, which would end the Ruby string literal it is written into. The certificate expression is generated from a fixed grammar and cannot legitimately contain one."
  else if value.endsWith "\\" then
    .error s!"{what} ends with a backslash, which a single-quoted Ruby literal reads as escaping the closing quote."
  else if value.any fun c => c.toNat < 0x20 || c.toNat > 0x7e then
    .error s!"{what} carries a character outside printable ASCII. A formula is source code a user's Homebrew executes; a value that cannot be read on the page does not belong in one."
  else .ok value

/-- The url a release asset is served from, up to its name. -/
private def downloadBase (repository : String) (version : Version) : String :=
  s!"https://github.com/{repository}/releases/download/{version.tag}/"

/-- One platform's two lines, indented for its block. -/
private def pinLines (spec : Spec) (pin : Pin) : List String :=
  [s!"      url \"{downloadBase spec.repository spec.version}" ++ "#{ASSET_PREFIX}"
     ++ pin.target.name ++ "\"",
   s!"      sha256 \"{pin.digest.hex}\""]

/-- One operating system's block, or nothing when this release pinned no binary
    for it.

    Nothing, rather than an empty block: `on_macos do end` is legal Ruby and
    tells a reader that macOS was considered and found empty, which is exactly
    the wrong impression when the truth is that no macOS target was pinned. The
    fallback url is what keeps the spec resolvable there. -/
private def osLines (spec : Spec) (os : String) : Except String (List String) := do
  let mut lines : List String := []
  for cpu in cpuOrder do
    match spec.pins.find? fun pin => pin.target.os == os && pin.target.cpu == cpu with
    | none => pure ()
    | some pin =>
        let some block := cpuBlock cpu
          | .error s!"'{pin.target.name}' has cpu '{cpu}', and this renderer knows no Homebrew block for it. Adding a processor means teaching it which of `on_arm` / `on_intel` the target belongs in; rendering it into neither would produce a formula that looks complete and serves nothing there."
        lines := lines ++ [s!"    {block} do"] ++ pinLines spec pin ++ ["    end"]
  if lines.isEmpty then return []
  let some block := osBlock os
    | .error s!"this renderer knows no Homebrew block for the operating system '{os}'."
  return [s!"  {block} do"] ++ lines ++ ["  end", ""]

/-- Every target is one this renderer can place.

    Checked over the whole pin list before any block is written, so a target with
    an unknown `os` refuses rather than being dropped by the per-block lookup
    above — which would silently produce a formula serving nothing there. -/
private def placeable (spec : Spec) : Except String Unit := do
  for pin in spec.pins do
    if (osBlock pin.target.os).isNone then
      .error s!"'{pin.target.name}' has os '{pin.target.os}', and this renderer knows no Homebrew block for it. Adding an operating system means teaching it which of `on_macos` / `on_linux` the target belongs in; a target it cannot place would be dropped from the formula, which looks exactly like a target the release did not build."
    if (cpuBlock pin.target.cpu).isNone then
      .error s!"'{pin.target.name}' has cpu '{pin.target.cpu}', and this renderer knows no Homebrew block for it. Adding a processor means teaching it which of `on_arm` / `on_intel` the target belongs in."

/-- The header, down to the licence line.

    The `version` line is emitted exactly when Homebrew's own scanner would read
    the wrong value from the url. Homebrew scans a version out of the url and
    `brew audit` rejects an explicit one as redundant with it — but the scanner
    drops a SemVer prerelease suffix, so on a prerelease every `v#\{version}` url
    below would point at a tag that does not exist and the formula would claim
    the stable number. The line is therefore present exactly when audit does not
    call it redundant. -/
private def headerLines (spec : Spec) : Except String (List String) := do
  let repository ← rubySafe "the release repository" spec.repository
  let tap ← rubySafe "the Homebrew tap" spec.tap
  let issuer ← rubySafe "the certificate OIDC issuer" spec.issuer
  let identity ← rubySafeRaw "the certificate identity expression" spec.certificateIdentity
  let intro : List String :=
    ["# frozen_string_literal: true",
     "",
     "# Homebrew formula for tl, rendered by `tlrelease homebrew-render` from the",
     "# signed release manifest and pushed by the release workflow to the tap",
     s!"# {tap}.",
     "#",
     "# The copy tracked in this repository is the same rendering at the placeholder",
     "# release, so it cannot be installed by accident — a placeholder digest matches",
     "# nothing Homebrew would ever download — and an edit to it is a failing test",
     "# rather than a formula pinning a release that does not exist.",
     "#",
     "# Every url below names its release tag literally rather than interpolating",
     "# `version`. The two are the same string, and writing it out means no url",
     "# depends on what Homebrew's version scanner makes of the one above it.",
     "#",
     "# Two independent checks, both fail-closed and neither bypassable from the",
     "# command line:",
     "#",
     "#   1. Homebrew's own `sha256` on each url. A mismatch aborts the install; there",
     "#      is no --force that accepts a wrong digest.",
     "#   2. A Sigstore verification against the pinned certificate identity, run in",
     "#      `install`. `cosign` is a hard dependency rather than an optional nicety,",
     "#      because a signature check that silently does not run is the failure this",
     "#      formula exists to prevent. There is deliberately no environment variable",
     "#      to skip it: the installer's TL_INSTALL_SKIP_SIGNATURE escape exists for",
     "#      machines that cannot run cosign, and on such a machine Homebrew would",
     "#      simply install cosign first.",
     "class Tl < Formula",
     "  desc \"Formally verified, git-native task tracker for AI agents\"",
     s!"  homepage \"https://github.com/{repository}\"",
     "  # The stable spec needs a url for *every* platform, not only the ones this",
     "  # release publishes a binary for. macOS x86-64 is Best-effort (ADR-0006), so",
     "  # a release whose Intel leg failed pins no binary there — and a formula whose",
     "  # stable spec has no url for the running platform makes Homebrew raise",
     "  # `formula requires at least a URL`, with a Ruby backtrace and \"Please report",
     "  # this issue\", on *load*: for `brew info`, `brew upgrade`, and any `brew",
     "  # update` that touches the tap, not just `brew install tl`. One broken",
     "  # Best-effort leg would take the whole tap down for every Intel Mac.",
     "  #",
     "  # So the top-level url is the release's SHA256SUMS, which every release",
     "  # publishes and whose digest this formula already knows. Each platform that",
     "  # *did* build overrides it below with its own binary. On a platform that did",
     "  # not, the spec still resolves, Homebrew downloads a few hundred bytes, and",
     "  # `install` refuses with an explanation naming the tier — a message instead of",
     "  # a crash report.",
     s!"  url \"{downloadBase repository spec.version}SHA256SUMS\""]
  let versionLine : List String :=
    if spec.version.isPrerelease then
      ["  # Homebrew scans the version out of the url above and `brew audit` calls an",
       "  # explicit one redundant with it — but its scanner drops a SemVer prerelease",
       "  # suffix, so without this line every url below would name a tag that does",
       "  # not exist and this formula would claim the stable version number.",
       s!"  version \"{spec.version.render}\""]
    else []
  let rest : List String :=
    [s!"  sha256 \"{spec.sumsDigest.hex}\"",
     "  license \"Apache-2.0\"",
     "",
     "  depends_on \"cosign\"",
     "  depends_on \"git\"",
     "",
     "  # The pinned signing identity, rendered from release/identity.json — which is",
     "  # what makes this the same pin the standalone verifier and the installer use",
     "  # rather than a fourth copy of it that can drift.",
     s!"  OIDC_ISSUER = \"{issuer}\"",
     "  # Deliberately one long line, not a continuation: a reader comparing the",
     "  # copies of this pin by eye should see the same bytes in each, and a split",
     "  # literal would be equal at runtime and different on the page. `brew style`",
     "  # permits the length; it does not permit an inline rubocop directive, so",
     "  # there is none.",
     s!"  CERTIFICATE_IDENTITY = '{identity}'",
     "",
     "  # The asset names are composed from this prefix rather than written out.",
     "  # The repository's task-ID lint reads a `tl-` affix followed by Crockford",
     "  # digits as a tracker reference, and the macOS asset names match it;",
     "  # release.yml builds its asset names the same way for the same reason.",
     "  ASSET_PREFIX = \"tl-\"",
     "",
     "  # The targets this particular rendering pins a binary for. A Best-effort",
     "  # target the release did not build is absent from both this list and the",
     "  # blocks below, and `install` consults it before doing anything: without it",
     "  # the download would succeed (the fallback url above) and `bin.install` would",
     "  # then fail on a file that was never fetched.",
     s!"  PINNED_TARGETS = %w[{String.intercalate " " spec.pinnedTargets}].freeze",
     ""]
  return intro ++ versionLine ++ rest

/-- Everything from `def target_name` to the end, which no release varies. -/
private def bodyLines (repository : String) : List String :=
  ["  def target_name",
   "    os = OS.mac? ? \"darwin\" : \"linux\"",
   "    cpu = Hardware::CPU.arm? ? \"arm64\" : \"x64\"",
   "    \"" ++ "#{os}-#{cpu}" ++ "\"",
   "  end",
   "",
   "  def asset_name",
   "    \"" ++ "#{ASSET_PREFIX}#{target_name}" ++ "\"",
   "  end",
   "",
   "  def install",
   "    unless PINNED_TARGETS.include?(target_name)",
   "      odie <<~MESSAGE",
   "        tl " ++ "#{version}" ++ " publishes no " ++ "#{target_name}" ++ " binary.",
   "        That target is Best-effort (ADR-0006): it is built and smoke-tested, but a",
   "        failing leg does not block a release, and this release shipped without it.",
   "        Install a later release once one is published, use the Supported build for",
   "        another platform, or build from source with Lean 4:",
   s!"          https://github.com/{repository}",
   "      MESSAGE",
   "    end",
   "",
   "    # Homebrew has already checked the digest of the downloaded file by the",
   "    # time this runs. What it has not checked is who produced it, which is what",
   "    # the bundle establishes: fetch the per-asset bundle from the same release",
   "    # and verify it against the pinned identity before anything is installed.",
   "    #",
   "    # A raw curl rather than a `resource`: a resource must declare a sha256,",
   "    # and the bundle's digest is not knowable when this formula is rendered —",
   "    # SHA256SUMS is written and signed before the per-asset bundles exist, so",
   "    # they are deliberately not listed in it. The bundle needs no digest pin",
   "    # anyway; its authenticity is exactly what cosign establishes against the",
   "    # certificate identity below, and a tampered bundle fails that check.",
   "    bundle = \"" ++ "#{asset_name}" ++ ".sigstore.json\"",
   "    system \"curl\", \"--fail\", \"--silent\", \"--show-error\", \"--location\", \"--retry\", \"3\",",
   "           \"--proto\", \"=https\", \"--proto-redir\", \"=https\",",
   "           \"--output\", bundle,",
   "           \"" ++ s!"https://github.com/{repository}/releases/download/v" ++ "#{version}/#{bundle}" ++ "\"",
   "",
   "    # The staged copy, not `cached_download`: `bin.install` moves rather than",
   "    # copies, so installing the cached file would empty Homebrew's download",
   "    # cache and make a later reinstall or prefetch fetch it again.",
   "    system formula_opt_bin(\"cosign\")/\"cosign\", \"verify-blob\", asset_name,",
   "           \"--bundle\", bundle,",
   "           \"--certificate-oidc-issuer\", OIDC_ISSUER,",
   "           \"--certificate-identity-regexp\", CERTIFICATE_IDENTITY",
   "",
   "    bin.install asset_name => \"tl\"",
   "    chmod 0755, bin/\"tl\"",
   "",
   "    # ADR-0006 requires the third-party notice to travel with every",
   "    # distribution artifact. The npm packages bundle it because a package has",
   "    # somewhere to put it; a bare binary does not, so the release publishes it",
   "    # as a companion asset and it is installed here. Fetched rather than",
   "    # declared as a `resource` for the same reason as the bundle: a resource",
   "    # needs a sha256 known at rendering time, and the digest here comes from",
   "    # the release's own SHA256SUMS, which Homebrew has no way to consult.",
   "    #",
   "    # A release that does not publish it still installs: `tl licenses` prints",
   "    # the same content from the binary, and refusing a good binary over a",
   "    # missing sidecar would be the wrong trade.",
   "    # `quiet_system`, not `system`. Homebrew's `Formula#system` *raises*",
   "    # BuildError on a non-zero exit — its signature is `.void`, so it never",
   "    # returns a falsy value — which made the `else` branch below unreachable",
   "    # and turned a release without this optional asset, or one transient 404",
   "    # on it, into a failed install with a Homebrew crash report, after the",
   "    # binary had already been placed. `quiet_system` is the boolean form.",
   "    notice = \"THIRD-PARTY-LICENSES\"",
   "    if quiet_system \"curl\", \"--fail\", \"--silent\", \"--show-error\", \"--location\", \"--retry\", \"3\",",
   "                    \"--proto\", \"=https\", \"--proto-redir\", \"=https\",",
   "                    \"--output\", notice,",
   "                    \"" ++ s!"https://github.com/{repository}/releases/download/v" ++ "#{version}/#{notice}" ++ "\"",
   "      doc.install notice",
   "    else",
   "      opoo \"tl " ++ "#{version}" ++ " publishes no " ++ "#{notice}" ++ "; run `tl licenses` for the same content.\"",
   "    end",
   "  end",
   "",
   "  test do",
   "    # The version the formula claims and the version the binary reports must",
   "    # agree; a formula pointing at the wrong release would otherwise install",
   "    # silently.",
   "    assert_match version.to_s, shell_output(\"" ++ "#{bin}/tl version" ++ "\")",
   "",
   "    # A real round trip, so the test fails on a binary that starts but cannot",
   "    # touch a repository.",
   "    system \"git\", \"init\", \"-q\", testpath/\"repo\"",
   "    ENV[\"TL_ACTOR\"] = \"brew-test\"",
   "    Dir.chdir(testpath/\"repo\") do",
   "      system bin/\"tl\", \"init\", \"--json\"",
   "      output = shell_output(\"" ++ "#{bin}/tl create smoke --json" ++ "\")",
   "      assert_match '\"ok\":true', output",
   "      assert_match '\"count\":1', shell_output(\"" ++ "#{bin}/tl ready --json" ++ "\")",
   "    end",
   "  end",
   "end"]

/-- The complete formula, as the bytes to write.

    Deterministic: the same spec renders the same text on every run, which is
    what makes the tap comparison "is this the formula this release renders"
    rather than "does this diff look small". -/
def render (spec : Spec) : Except String String := do
  placeable spec
  let mut lines ← headerLines spec
  for os in osOrder do
    lines := lines ++ (← osLines spec os)
  return String.intercalate "\n" (lines ++ bodyLines spec.repository) ++ "\n"

/-! ## The commands

Two, because there are two formulae and they answer different questions. The
release rendering describes one signed release and is what the tap receives. The
placeholder rendering describes no release at all: it is the copy tracked in this
repository, which exists so that real Homebrew can load, style and audit the
*shape* this renderer produces on every commit, long before a release renders
one. Both go through `render`, so what CI audits is the thing a release
publishes. -/

/-- The spec a verified release renders from. Every value comes from the signed
    manifest; nothing here consults a checkout. -/
def specOf (description : ManifestDescription) (sumsDigest : Sha256) : Spec :=
  { version := description.version
    repository := description.repository
    tap := description.homebrew.tap
    issuer := description.signing.certificateOidcIssuer
    certificateIdentity := description.signing.certificateIdentityRegexp
    sumsDigest := sumsDigest
    pins := description.pinned.map fun (target, digest) => { target, digest } }

/-- The digest every placeholder url pins: sixty-four zeroes, which is not the
    SHA-256 of anything Homebrew would ever download. That is the property — the
    tracked formula cannot be installed by accident. -/
def placeholderDigestHex : String := String.ofList (List.replicate 64 '0')

/-- The release a placeholder formula claims: none. `0.0.0` is a version this
    project will never tag, so every url in the tracked formula names a release
    that does not exist. -/
def placeholderVersionText : String := "0.0.0"

/-- The tracked formula's spec: this repository's identity, every distributed
    target, and a digest that matches nothing. -/
def placeholderSpec (identity : Identity) (targets : Targets) : Except String Spec := do
  let version ← Version.parse "the placeholder version" placeholderVersionText
  let digest ← Sha256.parse "the placeholder digest" placeholderDigestHex
  return {
    version
    repository := identity.repository
    tap := identity.homebrewTap
    issuer := identity.certificateOidcIssuer
    certificateIdentity := identity.certificateIdentityRegexp
    sumsDigest := digest
    pins := targets.targets.map fun target => { target, digest } }

/-- Refuse unless every release-blocking target has a url, then render.

    One function for both commands, so the coverage rule cannot hold for the
    formula CI audits and not for the one a release publishes. -/
def renderCovering (targets : List Target) (spec : Spec) : Except String String := do
  match coverageBlockers targets spec.pinnedTargets with
  | [] => render spec
  | blockers =>
      .error ("this release does not publish every Supported target, so no formula may be rendered from it.\n"
        ++ String.join (blockers.map fun blocker => s!"  {blocker}\n")
        ++ "A formula whose stable spec has no url for a platform raises on *load*, for every brew command touching the tap and not only `brew install tl`.")

private def renderOptions : List OptionSpec :=
  [{ name := "dist", takesValue := true },
   { name := "manifest", takesValue := true },
   outputOption, outputDirectoryOption]

private structure RenderArgs where
  dist : String
  manifestPath : String
  base : Write.OutputDirectory
  output : Write.OutputPath

private def renderArgs (options : Options) : Except String RenderArgs := do
  let (base, output) ← resolveOutput options
  return {
    dist := ← options.required "dist"
    manifestPath := ← options.required "manifest"
    base, output }

private def renderDecision (args : RenderArgs) : Decision String := do
  let description ← readParsed args.manifestPath ManifestDescription.parse
  -- The fallback url points at the release's own `SHA256SUMS`, which is the one
  -- asset a manifest structurally cannot describe — the sums file lists the
  -- manifest — so its digest is computed from the directory the caller has
  -- already authenticated rather than read out of the document.
  let digester ← ofIO Digester.resolve
  let sumsDigest ← ofIO (digester.digest (args.dist ++ "/SHA256SUMS"))
  let spec := specOf description sumsDigest
  let formula ← ofExcept (renderCovering description.distributedTargets spec)
  let disclosure ← ofIO (writeEvidence args.base args.output formula)
  return disclosing
    s!"wrote {args.output.render} in {args.base.path} for {description.tag}, pinning {spec.pins.length} of {description.targets.length} targets{if description.homebrew.push then "" else " (a prerelease: generated and attached, not pushed to the tap)"}"
    disclosure

private def renderCommand : Command :=
  optionCommand "homebrew-render" "--dist <dir> --manifest <path> --output <name> [--output-dir <dir>]"
    "Render the complete Homebrew formula for a verified release, from its signed manifest."
    ["--dist", "dist", "--manifest", "dist/release-manifest.json",
     "--output", "tl.rb", "--output-dir", "dist"]
    renderOptions renderArgs renderDecision

private def placeholderOptions : List OptionSpec :=
  [{ name := "identity", takesValue := true },
   { name := "targets", takesValue := true },
   outputOption, outputDirectoryOption]

private structure PlaceholderArgs where
  identityPath : String
  targetsPath : String
  base : Write.OutputDirectory
  output : Write.OutputPath

private def placeholderArgs (options : Options) : Except String PlaceholderArgs := do
  let (base, output) ← resolveOutput options
  return {
    identityPath := ← options.required "identity"
    targetsPath := ← options.required "targets"
    base, output }

private def placeholderDecision (args : PlaceholderArgs) : Decision String := do
  let identity ← readParsed args.identityPath Identity.parse
  let targets ← readParsed args.targetsPath Targets.parse
  let spec ← ofExcept (placeholderSpec identity targets)
  let formula ← ofExcept (renderCovering targets.targets spec)
  let disclosure ← ofIO (writeEvidence args.base args.output formula)
  return disclosing
    s!"wrote {args.output.render} in {args.base.path} — the placeholder formula, pinning {spec.pins.length} targets at a digest that matches nothing"
    disclosure

private def placeholderCommand : Command :=
  optionCommand "homebrew-placeholder"
    "--identity <path> --targets <path> --output <name> [--output-dir <dir>]"
    "Render the tracked placeholder formula, which pins no release and is what the drift guard compares."
    ["--identity", "release/identity.json", "--targets", "release/targets.json",
     "--output", "tl.rb", "--output-dir", "Formula"]
    placeholderOptions placeholderArgs placeholderDecision

def homebrewCommands : List Command := [renderCommand, placeholderCommand]

end Homebrew

export Homebrew (homebrewCommands)

end Release
