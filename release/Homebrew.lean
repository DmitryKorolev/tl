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

/-- Every row: the formula pins something, and it pins every target whose
    absence would block the release.

    The target set comes from the manifest's own rows rather than from a
    checkout's `release/targets.json`: the question is whether *this release*
    published every target it says is release-blocking, and a checkout read at
    publication time is a different release's answer.

    The first row is not implied by the rest. A release whose targets are all
    Best-effort and all failed satisfies every per-target row by having nothing
    release-blocking to satisfy, and renders a formula with no url, no block and
    an empty pin list — one that loads on every platform and installs on none. -/
def coverageChecks (targets : List Target) (pinned : List String) : List Check :=
  { held := !pinned.isEmpty,
    failure := "the formula would pin no binary at all. Every target this release describes is Best-effort and none of them arrived, so there is nothing to serve: the formula would load on every platform and refuse to install on all of them, which is a tap update that reports success and publishes nothing." }
    :: targets.map (coverageCheck pinned)

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

/-- A list with something in it is not the empty list. -/
private theorem notEmpty_iff {α : Type} (items : List α) :
    (!items.isEmpty) = true ↔ items ≠ [] := by
  match items with
  | [] =>
      constructor
      · intro absurdity; exact Bool.noConfusion absurdity
      · intro empty; exact absurd rfl empty
  | head :: rest =>
      constructor
      · intro _; exact List.cons_ne_nil head rest
      · intro _; rfl

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
      pinned ≠ []
        ∧ ∀ target ∈ targets,
            target.tier.releaseBlocking = true → pinned.contains target.name = true := by
  rw [formulaCovers, Check.allHeld, coverageChecks, List.all_cons, Bool.and_eq_true,
    List.all_eq_true]
  refine and_congr (notEmpty_iff pinned) ?_
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
      pinned ≠ []
        ∧ ∀ target ∈ targets,
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

/-- The first value repeated in a sorted list. -/
private def adjacentRepeat : List String → Option String
  | first :: second :: rest =>
      if first == second then some first else adjacentRepeat (second :: rest)
  | _ => none

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
    -- Homebrew selects a spec by platform, so two targets on one platform have
    -- one block between them and the block-writer below would take whichever it
    -- found first. The other would keep its name in the pin list and have no
    -- url — a Supported target that `install` admits and cannot fetch, which is
    -- exactly the shape the coverage rule exists to prevent and which the
    -- coverage rule cannot see, because its `pinned` means "named" rather than
    -- "served". `release/targets.json` already carries `libc` to describe such
    -- variants, so this is one row away from being reachable.
    pure ()
  -- The platform collision, read pairwise off a sorted list rather than by
  -- filtering every pin for every pin. Same answer, and the repository's
  -- proportional-work rule applies to a command path whether or not today's
  -- list is short.
  let platforms := (spec.pins.map fun pin => s!"{pin.target.os}/{pin.target.cpu}").mergeSort (· ≤ ·)
  match adjacentRepeat platforms with
  | some platform =>
      .error s!"more than one pinned target is {platform}. A Homebrew formula selects one spec per platform, so they would share one block and only the first would get a url — the rest would be listed as pinned and install nothing. Homebrew has no libc selector; distributing two builds for one platform needs a different formula shape, decided deliberately."
  | none => pure ()

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

/-! ## Updating the tap

A tap carries one formula, so publication is a replacement rather than an
addition, and it has to be safe to run twice: a release job that failed partway
and is retried must not produce a second commit saying the same thing, and must
not report success having left the tap without the formula.

The state that decides is the *remote branch's* copy, not the checkout's. A
checkout is four states deep — the working tree, the index, the commit, and what
the remote actually holds — and a comparison against the shallowest of them
reads every deeper failure as success: a run whose `git commit` failed leaves a
working tree that already holds the right bytes, so a retry that classified the
working tree would say "already carries this formula", push nothing, and exit
zero over a tap that never received it. So the current state is read from the
remote, the push names its destination explicitly rather than letting
`branch.<name>.remote` choose one, and the remote is read again afterwards to
establish that the bytes arrived.

Comparison is over the *formula text*, not over archive bytes: what a tap serves
is this file, and two renderings of one release are byte-identical by
construction.
-/

/-- What the tap's published branch holds, against what this release renders. -/
inductive TapState where
  | absent
  | identical
  | differs
  deriving DecidableEq, Repr

def TapState.describe : TapState → String
  | .absent => "the tap's published branch carries no formula for tl yet"
  | .identical => "the tap's published branch already carries exactly this formula"
  | .differs => "the tap's published branch carries a different formula"

/-- Classify what the tap's published branch holds.

    The `Option` is the *remote's* copy — absent when the branch does not exist
    or does not carry the file — because that is the only state a publication
    decision may be taken on. -/
def tapDisposition (rendered : String) (existing : Option String) : TapState :=
  match existing with
  | none => .absent
  | some text =>
      match text == rendered with
      | true => .identical
      | false => .differs

/-- **The tap is left alone exactly when it already holds this formula.**

    The direction that matters is left to right: `identical` is the answer that
    skips a publication, so a comparison that drifted into saying it when the
    texts differ would leave the tap pinning an earlier release while the job
    reported success. Right to left is what a classifier that never said
    `identical` would fail, and that one is not idle either — it is what makes a
    retried release job a no-op rather than a second commit saying the same
    thing. -/
theorem tapDisposition_identical_iff (rendered : String) (existing : Option String) :
    tapDisposition rendered existing = .identical ↔ existing = some rendered := by
  cases existing with
  | none =>
      constructor
      · intro impossible; exact TapState.noConfusion impossible
      · intro impossible; cases impossible
  | some text =>
      rw [tapDisposition]
      cases matched : text == rendered with
      | true =>
          constructor
          · intro _; exact congrArg some (beq_iff_eq.mp matched)
          · intro _; rfl
      | false =>
          constructor
          · intro impossible; exact TapState.noConfusion impossible
          · intro isRendered
            rw [Option.some.inj isRendered, beq_self_eq_true] at matched
            exact Bool.noConfusion matched

/-- **A formula is written where there is none exactly when the tap has none.**

    Stated as well, because `absent` and `differs` take the same action and
    collapsing them would be invisible in the output: the message a maintainer
    reads is the only place the two are distinguished. -/
theorem tapDisposition_absent_iff (rendered : String) (existing : Option String) :
    tapDisposition rendered existing = .absent ↔ existing = none := by
  cases existing with
  | none => exact Iff.intro (fun _ => rfl) (fun _ => rfl)
  | some text =>
      rw [tapDisposition]
      cases matched : text == rendered with
      | true =>
          constructor
          · intro impossible; exact TapState.noConfusion impossible
          · intro impossible; cases impossible
      | false =>
          constructor
          · intro impossible; exact TapState.noConfusion impossible
          · intro impossible; cases impossible

/-- Whether a checkout's `origin` names the tap this release publishes to.

    What this establishes is narrow and worth stating exactly: the repository
    the job cloned is named for the tap the signed manifest describes. It is not
    a claim about the host, the credential, or who controls that repository —
    the remote is composed by the release workflow from a secret, and a workflow
    that points somewhere else is a change under protected review rather than
    something this comparison can see. What it does catch is the failure that
    has no other guard: a job that cloned the wrong repository and would
    otherwise commit this release's formula into it.

    `github.com` is deliberately not required. Pinning the host would make the
    publication path untestable against a local repository, and the coverage
    that buys is worth more than a host check the threat model does not lean
    on. -/
def tapRemoteAccepts (tap : String) (url : String) : Bool :=
  let trimmed := url.trimAscii.toString
  let withoutGit := if trimmed.endsWith ".git" then (trimmed.dropEnd 4).toString else trimmed
  let stripped := if withoutGit.endsWith "/" then (withoutGit.dropEnd 1).toString else withoutGit
  stripped.endsWith ("/" ++ tap) || stripped.endsWith (":" ++ tap)

/-- The identity the tap commit is authored under. A repository the release
    workflow writes to on nobody's behalf but its own, so it says so rather than
    borrowing whichever identity the runner happens to have configured. -/
private def commitAuthorName : String := "tl release"

private def commitAuthorEmail : String := "tl-release@users.noreply.github.com"

/-- Where a tap keeps its formula. Fixed by Homebrew, not by us. -/
private def tapFormulaComponents : List String := ["Formula", "tl.rb"]

private def tapFormulaRelative : String := String.intercalate "/" tapFormulaComponents

private def publishOptions : List OptionSpec :=
  [{ name := "dist", takesValue := true },
   { name := "manifest", takesValue := true },
   { name := "tap", takesValue := true },
   { name := "dry-run", takesValue := false }]

private structure PublishArgs where
  dist : String
  manifestPath : String
  tap : Write.OutputDirectory
  tapPath : String
  dryRun : Bool

private def publishArgs (options : Options) : Except String PublishArgs := do
  let tapPath ← options.required "tap"
  return {
    dist := ← options.required "dist"
    manifestPath := ← options.required "manifest"
    tap := ← Write.OutputDirectory.parse "--tap" tapPath
    tapPath
    dryRun := options.given "dry-run" }

/-- Run `git` inside the tap checkout, with its output as a value.

    No refusal written here quotes the remote url, and the url is never read
    into one: the workflow's remote carries the publication credential, and the
    release log is the one place every failure is read from. What this cannot
    control is git's own diagnosis, which it passes through — `git push` may
    name the remote it could not reach. GitHub Actions masks the secret it
    interpolated into that url, and that masking is what covers the passed-through
    case; it is a platform property rather than one this command establishes. -/
private def gitRaw (tap : String) (args : List String) : Decision String := do
  let output ← ofIO (succeeded "git" ((["-C", tap] ++ args).toArray))
  return output.stdout

private def gitIn (tap : String) (args : List String) : Decision String := do
  return (← gitRaw tap args).trimAscii.toString

/-- Whether anything is staged for the formula.

    `git diff --cached` answers with its exit status — `1` is "there is a
    difference", which is not a failure — so this is one of the two places that
    reads a status rather than requiring zero. It is deliberately not the
    publication decision: what is staged is a fact about the index, and a retry
    after a failed push has the commit already made and nothing staged. The
    decision is the remote comparison above it. -/
private def somethingStaged (tap : String) : Decision Bool := do
  let outcome ← ofIO (do return .ok (← Release.run "git"
    #["-C", tap, "diff", "--cached", "--quiet", "--", tapFormulaRelative]))
  match outcome with
  | .completed output =>
      if output.exitCode == 0 then return false
      else if output.exitCode == 1 then return true
      else
        decline s!"`git diff --cached` exited {output.exitCode} in {tap}. It reports 0 for no staged change and 1 for one; anything else means it could not look, and treating that as either answer would decide a publication on a comparison that did not happen."
  | outcome =>
      decline (outcome.failureMessage.getD "git could not be run")

/-- The branch this checkout publishes.

    `symbolic-ref` rather than `rev-parse --abbrev-ref`, because a tap that has
    just been created has no commits and `rev-parse` cannot name a branch that
    is not yet born — which is a legitimate first publication, not a broken
    checkout. A detached HEAD is the one this has to refuse, and it is the case
    `symbolic-ref` reports by exiting non-zero with nothing to say, so the
    message is written here. -/
private def currentBranch (tap : String) : Decision String := do
  let outcome ← ofIO (do
    return .ok (← Release.run "git" #["-C", tap, "symbolic-ref", "--quiet", "--short", "HEAD"]))
  match outcome with
  | .completed output =>
      let name := output.stdout.trimAscii.toString
      if output.exitCode == 0 && !name.isEmpty then return name
      else
        decline s!"the checkout at {tap} is not on a branch, so there is no branch for this release to publish to. Clone the tap rather than checking out a commit from it."
  | outcome => decline (outcome.failureMessage.getD "git could not be run")

/-- What the remote's published branch holds, and whether it is there at all.

    Two facts rather than one `Option`, because they have different
    consequences and collapsing them hid the second. "The tap carries no
    formula yet" is a state to publish into; "there is no branch here" is the
    absence of anything a checkout could be compared against, and it is the one
    case where what this command pushes is not confined by the tap's own
    history. -/
private structure RemoteBranch where
  /-- Whether `origin` carries the branch. False makes `FETCH_HEAD` meaningless:
      nothing was fetched, so nothing below may diff against it. -/
  present : Bool
  /-- The formula that branch carries, when it carries one. -/
  formula : Option String

/-- What the remote's published branch holds for the formula.

    Read from the remote rather than from the checkout, and read *before*
    anything is written: this is the only state a publication decision may be
    taken on, and every other one is a stage on the way to it. -/
private def remoteBranch (tapPath branch : String) : Decision RemoteBranch := do
  -- Does the branch exist there at all? A tap that has just been created has no
  -- branches, and a first publication creates one; asking the remote is also
  -- what establishes it can be reached before a byte is written.
  let heads ← gitIn tapPath ["ls-remote", "--heads", "origin", branch]
  if heads.isEmpty then return { present := false, formula := none }
  let _ ← gitIn tapPath ["fetch", "--quiet", "origin", branch]
  -- `ls-tree` rather than `show`, so "the branch does not carry this file" is
  -- an empty answer instead of a non-zero status this would have to tell apart
  -- from a repository it could not read.
  let entry ← gitIn tapPath ["ls-tree", "FETCH_HEAD", "--", tapFormulaRelative]
  if entry.isEmpty then return { present := true, formula := none }
  return { present := true
           formula := some (← gitRaw tapPath ["show", s!"FETCH_HEAD:{tapFormulaRelative}"]) }

/-- The paths a `-z` listing named.

    `-z` rather than splitting lines, and it is not fastidiousness: git quotes a
    path containing a newline, a quote or a non-ASCII byte in its ordinary
    listings, so a line-split reading would see `"caf\303\251.txt"` as a name
    unlike the formula's and, worse, would read a path with an embedded newline
    as two names that are each unlike it. Both directions of that error are the
    same failure here — a comparison that does not recognise what it was given.
    NUL-separated output is the one spelling git never rewrites. -/
private def namedPaths (listing : String) : List String :=
  (listing.splitOn "\x00").filter (· != "")

/-- Everything the push would carry into the tap beyond the branch it read.

    A push sends a branch, not a file. This command writes one path and stages
    one path, and neither of those facts constrains what `git push` then sends:
    a checkout holding an unrelated local commit publishes that commit too, and
    the release job reports having pushed a formula. The tap is a public
    repository that `brew install` resolves through, so what lands in it is not
    a private matter for the checkout it was pushed from.

    Both questions are asked because each is blind to the other. The tree diff
    is what the tap ends up serving, and it sees content a merge brought in that
    no single commit's own listing names; the per-commit listing sees a path
    that was added and reverted again, which the tree diff cancels to nothing
    while the history still carries it. Their union is what the push publishes.

    Nothing is asked when the branch is absent: there is no fetched tip to
    compare against, and a push that *creates* the branch publishes the local
    history by definition rather than in addition to something. -/
private def wouldPublishBeyondFormula (tapPath : String) (branch : RemoteBranch) :
    Decision (List String) := do
  if !branch.present then return []
  let carried ← gitRaw tapPath ["diff", "--name-only", "-z", "FETCH_HEAD", "HEAD"]
  let touched ← gitRaw tapPath ["log", "--format=", "--name-only", "-z", "FETCH_HEAD..HEAD"]
  let named := namedPaths carried ++ namedPaths touched
  return (named.filter (· != tapFormulaRelative)).eraseDups

private def publishDecision (args : PublishArgs) : Decision String := do
  let description ← readParsed args.manifestPath ManifestDescription.parse
  -- Rendered here rather than taken as a path. A `--formula` argument makes the
  -- bytes this pushes independent of the manifest it reports them as: passing
  -- the tracked placeholder would publish `version 0.0.0` and five all-zero
  -- digests to the tap while the command said it had pushed the formula for
  -- this release. There is one formula for a release and it is a function of
  -- the release, so this renders it.
  let digester ← ofIO Digester.resolve
  let sumsDigest ← ofIO (digester.digest (args.dist ++ "/SHA256SUMS"))
  let spec := specOf description sumsDigest
  let formula ← ofExcept (renderCovering description.distributedTargets spec)
  -- A tap carries one formula, so pushing a prerelease would make
  -- `brew install tl` resolve to it (ADR-0006). Read off the manifest rather
  -- than off the shape of the tag, and reported as an outcome rather than a
  -- refusal: nothing went wrong, this release does not update the tap.
  if !description.homebrew.push then
    return s!"{description.tag} is a prerelease, so {description.homebrew.tap} keeps the formula it has — a tap carries one formula, and `brew install tl` resolves to whatever is in it"
  -- Both urls, and before anything else about the checkout: which repository
  -- this would publish into does not depend on the checkout having commits, and
  -- an empty tap is a legitimate first publication. They can differ, and only
  -- one of them is where the bytes go — `remote.origin.pushurl` overrides the
  -- fetch url for pushes, so checking only `get-url` would read the state of one
  -- repository and publish into another, reporting the one it had read.
  let fetchUrl ← gitIn args.tapPath ["remote", "get-url", "origin"]
  let pushUrl ← gitIn args.tapPath ["remote", "get-url", "--push", "origin"]
  if !tapRemoteAccepts description.homebrew.tap fetchUrl then
    decline s!"the checkout at {args.tapPath} fetches 'origin' from something that does not name {description.homebrew.tap}, which is the tap this release's manifest describes. Its url is deliberately not repeated here because a release job's remote carries the publication credential. Clone the tap the manifest names, or find out why this job was pointed somewhere else."
  if !tapRemoteAccepts description.homebrew.tap pushUrl then
    decline s!"the checkout at {args.tapPath} pushes 'origin' to something that does not name {description.homebrew.tap}, even though it fetches from the tap. That is what `remote.origin.pushurl` does, and it means this run would read one repository's formula and publish into another. The urls are not repeated here because a release job's remote carries the publication credential."
  let branch ← currentBranch args.tapPath
  let formulaDirectory := args.tapPath ++ "/Formula"
  let formulaDirectoryExists ← ofIO (do return .ok (← System.FilePath.isDir formulaDirectory))
  if !formulaDirectoryExists then
    decline s!"{formulaDirectory} is not a directory. A Homebrew tap keeps its formulae under Formula/, and creating it here would mean this command deciding the shape of a repository it is only supposed to update. Create it in the tap and commit it once."
  let published ← remoteBranch args.tapPath branch
  let state := tapDisposition formula published.formula
  -- Idempotence, over the remote. A retried job reaches this and stops because
  -- the *tap* already has the formula, not because this checkout does.
  if state == .identical then
    return s!"{description.homebrew.tap} already carries the formula for {description.tag} on {branch}; nothing to push"
  -- Before the dry run as well as before the write, so a rehearsal answers the
  -- question a rehearsal is for: whether running this for real would publish
  -- only the formula.
  let strangers ← wouldPublishBeyondFormula args.tapPath published
  if !strangers.isEmpty then
    decline s!"the checkout at {args.tapPath} is ahead of {branch} on {description.homebrew.tap} by changes to {String.intercalate ", " strangers}, and pushing this release's formula would publish those too — a push sends the branch, not the file this command wrote. The tap is what `brew install tl` resolves through, so this would be published rather than kept locally. Clone the tap fresh and re-run; if those changes belong in the tap, push them deliberately first."
  if args.dryRun then
    return s!"{state.describe}, and this release would replace it with the formula for {description.tag} — not written, --dry-run"
  let path ← ofExcept (Write.OutputPath.parse "the tap formula" tapFormulaRelative)
  let disclosure ← ofIO (writeEvidence args.tap path formula)
  let _ ← gitIn args.tapPath ["add", "--", tapFormulaRelative]
  -- Committed only when there is something to commit. A previous run that
  -- committed and then failed to push leaves the commit in place, and `git
  -- commit` with an empty index is a non-zero status this must not read as a
  -- failed publication — the publication decision was taken above, against the
  -- remote.
  if ← somethingStaged args.tapPath then
    -- `--only <path>`, so the commit is this file whatever else the index holds.
    -- The check above establishes that the *history* carries nothing unrelated;
    -- this establishes that the commit about to join it does not either, and it
    -- does so by construction rather than by having looked. A maintainer's
    -- half-staged edit is left staged rather than committed or discarded: this
    -- command publishes a formula, and rearranging someone's index is not
    -- within that. `-m` precedes `--`, because after `--` git reads every word
    -- as a pathspec.
    let _ ← gitIn args.tapPath
      ["-c", s!"user.name={commitAuthorName}", "-c", s!"user.email={commitAuthorEmail}",
       "commit", "--only", "--no-verify",
       "-m", s!"tl {description.tag}: pin the released digests", "--", tapFormulaRelative]
  -- Named explicitly. A bare `git push` consults `branch.<name>.remote` and
  -- `push.default`, so the destination would be configuration rather than the
  -- remote this command just checked.
  let _ ← gitIn args.tapPath ["push", "origin", s!"HEAD:refs/heads/{branch}"]
  -- And read back. "Pushed" is a claim about the remote, and the only evidence
  -- for it is the remote: a push that reported success while the ref did not
  -- move is exactly the outcome this command exists to make impossible.
  let landed ← remoteBranch args.tapPath branch
  if tapDisposition formula landed.formula != .identical then
    decline s!"the push to {description.homebrew.tap} reported success and {branch} there does not carry this release's formula. Nothing about the tap can be assumed from here; look at the branch before re-running."
  return disclosing
    s!"pushed the formula for {description.tag} to {description.homebrew.tap} on {branch}, and read it back ({state.describe})"
    disclosure

private def publishCommand : Command :=
  optionCommand "homebrew-publish"
    "--dist <dir> --manifest <path> --tap <dir> [--dry-run]"
    "Update the tap with this release's formula, once: an identical one is a no-op and a prerelease is not pushed."
    ["--dist", "dist", "--manifest", "dist/release-manifest.json", "--tap", "tap", "--dry-run"]
    publishOptions publishArgs publishDecision

def homebrewCommands : List Command := [renderCommand, placeholderCommand, publishCommand]

end Homebrew

export Homebrew (homebrewCommands)

end Release
