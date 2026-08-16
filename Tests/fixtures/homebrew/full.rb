# frozen_string_literal: true

# Homebrew formula for tl, rendered by `tlrelease homebrew-render` from the
# signed release manifest and pushed by the release workflow to the tap
# DmitryKorolev/homebrew-tap.
#
# The copy tracked in this repository is the same rendering at the placeholder
# release, so it cannot be installed by accident — a placeholder digest matches
# nothing Homebrew would ever download — and an edit to it is a failing test
# rather than a formula pinning a release that does not exist.
#
# Every url below names its release tag literally rather than interpolating
# `version`. The two are the same string, and writing it out means no url
# depends on what Homebrew's version scanner makes of the one above it.
#
# Two independent checks, both fail-closed and neither bypassable from the
# command line:
#
#   1. Homebrew's own `sha256` on each url. A mismatch aborts the install; there
#      is no --force that accepts a wrong digest.
#   2. A Sigstore verification against the pinned certificate identity, run in
#      `install`. `cosign` is a hard dependency rather than an optional nicety,
#      because a signature check that silently does not run is the failure this
#      formula exists to prevent. There is deliberately no environment variable
#      to skip it: the installer's TL_INSTALL_SKIP_SIGNATURE escape exists for
#      machines that cannot run cosign, and on such a machine Homebrew would
#      simply install cosign first.
class Tl < Formula
  desc "Formally verified, git-native task tracker for AI agents"
  homepage "https://github.com/DmitryKorolev/tl"
  # The stable spec needs a url for *every* platform, not only the ones this
  # release publishes a binary for. macOS x86-64 is Best-effort (ADR-0006), so
  # a release whose Intel leg failed pins no binary there — and a formula whose
  # stable spec has no url for the running platform makes Homebrew raise
  # `formula requires at least a URL`, with a Ruby backtrace and "Please report
  # this issue", on *load*: for `brew info`, `brew upgrade`, and any `brew
  # update` that touches the tap, not just `brew install tl`. One broken
  # Best-effort leg would take the whole tap down for every Intel Mac.
  #
  # So the top-level url is the release's SHA256SUMS, which every release
  # publishes and whose digest this formula already knows. Each platform that
  # *did* build overrides it below with its own binary. On a platform that did
  # not, the spec still resolves, Homebrew downloads a few hundred bytes, and
  # `install` refuses with an explanation naming the tier — a message instead of
  # a crash report.
  url "https://github.com/DmitryKorolev/tl/releases/download/v1.2.3/SHA256SUMS"
  sha256 "0000000000000000000000000000000000000000000000000000000000000009"
  license "Apache-2.0"

  depends_on "cosign"
  depends_on "git"

  # The pinned signing identity, rendered from release/identity.json — which is
  # what makes this the same pin the standalone verifier and the installer use
  # rather than a fourth copy of it that can drift.
  OIDC_ISSUER = "https://token.actions.githubusercontent.com"
  # Deliberately one long line, not a continuation: a reader comparing the
  # copies of this pin by eye should see the same bytes in each, and a split
  # literal would be equal at runtime and different on the page. `brew style`
  # permits the length; it does not permit an inline rubocop directive, so
  # there is none.
  CERTIFICATE_IDENTITY = '^https://github\.com/DmitryKorolev/tl/\.github/workflows/release\.yml@refs/tags/v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?$'

  # The asset names are composed from this prefix rather than written out.
  # The repository's task-ID lint reads a `tl-` affix followed by Crockford
  # digits as a tracker reference, and the macOS asset names match it;
  # release.yml builds its asset names the same way for the same reason.
  ASSET_PREFIX = "tl-"

  # The targets this particular rendering pins a binary for. A Best-effort
  # target the release did not build is absent from both this list and the
  # blocks below, and `install` consults it before doing anything: without it
  # the download would succeed (the fallback url above) and `bin.install` would
  # then fail on a file that was never fetched.
  PINNED_TARGETS = %w[darwin-arm64 darwin-x64 linux-arm64 linux-x64].freeze

  on_macos do
    on_arm do
      url "https://github.com/DmitryKorolev/tl/releases/download/v1.2.3/#{ASSET_PREFIX}darwin-arm64"
      sha256 "0000000000000000000000000000000000000000000000000000000000000003"
    end
    on_intel do
      url "https://github.com/DmitryKorolev/tl/releases/download/v1.2.3/#{ASSET_PREFIX}darwin-x64"
      sha256 "0000000000000000000000000000000000000000000000000000000000000004"
    end
  end

  on_linux do
    on_arm do
      url "https://github.com/DmitryKorolev/tl/releases/download/v1.2.3/#{ASSET_PREFIX}linux-arm64"
      sha256 "0000000000000000000000000000000000000000000000000000000000000002"
    end
    on_intel do
      url "https://github.com/DmitryKorolev/tl/releases/download/v1.2.3/#{ASSET_PREFIX}linux-x64"
      sha256 "0000000000000000000000000000000000000000000000000000000000000001"
    end
  end

  def target_name
    os = OS.mac? ? "darwin" : "linux"
    cpu = Hardware::CPU.arm? ? "arm64" : "x64"
    "#{os}-#{cpu}"
  end

  def asset_name
    "#{ASSET_PREFIX}#{target_name}"
  end

  def install
    unless PINNED_TARGETS.include?(target_name)
      odie <<~MESSAGE
        tl #{version} publishes no #{target_name} binary.
        That target is Best-effort (ADR-0006): it is built and smoke-tested, but a
        failing leg does not block a release, and this release shipped without it.
        Install a later release once one is published, use the Supported build for
        another platform, or build from source with Lean 4:
          https://github.com/DmitryKorolev/tl
      MESSAGE
    end

    # Homebrew has already checked the digest of the downloaded file by the
    # time this runs. What it has not checked is who produced it, which is what
    # the bundle establishes: fetch the per-asset bundle from the same release
    # and verify it against the pinned identity before anything is installed.
    #
    # A raw curl rather than a `resource`: a resource must declare a sha256,
    # and the bundle's digest is not knowable when this formula is rendered —
    # SHA256SUMS is written and signed before the per-asset bundles exist, so
    # they are deliberately not listed in it. The bundle needs no digest pin
    # anyway; its authenticity is exactly what cosign establishes against the
    # certificate identity below, and a tampered bundle fails that check.
    bundle = "#{asset_name}.sigstore.json"
    system "curl", "--fail", "--silent", "--show-error", "--location", "--retry", "3",
           "--proto", "=https", "--proto-redir", "=https",
           "--output", bundle,
           "https://github.com/DmitryKorolev/tl/releases/download/v#{version}/#{bundle}"

    # The staged copy, not `cached_download`: `bin.install` moves rather than
    # copies, so installing the cached file would empty Homebrew's download
    # cache and make a later reinstall or prefetch fetch it again.
    system formula_opt_bin("cosign")/"cosign", "verify-blob", asset_name,
           "--bundle", bundle,
           "--certificate-oidc-issuer", OIDC_ISSUER,
           "--certificate-identity-regexp", CERTIFICATE_IDENTITY

    bin.install asset_name => "tl"
    chmod 0755, bin/"tl"

    # ADR-0006 requires the third-party notice to travel with every
    # distribution artifact. The npm packages bundle it because a package has
    # somewhere to put it; a bare binary does not, so the release publishes it
    # as a companion asset and it is installed here. Fetched rather than
    # declared as a `resource` for the same reason as the bundle: a resource
    # needs a sha256 known at rendering time, and the digest here comes from
    # the release's own SHA256SUMS, which Homebrew has no way to consult.
    #
    # A release that does not publish it still installs: `tl licenses` prints
    # the same content from the binary, and refusing a good binary over a
    # missing sidecar would be the wrong trade.
    # `quiet_system`, not `system`. Homebrew's `Formula#system` *raises*
    # BuildError on a non-zero exit — its signature is `.void`, so it never
    # returns a falsy value — which made the `else` branch below unreachable
    # and turned a release without this optional asset, or one transient 404
    # on it, into a failed install with a Homebrew crash report, after the
    # binary had already been placed. `quiet_system` is the boolean form.
    notice = "THIRD-PARTY-LICENSES"
    if quiet_system "curl", "--fail", "--silent", "--show-error", "--location", "--retry", "3",
                    "--proto", "=https", "--proto-redir", "=https",
                    "--output", notice,
                    "https://github.com/DmitryKorolev/tl/releases/download/v#{version}/#{notice}"
      doc.install notice
    else
      opoo "tl #{version} publishes no #{notice}; run `tl licenses` for the same content."
    end
  end

  test do
    # The version the formula claims and the version the binary reports must
    # agree; a formula pointing at the wrong release would otherwise install
    # silently.
    assert_match version.to_s, shell_output("#{bin}/tl version")

    # A real round trip, so the test fails on a binary that starts but cannot
    # touch a repository.
    system "git", "init", "-q", testpath/"repo"
    ENV["TL_ACTOR"] = "brew-test"
    Dir.chdir(testpath/"repo") do
      system bin/"tl", "init", "--json"
      output = shell_output("#{bin}/tl create smoke --json")
      assert_match '"ok":true', output
      assert_match '"count":1', shell_output("#{bin}/tl ready --json")
    end
  end
end
