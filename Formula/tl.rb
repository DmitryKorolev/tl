# frozen_string_literal: true

# Homebrew formula for tl, maintained here and copied to the tap
# (DmitryKorolev/homebrew-tap) by the release workflow. The tap is the
# distribution point; this file is the source of truth, so the identity pins
# below sit in the same repository as release/identity.json and are checked
# against it by Tests/ReleaseTests.lean.
#
# Generated in part: `scripts/gen-homebrew-formula.sh` fills in VERSION and the
# per-platform SHA-256 digests from a release's signed SHA256SUMS. The digests
# below are placeholders until the first release fills them.
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
  version "0.0.0"
  license "Apache-2.0"

  depends_on "cosign"
  depends_on "git"

  # The pinned signing identity. Kept byte-identical to release/identity.json;
  # Tests/ReleaseTests.lean fails if these drift, because this is a fourth
  # place the same pin lives and the one a Homebrew user actually relies on.
  OIDC_ISSUER = "https://token.actions.githubusercontent.com"
  # Deliberately one long line, not a continuation: the drift guard in
  # Tests/ReleaseTests.lean compares this against release/identity.json as
  # text, and a reader comparing the four copies by eye should see the same
  # bytes in each. A split literal would be equal at runtime and different on
  # the page, which is the wrong trade for a pin.
  # rubocop:disable Layout/LineLength
  CERTIFICATE_IDENTITY = '^https://github\.com/DmitryKorolev/tl/\.github/workflows/release\.yml@refs/tags/v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z]+([.-][0-9A-Za-z]+)*)?$'
  # rubocop:enable Layout/LineLength

  on_macos do
    on_arm do
      url "https://github.com/DmitryKorolev/tl/releases/download/v#{version}/tl-darwin-arm64"
      sha256 "0000000000000000000000000000000000000000000000000000000000000000"
    end
    on_intel do
      url "https://github.com/DmitryKorolev/tl/releases/download/v#{version}/tl-darwin-x64"
      sha256 "0000000000000000000000000000000000000000000000000000000000000000"
    end
  end

  on_linux do
    on_arm do
      url "https://github.com/DmitryKorolev/tl/releases/download/v#{version}/tl-linux-arm64"
      sha256 "0000000000000000000000000000000000000000000000000000000000000000"
    end
    on_intel do
      url "https://github.com/DmitryKorolev/tl/releases/download/v#{version}/tl-linux-x64"
      sha256 "0000000000000000000000000000000000000000000000000000000000000000"
    end
  end

  def asset_name
    if OS.mac?
      Hardware::CPU.arm? ? "tl-darwin-arm64" : "tl-darwin-x64"
    else
      Hardware::CPU.arm? ? "tl-linux-arm64" : "tl-linux-x64"
    end
  end

  def install
    # Homebrew has already checked the digest of the downloaded file by the
    # time this runs. What it has not checked is who produced it, which is what
    # the bundle establishes: fetch the per-asset bundle from the same release
    # and verify it against the pinned identity before anything is installed.
    bundle = "#{asset_name}.sigstore.json"
    system "curl", "--fail", "--silent", "--show-error", "--location", "--retry", "3",
           "--output", bundle,
           "https://github.com/DmitryKorolev/tl/releases/download/v#{version}/#{bundle}"

    system Formula["cosign"].opt_bin/"cosign", "verify-blob", cached_download,
           "--bundle", bundle,
           "--certificate-oidc-issuer", OIDC_ISSUER,
           "--certificate-identity-regexp", CERTIFICATE_IDENTITY

    bin.install cached_download => "tl"
    chmod 0755, bin/"tl"
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
