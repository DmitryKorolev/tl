/- Reviewed inputs and process plans for local/CI hermetic validation. -/
import release.Process

namespace Release.Hermetic

def image : String := "docker.io/alpine/git@sha256:53a6239398162098fed2f49a46512f9cbba9e3f31b9f2cea4fa90129ee069a99"
def builderImage : String := "docker.io/library/ubuntu@sha256:a61567bd31828687156d735ea8eb01ba4e37636e225dd6a48ba94136a70d9d61"
def completion : String := "hermetic validation completed (protocol v1)"
def launcherCompletion : String := "npm launcher hermetic suite: passed"

def completed (output : ProcessOutput) (verdict : String) : Bool :=
  output.exitCode == 0 && (output.stdout.trimAscii.toString.splitOn "\n").getLast! == verdict

theorem completed_iff (output : ProcessOutput) (verdict : String) :
    completed output verdict = true ↔ output.exitCode = 0 ∧
      (output.stdout.trimAscii.toString.splitOn "\n").getLast! = verdict := by
  simp only [completed, Bool.and_eq_true, beq_iff_eq]

def hostSupported (os arch : String) : Bool :=
  ["Linux", "Darwin"].contains os && ["x86_64", "amd64", "arm64", "aarch64"].contains arch

structure Input where
  file : String
  url : String
  sha256 : String
  deriving Repr

def inputs : List Input := [
  { file := "busybox.apk", url := "https://dl-cdn.alpinelinux.org/alpine/v3.22/main/x86_64/busybox-static-1.37.0-r20.apk",
    sha256 := "488ad6efd04b5a722719e79f8e0dcc2c24afd6758867af3ce41b04839e60c74b" },
  { file := "actionlint.tar.gz", url := "https://github.com/rhysd/actionlint/releases/download/v1.7.12/actionlint_1.7.12_linux_amd64.tar.gz",
    sha256 := "8aca8db96f1b94770f1b0d72b6dddcb1ebb8123cb3712530b08cc387b349a3d8" },
  { file := "shellcheck.tar.xz", url := "https://github.com/koalaman/shellcheck/releases/download/v0.11.0/shellcheck-v0.11.0.linux.x86_64.tar.xz",
    sha256 := "8c3be12b05d5c177a04c29e3c78ce89ac86f1595681cab149b65b97c4e227198" },
  { file := "elan.tar.gz", url := "https://github.com/leanprover/elan/releases/download/v4.2.3/elan-x86_64-unknown-linux-gnu.tar.gz",
    sha256 := "df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2" }]

def requiredTools : List String :=
  "awk basename cat chmod cp cut dirname env find git grep head id ln ls mkdir mktemp mv pwd readlink rm sed sha256sum sh shellcheck sleep sort stat tail tar touch tr uname wc actionlint tlrelease".splitOn " "
def forbiddenRuntimes : List String := ["python", "python3", "ruby", "brew", "node", "npm"]
def positiveFiles : List String :=
  ["static/bin/busybox.static", "tools/tlrelease", "tools/actionlint", "tools/shellcheck", "launcher-suite", "packed/package/bin/tl"]

/-- Complete argv: mount paths remain arguments, never shell fragments.
Rootless UID 0 maps to the caller and is checked against scratch ownership. -/
def containerArgs (root scratch : String) : Array String := #[
  "run", "--rm", "--platform", "linux/amd64", "--network", "none", "--read-only",
  "--read-only-tmpfs=false", "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
  "--userns", "host", "--user", "0:0",
  "--mount", s!"type=bind,source={root},target=/workspace,readonly",
  "--mount", s!"type=bind,source={scratch},target=/scratch",
  "--mount", s!"type=bind,source={scratch}/static/bin/busybox.static,target=/bin/busybox,readonly",
  "--mount", s!"type=bind,source={scratch}/lib,target=/lib",
  "--mount", s!"type=bind,source={scratch}/lib64,target=/lib64",
  "--workdir", "/workspace", "--env", "HOME=/scratch/home", "--env", "TMPDIR=/scratch/tmp",
  "--env", "PATH=/scratch/tools:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
  "--entrypoint", "/scratch/tools/tlrelease", image,
  "hermetic-worker", "--root", "/workspace", "--scratch", "/scratch"]

structure Call where
  tool : String
  args : Array String
  timeoutMs : Nat := 120000
  deriving Repr, BEq

def builderCreate (name root scratch : String) : Call :=
  { tool := "podman", args := #["create", "--name", name, "--platform", "linux/amd64",
    "--workdir", "/", "--mount", s!"type=bind,source={root},target=/source,readonly",
    "--mount", s!"type=bind,source={scratch},target=/scratch", "--entrypoint", "sleep", builderImage, "infinity"] }

/-- Build the same target from the actual checkout configuration. Preparation
may fetch dependencies; only the later evidence container is runtime-stripped. -/
def builderCalls (name : String) : List Call :=
  let inside (args : Array String) (timeout : Nat := 120000) : Call :=
    { tool := "podman", args := #["exec", "--workdir", "/build", "--env", "ELAN_HOME=/build/elan",
        "--env", "PATH=/build/elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", name] ++ args,
      timeoutMs := timeout }
  [ { tool := "podman", args := #["start", name] },
    { tool := "podman", args := #["exec", name, "mkdir", "-p", "/build"] },
    inside #["apt-get", "update"] 600000,
    inside #["apt-get", "install", "-y", "--no-install-recommends", "ca-certificates", "curl", "git", "gcc", "libc6-dev", "zstd"] 600000,
    inside #["cp", "-R", "/source/release", "/source/ffi", "/source/lakefile.lean", "/source/lake-manifest.json", "/source/lean-toolchain", "/build/"],
    inside #["tar", "-xzf", "/scratch/elan.tar.gz", "-C", "/build"],
    inside #["/build/elan-init", "-y", "--no-modify-path", "--default-toolchain", "none"],
    inside #["lake", "-KreleaseOnly=true", "update"] 600000,
    inside #["lake", "-KreleaseOnly=true", "build", "tlreleaseStatic", "--wfail"] 1800000,
    inside #["cp", "/build/.lake/build/bin/tlrelease-static", "/scratch/tools/tlrelease"] ]

def evidenceCalls : List Call := [
  { tool := "sha256sum", args := #["-c", "/scratch/positive-inputs.sha256"] },
  { tool := "git", args := #["--version"] },
  { tool := "shellcheck", args := #["--version"] },
  { tool := "actionlint", args := #["-version"] },
  { tool := "shellcheck", args := #["-S", "warning", "-s", "sh", "/scratch/launcher-suite"] },
  { tool := "/scratch/tools/tlrelease", args := #["policy", "--profile", "release", "--strict"], timeoutMs := 600000 }]

end Release.Hermetic
