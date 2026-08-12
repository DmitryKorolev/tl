/-
The SHA-256 of a file, from a tool that has been shown to compute SHA-256.

Not implemented here, deliberately. The project *does* have a working SHA-256 in
Lean — `Tl.Hash.Sha256`, which the store uses — and it is the right thing there
and the wrong thing here, for two independent reasons.

The first is structural and settles it on its own: `release/` imports nothing
from `Tl/`, because release administration must not become part of the shipped
product. Reaching that implementation would mean either breaking that boundary
or keeping a second copy of a cryptographic primitive in this directory, and a
second copy that drifts is worse than no copy.

The second holds even if the boundary did not: a release binary is on the order
of a hundred megabytes and there are four of them. Hashing that in Lean would
make the signing step the slowest thing in the pipeline for no gain in
assurance — the digests here are checked against each build leg's own record and
against `SHA256SUMS`, so the property that matters is that two independent
computations agree, not which program did the arithmetic.

What that trade costs, and what is done about it. Shelling out means trusting a
program on PATH, and the failure that trust admits is silent and total: a
`shasum` whose `-a 256` was ignored prints SHA-1 digests, of the right shape
and the wrong length — or, worse, a wrapper that prints a plausible constant.
Nothing downstream would notice. So the tool is not trusted for being named
correctly; it is asked for the digest of a known input and checked against the
answer before any release byte reaches it. A tool that fails that is
`unavailable`, not wrong-once.

The other half of the shell defect this replaces is the status. `sha256sum "$f"
| cut -d' ' -f1` returns `cut`'s status, which is zero whether or not
`sha256sum` ran, so an unreadable file produced an empty digest and a
successful pipeline. Here the run is a `RunOutcome`, the parse is an `Except`,
and the result is a `Sha256` — a type whose only constructor is a parser — so
there is no point along the path where a non-answer has the shape of an answer.
-/
import release.Model
import release.Process

namespace Release

/-! ## The known-answer probe -/

/-- The input the probe hashes: three bytes, no newline. It is the example
    input in FIPS 180-4 §D.1, so the expected digest below can be checked
    against the standard rather than against this program's own output — which
    is the only way a self-test means anything. -/
private def probeInput : String := "abc"

/-- SHA-256("abc"), FIPS 180-4 §D.1. -/
private def probeDigest : String :=
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

/-! ## Reading a tool's answer -/

/-- The digest out of a line the tool printed.

    Every candidate below writes `<digest>  <path>`, so the answer is the first
    whitespace-delimited field of the first line. Taken by splitting rather than
    by a fixed width, because a tool that printed something else entirely
    should reach `Sha256.parse` and be refused there, not be silently truncated
    to sixty-four characters of whatever it said.

    GNU `sha256sum` prefixes the whole line with a backslash when the file name
    contains a backslash or a newline. That makes the first field 65 characters,
    which `Sha256.parse` refuses — the correct outcome: a release asset whose
    name contains a newline is not one to describe in a signed manifest. -/
private def digestField (text : String) : String :=
  let firstLine := (text.splitOn "\n").headD ""
  ((firstLine.trimAscii.toString.splitOn " ").headD "").trimAscii.toString

/-- One way of asking for a SHA-256, as a command and the arguments that come
    before the path.

    `sha256sum` first because it is what Linux runners have and it does one
    thing. `shasum -a 256` is the macOS fallback; its default is SHA-1, which is
    exactly why the probe exists.

    Public, and `resolveFrom` takes the list, so a test can hand this the tool
    that is not installed and the tool that answers with the wrong function.
    Both are refusals that cannot be reached by removing something from the
    machine the tests run on. -/
structure Candidate where
  command : String
  leadingArgs : Array String
  deriving Repr

def digestCandidates : List Candidate :=
  [{ command := "sha256sum", leadingArgs := #[] },
   { command := "shasum", leadingArgs := #["-a", "256"] }]

/-- A digest tool that has been asked for a known answer and gave it.

    Private constructor: the point of this module is that no value of this type
    exists until the probe has passed, so a caller cannot hold an unverified
    tool. Resolved once per run and carried, because the probe is a process
    spawn and the alternative is one per asset. -/
structure Digester where
  private mk ::
  command : String
  leadingArgs : Array String

/-- Ask one candidate for the digest of the probe file. Returns the reason it
    is unusable, or nothing if it answered correctly. -/
private def probe (candidate : Candidate) (probePath : String) :
    IO (Option String) := do
  match ← succeeded candidate.command (candidate.leadingArgs.push probePath) with
  | .error message => return some message
  | .ok output =>
      let answered := digestField output.stdout
      if answered == probeDigest then return none
      else return (some
        s!"'{candidate.command}' is on PATH but does not compute SHA-256: asked for the digest of the three bytes 'abc' it answered '{answered}', and SHA-256 of that input is {probeDigest} (FIPS 180-4 D.1). A tool whose SHA-256 mode is not SHA-256 — the usual cause is a 'shasum' that ignores -a 256, or a wrapper — would fill a signed manifest with digests of the wrong function, and nothing downstream would notice. Repair the installation rather than working around this.")

/-- Find a digest tool among `candidates` and establish that it computes
    SHA-256, or refuse.

    Every candidate is tried and every reason collected, so the refusal names
    what was wrong with each rather than only the last: "no sha256sum, and the
    shasum that is there is broken" and "neither is installed" have different
    remedies. -/
def Digester.resolveFrom (candidates : List Candidate) : IO (Except String Digester) := do
  -- Creating and writing the probe file is filesystem work, and a read-only
  -- temporary directory or a full disk would otherwise throw straight past
  -- every caller: an escaping `IO.Error` is a backtrace and a status outside
  -- the three this tool documents, which is not a decision. It becomes a
  -- refusal saying which step could not run.
  match ← (do
      let probeDir ← IO.FS.createTempDir
      IO.FS.writeFile ((probeDir / "probe").toString) probeInput
      return probeDir).toBaseIO with
  | .error error =>
      return .error s!"the digest tool could not be checked: writing the known-answer probe failed ({error}). The tool is asked for the digest of a known input before any release byte reaches it, so a probe that cannot be written is a check that cannot run — which is a refusal, not a reason to trust the tool for its name."
  | .ok probeDir =>
      let probePath := (probeDir / "probe").toString
      try
        let mut reasons : Array String := #[]
        for candidate in candidates do
          match ← probe candidate probePath with
          | none => return .ok ⟨candidate.command, candidate.leadingArgs⟩
          | some reason => reasons := reasons.push reason
        return .error
          s!"no working SHA-256 tool: {String.intercalate " Also, " reasons.toList} Install coreutils (Linux) or use the system shasum (macOS). The digest check is mandatory and cannot be skipped — a release described by digests nothing computed is not a smaller claim, it is a signed claim that nothing was checked."
      finally
        try IO.FS.removeDirAll probeDir catch _ => pure ()

def Digester.resolve : IO (Except String Digester) :=
  Digester.resolveFrom digestCandidates

/-! ## What may be hashed -/

/-- Why a path is not something to hash, or nothing if it is an ordinary file.

    Checked without following symbolic links, and that is the whole point:
    `metadata` follows them, so a link in the release directory pointing at a
    file outside it would be typed as an ordinary file, hashed through the link,
    and described in the signed manifest as an asset of this release. What is
    published is the link, whose bytes are the target's path. The two are
    different things and only one of them is what the manifest would claim.

    A directory is refused for the same reason in the opposite direction: the
    digest tools report it as an error, but reporting it here says which path
    and why. -/
def unhashableReason (path : String) : IO (Option String) := do
  match ← (System.FilePath.symlinkMetadata path).toBaseIO with
  | .error error =>
      return some s!"'{path}' could not be read ({error})."
  | .ok metadata =>
      match metadata.type with
      | .file => return none
      | .dir => return some s!"'{path}' is a directory, not a file."
      | .symlink => return some s!"'{path}' is a symbolic link. A release directory holds the bytes it publishes; a link would be described in the manifest by the digest of whatever it points at, while what a consumer receives is the link. Replace it with the file itself."
      | .other => return some s!"'{path}' is neither an ordinary file nor a directory — a device, a socket or a named pipe. Nothing in a release is one of those, and hashing it would either block or describe something that is not a file."

/-! ## The digest -/

/-- A path the digest tool cannot read as anything but a path.

    Two ways a bare path stops being one. A leading `-` is an option, and every
    tool here would either reject it or accept it as a flag it happens to know.
    A path that is exactly `-` is *stdin* to every one of them — and stdin is
    `/dev/null` for everything this module spawns, so `sha256sum -` succeeds and
    answers with the digest of nothing: a real digest, of the right shape, of
    the wrong bytes, exiting zero. That is a fail-open of exactly the kind this
    port exists to remove, and the fix is a prefix rather than a refusal: a
    relative path prefixed with a dot and a separator names the file
    unambiguously, and there is no reason to forbid a name the filesystem
    allows.

    Absolute paths are already unambiguous and are left alone, so the common
    case reads unchanged in a log. -/
private def unambiguousPath (path : String) : String :=
  if path.startsWith "/" then path else "./" ++ path

/-- The SHA-256 of one file.

    Every failure is a value: the path is not an ordinary file, the tool could
    not be run or did not finish, it ran and failed, or it answered something
    that is not a digest. None of them can be mistaken for an answer, because
    the answer's type has no other inhabitant. -/
def Digester.digest (digester : Digester) (path : String) :
    IO (Except String Sha256) := do
  match ← unhashableReason path with
  | some reason => return .error reason
  | none =>
      match ← succeeded digester.command (digester.leadingArgs.push (unambiguousPath path)) with
      | .error message => return .error message
      | .ok output =>
          -- The tool's own status was zero, so this is not a failure it
          -- reported — it is output this program cannot read as a digest, which
          -- means the tool is not the one it was taken for.
          return (Sha256.parse s!"the digest of '{path}'" (digestField output.stdout)).mapError
            fun message =>
              s!"{message} '{digester.command}' exited zero and printed this, so it is not reporting a failure — it is not the tool it was taken for. Check what is first on PATH under that name."

end Release
