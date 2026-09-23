/-
Signing the commit that publishes a formula into the Homebrew tap.

A formula is executable installation code, not a pointer to an artifact: whoever
can change it can change a url and the digest it pins together, or drop the
cosign verification `install` performs. The release artifacts are authenticated
by their Sigstore signatures; the formula that fetches them is authenticated, as
far as this tool can make it, by the signature on the tap commit that carries
it. The two are separate claims and neither stands in for the other.

The policy is that every tap commit this tool publishes is signed by one
explicitly selected release signer, and that nothing ambient can change that:

- The signer is a tracked record — committer name, committer email, and the SSH
  public key — named on the command line, never discovered from configuration.
- The private key is a file named on the command line. It must open without a
  passphrase, and its public half must be the recorded key; both are checked
  before anything is written, so a key that would fail or prompt is a refusal
  that names the fix rather than a publish that stops halfway.
- Every signing setting git reads is passed with `-c`, which outranks every
  configuration file, and the identity is also pinned through the
  `GIT_AUTHOR_*`/`GIT_COMMITTER_*` variables, which outrank `-c user.*`.
  `commit -S` fails the commit when signing fails, so there is no unsigned
  fallback to reach.
- Before the push, every commit the push would publish is verified against an
  allowed-signers file holding only the recorded key. That is what stops a
  retry from pushing an unsigned commit an earlier run left behind.

What this does not establish, stated rather than implied: nothing downstream
enforces the signature. Homebrew does not verify tap commit signatures, and a
GitHub "require signed commits" rule accepts any signature GitHub can verify,
not this signer in particular. The check here is the one enforcement point, and
it constrains this tool rather than an attacker holding the tap credential.
-/
import release.Command
import release.Json
import release.Process

namespace Release

namespace TapSigning

open Lean (Json)

/-! ## Which git can sign -/

/-- The first git release that signs commits with an SSH key (`gpg.format=ssh`).
    This is higher than the git floor tl itself runs on, and it binds only the
    release tool's tap publication. -/
def sshSigningFloor : Nat × Nat := (2, 34)

/-- The major and minor numbers from `git version`'s output.

    Real spellings carry suffixes — `git version 2.39.3 (Apple Git-146)`,
    `git version 2.34.1.windows.1` — so only the first two numbers are read. -/
def parseGitVersion (output : String) : Option (Nat × Nat) :=
  match output.trimAscii.toString.splitOn " " with
  | "git" :: "version" :: number :: _ =>
      match number.splitOn "." with
      | major :: minor :: _ => do
          let major ← major.toNat?
          let minor ← minor.toNat?
          return (major, minor)
      | _ => none
  | _ => none

/-- Whether a git of this version can sign with an SSH key. -/
def signsWithSsh (version : Nat × Nat) : Bool :=
  let (major, minor) := version
  let (floorMajor, floorMinor) := sshSigningFloor
  major > floorMajor || (major == floorMajor && minor ≥ floorMinor)

/-! ## The signer record -/

/-- Who signs tap commits: the committer identity the commits carry, and the
    public half of the key that signs them. -/
structure Signer where
  name : String
  email : String
  keyType : String
  keyBody : String
  deriving Repr, Inhabited, DecidableEq

/-- The key as an OpenSSH public-key line, without a comment. -/
def Signer.publicKey (signer : Signer) : String :=
  s!"{signer.keyType} {signer.keyBody}"

/-- An allowed-signers file naming this signer and nothing else, and only for
    git's signing namespace. -/
def Signer.allowedSigners (signer : Signer) : String :=
  s!"{signer.email} namespaces=\"git\" {signer.publicKey}\n"

/-- The one key type accepted. Narrower than what git and GitHub accept, on
    purpose: a release signer is generated once for this purpose, and one type
    means one shape to check. -/
def acceptedKeyType : String := "ssh-ed25519"

private def printable (c : Char) : Bool := c.toNat ≥ 0x20 && c.toNat ≤ 0x7e

private def base64Char (c : Char) : Bool :=
  c.isAlphanum || c == '+' || c == '/' || c == '='

/-- A committer name git will record as given: printable ASCII, no angle
    brackets, and no surrounding spaces, which git would strip. -/
def nameAccepted (name : String) : Bool :=
  !name.isEmpty && name.all (fun c => printable c && c != '<' && c != '>') &&
    !name.startsWith " " && !name.endsWith " "

/-- A committer email that is also a literal allowed-signers principal: the
    principal field is a pattern list, so `,`, `*`, `?` and `!` would widen it,
    and a space or quote would end it. -/
def emailAccepted (email : String) : Bool :=
  (email.splitOn "@").length == 2 &&
    email.all (fun c => printable c && !" <>,*?!\"".contains c)

/-- Parse `type base64`, refusing a comment or anything else after the key. -/
def parsePublicKey (what : String) (text : String) : Except String (String × String) :=
  match text.splitOn " " with
  | [keyType, keyBody] =>
      if keyType != acceptedKeyType then
        .error s!"{what}: is a {keyType} key. The tap signer is an {acceptedKeyType} key; generate one with `ssh-keygen -t ed25519` and record its public half."
      else if keyBody.isEmpty || !keyBody.all base64Char then
        .error s!"{what}: the key body is not base64. Copy the second field of the .pub file exactly."
      else .ok (keyType, keyBody)
  | _ =>
      .error s!"{what}: is not '<type> <base64>'. Record the first two fields of the .pub file, without its comment."

def Signer.parse (document : String) (text : String) : Except String Signer := do
  let cursor : Cursor := { document }
  let root ← parseDocument cursor text
  let name ← nonEmptyStringField cursor root "name"
  unless nameAccepted name do
    (cursor.at "name").fail "is not a committer name git records unchanged. Use printable ASCII without '<', '>' or surrounding spaces."
  let email ← nonEmptyStringField cursor root "email"
  unless emailAccepted email do
    (cursor.at "email").fail "is not a plain address. Use one '@' and no spaces, quotes, angle brackets, or ',', '*', '?', '!' — the address is also the allowed-signers principal, where those characters are pattern syntax."
  let (keyType, keyBody) ←
    parsePublicKey (cursor.at "publicKey").render (← nonEmptyStringField cursor root "publicKey")
  return { name, email, keyType, keyBody }

/-! ## Preparing to sign -/

/-- Everything a signed commit and its verification need, resolved once. -/
structure Prepared where
  signer : Signer
  /-- The private key, as an absolute path: git runs inside the tap checkout,
      and a relative path would resolve there. -/
  keyPath : String
  allowedSignersPath : String
  /-- An empty directory, so no hook in the checkout or the operator's
      configuration runs during the commit. `--no-verify` skips only
      `pre-commit` and `commit-msg`. -/
  hooksPath : String
  /-- The recorded key's `SHA256:` fingerprint, as git reports a verified key. -/
  fingerprint : String

/-- Run a tool, requiring it to finish and exit zero, with a refusal naming what
    was being established. -/
private def ranOk (what : String) (command : String) (args : Array String) :
    Decision ProcessOutput := do
  match ← ofIO (do return .ok (← Release.run command args)) with
  | .completed output =>
      if output.exitCode == 0 then return output
      else
        let detail := if output.stderr.trimAscii.isEmpty then output.stdout else output.stderr
        decline s!"{what}: '{command}' exited {output.exitCode}: {detail.trimAscii}"
  | outcome => decline s!"{what}: {outcome.failureMessage.getD s!"'{command}' could not be run"}"

/-- Refuse unless the git on PATH can sign with an SSH key. -/
def requireSigningGit : Decision Unit := do
  let output ← ofIO (succeededGit #["version"])
  match parseGitVersion output.stdout with
  | none =>
      decline s!"`git version` answered '{output.stdout.trimAscii}', which does not read as a version. Tap commits are signed with an SSH key, which needs git {sshSigningFloor.1}.{sshSigningFloor.2} or newer; put such a git first on PATH."
  | some version =>
      unless signsWithSsh version do
        decline s!"git {version.1}.{version.2} cannot sign a commit with an SSH key, and tap commits are always signed. Put git {sshSigningFloor.1}.{sshSigningFloor.2} or newer first on PATH and re-run; nothing has been written."

/-- Read the signer record and check the private key against it, then write the
    verification files into `scratch`.

    The key is opened with an explicit empty passphrase, so a key that needs one
    is a refusal here rather than a prompt during the commit. -/
def prepare (signerPath keyPath scratch : String) : Decision Prepared := do
  let signer ← readParsed signerPath Signer.parse
  requireSigningGit
  unless ← ofIO (do return .ok (← System.FilePath.pathExists keyPath)) do
    decline s!"there is no signing key at {keyPath}. Tap commits are signed by the release signer recorded in {signerPath}; pass its private key with --signing-key. There is no unsigned mode."
  let keyPath ← attempt s!"resolving {keyPath}" (IO.FS.realPath keyPath)
  let keyPath := keyPath.toString
  let derived ← ranOk
    s!"the signing key at {keyPath} could not be opened without a passphrase or interaction. A release signer must sign non-interactively: use an unencrypted key readable only by its owner (mode 600)"
    "ssh-keygen" #["-y", "-P", "", "-f", keyPath]
  match derived.stdout.trimAscii.toString.splitOn " " with
  | keyType :: keyBody :: _ =>
      unless keyType == signer.keyType && keyBody == signer.keyBody do
        decline s!"the signing key at {keyPath} is not the release signer recorded in {signerPath}. Its public half is {keyType} {keyBody}. Pass the key that record names, or, if the signer was deliberately rotated, update the record in a reviewed change first."
  | _ =>
      decline s!"`ssh-keygen -y` did not print a public key for {keyPath}. Check that the file is an OpenSSH private key."
  let allowedSignersPath := scratch ++ "/allowed_signers"
  let publicPath := scratch ++ "/signer.pub"
  let hooksPath := scratch ++ "/hooks"
  attempt s!"writing the verification files under {scratch}" (do
    IO.FS.writeFile allowedSignersPath signer.allowedSigners
    IO.FS.writeFile publicPath (signer.publicKey ++ "\n")
    IO.FS.createDirAll hooksPath)
  let listed ← ranOk s!"computing the fingerprint of the key recorded in {signerPath}"
    "ssh-keygen" #["-l", "-f", publicPath]
  match listed.stdout.trimAscii.toString.splitOn " " with
  | _ :: fingerprint :: _ =>
      return { signer, keyPath, allowedSignersPath, hooksPath, fingerprint }
  | _ =>
      decline s!"`ssh-keygen -l` did not print a fingerprint for the key recorded in {signerPath}."

/-- A private directory for the signing material, removed on every path out. -/
def withScratch (body : String → Decision α) : Decision α := do
  let scratch ← attempt "creating a private directory for the signing material; check the temporary directory"
    IO.FS.createTempDir
  try body scratch.toString
  finally
    try IO.FS.removeDirAll scratch catch _ => pure ()

/-! ## Signing -/

/-- The `-c` settings for the commit. Each one outranks the same key in any
    configuration file, so nothing the operator or the checkout configures can
    choose another key, format, program, or hook. -/
def commitConfig (prepared : Prepared) : List String :=
  ["-c", s!"user.name={prepared.signer.name}", "-c", s!"user.email={prepared.signer.email}",
   "-c", "gpg.format=ssh", "-c", s!"user.signingkey={prepared.keyPath}",
   "-c", "gpg.ssh.program=ssh-keygen", "-c", "commit.gpgsign=true",
   "-c", s!"core.hooksPath={prepared.hooksPath}"]

/-- The identity again, as the variables that outrank `-c user.*`.

    `SSH_AUTH_SOCK` is left alone. `ssh-keygen -Y sign` consults an agent only
    for the key the named file holds, so an agent can hold that key or not but
    cannot substitute another; and the push needs the operator's credentials. -/
def commitEnvironment (signer : Signer) : Array (String × Option String) :=
  #[("GIT_AUTHOR_NAME", some signer.name), ("GIT_AUTHOR_EMAIL", some signer.email),
    ("GIT_COMMITTER_NAME", some signer.name), ("GIT_COMMITTER_EMAIL", some signer.email)]

/-! ## Verifying what the push would publish -/

/-- The `-c` settings for verification: the recorded key is the only one git may
    accept, and `log.showSignature` cannot interleave its own report with the
    format below. -/
def verificationConfig (prepared : Prepared) : List String :=
  ["-c", "gpg.format=ssh", "-c", "gpg.ssh.program=ssh-keygen",
   "-c", s!"gpg.ssh.allowedSignersFile={prepared.allowedSignersPath}",
   "-c", "log.showSignature=false"]

/-- `git log`'s format for one commit: hash, signature status, signing-key
    fingerprint, committer email. -/
def observationFormat : String := "--format=%H%x09%G?%x09%GK%x09%ce"

/-- One commit, as git reports its signature. -/
structure Observed where
  commit : String
  status : String
  key : String
  committer : String
  deriving Repr, DecidableEq

def parseObserved (line : String) : Option Observed :=
  match line.splitOn "\t" with
  | [commit, status, key, committer] => some { commit, status, key, committer }
  | _ => none

/-- Whether a commit may be published: a good signature (`G`, which git reports
    only for a key in the allowed-signers file), by the recorded key, on a
    commit carrying the recorded committer. -/
def accepted (signer : Signer) (fingerprint : String) (observed : Observed) : Bool :=
  observed.status == "G" && observed.key == fingerprint && observed.committer == signer.email

/-- **A commit is accepted exactly when it has a good signature by the recorded
    key and carries the recorded committer.** Left to right is the policy; it is
    stated so that a later edit cannot quietly accept `U` (a valid signature by
    a key the file does not name) or drop the fingerprint comparison. -/
theorem accepted_iff (signer : Signer) (fingerprint : String) (observed : Observed) :
    accepted signer fingerprint observed = true ↔
      observed.status = "G" ∧ observed.key = fingerprint ∧ observed.committer = signer.email := by
  simp only [accepted, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- Why a commit was not accepted, for the refusal. -/
def Observed.reason (signer : Signer) (fingerprint : String) (observed : Observed) : String :=
  let short := observed.commit.take 12
  if observed.status == "N" then s!"{short} is not signed"
  else if observed.status != "G" || observed.key != fingerprint then
    s!"{short} is not signed by the release signer (git reports '{observed.status}' for key '{observed.key}')"
  else s!"{short} is committed by {observed.committer}, not {signer.email}"

/-- Refuse unless every commit in `range` is accepted. -/
def verifyRange (tapPath : String) (prepared : Prepared) (range : String) (whenRefused : String) :
    Decision Unit := do
  let output ← ofIO (succeededGit ((["-C", tapPath] ++ verificationConfig prepared ++
    ["log", observationFormat, range, "--"]).toArray))
  let lines := (output.stdout.splitOn "\n").filter (· != "")
  let mut refused : List String := []
  for line in lines do
    match parseObserved line with
    | none => decline s!"`git log` described a commit as '{line}', which is not the four fields asked for; nothing was pushed."
    | some observed =>
        unless accepted prepared.signer prepared.fingerprint observed do
          refused := refused ++ [observed.reason prepared.signer prepared.fingerprint]
  unless refused.isEmpty do
    decline s!"{String.intercalate "; " refused}. {whenRefused}"

end TapSigning

end Release
