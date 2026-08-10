/-
The signing pin, in a form a POSIX shell can read without a JSON parser.

`scripts/verify-release-artifacts.sh` needed `python3` for exactly one thing:
reading two strings out of `release/identity.json`. It could not scrape them,
and the comment there explains why — the certificate expression contains `\.`,
which JSON stores as `\\.`, so a text scrape hands cosign a pattern meaning
"a literal backslash followed by any character". That matches no real
certificate, so the verifier would reject every genuine signature while looking
exactly like a verification failure rather than a broken verifier.

But that verifier is a user-facing path: it is what VERIFYING.md tells a reader
to run, and requiring an interpreter to check a signature is a dependency this
project chose for its own convenience and charged to the user. So the pin is
published in a form that needs no parser at all.

`release/identity.pin` is exactly two lines: the OIDC issuer, then the
certificate identity expression. It is **data**, never sourced and never
evaluated — the shell reads it with `IFS= read -r` from one opened descriptor
and passes the values to cosign as arguments. Both properties matter: `read -r`
does not interpret backslashes, which is what makes the escaped expression
survive; and one descriptor means both lines come from a single read of a
single file, so a file replaced between two reads cannot contribute one line
each.

Generating it here rather than committing it by hand is what keeps it honest:
the values come from `release/identity.json`, which is the machine-readable pin
every other consumer already agrees with, and this generator refuses to write a
pin the shell could not read back unambiguously.
-/
import release.Command
import release.Model

namespace Release

/-- Two lines, and the file must not be able to say anything else. A value
    carrying a newline would silently become two lines and shift the file's
    meaning; a carriage return would ride into the value cosign is given and
    make the expression match nothing. Both are refused at generation, which is
    the only moment anyone can fix them. -/
private def pinnableValue (what : String) (value : String) : Except String String :=
  if value.isEmpty then
    .error s!"{what} is empty. An empty issuer does not constrain the certificate at all, and an empty expression matches every certificate — either is a pin that checks nothing."
  else if value.any (fun c => c == '\n' || c == '\r') then
    .error s!"{what} contains a line break. release/identity.pin is exactly two lines, so a value carrying one would change what the file says rather than what it means; repair release/identity.json."
  else if value.any (fun c => c.toNat < 0x20 || c.toNat > 0x7e) then
    .error s!"{what} contains a character outside printable ASCII. The pin is read by a POSIX shell and handed to cosign verbatim; anything the terminal or the shell might reinterpret does not belong in it."
  else .ok value

/-- cosign matches unanchored. Both anchors are required, and the tail one is
    not pedantry: a git tag name may contain `/`, so a head-only expression
    accepts an identity that merely *begins* with this repository's. -/
private def anchoredExpression (expression : String) : Except String String :=
  if !expression.startsWith "^" then
    .error s!"the certificate identity expression is not anchored at ^ ('{expression}'). cosign matches unanchored, so this would accept a certificate whose identity merely contains this repository's."
  else if !expression.endsWith "$" then
    .error s!"the certificate identity expression is not anchored at $ ('{expression}'). cosign matches unanchored, so this would accept any identity that merely begins with this one — and a tag name may contain '/', so trailing content is reachable."
  else .ok expression

/-- The pin's bytes: issuer, expression, each on its own line. -/
def renderPin (identity : Identity) : Except String String := do
  let issuer ← pinnableValue "the OIDC issuer" identity.certificateOidcIssuer
  let expression ← pinnableValue "the certificate identity expression"
    identity.certificateIdentityRegexp
  let expression ← anchoredExpression expression
  return issuer ++ "\n" ++ expression ++ "\n"

/-- Read a pin back, applying every rule the shell verifier applies. Kept here
    so the shell's refusals and this tool's have one definition to agree with:
    the generator cannot emit a pin the reader would reject. -/
def parsePin (document : String) (text : String) : Except String Identity := do
  let lines := text.splitOn "\n"
  -- A well-formed file ends in a newline, so splitting gives a trailing "".
  let (rows, trailing) :=
    match lines.reverse with
    | "" :: rest => (rest.reverse, true)
    | _ => (lines, false)
  if !trailing then
    .error s!"{document}: does not end with a newline. The pin is a two-line text file; a truncated write is the usual cause."
  match rows with
  | [issuerLine, expressionLine] =>
      let issuer ← pinnableValue s!"{document}: the OIDC issuer (line 1)" issuerLine
      let expression ← pinnableValue s!"{document}: the certificate identity expression (line 2)"
        expressionLine
      let expression ← anchoredExpression expression
      return { repository := "", npmPackage := "", releaseWorkflow := ""
               certificateOidcIssuer := issuer, certificateIdentityRegexp := expression }
  | [] | [_] =>
      .error s!"{document}: has {rows.length} line(s); the pin is exactly two — the OIDC issuer, then the certificate identity expression. A pin missing either half checks nothing."
  | _ =>
      .error s!"{document}: has {rows.length} lines; the pin is exactly two. Extra lines are refused rather than ignored: a reader that skipped them could be handed a second, different pin below the one it used."

private def writePinCommand : Command := {
  name := "write-pin"
  arguments := "<identity.json> <output.pin>"
  summary := "Write the two-line signing pin the shell verifier reads, from the machine-readable identity."
  run := fun args => do
    match args with
    | [identityPath, outputPath] =>
        match ← readTextFile identityPath with
        | .error message => refuse s!"tlrelease write-pin: {message}"
        | .ok text =>
            match Identity.parse identityPath text >>= renderPin with
            | .error message => refuse s!"tlrelease write-pin: {message}"
            | .ok pin =>
                -- Read back through the same rules the shell applies, before
                -- the file exists. A generator that can emit something its own
                -- reader refuses is a generator that turns a repair into an
                -- outage.
                match parsePin outputPath pin with
                | .error message =>
                    refuse s!"tlrelease write-pin: refusing to write a pin this reader would reject: {message}"
                | .ok _ =>
                    -- A failed write is a refusal, not an exception. An
                    -- unreadable directory or a full disk would otherwise
                    -- escape as a Lean backtrace, which is the traceback-for-a-
                    -- message regression this port exists to remove.
                    -- Written beside the target and renamed over it. The pin
                    -- is a trust anchor: a partial write straight onto the
                    -- path would leave a truncated file where a valid one had
                    -- been, and the verifier would then refuse every genuine
                    -- signature. `rename` within a directory is atomic, so a
                    -- reader sees either the old pin or the new one.
                    let temporary := outputPath ++ ".tmp"
                    match ← (try
                        IO.FS.writeFile temporary pin
                        IO.FS.rename temporary outputPath
                        pure (Except.ok ())
                      catch error => do
                        try IO.FS.removeFile temporary catch _ => pure ()
                        pure (Except.error s!"could not write {outputPath}: {error}")) with
                    | .error message => refuse s!"tlrelease write-pin: {message}"
                    | .ok () =>
                        IO.println s!"tlrelease write-pin: wrote {outputPath}"
                        return 0
    | _ => misuse "usage: tlrelease write-pin <identity.json> <output.pin>" }

private def checkPinCommand : Command := {
  name := "check-pin"
  arguments := "<identity.json> <pin>"
  summary := "Refuse if the two-line pin has drifted from the machine-readable identity."
  run := fun args => do
    match args with
    | [identityPath, pinPath] =>
        match ← readTextFile identityPath, ← readTextFile pinPath with
        | .error message, _ => refuse s!"tlrelease check-pin: {message}"
        | _, .error message => refuse s!"tlrelease check-pin: {message}"
        | .ok identityText, .ok pinText =>
            match Identity.parse identityPath identityText >>= renderPin with
            | .error message => refuse s!"tlrelease check-pin: {message}"
            | .ok expected =>
                if expected == pinText then
                  IO.println s!"tlrelease check-pin: {pinPath} matches {identityPath}"
                  return 0
                else
                  refuse s!"tlrelease check-pin: {pinPath} is not what {identityPath} produces. Regenerate it with `tlrelease write-pin {identityPath} {pinPath}` and commit the result; the pin is what the shell verifier checks signatures against, so a stale one is a check against the wrong identity."
    | _ => misuse "usage: tlrelease check-pin <identity.json> <pin>" }

def identityCommands : List Command := [writePinCommand, checkPinCommand]

end Release
