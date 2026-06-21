/-
`Tl.Cli.Resolve` — id/slug resolution (ADR-0007 §resolution) and the actor
chain (ADR-0013).

The `tl-` prefix is the unconditional discriminator: a token beginning with
it is an id — stripped, ASCII-case-folded, Crockford-symbol-aliased
(`o`→`0`, `i`/`l`→`1`), then matched as a full id or unambiguous prefix; any
other token is a slug (case-folded, never symbol-aliased — slugs are author
intent). `>1` match → `ambiguous-id` naming the full `tl-…` candidates.

The actor resolves first-hit-wins: `--assignee` (unless `me`) → `TL_ACTOR` →
git `user.email` → `<os-user>@<hostname>`; `me` resolves through the same
chain (ADR-0013).
-/
import Tl.Cli.Project
import Tl.Sync.Ref  -- `runBounded`: a hung git-config/hostname must not wedge a verb

namespace Tl.Cli

open Tl.Store
open Tl.Kernel
open Tl.Format

/-- Normalize a typed id token: case-fold + Crockford symbol aliases. -/
def normalizeIdToken (s : String) : String :=
  String.ofList (s.toList.map (fun c =>
    match c.toLower with
    | 'o' => '0'
    | 'i' | 'l' => '1'
    | c' => c'))

private def ambiguous (input : String) (candidates : List IssueId) : Tl.Error :=
  { code := .ambiguousId
    message := s!"'{input}' matches {candidates.length} issues — use a longer prefix or the full id: {String.intercalate ", " (candidates.map displayId)}"
    context := [("input", .str input),
                ("candidates", .arr (candidates.map (Lean.Json.str ∘ displayId)).toArray)] }

private def notFound (input : String) (what : String) : Tl.Error :=
  { code := .notFound
    message := s!"no issue {what} '{input}' — check `tl list`, or use the full tl-… id"
    context := [("input", .str input)] }

/-- Resolve a positional issue token against a state (ADR-0007). -/
def resolveToken (s : State) (tok : String) : Except Tl.Error IssueId :=
  -- the discriminator is case-insensitive like the rest of id input
  -- (ADR-0007: ids case-fold; a slug can never begin with tl-)
  if tok.toLower.startsWith "tl-" then
    let pref := normalizeIdToken (tok.drop 3 |>.toString)
    if pref.isEmpty then
      .error (notFound tok "with id")
    else
      match s.presentIssues.filter (·.startsWith pref) with
      | [i] => .ok i
      | [] => .error (notFound tok "with id")
      | many => .error (ambiguous tok many)
  else
    let slug := tok.toLower
    let bySlug := s.presentIssues.filter (fun i =>
      ((s.issueData i).slug.value.getD none) == some slug)
    match bySlug with
    | [i] => .ok i
    | [] => .error (notFound tok "with slug")
    | many => .error (ambiguous tok many)

/-- The ADR-0013 actor chain. `repoDir` (the `--dir` override, when given) is where
    the git-config read runs via `git -C` — so under `--dir repoB` the actor comes
    from repoB's `user.email`, not the process cwd's repo. -/
def resolveActor (flag : Option String) (repoDir : Option String := none) : IO String := do
  if let some a := flag then
    if a != "me" then return a
  if let some a := ← IO.getEnv "TL_ACTOR" then
    if !a.isEmpty then return a
  -- read user.email from the target repo (`git -C <repoDir>` walks up to its repo
  -- root), not the process cwd — so `--dir repoB` records repoB's identity. Bound
  -- the read: a hung credential/exec helper (a config `include` firing one) or an
  -- NFS-hung dir must not wedge a mutating verb — on timeout/error we fall through
  -- the ADR-0013 chain (5s, like the local-git bound).
  let cArgs := match repoDir with | some p => #["-C", p] | none => #[]
  let git ← (Tl.Sync.runBounded
      { cmd := "git", args := cArgs ++ #["config", "--get", "user.email"] } ByteArray.empty 5000).toBaseIO
  if let .ok (0, outBytes, _) := git then
    if let some s := String.fromUTF8? outBytes then
      let email := s.trimAscii.toString
      if !email.isEmpty then return email
  let user := (← IO.getEnv "USER").getD ((← IO.getEnv "LOGNAME").getD "unknown")
  let host ← (Tl.Sync.runBounded { cmd := "hostname", args := #[] } ByteArray.empty 5000).toBaseIO
  let mut hostname := "localhost"
  if let .ok (0, outBytes, _) := host then
    if let some s := String.fromUTF8? outBytes then
      let h := s.trimAscii.toString
      unless h.isEmpty do hostname := h
  return s!"{user}@{hostname}"

end Tl.Cli
