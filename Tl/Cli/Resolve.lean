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
  if tok.startsWith "tl-" then
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

/-- The ADR-0013 actor chain. -/
def resolveActor (flag : Option String) : IO String := do
  if let some a := flag then
    if a != "me" then return a
  if let some a := ← IO.getEnv "TL_ACTOR" then
    if !a.isEmpty then return a
  let git ← IO.Process.output { cmd := "git", args := #["config", "--get", "user.email"] }
    |>.toBaseIO
  if let .ok out := git then
    if out.exitCode == 0 && !out.stdout.trimAscii.toString.isEmpty then
      return out.stdout.trimAscii.toString
  let user := (← IO.getEnv "USER").getD ((← IO.getEnv "LOGNAME").getD "unknown")
  let host ← IO.Process.output { cmd := "hostname", args := #[] } |>.toBaseIO
  let hostname := match host with
    | .ok out => if out.exitCode == 0 then out.stdout.trimAscii.toString else "localhost"
    | .error _ => "localhost"
  return s!"{user}@{hostname}"

end Tl.Cli
