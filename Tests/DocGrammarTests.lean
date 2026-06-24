/-
`Tests.DocGrammarTests` — the docs↔grammar drift guard (ADR-0011/ADR-0020).

`Tests.GrammarTests` pins parser↔schema agreement (both read `commandSpecs`, so
they cannot drift). What it does *not* cover is the prose: the 2026-06-16 gap
analysis found docs presenting landed surface as future and naming unbuilt
flags. This guards that class — the authoritative shipped-surface block in
`docs/vision.md` must equal `Tl.Cli.Grammar.commandSpecs`, so the docs can no
longer silently over-promise (a fenced verb/flag absent from the grammar) or
under-document (a shipped verb/flag absent from the block).

Robustness by construction: it reads only the single fenced region delimited by
`<!-- tl:grammar-surface … -->` and compares it against `helpJson` (computed
from the same `commandSpecs` the parser reads). The narrative tables — which
intentionally name destination-surface verbs (`edit`, `--licenses`, `ready
--assignee`) — are outside the region and never read, so they cannot
false-positive. The comparison is set *equality*, so drift in either direction
fails. Tested I/O shell (ADR-0004); no Mathlib (ADR-0009).
-/
import Tl.Cli.Grammar
import Tests.Harness

namespace Tl.Tests

open System (FilePath)
open Tl.Cli
open Lean (Json)

private def jGet (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
private def jArr (j : Json) (k : String) : List Json :=
  ((jGet j k).bind (fun v => v.getArr?.toOption)).map (·.toList) |>.getD []
private def jStr (j : Json) (k : String) : Option String :=
  (jGet j k).bind (fun v => v.getStr?.toOption)

/-- Does `hay` contain `needle` as a substring? -/
private def lineHas (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- Order-independent multiset equality for the flag/command name lists. The
    length guard rejects a duplicated entry that would otherwise pass `contains`
    both ways. -/
private def sameSet (a b : List String) : Bool :=
  a.all (fun x => b.contains x) && b.all (fun x => a.contains x) && a.length == b.length

/-- Parse one surface line: the leading non-flag tokens are the command key
    (e.g. `dep add`), and every remaining token must be a `--flag` (kept verbatim
    with its dashes). A positional or value after a flag is a malformed line (the
    block carries neither). -/
private def parseSurfaceLine (line : String) : Except String (String × List String) :=
  let toks := (line.splitOn " ").filter (· != "")
  let cmdToks := toks.takeWhile (fun t => !(t.startsWith "-"))
  let rest := toks.dropWhile (fun t => !(t.startsWith "-"))
  if rest.all (fun t => t.startsWith "--") then
    .ok (String.intercalate " " cmdToks, rest)
  else
    .error s!"malformed surface line (a positional or value after a flag?): '{line}'"

/-- The shipped surface, materialized from the grammar (the source of truth);
    flag names carry the `--` prefix to match the doc-block tokens verbatim. -/
private def grammarSurface : List (String × List String) :=
  (jArr (helpJson none) "commands").filterMap (fun c =>
    (jStr c "command").map (fun name =>
      (name, (jArr c "flags").filterMap (fun f => (jStr f "name").map ("--" ++ ·)))))

/-- The docs↔grammar drift guard. -/
def docGrammarTests : IO (List Outcome) := do
  let visionPath : FilePath := "docs/vision.md"
  if !(← visionPath.pathExists) then
    return [check "doc-grammar: docs/vision.md present at cwd" false
      s!"could not find {visionPath} under cwd {(← IO.currentDir)} — run tltest from the repo root"]
  let content ← IO.FS.readFile visionPath
  let lines := content.splitOn "\n"
  -- The fenced authoritative region, exclusive of the marker lines.
  let afterStart := (lines.dropWhile (fun l => !(lineHas l "tl:grammar-surface start"))).drop 1
  let region := afterStart.takeWhile (fun l => !(lineHas l "tl:grammar-surface end"))
  -- Keep only the command lines: drop the code-fence markers and blanks. No
  -- trim needed — the tokenizer drops empty tokens, so indented command lines
  -- still parse, while a stray fence line fails loudly rather than passing.
  let cmdLines := region.filter (fun l =>
    !(l.isEmpty) && !(l.startsWith "```") && !(l.startsWith "<!--"))
  let parsed := cmdLines.map parseSurfaceLine
  let parseErrors := parsed.filterMap (fun | .error e => some e | .ok _ => none)
  let docSurface := parsed.filterMap (fun | .ok v => some v | .error _ => none)
  let docCmds := docSurface.map (·.1)
  let gramCmds := grammarSurface.map (·.1)
  let overPromised := docCmds.filter (fun c => !(gramCmds.contains c))
  let underDocumented := gramCmds.filter (fun c => !(docCmds.contains c))
  let mut outs : List Outcome :=
    [ check "vision tl:grammar-surface region parsed the shipped command set"
        (docSurface.length ≥ 30)
        s!"parsed {docSurface.length} commands from the tl:grammar-surface region in docs/vision.md — markers missing, region empty, or not run from the repo root?",
      check "vision surface lines are well-formed (command key + --flags only)"
        parseErrors.isEmpty s!"{parseErrors}",
      check "no command in the vision surface block is unshipped (over-promise guard)"
        overPromised.isEmpty
        s!"docs/vision.md tl:grammar-surface lists {overPromised}, absent from Grammar.commandSpecs — drop them from the block or add the verb to the grammar",
      check "every shipped command is in the vision surface block (under-document guard)"
        underDocumented.isEmpty
        s!"Grammar.commandSpecs has {underDocumented}, absent from the docs/vision.md tl:grammar-surface block — add them" ]
  -- Per-command flag equality, for the commands the grammar actually ships.
  for (cmd, gFlags) in grammarSurface do
    match docSurface.find? (·.1 == cmd) with
    | some (_, dFlags) =>
        outs := outs ++ [check s!"surface flags match grammar for `{cmd}`"
          (sameSet dFlags gFlags)
          s!"vision block lists {dFlags}; grammar has {gFlags} — reconcile the tl:grammar-surface line for `{cmd}`"]
    | none => pure ()
  return outs

end Tl.Tests
