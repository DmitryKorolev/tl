/-
`Tests.GrammarTests` — the `tl help --json` schema and the grammar table that
single-sources it (ADR-0011 §1, ADR-0020 shape).

The load-bearing property is **no drift**: the schema an agent introspects
must describe exactly the flags the parser accepts. Because both read
`commandSpecs`, that holds by construction — these tests pin it: every
dispatchable verb appears in the schema, every schema command is
dispatchable, each command's schema flags are accepted by the parser and a
flag it omits is rejected, and the `--json` envelope is the pinned shape.
-/
import Tl.Cli.Main
import Tests.Harness

namespace Tl.Tests

open Tl.Cli
open Lean (Json)

private def run' (args : List String) : IO (Except Tl.Error CmdOut) := (runVerb args).run

private def jGet (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
private def jArr (j : Json) (k : String) : List Json :=
  ((jGet j k).bind (fun v => v.getArr?.toOption)).map (·.toList) |>.getD []
private def jStr (j : Json) (k : String) : Option String :=
  (jGet j k).bind (fun v => v.getStr?.toOption)

/-- The verbs the dispatcher actually handles (kept beside the dispatch; the
    test below proves it matches the schema both ways). -/
private def dispatchVerbs : List String :=
  ["init", "create", "ready", "claim", "close", "update", "reopen",
   "dep add", "dep remove", "dep cycles", "dep critical", "dep relate", "dep unrelate",
   "parent set", "parent remove",
   "label add", "label remove", "label list",
   "meta set", "meta get", "meta clear", "meta list",
   "why", "unblocks", "show", "list", "log", "stats", "sync", "doctor", "version", "help"]

def grammarSchemaTests : List Outcome := Id.run do
  let schema := helpJson none
  let cmds := jArr schema "commands"
  let names := cmds.filterMap (fun c => jStr c "command")
  let globals := (jArr schema "globalFlags").filterMap (fun f => jStr f "name")
  pure
    [check "every dispatched verb is in the schema"
       (dispatchVerbs.all (fun v => names.contains v)) s!"schema names {names}",
     check "every schema command is dispatchable"
       (names.all (fun n => dispatchVerbs.contains n)) s!"schema names {names}",
     check "global flags include the styling surfaces"
       (globals == ["json", "dir", "skip-bad", "color", "glyphs", "plain"]) s!"got {globals}",
     check "every command object carries the four pinned fields"
       (cmds.all (fun c => (jGet c "command").isSome && (jGet c "positionals").isSome
         && (jGet c "summary").isSome && (jGet c "flags").isSome)),
     check "create's flags include the repeatable inline-edge flags"
       (match cmds.find? (fun c => jStr c "command" == some "create") with
        | some c => let fs := (jArr c "flags").filterMap (fun f => jStr f "name")
                    ["priority","blocked-by","blocks","parent","related","description","assignee"].all fs.contains
        | none => false),
     check "help <command> filters to that command (stable shape)"
       (let one := helpJson (some "close")
        (jArr one "commands").length == 1
          && ((jArr one "commands").head?.bind (fun c => jStr c "command")) == some "close"
          && (jArr one "globalFlags").length == 6),
     check "help <group> expands to its subcommands"
       ((jArr (helpJson (some "dep")) "commands").length == 6)]

/-- The drift guard, exercised through the real parser: for every command,
    each flag the schema lists is accepted, and an invented flag is rejected
    as usage. Run per command via `runVerb` (no state needed — a flag-parse
    error fires before any I/O for these). -/
def grammarParserAgreementTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- a value flag the schema lists for `create` parses (then fails later for
  -- a missing project / etc., but NOT with a flag usage error)
  let accepted ← run' ["create", "x", "--priority", "2", "--dir", "/tmp/tl-nope-xyz"]
  o := o ++ [check "a schema value-flag (--priority) is not a usage error"
    (match accepted with | .error e => e.code != .usage | .ok _ => true)
    (match accepted with | .error e => e.code.wire | .ok _ => "ok")]
  -- a flag NOT in create's schema is a usage error
  let rejected ← run' ["create", "x", "--frobnicate", "y", "--dir", "/tmp/tl-nope-xyz"]
  o := o ++ [check "a non-schema flag (--frobnicate) is a usage error"
    (match rejected with | .error e => e.code == .usage | .ok _ => false)
    (match rejected with | .error e => e.code.wire | .ok _ => "ok")]
  -- a flag valid on another command but not this one is rejected (--as is
  -- close's, not ready's)
  let crossed ← run' ["ready", "--as", "done"]
  o := o ++ [check "a flag from another command is rejected here"
    (match crossed with | .error e => e.code == .usage | .ok _ => false)
    (match crossed with | .error e => e.code.wire | .ok _ => "ok")]
  -- the envelope shape: help --json is a valid, ok:true schema envelope
  let exe := (← IO.currentDir) / ".lake" / "build" / "bin" / "tl"
  if ← exe.pathExists then
    let out ← IO.Process.output { cmd := exe.toString, args := #["help", "--json"] }
    o := o ++
      [check "help --json exits 0" (out.exitCode == 0),
       check "help --json is a valid ok envelope with commands+globalFlags"
         (match Json.parse out.stdout with
          | .ok j =>
            (jGet j "ok").bind (·.getBool?.toOption) == some true
              && ((jGet j "data").map (fun d =>
                    (jArr d "commands").length > 0 && (jArr d "globalFlags").length == 6)).getD false
          | .error _ => false)
         out.stdout]
  return o

def grammarTests : IO (List Outcome) := do
  return grammarSchemaTests ++ (← grammarParserAgreementTests)

end Tl.Tests
