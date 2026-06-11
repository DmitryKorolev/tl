/-
`Tl.Cli.Main` — verb dispatch, argument parsing, and the stream/exit
discipline (ADR-0008 §`--json`).

With `--json` the one envelope (success or error) goes to stdout and every
incidental note to stderr; without it, data to stdout, errors/notes to
stderr. Argument-parse failures honor `--json` if the raw argv contains it
anywhere (emit the `usage` envelope, exit 2). Every error exits with its
pinned code (ADR-0008); notes (foreign-refusal disclosures, clamp warnings)
never change the exit.
-/
import Tl.Cli.Commands

namespace Tl.Cli

open Tl.Store
open Lean (Json)

structure Argv where
  positionals : List String := []
  kvs : List (String × String) := []
  bools : List String := []

namespace Argv

def getAll (a : Argv) (k : String) : List String :=
  a.kvs.filterMap (fun (n, v) => if n == k then some v else none)

def get? (a : Argv) (k : String) : Option String := (a.getAll k).head?

def has (a : Argv) (k : String) : Bool := a.bools.contains k

end Argv

private def usageErr (msg : String) : Tl.Error :=
  .mk' .usage (msg ++ " — see `tl help`")

/-- Parse flags: `--name value`, `--name=value`, bare `--name` for booleans,
    `-p` as `--priority`. Unknown flags are `usage` errors. -/
def parseArgs (valFlags boolFlags : List String) : List String → Except Tl.Error Argv
  | args => go args {}
where
  go : List String → Argv → Except Tl.Error Argv
    | [], acc => .ok acc
    | arg :: rest, acc =>
      let arg := if arg == "-p" then "--priority" else arg
      if arg.startsWith "--" then
        let body := (arg.drop 2).toString
        match body.splitOn "=" with
        | [name, value] =>
          if valFlags.contains name then go rest { acc with kvs := acc.kvs ++ [(name, value)] }
          else .error (usageErr s!"unknown or non-value flag --{name}")
        | _ =>
          if valFlags.contains body then
            match rest with
            | v :: rest' =>
              if v.startsWith "--" then .error (usageErr s!"--{body} needs a value")
              else go rest' { acc with kvs := acc.kvs ++ [(body, v)] }
            | [] => .error (usageErr s!"--{body} needs a value")
          else if boolFlags.contains body then
            go rest { acc with bools := acc.bools ++ [body] }
          else .error (usageErr s!"unknown flag --{body}")
      else
        go rest { acc with positionals := acc.positionals ++ [arg] }

private def globalVal : List String := ["dir"]
private def globalBool : List String := ["json", "skip-bad"]

private def natFlag (a : Argv) (k : String) (default : Nat) : Except Tl.Error Nat :=
  match a.get? k with
  | none => .ok default
  | some v => match v.toNat? with
    | some n => .ok n
    | none => .error (usageErr s!"--{k} must be a number (got '{v}')")

private def priorityFlag (a : Argv) : Except Tl.Error (Option Nat) :=
  match a.get? "priority" with
  | none => .ok none
  | some v => match v.toNat? with
    | some n => if n ≤ 4 then .ok (some n) else .error (usageErr s!"--priority must be 0-4 (got {v})")
    | none => .error (usageErr s!"--priority must be 0-4 (got '{v}')")

def usageText : String :=
  "tl — a dependency-aware task tracker for agents

usage:
  tl init                                    create the state directory (repo toplevel)
  tl create \"<title>\" [--blocked-by <id>]... [--blocks <id>]...
            [--parent <id>]... [--related <id>]... [-p 0-4]
  tl ready [--limit N]                       ranked workable items (default 10; 0 = all)
  tl claim <id> [--assignee <name>]          take a ready item (refused otherwise)
  tl close <id> --as done|cancelled|duplicate [--of <id>]
  tl update <id> [--title T] [-p 0-4] [--description D] [--notes N]
  tl dep add <id> <blocked-by>               <id> is blocked by <blocked-by>
  tl dep remove <id> <blocked-by>            retract that edge
  tl why <id>                                the transitive unclosed blockers
  tl dep cycles                              report cycles (blocks/parent/readiness)
  tl show <id>
  tl list [--limit N]
  tl doctor                                  local health checks
  tl version
  tl help

global: --json (stable envelope on stdout) · --dir <state-dir> (skip discovery)
        --skip-bad (reads: skip malformed lines, disclosed on stderr)
"

private def actorOf (a : Argv) : TlM String :=
  liftSys (fun e => .mk' .internal s!"{e}") (resolveActor (a.get? "assignee"))

/-- Build the command outcome for an argv (the verb is the first token). -/
def runVerb : List String → TlM CmdOut
  | [] => return { data := Json.str usageText, human := usageText }
  | verb :: rest => do
    let parse (vals bools : List String) : TlM Argv :=
      MonadExcept.ofExcept (parseArgs (vals ++ globalVal) (bools ++ globalBool) rest)
    match verb with
    | "help" | "--help" => return { data := Json.str usageText, human := usageText }
    | "version" => do
      let _ ← parse [] []
      return cmdVersion
    | "init" => do
      let a ← parse [] []
      cmdInit (a.get? "dir")
    | "create" => do
      let a ← parse ["priority", "blocked-by", "blocks", "parent", "related", "assignee"] []
      let some title := a.positionals.head?
        | throw (usageErr "create needs a title")
      unless a.positionals.length == 1 do
        throw (usageErr "create takes exactly one title (quote it)")
      let prio ← MonadExcept.ofExcept (priorityFlag a)
      let actor ← actorOf a
      cmdCreate (a.get? "dir") title prio actor
        (a.getAll "blocked-by") (a.getAll "blocks") (a.getAll "parent") (a.getAll "related")
    | "ready" => do
      let a ← parse ["limit"] []
      let limit ← MonadExcept.ofExcept (natFlag a "limit" 10)
      cmdReady (a.get? "dir") limit
    | "list" => do
      let a ← parse ["limit"] []
      let limit ← MonadExcept.ofExcept (natFlag a "limit" 10)
      cmdList (a.get? "dir") limit
    | "show" => do
      let a ← parse [] []
      let some tok := a.positionals.head? | throw (usageErr "show needs an issue id")
      cmdShow (a.get? "dir") tok
    | "why" => do
      let a ← parse [] []
      let some tok := a.positionals.head? | throw (usageErr "why needs an issue id")
      cmdWhy (a.get? "dir") tok
    | "claim" => do
      let a ← parse ["assignee"] []
      let some tok := a.positionals.head? | throw (usageErr "claim needs an issue id")
      let actor ← actorOf a
      cmdClaim (a.get? "dir") tok actor
    | "close" => do
      let a ← parse ["as", "of", "assignee"] []
      let some tok := a.positionals.head? | throw (usageErr "close needs an issue id")
      let some asStr := a.get? "as"
        | throw (usageErr "close needs --as done|cancelled|duplicate")
      let actor ← actorOf a
      cmdClose (a.get? "dir") tok asStr (a.get? "of") actor
    | "update" => do
      let a ← parse ["title", "priority", "description", "notes", "assignee"] []
      let some tok := a.positionals.head? | throw (usageErr "update needs an issue id")
      let prio ← MonadExcept.ofExcept (priorityFlag a)
      let actor ← actorOf a
      cmdUpdate (a.get? "dir") tok (a.get? "title") (a.get? "description")
        (a.get? "notes") prio actor
    | "dep" => do
      match rest with
      | "add" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (["assignee"] ++ globalVal) globalBool rest')
        match a.positionals with
        | [x, y] => cmdDepAdd (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "dep add takes <id> <blocked-by>")
      | "remove" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (["assignee"] ++ globalVal) globalBool rest')
        match a.positionals with
        | [x, y] => cmdDepRemove (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "dep remove takes <id> <blocked-by>")
      | "cycles" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs globalVal globalBool rest')
        cmdDepCycles (a.get? "dir")
      | _ => throw (usageErr "dep takes add|remove|cycles")
    | "doctor" => do
      let a ← parse [] []
      cmdDoctor (a.get? "dir")
    | other => throw (usageErr s!"unknown command '{other}'")

/-- The executable entry: streams + exit codes (ADR-0008). -/
def run (args : List String) : IO UInt32 := do
  let jsonMode := args.contains "--json"
  match ← (runVerb args).run with
  | .ok out =>
    for note in out.notes do
      IO.eprintln s!"tl: {note}"
    if jsonMode then
      IO.println (okEnvelope out.data)
    else if !out.human.isEmpty then
      IO.println out.human
    return 0
  | .error e =>
    if jsonMode then
      IO.println (errorEnvelope e)
      IO.eprintln s!"tl: {e.message}"
    else
      IO.eprintln s!"tl: {e.message}"
    return e.code.exitCode

end Tl.Cli
