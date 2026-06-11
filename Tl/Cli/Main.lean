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
import Tl.Cli.Grammar

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
    `-p` as `--priority`. Unknown flags, and a repeated single-value flag,
    are `usage` errors. -/
def parseArgs (valFlags boolFlags : List String) : List String → Except Tl.Error Argv
  | args => go args {}
where
  addVal (acc : Argv) (name value : String) : Except Tl.Error Argv :=
    if (acc.kvs.any (·.1 == name)) && !repeatableFlags.contains name then
      .error (usageErr s!"--{name} given more than once (it takes a single value)")
    else .ok { acc with kvs := acc.kvs ++ [(name, value)] }
  go : List String → Argv → Except Tl.Error Argv
    | [], acc => .ok acc
    | arg :: rest, acc =>
      let arg := if arg == "-p" then "--priority" else arg
      if arg.startsWith "--" then
        let body := (arg.drop 2).toString
        -- split at the FIRST '=' only: values may contain '='
        match body.splitOn "=" with
        | name :: rest1 :: restN =>
          let value := String.intercalate "=" (rest1 :: restN)
          if valFlags.contains name then do go rest (← addVal acc name value)
          else .error (usageErr s!"unknown or non-value flag --{name}")
        | _ =>
          if valFlags.contains body then
            match rest with
            | v :: rest' =>
              if v.startsWith "--" then .error (usageErr s!"--{body} needs a value")
              else do go rest' (← addVal acc body v)
            | [] => .error (usageErr s!"--{body} needs a value")
          else if boolFlags.contains body then
            go rest { acc with bools := acc.bools ++ [body] }
          else .error (usageErr s!"unknown flag --{body}")
      else
        go rest { acc with positionals := acc.positionals ++ [arg] }

private def globalVal : List String := ["dir", "color", "glyphs"]
private def globalBool : List String := ["json", "skip-bad", "plain"]

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

private def actorOf (a : Argv) : TlM String :=
  liftSys (fun e => .mk' .internal s!"{e}") (resolveActor (a.get? "assignee"))

/-- Exactly one positional, or a `usage` error — surplus positionals are
    never silently dropped (e.g. an unquoted multi-word title, or a second
    id the user expected to be acted on). `noun` names the expected token. -/
private def onePositional (a : Argv) (verb noun : String) : Except Tl.Error String :=
  match a.positionals with
  | [tok] => .ok tok
  | [] => .error (usageErr s!"{verb} needs {noun}")
  | _ => .error (usageErr s!"{verb} takes exactly one positional argument ({noun}) — got {a.positionals.length} (quote multi-word values)")

/-- No positionals, or a `usage` error. -/
private def noPositionals (a : Argv) (verb : String) : Except Tl.Error Unit :=
  if a.positionals.isEmpty then .ok ()
  else .error (usageErr s!"{verb} takes no positional arguments — got {a.positionals.length}")

/-- Build the command outcome for an argv (the verb is the first token).
    Each arm's accepted flags come from the `Grammar` table via `parse`, so
    the parser, the human help, and the `--json` schema never drift. -/
def runVerb : List String → TlM CmdOut
  | [] => return { data := helpJson none, human := helpText none }
  | verb :: rest => do
    -- the flags this command accepts are looked up from the grammar table,
    -- not hardcoded here (single source of truth, Tl/Cli/Grammar.lean)
    let parse (cmd : String) : TlM Argv :=
      MonadExcept.ofExcept (parseArgs (valFlagsOf cmd ++ globalVal) (boolFlagsOf cmd ++ globalBool) rest)
    match verb with
    | "help" | "--help" => do
      let a ← parse "help"
      match a.positionals with
      | [] => return { data := helpJson none, human := helpText none }
      | [name] =>
        if (commandsMatching name).isEmpty then
          throw (usageErr s!"no command '{name}' to describe")
        else return { data := helpJson (some name), human := helpText (some name) }
      | _ => throw (usageErr "help takes at most one command name")
    | "version" => do
      let a ← parse "version"
      MonadExcept.ofExcept (noPositionals a "version")
      return cmdVersion
    | "init" => do
      let a ← parse "init"
      MonadExcept.ofExcept (noPositionals a "init")
      cmdInit (a.get? "dir")
    | "create" => do
      let a ← parse "create"
      let title ← MonadExcept.ofExcept (onePositional a "create" "title")
      let prio ← MonadExcept.ofExcept (priorityFlag a)
      let actor ← actorOf a
      -- the ADR-0017 §8 description precedence: --description wins; else a
      -- non-TTY stdin is read to EOF as the body (empty/blank = absent);
      -- the $EDITOR path is the stage-2 `edit` surface
      let desc : Option String ← match a.get? "description" with
        | some d => pure (some d)
        | none =>
          liftSys (fun e => .mk' .internal s!"cannot read stdin: {e}") do
            let stdin ← (IO.getStdin : IO IO.FS.Stream)
            if ← stdin.isTty then
              pure none
            else
              let body ← stdin.readToEnd
              let body := if body.endsWith "\n" then (body.dropEnd 1).toString else body
              pure (if body.trimAscii.toString.isEmpty then none else some body)
      cmdCreate (a.get? "dir") title prio desc actor
        (a.getAll "blocked-by") (a.getAll "blocks") (a.getAll "parent") (a.getAll "related")
    | "ready" => do
      let a ← parse "ready"
      MonadExcept.ofExcept (noPositionals a "ready")
      let limit ← MonadExcept.ofExcept (natFlag a "limit" 10)
      cmdReady (a.get? "dir") limit (a.has "skip-bad")
    | "list" => do
      let a ← parse "list"
      MonadExcept.ofExcept (noPositionals a "list")
      let limit ← MonadExcept.ofExcept (natFlag a "limit" 10)
      cmdList (a.get? "dir") limit (a.has "skip-bad")
    | "log" => do
      let a ← parse "log"
      let idTok ← match a.positionals with
        | [] => pure none
        | [tok] => pure (some tok)
        | _ => throw (usageErr "log takes at most one issue id")
      let limit ← MonadExcept.ofExcept (natFlag a "limit" 10)
      cmdLog (a.get? "dir") idTok limit (a.has "skip-bad")
    | "stats" => do
      let a ← parse "stats"
      MonadExcept.ofExcept (noPositionals a "stats")
      cmdStats (a.get? "dir") (a.has "skip-bad")
    | "reopen" => do
      let a ← parse "reopen"
      let tok ← MonadExcept.ofExcept (onePositional a "reopen" "an issue id")
      let actor ← actorOf a
      cmdReopen (a.get? "dir") tok actor
    | "show" => do
      let a ← parse "show"
      let tok ← MonadExcept.ofExcept (onePositional a "show" "an issue id")
      cmdShow (a.get? "dir") tok (a.has "skip-bad")
    | "why" => do
      let a ← parse "why"
      let tok ← MonadExcept.ofExcept (onePositional a "why" "an issue id")
      cmdWhy (a.get? "dir") tok (a.has "skip-bad")
    | "claim" => do
      let a ← parse "claim"
      let tok ← MonadExcept.ofExcept (onePositional a "claim" "an issue id")
      let actor ← actorOf a
      cmdClaim (a.get? "dir") tok actor
    | "close" => do
      let a ← parse "close"
      let tok ← MonadExcept.ofExcept (onePositional a "close" "an issue id")
      let some asStr := a.get? "as"
        | throw (usageErr "close needs --as done|cancelled|duplicate")
      let actor ← actorOf a
      cmdClose (a.get? "dir") tok asStr (a.get? "of") actor
    | "update" => do
      let a ← parse "update"
      let tok ← MonadExcept.ofExcept (onePositional a "update" "an issue id")
      let prio ← MonadExcept.ofExcept (priorityFlag a)
      let actor ← actorOf a
      cmdUpdate (a.get? "dir") tok (a.get? "title") (a.get? "description")
        (a.get? "notes") prio actor
    | "dep" => do
      match rest with
      | "add" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep add" ++ globalVal) (boolFlagsOf "dep add" ++ globalBool) rest')
        match a.positionals with
        | [x, y] => cmdDepAdd (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "dep add takes <id> <blocked-by>")
      | "remove" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep remove" ++ globalVal) (boolFlagsOf "dep remove" ++ globalBool) rest')
        match a.positionals with
        | [x, y] => cmdDepRemove (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "dep remove takes <id> <blocked-by>")
      | "cycles" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep cycles" ++ globalVal) (boolFlagsOf "dep cycles" ++ globalBool) rest')
        MonadExcept.ofExcept (noPositionals a "dep cycles")
        cmdDepCycles (a.get? "dir") (a.has "skip-bad")
      | _ => throw (usageErr "dep takes add|remove|cycles")
    | "doctor" => do
      let a ← parse "doctor"
      MonadExcept.ofExcept (noPositionals a "doctor")
      cmdDoctor (a.get? "dir")
    | other =>
      if other.startsWith "-" then
        throw (usageErr s!"flags follow the verb (e.g. `tl ready {other}`); no command named '{other}'")
      else
        throw (usageErr s!"unknown command '{other}'")

/-- Sanitize a JSON tree's string leaves (error-context values can embed raw
    log bytes). Strings and array elements are sanitized; nested objects in
    error context carry only code-built ids/bools (e.g. `reasons`), so they
    pass through. -/
private partial def sanitizeJson : Json → Json
  | .str s => .str (sanitizeSingle s)
  | .arr a => .arr (a.map sanitizeJson)
  | other => other

/-- An error surfaced to a human/agent passes through the ADR-0014 sanitizer:
    decode errors interpolate raw hostile log bytes into `message`/context, so
    the surfacing chokepoint strips ANSI/control bytes on both the stderr and
    the `--json error` paths (the one place every error funnels through). -/
private def sanitizeError (e : Tl.Error) : Tl.Error :=
  { e with message := sanitizeSingle e.message,
           context := e.context.map (fun (k, v) => (k, sanitizeJson v)) }

/-- The executable entry: streams + exit codes (ADR-0008). -/
def run (args : List String) : IO UInt32 := do
  let jsonMode := args.contains "--json"
  let style ← Style.resolve args
  match ← (runVerb args).run with
  | .ok out =>
    for note in out.notes do
      IO.eprintln s!"tl: {sanitizeSingle note}"
    if jsonMode then
      IO.println (okEnvelope out.data)
    else
      let human := (out.render.map (· style)).getD out.human
      if !human.isEmpty then IO.println human
    return 0
  | .error e =>
    let e := sanitizeError e
    if jsonMode then
      IO.println (errorEnvelope e)
      IO.eprintln s!"tl: {e.message}"
    else
      IO.eprintln s!"tl: {e.message}"
    return e.code.exitCode

end Tl.Cli
