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

/-- Render a bounded list of commands that accept a flag. -/
private def commandDestinations (commands : List String) (limit : Nat := 4) : String :=
  let shown := commands.take limit
  let remaining := commands.length - shown.length
  let rendered := String.intercalate " / " (shown.map fun command => s!"`tl {command}`")
  if remaining == 0 then rendered else s!"{rendered} / … and {remaining} more commands"

/-- An unknown-flag `usage` error that teaches where the flag *does* live: the
    verb it was given to, the commands that accept it (from the grammar table, so
    the hint cannot drift), and `tl help <verb>` for the rest. This path matters
    most for the read facets, which are deliberately split across `ready` and
    `list` — `tl ready --status open` should name `tl list --status`, not just
    report an unknown flag (ADR-0008: a message says what to do next). The help
    command it names is the *topic* — `help` takes at most one name, so
    a two-token verb like `dep add` must be offered as `tl help dep`, which
    already lists every `dep *` subcommand's flags. -/
private def unknownFlagErr (verb name : String) : Tl.Error :=
  let where? := (commandsWithFlag name).filter (fun c => c != verb)
  let topic := (verb.splitOn " ").headD verb
  let onVerb := s!" on `tl {verb}`"
  let hint := match where? with
    | [] => s!"run `tl help {topic}` for the flags it takes"
    | cs => s!"{commandDestinations cs} take" ++
        (if cs.length == 1 then "s it" else " it") ++
        s!"; `tl help {topic}` lists {topic}'s own flags"
  -- `.mk'` directly, not `usageErr`: the hint already names the precise help
  -- command, so the generic "see `tl help`" tail would just repeat it
  .mk' .usage s!"unknown flag --{name}{onVerb} — {hint}"

/-- Parse flags: `--name value`, `--name=value`, bare `--name` for booleans,
    `-p` as `--priority`. Unknown flags, and a repeated single-value flag,
    are `usage` errors. `verb` only shapes those messages (it is the command the
    flags were given to); the accepted-flag lists are the caller's. -/
def parseArgs (valFlags boolFlags repeatable : List String) (verb : String) :
    List String → Except Tl.Error Argv
  | args => go args {}
where
  addVal (acc : Argv) (name value : String) : Except Tl.Error Argv :=
    if (acc.kvs.any (·.1 == name)) && !repeatable.contains name then
      .error (usageErr s!"--{name} given more than once (it takes a single value)")
    else .ok { acc with kvs := acc.kvs ++ [(name, value)] }
  go : List String → Argv → Except Tl.Error Argv
    | [], acc => .ok acc
    | arg :: rest, acc =>
      let arg := if arg == "-p" then "--priority" else arg
      if arg.startsWith "--" then
        let body := (arg.drop 2).toString
        -- split at the first '=' only: values may contain '='
        match body.splitOn "=" with
        | name :: rest1 :: restN =>
          let value := String.intercalate "=" (rest1 :: restN)
          if valFlags.contains name then do go rest (← addVal acc name value)
          else if boolFlags.contains name then
            .error (usageErr s!"--{name} is a boolean flag on `tl {verb}` — pass it bare (`--{name}`), not `--{name}={value}`")
          else .error (unknownFlagErr verb name)
        | _ =>
          if valFlags.contains body then
            match rest with
            | v :: rest' =>
              if v.startsWith "--" then .error (usageErr s!"--{body} needs a value")
              else do go rest' (← addVal acc body v)
            | [] => .error (usageErr s!"--{body} needs a value")
          else if boolFlags.contains body then
            go rest { acc with bools := acc.bools ++ [body] }
          else .error (unknownFlagErr verb body)
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
  | some v => (parsePriorityValue v).map some

private def actorOf (a : Argv) : TlM String :=
  -- pass the `--dir` override so the git-config actor read runs in the target repo
  -- (`git -C`), not the process cwd (ADR-0013)
  liftSys (fun e => .mk' .internal s!"{e}") (resolveActor (a.get? "actor") (a.get? "dir"))

/-- Exactly one positional, or a `usage` error — surplus positionals are
    never silently dropped (e.g. an unquoted multi-word title, or a second
    id the user expected to be acted on). `noun` names the expected token. -/
private def onePositional (a : Argv) (verb noun : String) : Except Tl.Error String :=
  match a.positionals with
  | [tok] => .ok tok
  | [] => .error (usageErr s!"{verb} needs {noun}")
  | _ => .error (usageErr s!"{verb} takes exactly one positional argument ({noun}) — got {a.positionals.length} (quote multi-word values)")

/-- `create` positionals: the `<title>`, plus an optional trailing `-` — the
    explicit stdin sentinel (read the body from stdin; ADR-0017 §8). -/
private def createPositionals (a : Argv) : Except Tl.Error (String × Bool) :=
  match a.positionals with
  | [tok] => .ok (tok, false)
  | [tok, "-"] => .ok (tok, true)
  | [] => .error (usageErr "create needs a title")
  | _ => .error (usageErr "create takes a title, optionally followed by `-` to read the body from stdin (quote multi-word values)")

/-- Explicit text input shared by create, update and note add. Field-specific
    empty-body semantics belong to the caller, after a successful read. -/
private def readStdinText : TlM String :=
  liftSys (fun e => .mk' .internal
    s!"cannot read stdin: {e}; supply readable text on stdin or pass the text directly as an argument") do
    let body ← (← (IO.getStdin : IO IO.FS.Stream)).readToEnd
    pure (if body.endsWith "\n" then (body.dropEnd 1).toString else body)

/-- No positionals, or a `usage` error. -/
private def noPositionals (a : Argv) (verb : String) : Except Tl.Error Unit :=
  if a.positionals.isEmpty then .ok ()
  else .error (usageErr s!"{verb} takes no positional arguments — got {a.positionals.length}")

/-- The actor `--assignee me` resolves to on a read command, or `none` when no
    `me` token was given. Resolution runs only when `me` is actually present, so
    the other facets never touch git/env (ADR-0013): for a read filter `me` is the
    *ambient* actor (`TL_ACTOR` → git config → `user@host`) — there is no
    `--actor` write-provenance override on a read command. The raw tokens (incl.
    `me`) stay with the caller for the human echo. Shared by `ready` and `list`. -/
private def resolveMeActor (a : Argv) (assignees : List String) : TlM (Option String) :=
  if assignees.contains "me" then (do let m ← actorOf a; pure (some m)) else pure none

/-- Build the command outcome for an argv (the verb is the first token).
    Each arm's accepted flags come from the `Grammar` table via `parse`, so
    the parser, the human help, and the `--json` schema never drift. -/
def runVerb : List String → TlM CmdOut
  | [] => return { data := helpJson none, human := helpText none }
  | verb :: rest => do
    -- the flags this command accepts are looked up from the grammar table,
    -- not hardcoded here (single source of truth, Tl/Cli/Grammar.lean)
    let parse (cmd : String) : TlM Argv :=
      MonadExcept.ofExcept (parseArgs (valFlagsOf cmd ++ globalVal) (boolFlagsOf cmd ++ globalBool)
        (repeatableFlagsOf cmd) cmd rest)
    match verb with
    | "help" | "--help" | "-h" => do
      let a ← parse "help"
      match a.positionals with
      | [] => return { data := helpJson none, human := helpText none }
      | [name] =>
        if (commandsMatching name).isEmpty then
          throw (usageErr s!"no command '{name}' to describe")
        else return { data := helpJson (some name), human := helpText (some name) }
      | _ => throw (usageErr "help takes at most one command name")
    | "version" | "--version" | "-v" => do
      let a ← parse "version"
      MonadExcept.ofExcept (noPositionals a "version")
      return cmdVersion
    | "licenses" | "--licenses" => do
      let a ← parse "licenses"
      MonadExcept.ofExcept (noPositionals a "licenses")
      return cmdLicenses
    | "init" => do
      let a ← parse "init"
      MonadExcept.ofExcept (noPositionals a "init")
      cmdInit (a.get? "dir") (a.has "stealth")
    | "import" => do
      let a ← parse "import"
      let tok ← MonadExcept.ofExcept (onePositional a "import" "a path to a .jsonl file or directory")
      let maxN ← match a.get? "max" with
        | none => pure none
        | some v => match v.toNat? with
          | some n => pure (some n)
          | none => throw (usageErr s!"--max must be a whole number of bytes (got '{v}')")
      cmdImport (a.get? "dir") tok (a.get? "source") (a.has "force") (a.has "allow-large") maxN
    | "create" => do
      let a ← parse "create"
      -- positionals: <title>, optionally a trailing `-` (the stdin sentinel)
      let (title, dashPos) ← MonadExcept.ofExcept (createPositionals a)
      let prio ← MonadExcept.ofExcept (priorityFlag a)
      let actor ← actorOf a
      -- ADR-0017 §8 description precedence: `--description <text>` is the body;
      -- stdin is read to EOF as the body only on the explicit `-` sentinel
      -- (`--description -`, or a trailing `-`) — never an unrequested stdin, so an
      -- inherited, held-open pipe cannot hang `tl create`. (empty/blank = absent;
      -- the $EDITOR path is the stage-2 `edit` surface.)
      let descFlag := a.get? "description"
      let wantStdin := dashPos || descFlag == some "-"
      if dashPos && descFlag.isSome && descFlag != some "-" then
        throw (usageErr "give the body once — `--description <text>`, or `-`/`--description -` to read stdin, not both")
      let desc : Option String ←
        if wantStdin then do
          let body ← readStdinText
          pure (if body.trimAscii.toString.isEmpty then none else some body)
        else pure descFlag
      cmdCreate (a.get? "dir") title prio desc (a.get? "slug") actor
        (a.getAll "blocked-by") (a.getAll "blocks") (a.getAll "parent") (a.getAll "related")
    | "ready" => do
      let a ← parse "ready"
      MonadExcept.ofExcept (noPositionals a "ready")
      let limit ← MonadExcept.ofExcept (natFlag a "limit" 50)
      let assignees := a.getAll "assignee"
      let meActor ← resolveMeActor a assignees
      cmdReady (a.get? "dir") limit (a.has "skip-bad") (a.has "sync")
        (a.getAll "label") assignees meActor
    | "list" => do
      let a ← parse "list"
      MonadExcept.ofExcept (noPositionals a "list")
      let limit ← MonadExcept.ofExcept (natFlag a "limit" 50)
      let labels := a.getAll "label"
      let staleArg := a.get? "stale"
      let statuses := a.getAll "status"
      let assignees := a.getAll "assignee"
      let priorities := a.getAll "priority"
      -- Parse every facet before `me` consults git/env and before `cmdList`
      -- discovers or folds the project. Syntax errors must remain zero-I/O.
      let parsed ← MonadExcept.ofExcept
        (parseListFacets labels assignees statuses priorities staleArg)
      let meActor ← resolveMeActor a parsed.assignees
      cmdList (a.get? "dir") limit (!a.has "flat") (a.has "all") (a.has "skip-bad")
        (a.has "deferred") meActor (a.has "blocked") parsed
    | "log" => do
      let a ← parse "log"
      let idTok ← match a.positionals with
        | [] => pure none
        | [tok] => pure (some tok)
        | _ => throw (usageErr "log takes at most one issue id")
      let since := a.get? "since"
      let untilC := a.get? "until"
      -- `--last N` is the count tail (newest N); it caps like `--limit`, so the two
      -- together are a usage error rather than a silent precedence.
      if (a.get? "last").isSome && (a.get? "limit").isSome then
        throw (usageErr "log takes either --limit or --last, not both")
      let lastN ← match a.get? "last" with
        | none => pure none
        | some v => match v.toNat? with
          | some n => pure (some n)
          | none => throw (usageErr s!"--last must be a whole number (got '{v}')")
      -- `--since` drains (forward feed, exactly-once); plain and `--until` page
      -- (default 10, newest-first history browsing).
      let limit ← MonadExcept.ofExcept (natFlag a "limit" (if since.isSome then 0 else 10))
      cmdLog (a.get? "dir") idTok limit lastN since untilC (a.has "skip-bad")
    | "stats" => do
      let a ← parse "stats"
      MonadExcept.ofExcept (noPositionals a "stats")
      cmdStats (a.get? "dir") (a.has "skip-bad")
    | "reopen" => do
      let a ← parse "reopen"
      let tok ← MonadExcept.ofExcept (onePositional a "reopen" "an issue id")
      let actor ← actorOf a
      cmdReopen (a.get? "dir") tok actor
    | "defer" => do
      let a ← parse "defer"
      let tok ← MonadExcept.ofExcept (onePositional a "defer" "an issue id")
      let actor ← actorOf a
      cmdDefer (a.get? "dir") tok (a.get? "until") (a.get? "for") actor
    | "undefer" => do
      let a ← parse "undefer"
      let tok ← MonadExcept.ofExcept (onePositional a "undefer" "an issue id")
      let actor ← actorOf a
      cmdUndefer (a.get? "dir") tok actor
    | "show" => do
      let a ← parse "show"
      let tok ← MonadExcept.ofExcept (onePositional a "show" "an issue id")
      cmdShow (a.get? "dir") tok (a.has "skip-bad")
    | "why" => do
      let a ← parse "why"
      let tok ← MonadExcept.ofExcept (onePositional a "why" "an issue id")
      cmdWhy (a.get? "dir") tok (a.has "skip-bad")
    | "unblocks" => do
      let a ← parse "unblocks"
      let tok ← MonadExcept.ofExcept (onePositional a "unblocks" "an issue id")
      cmdUnblocks (a.get? "dir") tok (a.has "skip-bad")
    | "claim" => do
      let a ← parse "claim"
      let tok ← MonadExcept.ofExcept (onePositional a "claim" "an issue id")
      let actor ← actorOf a
      cmdClaim (a.get? "dir") tok actor (a.has "sync") (a.has "verify") (a.has "steal") (a.get? "stale")
    | "close" => do
      let a ← parse "close"
      let tok ← MonadExcept.ofExcept (onePositional a "close" "an issue id")
      let some asStr := a.get? "as"
        | throw (usageErr "close needs --as done|cancelled|duplicate")
      let actor ← actorOf a
      cmdClose (a.get? "dir") tok asStr (a.get? "of") actor
    | "update" => do
      -- the retired notes flags stay *parseable* (never advertised) so their
      -- usage errors can teach `tl note add` (ADR-0027)
      let a ← MonadExcept.ofExcept (parseArgs
        (valFlagsOf "update" ++ ["notes", "append-notes"] ++ globalVal)
        (boolFlagsOf "update" ++ globalBool) (repeatableFlagsOf "update") "update" rest)
      let tok ← MonadExcept.ofExcept (onePositional a "update" "an issue id")
      let prio ← MonadExcept.ofExcept (priorityFlag a)
      let actor ← actorOf a
      MonadExcept.ofExcept (validateUpdateNotes (a.get? "notes") (a.get? "append-notes"))
      let description ← if a.get? "description" == some "-" then
          some <$> readStdinText
        else pure (a.get? "description")
      cmdUpdate (a.get? "dir") tok (a.get? "title") description
        (a.get? "notes") (a.get? "append-notes") (a.get? "slug") prio actor
    | "parent" => do
      match rest with
      | "set" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "parent set" ++ globalVal) (boolFlagsOf "parent set" ++ globalBool) (repeatableFlagsOf "parent set") "parent set" rest')
        match a.positionals with
        | [x, y] => cmdParentSet (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "parent set takes <id> <new-parent>")
      | "remove" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "parent remove" ++ globalVal) (boolFlagsOf "parent remove" ++ globalBool) (repeatableFlagsOf "parent remove") "parent remove" rest')
        match a.positionals with
        | [x, y] => cmdParentRemove (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "parent remove takes <id> <parent>")
      | _ => throw (usageErr "parent takes set|remove")
    | "dep" => do
      match rest with
      | "add" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep add" ++ globalVal) (boolFlagsOf "dep add" ++ globalBool) (repeatableFlagsOf "dep add") "dep add" rest')
        match a.positionals with
        | [x, y] => cmdDepAdd (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "dep add takes <id> <blocked-by>")
      | "remove" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep remove" ++ globalVal) (boolFlagsOf "dep remove" ++ globalBool) (repeatableFlagsOf "dep remove") "dep remove" rest')
        match a.positionals with
        | [x, y] => cmdDepRemove (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "dep remove takes <id> <blocked-by>")
      | "cycles" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep cycles" ++ globalVal) (boolFlagsOf "dep cycles" ++ globalBool) (repeatableFlagsOf "dep cycles") "dep cycles" rest')
        MonadExcept.ofExcept (noPositionals a "dep cycles")
        cmdDepCycles (a.get? "dir") (a.has "skip-bad")
      | "critical" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep critical" ++ globalVal) (boolFlagsOf "dep critical" ++ globalBool) (repeatableFlagsOf "dep critical") "dep critical" rest')
        MonadExcept.ofExcept (noPositionals a "dep critical")
        cmdDepCritical (a.get? "dir") (a.has "skip-bad")
      | "path" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep path" ++ globalVal) (boolFlagsOf "dep path" ++ globalBool) (repeatableFlagsOf "dep path") "dep path" rest')
        match a.positionals with
        | [x, y] => cmdDepPath (a.get? "dir") x y (a.has "skip-bad")
        | _ => throw (usageErr "dep path takes <id> <id>")
      | "relate" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep relate" ++ globalVal) (boolFlagsOf "dep relate" ++ globalBool) (repeatableFlagsOf "dep relate") "dep relate" rest')
        match a.positionals with
        | [x, y] => cmdDepRelate (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "dep relate takes <id> <id>")
      | "unrelate" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "dep unrelate" ++ globalVal) (boolFlagsOf "dep unrelate" ++ globalBool) (repeatableFlagsOf "dep unrelate") "dep unrelate" rest')
        match a.positionals with
        | [x, y] => cmdDepUnrelate (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "dep unrelate takes <id> <id>")
      | _ => throw (usageErr "dep takes add|remove|cycles|critical|path|relate|unrelate")
    | "label" => do
      match rest with
      | "add" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "label add" ++ globalVal) (boolFlagsOf "label add" ++ globalBool) (repeatableFlagsOf "label add") "label add" rest')
        match a.positionals with
        | [x, y] => cmdLabelAdd (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "label add takes <id> <label>")
      | "remove" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "label remove" ++ globalVal) (boolFlagsOf "label remove" ++ globalBool) (repeatableFlagsOf "label remove") "label remove" rest')
        match a.positionals with
        | [x, y] => cmdLabelRemove (a.get? "dir") x y (← actorOf a)
        | _ => throw (usageErr "label remove takes <id> <label>")
      | "list" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "label list" ++ globalVal) (boolFlagsOf "label list" ++ globalBool) (repeatableFlagsOf "label list") "label list" rest')
        MonadExcept.ofExcept (noPositionals a "label list")
        cmdLabelList (a.get? "dir") (a.has "skip-bad")
      | _ => throw (usageErr "label takes add|remove|list")
    | "note" => do
      match rest with
      | "add" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "note add" ++ globalVal) (boolFlagsOf "note add" ++ globalBool) (repeatableFlagsOf "note add") "note add" rest')
        match a.positionals with
        | [x, t] => do
          -- Share the explicit text read; cmdNoteAdd retains its empty-entry guard.
          let text ← if t == "-" then readStdinText else pure t
          cmdNoteAdd (a.get? "dir") x text (← actorOf a)
        | _ => throw (usageErr "note add takes <id> <text> ('-' reads the text from stdin)")
      | "list" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "note list" ++ globalVal) (boolFlagsOf "note list" ++ globalBool) (repeatableFlagsOf "note list") "note list" rest')
        match a.positionals with
        | [x] => cmdNoteList (a.get? "dir") x (a.has "all") (a.has "skip-bad")
        | _ => throw (usageErr "note list takes <id>")
      | "remove" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "note remove" ++ globalVal) (boolFlagsOf "note remove" ++ globalBool) (repeatableFlagsOf "note remove") "note remove" rest')
        match a.positionals with
        | [x, n] => cmdNoteRemove (a.get? "dir") x n (← actorOf a)
        | _ => throw (usageErr "note remove takes <id> <note-id>")
      | _ => throw (usageErr "note takes add|list|remove")
    | "meta" => do
      match rest with
      | "set" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "meta set" ++ globalVal) (boolFlagsOf "meta set" ++ globalBool) (repeatableFlagsOf "meta set") "meta set" rest')
        match a.positionals with
        | [x, k, val] => cmdMetaSet (a.get? "dir") x k val (← actorOf a)
        | _ => throw (usageErr "meta set takes <id> <key> <value>")
      | "get" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "meta get" ++ globalVal) (boolFlagsOf "meta get" ++ globalBool) (repeatableFlagsOf "meta get") "meta get" rest')
        match a.positionals with
        | [x] => cmdMetaGet (a.get? "dir") x none (a.has "skip-bad")
        | [x, k] => cmdMetaGet (a.get? "dir") x (some k) (a.has "skip-bad")
        | _ => throw (usageErr "meta get takes <id> [<key>]")
      | "clear" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "meta clear" ++ globalVal) (boolFlagsOf "meta clear" ++ globalBool) (repeatableFlagsOf "meta clear") "meta clear" rest')
        match a.positionals with
        | [x, k] => cmdMetaClear (a.get? "dir") x k (← actorOf a)
        | _ => throw (usageErr "meta clear takes <id> <key>")
      | "list" :: rest' => do
        let a ← MonadExcept.ofExcept (parseArgs (valFlagsOf "meta list" ++ globalVal) (boolFlagsOf "meta list" ++ globalBool) (repeatableFlagsOf "meta list") "meta list" rest')
        match a.positionals with
        | [] => cmdMetaList (a.get? "dir") none (a.has "skip-bad")
        | [x] => cmdMetaList (a.get? "dir") (some x) (a.has "skip-bad")
        | _ => throw (usageErr "meta list takes an optional <id>")
      | _ => throw (usageErr "meta takes set|get|clear|list")
    | "sync" => do
      let a ← parse "sync"
      MonadExcept.ofExcept (noPositionals a "sync")
      cmdSync (a.get? "dir")
    | "doctor" => do
      let a ← parse "doctor"
      MonadExcept.ofExcept (noPositionals a "doctor")
      cmdDoctor (a.get? "dir") (a.has "sync")
    | other =>
      if other.startsWith "-" then
        throw (usageErr s!"flags follow the verb (e.g. `tl ready {other}`); no command named '{other}'")
      else
        -- did-you-mean: suggest the top-level verbs that share a prefix or first
        -- two characters with the typo, else point at `tl help` (teach the fix)
        let cmds := (commandSpecs.map (fun c => (c.command.splitOn " ").headD "")).eraseDups
        let near := cmds.filter (fun c =>
          c.startsWith other || other.startsWith c
            || (c.length ≥ 2 && other.length ≥ 2 && c.take 2 == other.take 2))
        -- `.mk'` directly when there is no suggestion: the hint already names
        -- `tl help`, so the generic `usageErr` tail would just repeat it
        if near.isEmpty then
          throw (.mk' .usage s!"unknown command '{other}' — run `tl help` for the command list")
        else
          throw (usageErr s!"unknown command '{other}' — did you mean: {String.intercalate ", " near.eraseDups}?")

/-- Sanitize a JSON tree's string leaves (error-context values can embed raw
    log bytes). Strings, array elements, *and object values* are sanitized
    recursively — a nested context object can carry an untrusted string (e.g.
    the import bounds violation list's per-record source id, ADR-0005), so it
    must not pass through unsanitized. Keys are code-built, left as-is. -/
private partial def sanitizeJson : Json → Json
  | .str s => .str (sanitizeSingle s)
  | .arr a => .arr (a.map sanitizeJson)
  | .obj kvs => Json.mkObj ((kvs.toArray.map (fun (k, v) => (k, sanitizeJson v))).toList)
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
      IO.println (okEnvelope out.data (out.notes.map sanitizeSingle))
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
