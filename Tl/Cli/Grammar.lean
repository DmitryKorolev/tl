/-
`Tl.Cli.Grammar` — the single source of truth for the command grammar
(ADR-0011 §1: machine-readable everything; the `tl help --json` schema dump).

One `commandSpecs` table drives three surfaces, so they cannot drift apart:
the argument parser (which flags/repeats each verb accepts), the human
`tl help` text, and the machine-readable `tl help --json` schema an agent
introspects. Adding a verb or flag means one edit here, and all three follow.

The `--json` schema shape is a forever-contract surface (ADR-0020,
additive-only from 1.0): `{ commands: [ { command, positionals, summary,
flags: [ { name, value, repeatable, summary } ] } ], globalFlags: [...] }`.
Pure; no I/O. -/
import Lean.Data.Json

namespace Tl.Cli

open Lean (Json)

/-- A flag: `name` without the leading `--`; `value` = takes a value (vs a
    bare boolean); `repeatable` = a second occurrence is allowed (else it is a
    usage error). -/
structure FlagSpec where
  name : String
  value : Bool
  repeatable : Bool := false
  summary : String

/-- A command and its surface. `command` is the full verb (`"dep add"` for
    subcommands); `positionals` is a human template (`"<id>"`, `""`). -/
structure CommandSpec where
  command : String
  positionals : String
  summary : String
  flags : List FlagSpec := []

/-- Flags accepted on every command (added by the parser globally). -/
def globalFlags : List FlagSpec :=
  [ { name := "json", value := false,
      summary := "emit the stable JSON envelope on stdout (errors too); the exit code carries the error" },
    { name := "dir", value := true,
      summary := "use this state directory, skipping discovery (the env var TL_DIR is the fallback)" },
    { name := "skip-bad", value := false,
      summary := "read commands only: skip malformed log lines, each disclosed on stderr" },
    { name := "color", value := true,
      summary := "auto | always | never (auto = a TTY without NO_COLOR); --json never colors" },
    { name := "glyphs", value := true,
      summary := "auto | unicode | ascii (auto detects the terminal)" },
    { name := "plain", value := false,
      summary := "shorthand for --color=never --glyphs=ascii" } ]

private def actorFlag : FlagSpec :=
  { name := "actor", value := true,
    summary := "record this actor (else TL_ACTOR, then git user.email, then user@host)" }

private def limitFlag : FlagSpec :=
  { name := "limit", value := true, summary := "max rows shown (default 50; 0 = all)" }

private def logLimitFlag : FlagSpec :=
  { name := "limit", value := true, summary := "max entries shown (0 = all; default 10, or all when --since)" }

private def logSinceFlag : FlagSpec :=
  { name := "since", value := true, summary := "only ops after this cursor — a resumable change-feed (pass the prior `cursor`)" }

private def syncFlag : FlagSpec :=
  { name := "sync", value := false,
    summary := "reconcile via refs/tl/log first, then run; best-effort — a remote failure degrades to a note, never fails the command" }

private def verifyFlag : FlagSpec :=
  { name := "verify", value := false,
    summary := "fetch + re-check readiness against the freshest state before taking; fails (verify-failed) if a configured remote is unreachable, degrades if none" }

private def stealFlag : FlagSpec :=
  { name := "steal", value := false,
    summary := "take over an already-claimed item, only if its claim is stale (see --stale / tl.staleAfter); no-op-extra on an unclaimed or own item" }

private def staleFlag : FlagSpec :=
  { name := "stale", value := true,
    summary := "the staleness window for --steal (e.g. 45m, 1h, 24h); overrides git config tl.staleAfter — no default" }

/-- The whole grammar. -/
def commandSpecs : List CommandSpec :=
  [ { command := "init", positionals := "", summary := "create the state directory (the repo toplevel, or --dir/TL_DIR)" },
    { command := "create", positionals := "<title> [-]",
      summary := "add an issue, wiring deps inline; body via --description, or `-` to read stdin",
      flags :=
        [ { name := "priority", value := true, summary := "0–4, 0 = highest (default 2); also -p" },
          { name := "blocked-by", value := true, repeatable := true, summary := "this issue is blocked by <id>" },
          { name := "blocks", value := true, repeatable := true, summary := "this issue blocks <id>" },
          { name := "parent", value := true, repeatable := true, summary := "make this issue a child of epic <id>" },
          { name := "related", value := true, repeatable := true, summary := "symmetric informational link to <id>" },
          { name := "description", value := true, summary := "the body; pass `-` (or a trailing `-`) to read it from stdin" },
          { name := "slug", value := true, summary := "optional display handle (kebab-case, digits ok; not identity)" },
          actorFlag ] },
    { command := "ready", positionals := "",
      summary := "ranked workable items: open, unblocked, non-epic, not deferred", flags := [limitFlag, syncFlag] },
    { command := "claim", positionals := "<id>",
      summary := "take a ready item (refused with structured reasons otherwise); --steal takes over a stale claim",
      flags := [actorFlag, syncFlag, verifyFlag, stealFlag, staleFlag] },
    { command := "close", positionals := "<id>",
      summary := "finish an issue; any closed status discharges its blockers",
      flags :=
        [ { name := "as", value := true, summary := "done | cancelled | duplicate (required)" },
          { name := "of", value := true, summary := "the canonical issue — only with --as duplicate" },
          actorFlag ] },
    { command := "update", positionals := "<id>",
      summary := "edit non-lifecycle scalars (status uses claim/close/reopen)",
      flags :=
        [ { name := "title", value := true, summary := "new title" },
          { name := "priority", value := true, summary := "0–4; also -p" },
          { name := "description", value := true, summary := "replace the body" },
          { name := "notes", value := true, summary := "replace the notes" },
          { name := "append-notes", value := true, summary := "append a line to the notes (read-modify-write; not atomic under concurrent writers)" },
          { name := "slug", value := true, summary := "set the display handle (kebab-case; not identity)" },
          actorFlag ] },
    { command := "reopen", positionals := "<id>",
      summary := "return a closed issue to open (clears the resolution and assignee)", flags := [actorFlag] },
    { command := "dep add", positionals := "<id> <blocked-by>",
      summary := "add a blocks edge: <id> becomes blocked by <blocked-by>", flags := [actorFlag] },
    { command := "dep remove", positionals := "<id> <blocked-by>",
      summary := "retract that blocks edge", flags := [actorFlag] },
    { command := "dep cycles", positionals := "",
      summary := "report dependency cycles (blocks / parent / readiness)" },
    { command := "dep critical", positionals := "",
      summary := "rank open issues by how many others they transitively block" },
    { command := "dep path", positionals := "<id> <id>",
      summary := "a blocks-edge path from the first issue to the second (cycle-breaking aid)" },
    { command := "dep relate", positionals := "<id> <id>",
      summary := "add a symmetric informational link between two issues", flags := [actorFlag] },
    { command := "dep unrelate", positionals := "<id> <id>",
      summary := "remove that informational link", flags := [actorFlag] },
    { command := "parent set", positionals := "<id> <new-parent>",
      summary := "set <id>'s parent to <new-parent> (replaces the current parent)", flags := [actorFlag] },
    { command := "parent remove", positionals := "<id> <parent>",
      summary := "detach <id> from <parent> (drop that parent edge)", flags := [actorFlag] },
    { command := "why", positionals := "<id>", summary := "the transitive unclosed blockers of an issue" },
    { command := "unblocks", positionals := "<id>", summary := "what closing this would make ready (its freed dependents)" },
    { command := "show", positionals := "<id>", summary := "one issue in full" },
    { command := "list", positionals := "", summary := "open issues as a hierarchy tree, oldest first (--all incl. closed; --flat for rows)",
      flags := [limitFlag,
                { name := "all", value := false, summary := "include closed (done/cancelled) issues, not just open" },
                { name := "flat", value := false,
                  summary := "one-line rows, oldest first, instead of the default hierarchy tree" },
                { name := "label", value := true, repeatable := true,
                  summary := "only issues carrying this label (repeatable ⇒ all of them)" },
                { name := "stale", value := true,
                  summary := "only stale claims: in-progress, claimed longer ago than this window (e.g. 45m, 1h, 24h); no default" }] },
    { command := "label add", positionals := "<id> <label>",
      summary := "add a label to an issue", flags := [actorFlag] },
    { command := "label remove", positionals := "<id> <label>",
      summary := "remove a label from an issue", flags := [actorFlag] },
    { command := "label list", positionals := "",
      summary := "every label in use, with issue counts" },
    { command := "meta set", positionals := "<id> <key> <value>",
      summary := "set an opaque metadata value (side-channel; drives nothing)", flags := [actorFlag] },
    { command := "meta get", positionals := "<id> [<key>]",
      summary := "read an issue's metadata (one key, or all)" },
    { command := "meta clear", positionals := "<id> <key>",
      summary := "remove a metadata key", flags := [actorFlag] },
    { command := "meta list", positionals := "[<id>]",
      summary := "metadata keys in use (one issue, or all with counts)" },
    { command := "log", positionals := "[<id>]",
      summary := "the op history, newest first (optionally one issue); --since for a resumable change-feed",
      flags := [logLimitFlag, logSinceFlag] },
    { command := "stats", positionals := "",
      summary := "counts by state plus ready / blocked / cycles totals" },
    { command := "sync", positionals := "",
      summary := "reconcile via refs/tl/log: publish + absorb siblings, then fetch/union/push to a configured remote" },
    { command := "doctor", positionals := "",
      summary := "local health checks (replica / clock / log / graph / stale claims / clock skew / sync posture)",
      flags := [syncFlag] },
    { command := "version", positionals := "", summary := "the product and log-format versions" },
    { command := "help", positionals := "[<command>]",
      summary := "this grammar — human, or machine-readable with --json" } ]

/-- The spec for an exact command name. -/
def specOf (cmd : String) : Option CommandSpec := commandSpecs.find? (·.command == cmd)

/-- The commands matching a help argument: the exact command, or all
    subcommands of a group (`"dep"` → `dep add`/`dep remove`/`dep cycles`). -/
def commandsMatching (name : String) : List CommandSpec :=
  commandSpecs.filter (fun c => c.command == name || c.command.startsWith (name ++ " "))

/-- The value-flag names a command accepts (for the parser). -/
def valFlagsOf (cmd : String) : List String :=
  ((specOf cmd).map (fun c => c.flags.filter (·.value) |>.map (·.name))).getD []

/-- The boolean-flag names a command accepts (for the parser). -/
def boolFlagsOf (cmd : String) : List String :=
  ((specOf cmd).map (fun c => c.flags.filter (fun f => !f.value) |>.map (·.name))).getD []

/-- Every value flag that may legitimately repeat (for the parser's
    repeated-flag check) — derived, so it can never disagree with the table. -/
def repeatableFlags : List String :=
  (commandSpecs.flatMap (·.flags) |>.filter (fun f => f.value && f.repeatable) |>.map (·.name)).eraseDups

/-! ### The `--json` schema (forever contract, ADR-0020) -/

private def flagJson (f : FlagSpec) : Json :=
  Json.mkObj [("name", .str f.name), ("value", .bool f.value),
              ("repeatable", .bool f.repeatable), ("summary", .str f.summary)]

private def commandJson (c : CommandSpec) : Json :=
  Json.mkObj [("command", .str c.command), ("positionals", .str c.positionals),
              ("summary", .str c.summary), ("flags", .arr (c.flags.map flagJson).toArray)]

/-- The schema dump: the whole grammar, or one command/group when `cmd` is
    given. Stable shape regardless (an agent parses `commands`/`globalFlags`
    either way). -/
def helpJson (cmd : Option String := none) : Json :=
  let cmds := match cmd with | some n => commandsMatching n | none => commandSpecs
  Json.mkObj [("commands", .arr (cmds.map commandJson).toArray),
              ("globalFlags", .arr (globalFlags.map flagJson).toArray)]

/-! ### The human help text -/

private def cmdLine (c : CommandSpec) : String :=
  let pos := if c.positionals.isEmpty then "" else " " ++ c.positionals
  s!"  tl {c.command}{pos}" ++
    (let pad := String.ofList (List.replicate (max 1 (34 - (c.command.length + pos.length + 5))) ' ')
     pad ++ c.summary)

private def flagLine (f : FlagSpec) : String :=
  let v := if f.value then " <v>" else ""
  let rep := if f.repeatable then " (repeatable)" else ""
  s!"      --{f.name}{v}{rep}  {f.summary}"

private def globalFooter : String :=
  "\nglobal flags (any command):\n" ++ String.intercalate "\n" (globalFlags.map flagLine)

/-- Human usage: the full listing, or one command/group with its flag detail. -/
def helpText (cmd : Option String := none) : String :=
  match cmd with
  | none =>
    "tl — a dependency-aware task tracker for agents\n\nusage:\n"
      ++ String.intercalate "\n" (commandSpecs.map cmdLine) ++ "\n" ++ globalFooter
  | some n =>
    let cmds := commandsMatching n
    String.intercalate "\n\n" (cmds.map (fun c =>
      cmdLine c ++ (if c.flags.isEmpty then "" else "\n" ++ String.intercalate "\n" (c.flags.map flagLine))))
      ++ "\n" ++ globalFooter

end Tl.Cli
