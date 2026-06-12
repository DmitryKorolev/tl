/-
`Tl.Cli.Render` — the human-facing rendering layer (ADR-0017).

Color and glyphs are independent surfaces (§6): `Style` carries a color mode
(`--color=auto|always|never`, honoring `NO_COLOR` and the stdout TTY) and a
glyph mode (`--glyphs=auto|unicode|ascii`); `--plain` = never + ascii. Color
is a *redundant* channel — applied per token, never the sole signal, so a
`NO_COLOR`/ascii reader loses nothing (§7).

This builds the one-line format (§1), the `show` detail view (§4) with a
children tree (§2, total on cyclic/dangling parent graphs via a visited
set), the footer/legend (§3), and the stats block (§5). `--json` never goes
through here (it is the machine contract). Tested I/O shell; no Mathlib.
-/
import Tl.Cli.Project

namespace Tl.Cli

open Tl.Store
open Tl.Kernel
open Tl.Format
open Lean (Json)

/-! ## Style: the two independent surfaces (ADR-0017 §6) -/

inductive ColorMode | on | off deriving DecidableEq
inductive GlyphMode | unicode | ascii deriving DecidableEq

structure Style where
  color : ColorMode
  glyph : GlyphMode

/-- Color off, ascii glyphs — what a pipe / `--plain` / `NO_COLOR` gets. -/
def Style.plain : Style := ⟨.off, .ascii⟩

private def rawVal (args : List String) (name : String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | a :: rest =>
      if a == name then rest.head?
      else if a.startsWith (name ++ "=") then some ((a.drop (name.length + 1)).toString)
      else go rest
  go args

/-- Resolve the style from the raw argv, `NO_COLOR`, and the stdout TTY
    (ADR-0017 §6). The two surfaces resolve independently. -/
def Style.resolve (args : List String) : IO Style := do
  let plain := args.contains "--plain"
  let noColor := (← IO.getEnv "NO_COLOR").isSome
  let tty ← (← IO.getStdout).isTty
  let color : ColorMode :=
    if plain then .off
    else match rawVal args "--color" with
      | some "always" => .on
      | some "never" => .off
      | _ => if tty && !noColor then .on else .off       -- auto
  let glyph : GlyphMode :=
    if plain then .ascii
    else match rawVal args "--glyphs" with
      | some "unicode" => .unicode
      | some "ascii" => .ascii
      | _ => if tty then .unicode else .ascii             -- auto
  return ⟨color, glyph⟩

/-! ## ANSI (built without `\x..` string escapes) -/

private def esc : String := String.singleton (Char.ofNat 27)

/-- Wrap `s` in an SGR sequence when color is on (`codes` e.g. "32", "1;31"). -/
def Style.paint (st : Style) (codes : String) (s : String) : String :=
  if st.color == .on then esc ++ "[" ++ codes ++ "m" ++ s ++ esc ++ "[0m" else s

/-! ## Status display state + glyph/color (ADR-0017 §1/§7) -/

/-- The effective display state a glyph/color reflects (§1: effective, not
    just stored). -/
inductive DState | ready | inProgress | blocked | deferred | done | cancelled
deriving DecidableEq

def displayState (v : View) (i : IssueId) : DState :=
  let s := v.state
  match State.effStatusWith v.rollup s i with
  | .Done => .done
  | .Cancelled => .cancelled
  | _ =>
    if (s.issueData i).statusOf == .InProgress then .inProgress
    else if deferredOf s v.now i then .deferred
    else if blockedOf v.rollup v.edges s i then .blocked
    else .ready

def DState.glyph (st : Style) : DState → String
  | .ready => if st.glyph == .unicode then "○" else "o"
  | .inProgress => if st.glyph == .unicode then "◐" else "*"
  | .blocked => if st.glyph == .unicode then "●" else "!"
  | .deferred => if st.glyph == .unicode then "❄" else "~"
  | .done => if st.glyph == .unicode then "✓" else "v"
  | .cancelled => if st.glyph == .unicode then "✗" else "x"

def DState.colorCode : DState → String
  | .ready => "32"        -- green
  | .inProgress => "33"   -- yellow
  | .blocked => "31"      -- red
  | .deferred => "36"     -- cyan
  | .done => "2;32"       -- dim green
  | .cancelled => "2"     -- dim/gray

def DState.word : DState → String
  | .ready => "open" | .inProgress => "in_progress" | .blocked => "blocked"
  | .deferred => "deferred" | .done => "done" | .cancelled => "cancelled"

private def prioToken (st : Style) (p : Nat) : String :=
  let codes := match p with | 0 => "1;31" | 1 => "33" | 3 => "2" | 4 => "2" | _ => ""
  let tok := s!"P{p}"
  if codes.isEmpty then tok else st.paint codes tok

/-! ## The one-line format (ADR-0017 §1) -/

/-- `<glyph> <id> <P#> [epic] <title>`, per-token colored; `title` dimmed when
    closed. Content is sanitized (ADR-0014). -/
def styledLine (st : Style) (v : View) (i : IssueId) : String :=
  let s := v.state
  let d := s.issueData i
  let ds := displayState v i
  let glyph := st.paint ds.colorCode (ds.glyph st)
  let id := st.paint "2" (displayId i)
  let prio := prioToken st d.priorityOf.val
  let epic := if !(State.kidsOfEdges v.pedges i).isEmpty then " " ++ st.paint "1" "[epic]" else ""
  let titleRaw := sanitizeSingle ((d.title.value).getD "(untitled)")
  let title := if ds == .done || ds == .cancelled then st.paint "2" titleRaw else titleRaw
  s!"{glyph} {id} {prio}{epic} {title}"

/-! ## Children tree (ADR-0017 §2) — total on cyclic/dangling parent graphs -/

private partial def treeLines (st : Style) (v : View) (i : IssueId)
    (pre : String) (visited : List IssueId) (keep : IssueId → Bool) : List String :=
  if visited.contains i then [pre ++ st.paint "2" "↺ " ++ styledLine st v i]
  else
    let kids := (v.state.presentChildren i).filter keep
    let n := kids.length
    kids.zipIdx.flatMap (fun (c, idx) =>
      let last := idx + 1 == n
      let conn := if st.glyph == .unicode then (if last then "└── " else "├── ")
                  else (if last then "\\-- " else "+-- ")
      let childPre := pre ++ (if st.glyph == .unicode then (if last then "    " else "│   ")
                              else (if last then "    " else "|   "))
      (pre ++ st.paint "2" conn ++ styledLine st v c)
        :: treeLines st v c childPre (i :: visited) keep)

/-- A forest (ADR-0017 §2, `list --tree`): each root rendered as its one-line
    node followed by its subtree. Roots are passed in (issues with no present
    canonical parent — an orphan or a dangling-parent issue renders at top
    level). Each subtree is total on cycles via `treeLines`' visited set. -/
def treeForest (st : Style) (v : View) (roots : List IssueId) (keep : IssueId → Bool) : List String :=
  roots.flatMap (fun r => styledLine st v r :: treeLines st v r "" [] keep)

/-! ## show detail view (ADR-0017 §4) -/

private def fence (st : Style) (label : String) (body : String) : List String :=
  if body.isEmpty then []
  else [st.paint "1" label, "  " ++ String.intercalate "\n  " (body.splitOn "\n"), ""]

def styledShow (st : Style) (v : View) (i : IssueId) : String := Id.run do
  let s := v.state
  let d := s.issueData i
  let ds := displayState v i
  let pr := provOf v.prov i
  let glyph := st.paint ds.colorCode (ds.glyph st)
  let idTok := st.paint "2" (displayId i)
  let statusTok := st.paint ds.colorCode ds.word
  let title := sanitizeSingle ((d.title.value).getD "(untitled)")
  let header := s!"{glyph} {idTok} · {title}   [" ++
    prioToken st d.priorityOf.val ++ " · " ++ statusTok ++ "]"
  let mut prov : List String := []
  if !(State.kidsOfEdges v.pedges i).isEmpty then prov := prov ++ [st.paint "1" "[epic]"]
  match d.assignee.value.getD none with
    | some a => prov := prov ++ [s!"assignee: {sanitizeSingle a}"] | none => pure ()
  match pr.createdAt with | some h => prov := prov ++ [s!"created:  {hlcIso h}"] | none => pure ()
  match pr.updatedAt with | some h => prov := prov ++ [s!"updated:  {hlcIso h}"] | none => pure ()
  match pr.closedAt with | some h => prov := prov ++ [s!"closed:   {hlcIso h}"] | none => pure ()
  match d.closeResolution.value.getD none with
    | some r => prov := prov ++ [s!"resolution: {resolutionWire r}"] | none => pure ()
  match d.deferUntilOf with | some t => prov := prov ++ [s!"deferred until: {Time.isoOfEpochMs t}"] | none => pure ()
  let labels := d.labels.presentElements
  let labelLine := if labels.isEmpty then []
    else ["labels: " ++ String.intercalate ", " (labels.map sanitizeSingle)]
  -- relationships
  let blockers := s.blockersOf i
  let deps := s.dependentsOf i
  let rel (label : String) (ids : List IssueId) : List String :=
    if ids.isEmpty then [] else [label ++ ": " ++ String.intercalate ", " (ids.map displayId)]
  let parentLine := match canonicalParent s i with
    | some p => ["parent: " ++ displayId p] | none => []
  let childrenBlock :=
    if (s.presentChildren i).isEmpty then []
    else st.paint "1" "children:" :: treeLines st v i "  " [] (fun _ => true)
  let body := [header] ++ (if prov.isEmpty then [] else [String.intercalate "  ·  " prov])
    ++ labelLine ++ [""]
    ++ fence st "DESCRIPTION" (sanitizeMulti ((d.description.value.getD none).getD ""))
    ++ fence st "NOTES" (sanitizeMulti ((d.notes.value.getD none).getD ""))
    ++ rel "blocked by" blockers ++ rel "blocks" deps ++ parentLine
    ++ childrenBlock
  return String.intercalate "\n" body

/-! ## Footer / legend (ADR-0017 §3) and stats block (§5) -/

/-- The glyph legend (each glyph in its color), self-documenting (§3/§7). -/
def legend (st : Style) : String :=
  let pair (ds : DState) := st.paint ds.colorCode (ds.glyph st) ++ " " ++ ds.word
  "  " ++ String.intercalate "   " ([DState.ready, .inProgress, .blocked, .deferred, .done, .cancelled].map pair)

/-- A footer: separator, a one-line summary, the legend, and a disclosed
    truncation note when a limit applied (§3 — never silent). -/
def footer (st : Style) (summary : String) (shown total : Nat) : String :=
  let rule := st.paint "2" "──"
  let trunc := if shown < total then s!"\nShowing {shown} of {total} — use --limit 0 for all" else ""
  s!"{rule}\n{summary}{trunc}\n{legend st}"

end Tl.Cli
