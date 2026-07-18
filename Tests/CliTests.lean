/-
`Tests.CliTests` — the CLI contract (ADR-0008 §`--json`, ADR-0020 shapes).

In-process rows drive `runVerb` — the same code path the binary runs —
against `--dir` temp states: per-verb payload fields, the guard refusals
with their pinned context, idempotent re-close, the dep-ack tri-state
(added/removed/noop), resolution (prefix, alias normalization, ambiguity,
slug-vs-id), doctor's checks, and the usage errors. Spawned-binary rows
cover what only a process boundary shows: stdout envelope bytes, exit
codes, `TL_DIR`, and `GIT_CEILING_DIRECTORIES`. The review-driven rows
(`--skip-bad` wiring, trailing-slash `--dir`, uppercase `TL-` tokens,
'='-bearing flag values, partial-init completion, render sanitization in
payloads, write-path refusal disclosures, the superseded claim outcome,
doctor surviving store damage) each pin a fixed contract bug.
-/
import Tl.Cli.Main
import Tests.Harness

namespace Tl.Tests

open Tl.Cli
open Tl.Store
open Tl.Kernel
open Tl.Format
open Lean (Json)

private def jGet (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
private def jStr (j : Json) (k : String) : Option String :=
  (jGet j k).bind (fun v => v.getStr?.toOption)
private def jBool (j : Json) (k : String) : Option Bool :=
  (jGet j k).bind (fun v => v.getBool?.toOption)
private def jNat (j : Json) (k : String) : Option Nat :=
  (jGet j k).bind (fun v => v.getNat?.toOption)
private def jArr (j : Json) (k : String) : List Json :=
  ((jGet j k).bind (fun v => v.getArr?.toOption)).map (·.toList) |>.getD []
/-- A string field of a nested object: `jSub j "cursor" "since"` reads
    `j.cursor.since` (the dual-edge `tl log` cursor, ADR-0025). -/
private def jSub (j : Json) (k sub : String) : Option String :=
  (jGet j k).bind (fun c => jStr c sub)

/-- Top-level member names of a JSON object, key-ascending (the canonical
    member order); `[]` for non-objects. Backs the exact-key-set shape pins:
    a field-presence predicate cannot catch an accidentally added or renamed
    payload field, `jKeys` equality can. -/
private def jKeys (j : Json) : List String :=
  match j with
  | .obj kvs => (kvs.toArray.map (·.1)).toList
  | _ => []

private def run' (args : List String) : IO (Except Tl.Error CmdOut) :=
  (runVerb args).run

private def expectData (name : String) (args : List String) (f : Json → Bool)
    (detail : Json → String := fun j => j.compress) : IO Outcome := do
  match ← run' args with
  | .ok out =>
    if f out.data then return { name, passed := true }
    else return { name, passed := false, msg := detail out.data }
  | .error e => return { name, passed := false, msg := s!"{e.code.wire}: {e.message}" }

private def expectErr (name : String) (args : List String) (code : Tl.ErrorCode)
    (ctxCheck : Tl.Error → Bool := fun _ => true) : IO Outcome := do
  match ← run' args with
  | .error e =>
    if e.code = code && ctxCheck e then return { name, passed := true }
    else return { name, passed := false, msg := s!"got {e.code.wire} ({e.message})" }
  | .ok out => return { name, passed := false, msg := s!"succeeded: {out.data.compress}" }

/-- A fresh initialized project; returns the `--dir` argument value. -/
private def freshDir : IO String := do
  let root ← IO.FS.createTempDir
  let target := (root / ".tl").toString
  let _ ← run' ["init", "--dir", target]
  return target

/-- Create an issue and return its bare id. -/
private def mkIssue (dir : String) (title : String) (extra : List String := []) : IO String := do
  match ← run' (["create", title, "--dir", dir, "--actor", "tester"] ++ extra) with
  | .ok out => return ((jStr out.data "id").getD "").drop 3 |>.toString
  | .error e => throw (IO.userError s!"create failed: {e.message}")

def cliBasicTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- version
  o := o ++ [← expectData "version payload" ["version"]
    (fun j => jStr j "version" == some "0.1.0" && jNat j "logFormat" == some 1)]
  -- licenses (ADR-0006): the embedded notice is byte-equal to the repo-root
  -- THIRD-PARTY-LICENSES file (the source of truth — a drifted regeneration
  -- fails here), human output IS the notice (human/json parity), the
  -- --licenses spelling dispatches, and positionals are refused
  let onDisk ← IO.FS.readFile "THIRD-PARTY-LICENSES"
  o := o ++
    [check "embedded thirdPartyLicenses matches THIRD-PARTY-LICENSES on disk"
       (thirdPartyLicenses == onDisk)
       s!"embedded {thirdPartyLicenses.length} bytes, file {onDisk.length} bytes — regenerate Tl/Cli/Licenses.lean from the file",
     check "the notice names the GMP/LGPLv3 obligation and libuv"
       ((thirdPartyLicenses.splitOn "GNU LESSER GENERAL PUBLIC LICENSE").length > 1
        && (thirdPartyLicenses.splitOn "libuv").length > 1) ""]
  -- drift test: the notice must attest the project's CURRENT pins. A
  -- lean-toolchain or lake-manifest.json bump fails here until the notice is
  -- regenerated (`lake env lean --run scripts/GenLicenses.lean`)
  let toolchainVer := ((← IO.FS.readFile "lean-toolchain").trimAscii.toString.splitOn ":").getLast!
  o := o ++ [check "the notice names the pinned toolchain version"
    ((thirdPartyLicenses.splitOn toolchainVer).length > 1)
    s!"lean-toolchain pins {toolchainVer} — regenerate the notice"]
  o := o ++ [match Json.parse (← IO.FS.readFile "lake-manifest.json") with
    | .ok m =>
      let revs := (jArr m "packages").filterMap (fun p => jStr p "rev")
      let missing := revs.filter (fun r => (thirdPartyLicenses.splitOn r).length ≤ 1)
      check "the notice carries every lake-manifest.json package rev"
        (!revs.isEmpty && missing.isEmpty)
        s!"manifest revs missing from the notice: {missing} — regenerate it"
    | .error e => { name := "the notice carries every manifest rev", passed := false,
                    msg := s!"lake-manifest.json did not parse: {e}" }]
  -- license-compatibility gate: every manifest package's LICENSE file must
  -- classify to the allowlist below (permissive, Apache-2.0-compatible,
  -- binary-embeddable with a notice). Adding a package under any other
  -- license — copyleft, unknown, or missing — fails here; extending the
  -- allowlist is a deliberate ADR-0006 edit, not a side effect of `lake update`
  match Json.parse (← IO.FS.readFile "lake-manifest.json") with
  | .ok m =>
    let names := (jArr m "packages").filterMap (fun p => jStr p "name")
    let mut bad : List String := []
    for n in names do
      let licPath := System.FilePath.mk ".lake" / "packages" / n / "LICENSE"
      let text ← try IO.FS.readFile licPath catch _ => pure ""
      -- allowlist, anchored to the head of the file (a license names itself
      -- up top; a mere mention further down must not classify the file)
      let head := String.intercalate "\n" ((text.splitOn "\n").take 40)
      let isApache := (head.splitOn "Apache License").length > 1
        && (head.splitOn "Version 2.0").length > 1
      let isMit := (head.splitOn "MIT License").length > 1
        || (head.splitOn "Permission is hereby granted, free of charge").length > 1
      -- belt for dual/mixed grants: the shared all-caps title substring of the
      -- whole GPL family (GPL, LGPL, AGPL — "GNU [LESSER|AFFERO] GENERAL
      -- PUBLIC LICENSE") anywhere in the file forces a human decision even if
      -- the head classified as permissive
      let gplFamily := (text.splitOn "GENERAL PUBLIC LICENSE").length > 1
      if !(isApache || isMit) || gplFamily then bad := bad ++ [n]
    o := o ++ [check "every manifest package license is on the permissive allowlist (Apache-2.0/MIT)"
      (!names.isEmpty && bad.isEmpty)
      s!"packages with a missing/copyleft/unclassified LICENSE: {bad} — an incompatible license needs an ADR-0006 decision, not a silent dep add"]
  | .error e =>
    o := o ++ [{ name := "manifest license allowlist", passed := false,
                 msg := s!"lake-manifest.json did not parse: {e}" }]
  o := o ++ [← expectData "licenses payload carries the notice text" ["licenses"]
    (fun j => jStr j "text" == some thirdPartyLicenses) (fun _ => "text ≠ embedded notice")]
  o := o ++ [match ← run' ["licenses"] with
    | .ok out => check "licenses human output is the notice (final newline deferred to println)"
        (out.human ++ "\n" == thirdPartyLicenses) ""
    | .error e => { name := "licenses human output", passed := false, msg := e.message }]
  o := o ++ [← expectData "--licenses dispatches like licenses" ["--licenses"]
    (fun j => jStr j "text" == some thirdPartyLicenses) (fun _ => "text ≠ embedded notice")]
  o := o ++ [← expectErr "licenses refuses positionals" ["licenses", "extra"] .usage]
  -- init: created, file contents, idempotent rerun
  let root ← IO.FS.createTempDir
  let target := (root / ".tl").toString
  o := o ++ [← expectData "init creates" ["init", "--dir", target]
    (fun j => jBool j "created" == some true && (jStr j "replica").isSome)]
  let replicaFile ← IO.FS.readFile (root / ".tl" / "local" / "replica")
  let gitignore ← IO.FS.readFile (root / ".tl" / ".gitignore")
  o := o ++
    [check "init minted a valid replica" (Tl.Clock.Replica.mk replicaFile.trimAscii.toString).valid,
     check "init wrote the * self-ignore" (gitignore == "*\n"),
     ← expectData "init is idempotent" ["init", "--dir", target]
       (fun j => jBool j "created" == some false)]
  -- discovery (ADR-0011 §3): init writes the gitignored primer and suggests
  -- the committed pointer without editing the user's agent file
  let root3 ← IO.FS.createTempDir
  IO.FS.writeFile (root3 / "AGENTS.md") "# proj\n"
  let initRes ← run' ["init", "--dir", (root3 / ".tl").toString]
  o := o ++
    [(match initRes with
      | .ok out => check "init suggests the discovery pointer in its notes"
          (out.notes.any (fun n => (n.splitOn "discoverable").length > 1))
          (String.intercalate "|" out.notes)
      | .error e => { name := "init suggests the discovery pointer", passed := false, msg := e.message }),
     check "init wrote the .tl/README.md primer"
       ((← IO.FS.readFile (root3 / ".tl" / "README.md")).startsWith "# tl"),
     check "init left a pre-existing AGENTS.md untouched"
       ((← IO.FS.readFile (root3 / "AGENTS.md")) == "# proj\n")]
  -- create echo (ADR-0020): display id, defaults, provenance, dependencies
  let dir ← freshDir
  o := o ++ [← expectData "create echoes the full issue"
    ["create", "Design the AST", "--dir", dir, "-p", "0", "--actor", "carol"]
    (fun j =>
      ((jStr j "id").getD "").startsWith "tl-"
      && jStr j "status" == some "open" && jStr j "effectiveStatus" == some "open"
      && jNat j "priority" == some 0 && jBool j "ready" == some true
      && jBool j "isEpic" == some false
      && ((jGet j "provenance").bind (fun p => jStr p "createdBy")) == some "carol"
      && (jStr j "createdAt").isSome && (jStr j "updatedAt").isSome)]
  -- default priority is 2
  o := o ++ [← expectData "create defaults priority 2" ["create", "x", "--dir", dir, "--actor", "t"]
    (fun j => jNat j "priority" == some 2)]
  -- sync progress notice (stderr-only, sanitized before it bypasses Main's chokepoint)
  o := o ++
    [check "remoteSyncNotice names the resolved remote"
       (remoteSyncNotice "origin" == "syncing with remote 'origin'…"),
     check "the surfaced sync notice strips control/ANSI bytes from the remote name"
       (sanitizeSingle (remoteSyncNotice "ev\x1b[31mil") == "syncing with remote 'evil'…")]
  return o

def cliWorkLoopTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let blocker ← mkIssue dir "Design the AST" ["-p", "0"]
  let blocked ← mkIssue dir "Write the parser" ["--blocked-by", "tl-" ++ blocker]
  -- ready: ranked, the blocked issue excluded; count/items; limit
  o := o ++
    [← expectData "ready lists only workable items" ["ready", "--dir", dir]
      (fun j => jNat j "count" == some 1
        && (jArr j "items").all (fun r => jStr r "id" == some ("tl-" ++ blocker))),
     ← expectData "create with inline edge shows dependencies"
       ["show", "tl-" ++ blocked, "--dir", dir]
       (fun j => (jArr j "dependencies").length == 1
         && jBool j "blocked" == some true && jBool j "ready" == some false),
     ← expectData "list counts all, capped items" ["list", "--dir", dir, "--limit", "1"]
       (fun j => jNat j "count" == some 2 && (jArr j "items").length == 1),
     ← expectData "--limit 0 means all" ["list", "--dir", dir, "--limit", "0"]
       (fun j => (jArr j "items").length == 2)]
  -- why: transitive blockers with direct flag
  o := o ++ [← expectData "why names the blocker" ["why", "tl-" ++ blocked, "--dir", dir]
    (fun j => jBool j "ready" == some false
      && (jArr j "blockedBy").all (fun r =>
            jStr r "id" == some ("tl-" ++ blocker) && jBool r "direct" == some true))]
  -- unblocks: the downward mirror — closing the blocker frees the blocked issue
  o := o ++ [← expectData "unblocks names the freed dependent" ["unblocks", "tl-" ++ blocker, "--dir", dir]
    (fun j => jNat j "count" == some 1
      && (jArr j "freed").all (fun r => jStr r "id" == some ("tl-" ++ blocked))),
   ← expectData "unblocks of a leaf frees nothing" ["unblocks", "tl-" ++ blocked, "--dir", dir]
    (fun j => jNat j "count" == some 0 && (jArr j "freed").length == 0)]
  -- dep critical: the blocker outranks the leaf (weight = transitive dependents)
  o := o ++ [← expectData "dep critical ranks the blocker first" ["dep", "critical", "--dir", dir]
    (fun j => jNat j "count" == some 1
      && ((jArr j "items").head?.bind (fun r => jStr r "id")) == some ("tl-" ++ blocker))]
  -- dep relate / unrelate: a symmetric link, visible in dependencies, retractable
  o := o ++ [← expectData "dep relate links two issues"
      ["dep", "relate", "tl-" ++ blocker, "tl-" ++ blocked, "--dir", dir, "--actor", "t"]
    (fun j => jStr j "status" == some "added"),
   ← expectData "the related edge shows in dependencies" ["show", "tl-" ++ blocker, "--dir", dir]
    (fun j => (jArr j "dependencies").any (fun e => jStr e "type" == some "related")),
   ← expectData "dep unrelate retracts it"
      ["dep", "unrelate", "tl-" ++ blocker, "tl-" ++ blocked, "--dir", dir, "--actor", "t"]
    (fun j => jStr j "status" == some "removed"),
   ← expectData "the related edge is gone" ["show", "tl-" ++ blocker, "--dir", dir]
    (fun j => !((jArr j "dependencies").any (fun e => jStr e "type" == some "related")))]
  -- claim refusals: not-ready target, with blockedBy reasons
  o := o ++ [← expectErr "claim of a blocked issue is not-claimable"
    ["claim", "tl-" ++ blocked, "--dir", dir, "--actor", "carol"] .notClaimable
    (fun e => e.context.any (fun (k, v) =>
      k == "reasons" && ((jGet v "blockedBy").isSome)))]
  -- claim the ready one: outcome won, assignee set
  o := o ++ [← expectData "claim wins and echoes the claim block"
    ["claim", "tl-" ++ blocker, "--dir", dir, "--actor", "carol"]
    (fun j => jStr j "assignee" == some "carol" && jStr j "status" == some "in_progress"
      && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won")]
  -- show now carries the recent-claim block
  o := o ++ [← expectData "show carries the recent claim block"
    ["show", "tl-" ++ blocker, "--dir", dir]
    (fun j => ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won")]
  -- already-claimed target refuses with assignee reason
  o := o ++ [← expectErr "claim of an in-progress issue is not-claimable"
    ["claim", "tl-" ++ blocker, "--dir", dir, "--actor", "dana"] .notClaimable
    (fun e => e.context.any (fun (k, v) =>
      k == "reasons" && ((jGet v "assignee").isSome || (jGet v "status").isSome)))]
  -- close: unblocked carries the freed dependent
  o := o ++ [← expectData "close frees the dependent (unblocked)"
    ["close", "tl-" ++ blocker, "--dir", dir, "--as", "done", "--actor", "carol"]
    (fun j => jStr j "closeResolution" == some "done" && (jStr j "closedAt").isSome
      && (jArr j "unblocked").any (fun x => x.getStr?.toOption == some ("tl-" ++ blocked)))]
  -- idempotent re-close: succeeds, empty unblocked, still closed
  o := o ++ [← expectData "re-close with the same resolution is a no-op"
    ["close", "tl-" ++ blocker, "--dir", dir, "--as", "done", "--actor", "carol"]
    (fun j => jStr j "status" == some "done" && (jArr j "unblocked").isEmpty)]
  -- different resolution is a plain rewrite
  o := o ++ [← expectData "re-close with a different resolution rewrites"
    ["close", "tl-" ++ blocker, "--dir", dir, "--as", "cancelled", "--actor", "carol"]
    (fun j => jStr j "closeResolution" == some "cancelled" && jStr j "status" == some "cancelled")]
  -- update echo
  o := o ++
    [← expectData "update rewrites the title"
      ["update", "tl-" ++ blocked, "--dir", dir, "--title", "Parser v2", "--actor", "t"]
      (fun j => jStr j "title" == some "Parser v2"),
     ← expectErr "update without flags is usage"
       ["update", "tl-" ++ blocked, "--dir", dir] .usage]
  -- append-notes: seeds when empty, then joins onto the prior notes with a newline;
  -- --notes still replaces wholesale; the two flags conflict
  o := o ++
    [← expectData "append-notes seeds notes when empty"
       ["update", "tl-" ++ blocked, "--dir", dir, "--append-notes", "first", "--actor", "t"]
       (fun j => jStr j "notes" == some "first"),
     ← expectData "append-notes joins onto existing notes with a newline"
       ["update", "tl-" ++ blocked, "--dir", dir, "--append-notes", "second", "--actor", "t"]
       (fun j => jStr j "notes" == some "first\nsecond"),
     ← expectData "--notes replaces the accumulated notes wholesale"
       ["update", "tl-" ++ blocked, "--dir", dir, "--notes", "reset", "--actor", "t"]
       (fun j => jStr j "notes" == some "reset"),
     ← expectErr "--notes and --append-notes together is usage"
       ["update", "tl-" ++ blocked, "--dir", dir, "--notes", "x", "--append-notes", "y",
        "--actor", "t"] .usage]
  return o

def cliCloseGuardTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let epic ← mkIssue dir "The epic"
  let child ← mkIssue dir "The child" ["--parent", "tl-" ++ epic]
  -- epic --as done refused with openChildren context
  o := o ++ [← expectErr "epic close --as done is not-closeable"
    ["close", "tl-" ++ epic, "--dir", dir, "--as", "done", "--actor", "t"] .notCloseable
    (fun e => e.context.any (fun (k, v) =>
      k == "reasons" && (jGet v "openChildren").isSome))]
  -- --as cancelled is allowed on an epic
  o := o ++ [← expectData "epic close --as cancelled is allowed"
    ["close", "tl-" ++ epic, "--dir", dir, "--as", "cancelled", "--actor", "t"]
    (fun j => jStr j "status" == some "cancelled")]
  -- all-children-closed epic: --as done is still refused (rollup-only, ADR-0003),
  -- but the message must not read the contradictory "open: 0" — it teaches
  -- already-done-via-rollup, and openChildren is the empty array
  let epic2 ← mkIssue dir "Rolled-up epic"
  let child2 ← mkIssue dir "Last child" ["--parent", "tl-" ++ epic2]
  let _ ← run' ["close", "tl-" ++ child2, "--dir", dir, "--as", "done", "--actor", "t"]
  o := o ++
    [← expectErr "epic close --as done with all children closed teaches rollup (not 'open: 0')"
      ["close", "tl-" ++ epic2, "--dir", dir, "--as", "done", "--actor", "t"] .notCloseable
      (fun e => (e.message.splitOn "already done via child rollup").length > 1
        && (e.message.splitOn "open:").length == 1)]
  -- duplicate: stored canonical target renders in display form
  let canonical ← mkIssue dir "The canonical"
  let dupe ← mkIssue dir "The dupe"
  o := o ++
    [← expectErr "self-duplicate is not-closeable"
      ["close", "tl-" ++ dupe, "--dir", dir, "--as", "duplicate", "--of", "tl-" ++ dupe,
       "--actor", "t"] .notCloseable
      (fun e => e.context.any (fun (k, v) =>
        k == "reasons" && (jGet v "selfDuplicate").isSome)),
     ← expectData "close --as duplicate records the canonical target"
       ["close", "tl-" ++ dupe, "--dir", dir, "--as", "duplicate", "--of", "tl-" ++ canonical,
        "--actor", "t"]
       (fun j => jStr j "status" == some "cancelled"
         && jStr j "closeResolution" == some "duplicate"
         && ((jGet j "meta").bind (fun m => jStr m "duplicate-of")) == some ("tl-" ++ canonical)),
     ← expectData "duplicate re-close with the same target is a no-op"
       ["close", "tl-" ++ dupe, "--dir", dir, "--as", "duplicate", "--of", "tl-" ++ canonical,
        "--actor", "t"]
       (fun j => jStr j "closeResolution" == some "duplicate"),
     -- deliberately allowed (the pinned `close --as duplicate [--of <id>]`
     -- surface): a targetless duplicate closes as cancelled/duplicate and
     -- records no duplicate-of meta — not an oversight
     ← (do
       let loner ← mkIssue dir "Targetless dupe"
       expectData "targetless --as duplicate is allowed (pinned contract)"
         ["close", "tl-" ++ loner, "--dir", dir, "--as", "duplicate", "--actor", "t"]
         (fun j => jStr j "status" == some "cancelled"
           && jStr j "closeResolution" == some "duplicate"
           && ((jGet j "meta").bind (fun m => jStr m "duplicate-of")).isNone)),
     ← expectData "child close completes the epic by rollup"
       (["close", "tl-" ++ child, "--dir", dir, "--as", "done", "--actor", "t"])
       (fun j => jStr j "status" == some "done")]
  -- the cancelled epic stays cancelled (manual-cancel precedence)
  o := o ++ [← expectData "manual epic cancel takes precedence over rollup"
    ["show", "tl-" ++ epic, "--dir", dir]
    (fun j => jStr j "effectiveStatus" == some "cancelled")]
  return o

def cliDepTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let a ← mkIssue dir "A"
  let b ← mkIssue dir "B"
  o := o ++
    [← expectData "dep add acks the edge"
      ["dep", "add", "tl-" ++ a, "tl-" ++ b, "--dir", dir, "--actor", "t"]
      (fun j => jStr j "type" == some "blocks" && jStr j "from" == some ("tl-" ++ b)
        && jStr j "to" == some ("tl-" ++ a) && jStr j "status" == some "added"),
     ← expectData "dep remove acks removal"
      ["dep", "remove", "tl-" ++ a, "tl-" ++ b, "--dir", dir, "--actor", "t"]
      (fun j => jStr j "status" == some "removed"),
     ← expectData "second dep remove is a disclosed noop"
      ["dep", "remove", "tl-" ++ a, "tl-" ++ b, "--dir", dir, "--actor", "t"]
      (fun j => jStr j "status" == some "noop")]
  -- a cycle: A blocked by B, B blocked by A
  let _ ← run' ["dep", "add", "tl-" ++ a, "tl-" ++ b, "--dir", dir, "--actor", "t"]
  let _ ← run' ["dep", "add", "tl-" ++ b, "tl-" ++ a, "--dir", dir, "--actor", "t"]
  o := o ++
    [← expectData "dep cycles reports the SCC witness" ["dep", "cycles", "--dir", dir]
      (fun j => jNat j "count" == some 1
        && (jArr j "cycles").all (fun c =>
             jStr c "kind" == some "blocks" && (jArr c "issues").length == 2)),
     ← expectData "doctor fails the graph check on a cycle" ["doctor", "--dir", dir]
      (fun j => jBool j "healthy" == some false
        && (jArr j "checks").any (fun c =>
             jStr c "name" == some "graph" && jStr c "status" == some "fail"
               && jNat c "cycles" == some 1)),
     ← expectData "neither cycle member is ready" ["ready", "--dir", dir]
      (fun j => jNat j "count" == some 0)]
  -- the human repair hint is kind-aware. Blocks-only witnesses teach
  -- `dep remove` and must not mention the parent verbs
  o := o ++ [← (match ← run' ["dep", "cycles", "--dir", dir] with
    | .ok out => pure (check "dep cycles hint for a blocks cycle teaches dep remove only"
        ((out.human.splitOn "tl dep remove").length > 1
          && (out.human.splitOn "tl parent").length == 1) out.human)
    | .error e => pure { name := "dep cycles hint (blocks)", passed := false, msg := e.message })]
  -- an incidental parent edge between the two blocks-cycle members is not
  -- part of any reported cycle (removing it cannot break one): the report
  -- stays a single blocks row and the hint must not name the parent verbs
  let _ ← run' ["parent", "set", "tl-" ++ a, "tl-" ++ b, "--dir", dir, "--actor", "t"]
  o := o ++
    [← expectData "an incidental parent edge adds no cycle row"
      ["dep", "cycles", "--dir", dir]
      (fun j => jNat j "count" == some 1
        && (jArr j "cycles").all (fun c => jStr c "kind" == some "blocks")),
     ← (match ← run' ["dep", "cycles", "--dir", dir] with
       | .ok out => pure (check
           "dep cycles hint ignores an incidental parent edge in a blocks witness"
           ((out.human.splitOn "tl dep remove").length > 1
             && (out.human.splitOn "tl parent").length == 1) out.human)
       | .error e => pure { name := "dep cycles hint (incidental parent)",
                            passed := false, msg := e.message })]
  -- parent-kind witness: a 2-cycle in the parent graph (`parent set` refuses
  -- only the direct self-parent; longer cycles are reported, not rejected)
  let pdir ← freshDir
  let p1 ← mkIssue pdir "P1"
  let p2 ← mkIssue pdir "P2"
  let _ ← run' ["parent", "set", "tl-" ++ p1, "tl-" ++ p2, "--dir", pdir, "--actor", "t"]
  let _ ← run' ["parent", "set", "tl-" ++ p2, "tl-" ++ p1, "--dir", pdir, "--actor", "t"]
  o := o ++
    [← expectData "dep cycles reports a parent-kind witness" ["dep", "cycles", "--dir", pdir]
      (fun j => jNat j "count" == some 1
        && (jArr j "cycles").all (fun c =>
             jStr c "kind" == some "parent" && (jArr c "issues").length == 2)),
     ← (match ← run' ["dep", "cycles", "--dir", pdir] with
       | .ok out => pure (check "dep cycles hint for a parent cycle teaches parent remove/set only"
           ((out.human.splitOn "tl parent remove").length > 1
             && (out.human.splitOn "tl parent set").length > 1
             && (out.human.splitOn "tl dep remove").length == 1) out.human)
       | .error e => pure { name := "dep cycles hint (parent)", passed := false, msg := e.message })]
  -- a blocks cycle beside the parent cycle: the hint teaches both verbs
  let p3 ← mkIssue pdir "P3"
  let p4 ← mkIssue pdir "P4"
  let _ ← run' ["dep", "add", "tl-" ++ p3, "tl-" ++ p4, "--dir", pdir, "--actor", "t"]
  let _ ← run' ["dep", "add", "tl-" ++ p4, "tl-" ++ p3, "--dir", pdir, "--actor", "t"]
  o := o ++ [← (match ← run' ["dep", "cycles", "--dir", pdir] with
    | .ok out => pure (check "dep cycles hint for mixed kinds teaches both verbs"
        ((out.human.splitOn "tl dep remove").length > 1
          && (out.human.splitOn "tl parent remove").length > 1) out.human)
    | .error e => pure { name := "dep cycles hint (mixed)", passed := false, msg := e.message })]
  -- a mixed-kind readiness deadlock (the epic rollup-waits on its child over
  -- a parent edge; the child is blocked by the epic over a blocks edge):
  -- both kinds occur inside the witness, so the hint teaches both verbs
  let rdir ← freshDir
  let re ← mkIssue rdir "R epic"
  let rc ← mkIssue rdir "R child" ["--parent", "tl-" ++ re]
  let _ ← run' ["dep", "add", "tl-" ++ rc, "tl-" ++ re, "--dir", rdir, "--actor", "t"]
  o := o ++
    [← expectData "dep cycles reports the readiness deadlock witness"
      ["dep", "cycles", "--dir", rdir]
      (fun j => jNat j "count" == some 1
        && (jArr j "cycles").all (fun c => jStr c "kind" == some "readiness")),
     ← (match ← run' ["dep", "cycles", "--dir", rdir] with
       | .ok out => pure (check "dep cycles hint for a mixed readiness deadlock teaches both verbs"
           ((out.human.splitOn "tl dep remove").length > 1
             && (out.human.splitOn "tl parent remove").length > 1) out.human)
       | .error e => pure { name := "dep cycles hint (readiness)", passed := false, msg := e.message })]
  -- a readiness witness is not always mixed-kind (`precCycles`: pure-blocks or
  -- mixed): blocks 2-cycles A↔B and B↔C with C closed leave one structural
  -- witness {A,B,C} but a pure-blocks precedence cycle {A,B} — a distinct node
  -- set that survives the readiness dedup filter. With zero parent edges in
  -- the state, the hint must not name the parent verbs
  let sdir ← freshDir
  let sa ← mkIssue sdir "SA"
  let sb ← mkIssue sdir "SB"
  let sc ← mkIssue sdir "SC"
  let _ ← run' ["dep", "add", "tl-" ++ sa, "tl-" ++ sb, "--dir", sdir, "--actor", "t"]
  let _ ← run' ["dep", "add", "tl-" ++ sb, "tl-" ++ sa, "--dir", sdir, "--actor", "t"]
  let _ ← run' ["dep", "add", "tl-" ++ sb, "tl-" ++ sc, "--dir", sdir, "--actor", "t"]
  let _ ← run' ["dep", "add", "tl-" ++ sc, "tl-" ++ sb, "--dir", sdir, "--actor", "t"]
  let _ ← run' ["close", "tl-" ++ sc, "--dir", sdir, "--as", "cancelled", "--actor", "t"]
  o := o ++
    [← expectData "a pure-blocks readiness witness survives the dedup filter"
      ["dep", "cycles", "--dir", sdir]
      (fun j => (jArr j "cycles").any (fun c => jStr c "kind" == some "readiness")
        && (jArr j "cycles").any (fun c => jStr c "kind" == some "blocks")
        && !(jArr j "cycles").any (fun c => jStr c "kind" == some "parent")),
     ← (match ← run' ["dep", "cycles", "--dir", sdir] with
       | .ok out => pure (check "dep cycles hint for a pure-blocks readiness witness teaches dep remove only"
           ((out.human.splitOn "tl dep remove").length > 1
             && (out.human.splitOn "tl parent").length == 1) out.human)
       | .error e => pure { name := "dep cycles hint (pure-blocks readiness)", passed := false, msg := e.message })]
  -- dep path (over the proved blocksPath extractor): a chain c blocks d blocks e
  -- (`dep add X Y` makes Y block X, so add d⊣c and e⊣d)
  let c ← mkIssue dir "C"
  let dd ← mkIssue dir "D"
  let e ← mkIssue dir "E"
  let _ ← run' ["dep", "add", "tl-" ++ dd, "tl-" ++ c, "--dir", dir, "--actor", "t"]
  let _ ← run' ["dep", "add", "tl-" ++ e, "tl-" ++ dd, "--dir", dir, "--actor", "t"]
  o := o ++
    [← expectData "dep path finds the transitive blocks chain"
      ["dep", "path", "tl-" ++ c, "tl-" ++ e, "--dir", dir]
      (fun j => jBool j "found" == some true
        && jStr j "from" == some ("tl-" ++ c) && jStr j "to" == some ("tl-" ++ e)
        && (jArr j "path").map (·.getStr?.toOption)
             == [some ("tl-" ++ c), some ("tl-" ++ dd), some ("tl-" ++ e)]),
     ← expectData "dep path reports no path in the reverse direction"
      ["dep", "path", "tl-" ++ e, "tl-" ++ c, "--dir", dir]
      (fun j => jBool j "found" == some false && (jArr j "path").isEmpty),
     ← expectData "dep path A A is empty when A is on no cycle"
      ["dep", "path", "tl-" ++ c, "tl-" ++ c, "--dir", dir]
      (fun j => jBool j "found" == some false),
     -- total on a cyclic graph: the a↔b blocks cycle built above still terminates
     ← expectData "dep path terminates and finds a path inside a blocks cycle"
      ["dep", "path", "tl-" ++ a, "tl-" ++ b, "--dir", dir]
      (fun j => jBool j "found" == some true && !(jArr j "path").isEmpty),
     -- wrong arity is a usage error (the new dep path dispatch branch)
     ← expectErr "dep path with one positional is usage"
      ["dep", "path", "tl-" ++ c, "--dir", dir] .usage]
  -- why renders the human blocker tree over the production liveBlockers accessor
  -- (the JSON tests don't read the rendered human; this covers that branch).
  -- why e: its blocker d, with d's blocker c nested under it (e⊣d⊣c).
  let whyOut ← run' ["why", "tl-" ++ e, "--dir", dir]
  o := o ++ [(match whyOut with
    | .ok out =>
      let h := (out.render.map (· Style.plain)).getD out.human
      -- styledLine renders the short id (tl- + first 4 chars); the tree nests c
      -- (d's blocker) under d (e's direct blocker) with the ascii last-connector
      check "why renders the nested blocker tree (production render path)"
        ((h.splitOn "\\-- ").length != 1
          && (h.splitOn ("tl-" ++ dd.take 4)).length != 1
          && (h.splitOn ("tl-" ++ c.take 4)).length != 1) h
    | .error er => { name := "why renders the nested blocker tree", passed := false, msg := er.message })]
  return o

/-- Reparenting (ADR-0003 §4): `parent set` is a courtesy replace (move under a
    new parent, dropping the old), `parent remove` detaches; multi-parent stays
    reported by `doctor`, never enforced, and a local `set` collapses it. -/
def cliReparentTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let e1 ← mkIssue dir "epic one"
  let e2 ← mkIssue dir "epic two"
  let t ← mkIssue dir "a task"
  -- move a root under an epic: canonical parent reflects it, status set, nothing replaced
  o := o ++ [← expectData "parent set moves a root under an epic"
    ["parent", "set", "tl-" ++ t, "tl-" ++ e1, "--dir", dir, "--actor", "t"]
    (fun j => jStr j "parent" == some ("tl-" ++ e1)
      && ((jGet j "reparent").bind (fun c => jStr c "status")) == some "set"
      && ((jGet j "reparent").map (fun c => (jArr c "replaced").isEmpty)) == some true)]
  -- reparent to a second epic replaces the first (replaced lists the old parent)
  o := o ++ [← expectData "parent set replaces the current parent"
    ["parent", "set", "tl-" ++ t, "tl-" ++ e2, "--dir", dir, "--actor", "t"]
    (fun j => jStr j "parent" == some ("tl-" ++ e2)
      && ((jGet j "reparent").bind (fun c => jStr c "status")) == some "set"
      && ((jGet j "reparent").map (fun c => (jArr c "replaced").any
            (fun x => x.getStr?.toOption == some ("tl-" ++ e1)))) == some true)]
  -- idempotent: already under e2 → noop, appends nothing
  o := o ++ [← expectData "parent set to the current parent is a noop"
    ["parent", "set", "tl-" ++ t, "tl-" ++ e2, "--dir", dir, "--actor", "t"]
    (fun j => ((jGet j "reparent").bind (fun c => jStr c "status")) == some "noop")]
  -- self-parent is a courtesy usage refusal
  o := o ++ [← expectErr "a task cannot be its own parent"
    ["parent", "set", "tl-" ++ t, "tl-" ++ t, "--dir", dir, "--actor", "t"] .usage]
  -- detach: parent remove drops the edge; the child becomes a root (no parent)
  o := o ++ [← expectData "parent remove detaches the child (now a root)"
    ["parent", "remove", "tl-" ++ t, "tl-" ++ e2, "--dir", dir, "--actor", "t"]
    (fun j => ((jGet j "reparent").bind (fun c => jStr c "status")) == some "removed"
      && (jGet j "parent").isNone)]
  o := o ++ [← expectData "a second parent remove is a disclosed noop"
    ["parent", "remove", "tl-" ++ t, "tl-" ++ e2, "--dir", dir, "--actor", "t"]
    (fun j => ((jGet j "reparent").bind (fun c => jStr c "status")) == some "noop")]
  -- multi-parent: a child born under two epics is reported by doctor (never
  -- rejected); a local `parent set` collapses it to a single parent
  let m ← freshDir
  let me1 ← mkIssue m "M epic one"
  let me2 ← mkIssue m "M epic two"
  let kid ← match ← run' ["create", "multi kid", "--dir", m, "--actor", "t",
                          "--parent", "tl-" ++ me1, "--parent", "tl-" ++ me2] with
    | .ok out => pure ((jStr out.data "id").getD "")
    | .error e => throw (IO.userError s!"create failed: {e.message}")
  o := o ++ [← expectData "doctor reports a born multi-parent" ["doctor", "--dir", m]
    (fun j => (jArr j "checks").any (fun c =>
      jStr c "name" == some "graph" && jNat c "multiParent" == some 1))]
  let _ ← run' ["parent", "set", kid, "tl-" ++ me1, "--dir", m, "--actor", "t"]
  o := o ++ [← expectData "parent set collapses the multi-parent" ["doctor", "--dir", m]
    (fun j => (jArr j "checks").any (fun c =>
      jStr c "name" == some "graph" && jNat c "multiParent" == some 0))]
  return o

def cliResolutionTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let a ← mkIssue dir "Target"
  -- prefix + alias/case normalization (o→0, i/l→1, case-fold)
  let prefix6 := (a.take 6).toString
  let aliased := String.ofList (prefix6.toList.map (fun c =>
    if c == '0' then 'O' else if c == '1' then 'l' else c.toUpper))
  o := o ++
    [← expectData "id prefix resolves" ["show", "tl-" ++ prefix6, "--dir", dir]
      (fun j => jStr j "id" == some ("tl-" ++ a)),
     ← expectData "aliased/uppercase id resolves" ["show", "tl-" ++ aliased, "--dir", dir]
      (fun j => jStr j "id" == some ("tl-" ++ a)),
     ← expectErr "unknown id is not-found" ["show", "tl-zzzzzzzzzzzzzzzz", "--dir", dir]
       .notFound,
     ← expectErr "a bare token is a slug, never an id" ["show", a, "--dir", dir] .notFound,
     ← expectErr "missing project is no-project" ["ready", "--dir", "/tmp/definitely-not-a-tl"]
       .noProject]
  -- ambiguity (pure resolver — crafted ids; CLI ids are random hashes)
  let st : Tl.Crdt.Stamp := ⟨1, 1, 1⟩
  let s := Tl.Kernel.fold
    [Tl.Kernel.Op.create "aaaaaaaaaaaaaaa0" st {},
     Tl.Kernel.Op.create "aaaaaaaaaaaaaaa1" { st with nonce := 2 } {}]
  o := o ++
    [check "shared prefix is ambiguous-id"
      (match resolveToken s "tl-aaaa" with
       | .error e => e.code == .ambiguousId
           && e.context.any (fun (k, v) => k == "candidates" && (v.getArr?.toOption.any (·.size == 2)))
       | .ok _ => false),
     check "the full id still resolves despite the shared prefix"
      (match resolveToken s "tl-aaaaaaaaaaaaaaa0" with
       | .ok i => i == "aaaaaaaaaaaaaaa0"
       | .error _ => false)]
  return o

def cliUsageTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  o := o ++
    [← expectErr "unknown command is usage" ["frobnicate"] .usage,
     ← expectErr "unknown flag is usage" ["ready", "--dir", dir, "--bogus"] .usage,
     ← expectErr "close without --as is usage" ["close", "tl-x", "--dir", dir] .usage,
     ← expectErr "close with a bad --as is usage"
       ["close", "tl-x", "--dir", dir, "--as", "wontfix"] .usage,
     ← expectErr "bad --limit is usage" ["ready", "--dir", dir, "--limit", "many"] .usage,
     ← expectErr "out-of-range -p is usage" ["create", "x", "--dir", dir, "-p", "9"] .usage,
     ← expectErr "missing flag value is usage" ["ready", "--dir"] .usage,
     -- the provenance flag is --actor (ADR-0013 actor/assignee split); the old --assignee
     -- spelling is dropped (reserved for the future assignee read filter) and now
     -- rejects as an unknown flag — a deliberate pre-1.0 breaking change.
     ← expectErr "the dropped --assignee provenance flag is now an unknown flag (usage)"
       ["create", "x", "--dir", dir, "--assignee", "carol"] .usage]
  -- --actor records provenance (the rename's positive half)
  o := o ++ [← expectData "the --actor flag records the provenance actor"
      ["create", "actored", "--dir", dir, "--actor", "grace"]
      (fun j => (jGet j "provenance").bind (fun p => jStr p "createdBy") == some "grace")]
  return o

/-- Spawned-binary rows: stdout envelope bytes, exit codes, env discovery. -/
def cliBinaryTests : IO (List Outcome) := do
  let exe := (← IO.currentDir) / ".lake" / "build" / "bin" / "tl"
  unless ← exe.pathExists do
    return [{ name := "binary present", passed := false,
              msg := "run `lake build` first: .lake/build/bin/tl missing" }]
  let mut o : List Outcome := []
  let spawn (args : List String) (env : List (String × Option String) := [])
      (cwd : Option System.FilePath := none) : IO IO.Process.Output :=
    IO.Process.output { cmd := exe.toString, args := args.toArray,
                        env := env.toArray, cwd }
  -- exact envelope bytes + exit code on stdout
  let out ← spawn ["version", "--json"]
  o := o ++
    [check "version --json envelope bytes"
      (out.stdout == "{\"schemaVersion\":2,\"ok\":true,\"data\":{\"logFormat\":1,\"version\":\"0.1.0\"}}\n")
      out.stdout,
     check "version exits 0" (out.exitCode == 0)]
  -- `tl licenses` stdout is byte-equal to the repo THIRD-PARTY-LICENSES file
  -- (the human string omits the final newline; println restores it)
  let lic ← spawn ["licenses"]
  o := o ++
    [check "licenses stdout is byte-equal to THIRD-PARTY-LICENSES"
      (lic.stdout == (← IO.FS.readFile "THIRD-PARTY-LICENSES"))
      s!"stdout {lic.stdout.length} bytes vs file",
     check "licenses exits 0" (lic.exitCode == 0)]
  -- usage error honors --json anywhere in argv: envelope on stdout, exit 2
  let bad ← spawn ["frobnicate", "--json"]
  o := o ++
    [check "usage error emits the error envelope on stdout"
      (bad.stdout.startsWith "{\"schemaVersion\":2,\"ok\":false,\"error\":{\"code\":\"usage\"")
      bad.stdout,
     check "usage exits 2" (bad.exitCode == 2)]
  -- no-project exit 3
  let root ← IO.FS.createTempDir
  let np ← spawn ["ready", "--json"] [] (some root)
  o := o ++ [check "no-project exits 3" (np.exitCode == 3) np.stdout]
  -- TL_DIR (the env path unit tests cannot reach)
  let target := (root / "state").toString
  let _ ← spawn ["init", "--dir", target]
  let viaEnv ← spawn ["list", "--json"] [("TL_DIR", some target)] (some root)
  o := o ++ [check "TL_DIR binds the state dir" (viaEnv.exitCode == 0) viaEnv.stdout]
  -- GIT_CEILING_DIRECTORIES stops the walk
  IO.FS.createDirAll (root / "proj" / "sub")
  let _ ← spawn ["init", "--dir", (root / "proj" / ".tl").toString]
  let found ← spawn ["list", "--json"] [("TL_DIR", none)] (some (root / "proj" / "sub"))
  -- ceilings compare textually (as in git): pass the resolved path, since the
  -- child's cwd canonicalizes /var → /private/var on macOS
  let realProj ← IO.FS.realPath (root / "proj")
  let ceiled ← spawn ["list", "--json"]
    [("TL_DIR", none), ("GIT_CEILING_DIRECTORIES", some realProj.toString)]
    (some (root / "proj" / "sub"))
  o := o ++
    [check "discovery from a subdir finds the project" (found.exitCode == 0) found.stdout,
     check "a ceiling directory stops discovery" (ceiled.exitCode == 3) ceiled.stdout]
  -- the ADR-0013 actor read runs in the --dir target repo (`git -C`), not the
  -- process cwd: from repoA, a create targeting repoB records repoB's user.email.
  -- TL_ACTOR is unset so the chain falls through to the git-config read.
  let gitIn (dir : System.FilePath) (args : List String) : IO Unit := do
    let _ ← IO.Process.output { cmd := "git", args := (["-C", dir.toString] ++ args).toArray }
    pure ()
  let repoA ← IO.FS.createTempDir
  let repoB ← IO.FS.createTempDir
  gitIn repoA ["init", "-q"]; gitIn repoA ["config", "user.email", "cwd@example.test"]
  gitIn repoB ["init", "-q"]; gitIn repoB ["config", "user.email", "target@example.test"]
  let bTl := (repoB / ".tl").toString
  let _ ← spawn ["init", "--dir", bTl] [("TL_ACTOR", none)] (some repoA)
  let _ ← spawn ["create", "task", "--dir", bTl] [("TL_ACTOR", none)] (some repoA)
  let logged ← spawn ["log", "--dir", bTl, "--json"] [("TL_ACTOR", none)] (some repoA)
  o := o ++ [
    check "actor reads the --dir target repo's user.email (git -C), not the cwd repo's"
      ((logged.stdout.splitOn "target@example.test").length > 1
        && (logged.stdout.splitOn "cwd@example.test").length == 1)
      logged.stdout]
  return o

/-- The ADR-0012 environment scrub, end to end against the compiled binary:
    for each routing / config-injection class an inherited hostile variable
    must neither redirect any git subprocess off the filesystem-discovered
    repository nor break tl (a bogus value is simply ignored). The victim
    repositories double as canaries — after every row they must still have
    no `refs/tl/log`. `syncEnvScrubTests` holds the control row proving git
    *does* honor this routing when unscrubbed. Also covers the onboarding
    shapes: a non-git state under a routing env stays repo-less, `git init`
    around existing state then syncs, un-stealthing lands in the discovered
    repo, and a ceiling stops init placement. -/
private def gitEnvMatrixRows (exe : System.FilePath) : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- every spawn unsets TL_DIR (cwd discovery is under test) and pins a
  -- neutral actor so no git identity leaks into the throwaway logs
  let spawn (args : List String) (env : List (String × Option String) := [])
      (cwd : Option System.FilePath := none) : IO IO.Process.Output :=
    IO.Process.output { cmd := exe.toString, args := args.toArray,
                        env := ([("TL_DIR", none), ("TL_ACTOR", some "tester")] ++ env).toArray,
                        cwd }
  let gitOut (dir : System.FilePath) (args : List String) : IO IO.Process.Output :=
    IO.Process.output { cmd := "git", args := (["-C", dir.toString] ++ args).toArray }
  -- fixture git calls THROW on failure: silently discarding them let a
  -- developer's global config (a `commit.gpgsign` with no usable key, a
  -- `core.hooksPath`) fail the seed commit, which cascaded into a worktree
  -- that was never created and a crash reading its replica — far from the
  -- cause. The caller turns a throw into one clear failing row.
  let git (dir : System.FilePath) (args : List String) : IO Unit := do
    let out ← gitOut dir args
    unless out.exitCode == 0 do
      throw (IO.userError
        s!"fixture `git {String.intercalate " " args}` in {dir} exited {out.exitCode}: {out.stderr.trimAscii}")
  let hasTlRef (dir : System.FilePath) : IO Bool := do
    pure ((← gitOut dir ["rev-parse", "--verify", "--quiet", "refs/tl/log"]).exitCode == 0)
  let tmp ← IO.FS.createTempDir
  -- the working repo A (one seed commit so worktrees can attach) and victim B
  let a := tmp / "a"
  let b := tmp / "b"
  IO.FS.createDirAll a
  IO.FS.createDirAll b
  git tmp ["init", "-q", a.toString]
  git tmp ["init", "-q", b.toString]
  IO.FS.writeFile (a / "f.txt") "seed\n"
  git a ["add", "f.txt"]
  -- the fixture commit is hermetic: signing off and hooks skipped, so the
  -- suite does not depend on the developer's global git configuration
  git a ["-c", "commit.gpgsign=false", "-c", "user.email=ci@example.test",
         "-c", "user.name=ci", "commit", "-q", "--no-verify", "-m", "seed"]
  let _ ← spawn ["init"] [] (some a)
  let _ ← spawn ["create", "probe task"] [] (some a)
  let bGitDir := (b / ".git").toString
  -- (1) repository routing: GIT_DIR must not publish A's data into B
  let s1 ← spawn ["sync", "--json"] [("GIT_DIR", some bGitDir)] (some a)
  o := o ++
    [check "sync under GIT_DIR succeeds against the discovered repo" (s1.exitCode == 0) s1.stdout,
     check "sync under GIT_DIR wrote refs/tl/log in A" (← hasTlRef a),
     check "sync under GIT_DIR left victim B untouched" (!(← hasTlRef b))]
  -- (2) hook-style inherited environment (git exports GIT_DIR/GIT_WORK_TREE/
  --     GIT_INDEX_FILE into hooks): same invariant
  let s2 ← spawn ["sync", "--json"]
    [("GIT_DIR", some bGitDir), ("GIT_WORK_TREE", some b.toString),
     ("GIT_INDEX_FILE", some (b / ".git" / "index").toString)] (some a)
  o := o ++
    [check "sync under a hook-style env succeeds" (s2.exitCode == 0) s2.stdout,
     check "hook-style env left victim B untouched" (!(← hasTlRef b))]
  -- (3) a bogus routing value is scrubbed, not tripped over — unscrubbed,
  --     rev-parse fails, tl classifies A as no-repo, and the local leg does
  --     not run (`list` would merely degrade, so `sync`'s leg report is the
  --     discriminating observation)
  let s3 ← spawn ["sync", "--json"] [("GIT_DIR", some "/nonexistent/nowhere")] (some a)
  o := o ++ [check "a bogus GIT_DIR is ignored (the local leg still runs)"
    (s3.exitCode == 0 && (s3.stdout.splitOn "\"ran\":true").length > 1) s3.stdout]
  -- (4) object-store routing: new objects written under a hostile
  --     GIT_OBJECT_DIRECTORY must land in A (readable there with a clean env)
  let _ ← spawn ["create", "second probe"] [] (some a)
  let s4 ← spawn ["sync", "--json"]
    [("GIT_OBJECT_DIRECTORY", some (b / ".git" / "objects").toString)] (some a)
  let readBack ← gitOut a ["ls-tree", "refs/tl/log"]
  o := o ++
    [check "sync under GIT_OBJECT_DIRECTORY succeeds" (s4.exitCode == 0) s4.stdout,
     check "ref objects are readable in A with a clean env"
       (readBack.exitCode == 0 && readBack.stdout != "") readBack.stderr]
  -- remote-leg rows: origin = bare A-remote; bare B-remote is the decoy
  let aBare := tmp / "a-remote.git"
  let bBare := tmp / "b-remote.git"
  git tmp ["init", "--bare", "-q", aBare.toString]
  git tmp ["init", "--bare", "-q", bBare.toString]
  git a ["remote", "add", "origin", aBare.toString]
  git a ["config", "protocol.file.allow", "always"]
  -- (5) namespace routing: GIT_NAMESPACE takes effect in the *receive* end
  --     of a push (local plumbing ignores it), so the canary is the bare
  --     remote — the ref must arrive as the real refs/tl/log, not under
  --     refs/namespaces/hostile/
  let s5 ← spawn ["sync", "--json"] [("GIT_NAMESPACE", some "hostile")] (some a)
  let shadow ← gitOut aBare ["rev-parse", "--verify", "--quiet", "refs/namespaces/hostile/refs/tl/log"]
  o := o ++
    [check "sync under GIT_NAMESPACE succeeds" (s5.exitCode == 0) s5.stdout,
     check "no namespaced shadow ref reached the remote" (shadow.exitCode != 0) shadow.stdout,
     check "the real refs/tl/log reached the remote" (← hasTlRef aBare)]
  -- (6) env config injection: rewriting remote.origin.url must not take
  --     (origin's ref deleted first, so its reappearance is the canary)
  git aBare ["update-ref", "-d", "refs/tl/log"]
  let s6 ← spawn ["sync", "--json"]
    [("GIT_CONFIG_COUNT", some "1"),
     ("GIT_CONFIG_KEY_0", some "remote.origin.url"),
     ("GIT_CONFIG_VALUE_0", some bBare.toString)] (some a)
  o := o ++
    [check "sync under GIT_CONFIG_COUNT injection succeeds" (s6.exitCode == 0) s6.stdout,
     check "the push landed on the real origin" (← hasTlRef aBare),
     check "the injected decoy remote got nothing" (!(← hasTlRef bBare))]
  -- (7) config-file redirection: a GIT_CONFIG_GLOBAL with url.insteadOf
  --     rewriting origin toward the decoy must not take
  git aBare ["update-ref", "-d", "refs/tl/log"]
  let crafted := tmp / "crafted-global.gitconfig"
  IO.FS.writeFile crafted
    ("[url \"" ++ bBare.toString ++ "\"]\n\tinsteadOf = " ++ aBare.toString ++ "\n")
  let s7 ← spawn ["sync", "--json"] [("GIT_CONFIG_GLOBAL", some crafted.toString)] (some a)
  o := o ++
    [check "sync under a crafted GIT_CONFIG_GLOBAL succeeds" (s7.exitCode == 0) s7.stdout,
     check "the insteadOf rewrite did not take (origin repopulated)" (← hasTlRef aBare),
     check "the insteadOf decoy got nothing" (!(← hasTlRef bBare))]
  -- (7b) the same insteadOf redirect by its other spelling: XDG_CONFIG_HOME
  --      relocates the *global config file itself* (<XDG>/git/config), so
  --      scrubbing GIT_CONFIG_GLOBAL without it closes nothing — unscrubbed,
  --      `tl sync` reports ok/pushed/origin while the ref lands in the decoy
  git aBare ["update-ref", "-d", "refs/tl/log"]
  let xdg := tmp / "xdg"
  IO.FS.createDirAll (xdg / "git")
  IO.FS.writeFile (xdg / "git" / "config")
    ("[url \"" ++ bBare.toString ++ "\"]\n\tinsteadOf = " ++ aBare.toString ++ "\n")
  let s7b ← spawn ["sync", "--json"] [("XDG_CONFIG_HOME", some xdg.toString)] (some a)
  o := o ++
    [check "sync under a crafted XDG_CONFIG_HOME succeeds" (s7b.exitCode == 0) s7b.stdout,
     check "the XDG insteadOf rewrite did not take (origin repopulated)" (← hasTlRef aBare),
     check "the XDG insteadOf decoy got nothing" (!(← hasTlRef bBare))]
  -- (8) the git -c internal channel: a garbage GIT_CONFIG_PARAMETERS would
  --     fail every git call if it reached one
  let s8 ← spawn ["sync", "--json"] [("GIT_CONFIG_PARAMETERS", some "complete garbage")] (some a)
  o := o ++ [check "garbage GIT_CONFIG_PARAMETERS is ignored" (s8.exitCode == 0) s8.stdout]
  -- (9) the legacy GIT_CONFIG file redirect targets exactly the `git config`
  --     builtin — the shape of every tl config read (tl.remote here would
  --     become a phantom remote and the push would stop reaching origin)
  git aBare ["update-ref", "-d", "refs/tl/log"]
  let craftedTl := tmp / "crafted-tl.gitconfig"
  IO.FS.writeFile craftedTl "[tl]\n\tremote = phantom\n"
  let s9 ← spawn ["sync", "--json"] [("GIT_CONFIG", some craftedTl.toString)] (some a)
  o := o ++
    [check "sync under a crafted GIT_CONFIG succeeds" (s9.exitCode == 0) s9.stdout,
     check "the phantom tl.remote did not take (origin repopulated)" (← hasTlRef aBare)]
  -- (10) linked worktree with a bogus GIT_COMMON_DIR: the shared-ref transport
  --      must keep working off the real common dir
  let w := tmp / "w"
  git a ["worktree", "add", "-q", w.toString]
  let _ ← spawn ["init"] [] (some w)
  let _ ← spawn ["create", "worktree probe"] [] (some w)
  let s10 ← spawn ["sync", "--json"] [("GIT_COMMON_DIR", some "/nonexistent/common")] (some w)
  let wReplica := (← IO.FS.readFile (w / ".tl" / "local" / "replica")).trimAscii.toString
  let shared ← gitOut a ["ls-tree", "refs/tl/log"]
  o := o ++
    [check "worktree sync under a bogus GIT_COMMON_DIR succeeds" (s10.exitCode == 0) s10.stdout,
     check "the worktree's segment reached the shared ref"
       ((shared.stdout.splitOn (wReplica ++ ".jsonl")).length > 1) shared.stdout]
  -- (11) onboarding: non-git state under GIT_DIR stays repo-less (no
  --      adoption of the env-routed repo as a sharing target) …
  let plain := tmp / "plain"
  IO.FS.createDirAll plain
  let _ ← spawn ["init"] [] (some plain)
  let _ ← spawn ["create", "plain probe"] [] (some plain)
  let s11 ← spawn ["sync", "--json"] [("GIT_DIR", some bGitDir)] (some plain)
  o := o ++
    [check "non-git state under GIT_DIR syncs as repo-less (remote null)"
       (s11.exitCode == 0 && (s11.stdout.splitOn "\"remote\":null").length > 1) s11.stdout,
     check "non-git state under GIT_DIR left victim B untouched" (!(← hasTlRef b))]
  -- … and `git init` around the same state later just starts sharing
  -- (ADR-0001 §4: no migration)
  git tmp ["init", "-q", plain.toString]
  let plainBare := tmp / "plain-remote.git"
  git tmp ["init", "--bare", "-q", plainBare.toString]
  git plain ["remote", "add", "origin", plainBare.toString]
  git plain ["config", "protocol.file.allow", "always"]
  let s11b ← spawn ["sync", "--json"] [] (some plain)
  o := o ++
    [check "git init around existing state then sync pushes" (s11b.exitCode == 0) s11b.stdout,
     check "the late-added remote received the log" (← hasTlRef plainBare)]
  -- (12) un-stealthing under a routing env: the refspec-free snapshot must
  --      land in the filesystem-discovered repo (ADR-0001 §7)
  let st := tmp / "st"
  IO.FS.createDirAll st
  git tmp ["init", "-q", st.toString]
  let _ ← spawn ["init", "--stealth"] [] (some st)
  let _ ← spawn ["create", "stealth probe"] [] (some st)
  let s12 ← spawn ["sync", "--json"] [("GIT_DIR", some bGitDir)] (some st)
  o := o ++ [check "stealth sync fails closed (stealth-mode) even under GIT_DIR"
    (s12.exitCode == 12) s12.stdout]
  IO.FS.removeFile (st / ".tl" / "local" / "stealth")
  let s12b ← spawn ["sync", "--json"] [("GIT_DIR", some bGitDir)] (some st)
  o := o ++
    [check "un-stealthed sync under GIT_DIR succeeds" (s12b.exitCode == 0) s12b.stdout,
     check "the un-stealth snapshot landed in the discovered repo" (← hasTlRef st),
     check "the un-stealth snapshot did not leak into victim B" (!(← hasTlRef b))]
  -- (13) a ceiling stops init placement: state lands at the cwd, not the
  --      repo toplevel above the ceiling
  let proj := tmp / "proj"
  IO.FS.createDirAll (proj / "sub")
  git tmp ["init", "-q", proj.toString]
  let realProj ← IO.FS.realPath proj
  let s13 ← spawn ["init", "--json"]
    [("GIT_CEILING_DIRECTORIES", some realProj.toString)] (some (proj / "sub"))
  o := o ++
    [check "a ceiling stops init placement (exit 0)" (s13.exitCode == 0) s13.stdout,
     check "init placed state at the cwd below the ceiling"
       ((← (proj / "sub" / ".tl").isDir) && !(← (proj / ".tl").pathExists)),
     check "init disclosed the ceiling stop"
       ((s13.stdout.splitOn "GIT_CEILING_DIRECTORIES").length > 1) s13.stdout]
  -- (13b) ceilings bound the ascent only (git semantics): the starting
  --       directory is always examined — a cwd that is itself listed still
  --       binds its own .tl (discovery) and still finds its own .git (init)
  let ownProj := tmp / "own"
  IO.FS.createDirAll ownProj
  git tmp ["init", "-q", ownProj.toString]
  let realOwn ← IO.FS.realPath ownProj
  let s13b ← spawn ["init", "--json"]
    [("GIT_CEILING_DIRECTORIES", some realOwn.toString)] (some ownProj)
  o := o ++
    [check "a ceiling at the cwd itself does not hide the cwd's repo"
       (s13b.exitCode == 0 && (← (ownProj / ".tl").isDir)
         && (s13b.stdout.splitOn "GIT_CEILING_DIRECTORIES").length == 1) s13b.stdout]
  let s13c ← spawn ["list", "--json"]
    [("GIT_CEILING_DIRECTORIES", some realOwn.toString)] (some ownProj)
  o := o ++
    [check "a ceiling at the cwd itself does not hide the cwd's .tl"
       (s13c.exitCode == 0) s13c.stdout]
  -- (14) doctor discloses the inherited routing env without failing health
  let s14 ← spawn ["doctor", "--json"] [("GIT_DIR", some bGitDir)] (some a)
  o := o ++ [check "doctor under GIT_DIR: healthy, gitRouting warns, names the var"
    (s14.exitCode == 0 && (s14.stdout.splitOn "\"healthy\":true").length > 1
      && (s14.stdout.splitOn "\"gitRouting\"").length > 1
      && (s14.stdout.splitOn "GIT_DIR").length > 1) s14.stdout]
  -- (14b) an inherited *config-relocation* var (GIT_CONFIG_COUNT) is scrubbed
  --       but must NOT surface in routingVars: production filters to
  --       repoRoutingVars, and a benign inherited config var is not a
  --       split-repository condition
  let s14c ← spawn ["doctor", "--json"] [("GIT_CONFIG_COUNT", some "0")] (some a)
  o := o ++ [check "doctor: an inherited config var is not surfaced in routingVars"
    (s14c.exitCode == 0 && (s14c.stdout.splitOn "\"routingVars\":[]").length > 1
      && (s14c.stdout.splitOn "GIT_CONFIG_COUNT").length == 1) s14c.stdout]
  -- (15) the actor fallback reads the discovered repo's user.email, not the
  --      env-routed repo's (ADR-0013 chain, unset TL_ACTOR)
  let x := tmp / "x"
  let y := tmp / "y"
  IO.FS.createDirAll x
  IO.FS.createDirAll y
  git tmp ["init", "-q", x.toString]
  git tmp ["init", "-q", y.toString]
  git x ["config", "user.email", "discovered@example.test"]
  git y ["config", "user.email", "routed@example.test"]
  let _ ← spawn ["init"] [] (some x)
  let _ ← spawn ["create", "actor probe"] [("TL_ACTOR", none), ("GIT_DIR", some (y / ".git").toString)] (some x)
  let logged ← spawn ["log", "--json"] [] (some x)
  o := o ++ [check "the actor fallback ignores GIT_DIR (reads the discovered repo)"
    ((logged.stdout.splitOn "discovered@example.test").length > 1
      && (logged.stdout.splitOn "routed@example.test").length == 1) logged.stdout]
  -- (16) the CARRIED RESIDUAL, pinned honestly (ADR-0012 Consequences /
  --      ADR-0014 T7): HOME cannot be scrubbed — it locates ~/.gitconfig,
  --      ~/.git-credentials and ~/.ssh, so unsetting it would break every
  --      authenticated remote. A HOME pointed at a directory the user does
  --      not control therefore CAN still inject a url.*.insteadOf rewrite and
  --      redirect the push, with no control of PATH or the git binary. tl does
  --      not prevent that. It discloses it: doctor reports the rewrite. Both
  --      halves are pinned here — if a future change closes the redirect, the
  --      first row fails and this comment (and the ADRs) must be revisited.
  let h := tmp / "h"
  let hReal := tmp / "h-real.git"
  let hDecoy := tmp / "h-decoy.git"
  IO.FS.createDirAll h
  git tmp ["init", "-q", h.toString]
  git tmp ["init", "--bare", "-q", hReal.toString]
  git tmp ["init", "--bare", "-q", hDecoy.toString]
  git h ["remote", "add", "origin", hReal.toString]
  git h ["config", "protocol.file.allow", "always"]
  let _ ← spawn ["init"] [] (some h)
  let _ ← spawn ["create", "residual probe"] [] (some h)
  let fakeHome := tmp / "fake-home"
  IO.FS.createDirAll fakeHome
  IO.FS.writeFile (fakeHome / ".gitconfig")
    ("[url \"" ++ hDecoy.toString ++ "\"]\n\tinsteadOf = " ++ hReal.toString ++ "\n")
  let s16 ← spawn ["sync", "--json"] [("HOME", some fakeHome.toString)] (some h)
  o := o ++
    [check "residual: a hostile HOME still redirects the push (tl does not prevent it)"
       (s16.exitCode == 0 && (← hasTlRef hDecoy) && !(← hasTlRef hReal)) s16.stdout]
  let s16b ← spawn ["doctor", "--json"] [("HOME", some fakeHome.toString)] (some h)
  o := o ++
    [check "residual: doctor discloses the insteadOf rewrite (warn, still healthy)"
       (s16b.exitCode == 0 && (s16b.stdout.splitOn "\"healthy\":true").length > 1
         && (s16b.stdout.splitOn "\"remoteRewrite\"").length > 1
         && (s16b.stdout.splitOn "insteadOf").length > 1) s16b.stdout]
  -- pushInsteadOf redirects the PUSH only, and the fetch-URL resolver misses
  -- it — the push target resolver (`remote get-url --push`) must catch it, or
  -- a push silently goes to the decoy with no disclosure. Reset BOTH bares
  -- first (the insteadOf row above already pushed to hDecoy) so `hasTlRef
  -- hDecoy` genuinely reflects THIS push, not a stale one.
  git hDecoy ["update-ref", "-d", "refs/tl/log"]
  git hReal ["update-ref", "-d", "refs/tl/log"]
  let pushHome := tmp / "push-home"
  IO.FS.createDirAll pushHome
  IO.FS.writeFile (pushHome / ".gitconfig")
    ("[url \"" ++ hDecoy.toString ++ "\"]\n\tpushInsteadOf = " ++ hReal.toString ++ "\n")
  let s16p ← spawn ["sync", "--json"] [("HOME", some pushHome.toString)] (some h)
  let s16pd ← spawn ["doctor", "--json"] [("HOME", some pushHome.toString)] (some h)
  o := o ++
    [check "residual: a pushInsteadOf rewrite redirects the push"
       (s16p.exitCode == 0 && (← hasTlRef hDecoy) && !(← hasTlRef hReal)) s16p.stdout,
     check "residual: doctor discloses a pushInsteadOf rewrite (push-URL resolver)"
       (s16pd.exitCode == 0 && (s16pd.stdout.splitOn "\"remoteRewrite\"").length > 1
         && (s16pd.stdout.splitOn hDecoy.toString).length > 1) s16pd.stdout]
  -- and with an ordinary HOME the same repo reports no rewrite
  let s16c ← spawn ["doctor", "--json"] [] (some h)
  o := o ++
    [check "no rewrite in an ordinary environment: remoteRewrite is null"
       (s16c.exitCode == 0 && (s16c.stdout.splitOn "\"remoteRewrite\":null").length > 1) s16c.stdout]
  -- a DELIBERATE distinct push URL (remote.origin.pushurl) is not a rewrite —
  -- the baseline is that raw push target, so doctor must not false-positive
  let pu := tmp / "pushurl"
  IO.FS.createDirAll pu
  git tmp ["init", "-q", pu.toString]
  git pu ["remote", "add", "origin", "https://fetch.example.test/x.git"]
  git pu ["config", "protocol.file.allow", "always"]
  git pu ["remote", "set-url", "--push", "origin", "ssh://push.example.test/x.git"]
  let _ ← spawn ["init"] [] (some pu)
  let s16u ← spawn ["doctor", "--json"] [] (some pu)
  o := o ++
    [check "a deliberate pushurl is not reported as a rewrite"
       (s16u.exitCode == 0 && (s16u.stdout.splitOn "\"remoteRewrite\":null").length > 1) s16u.stdout]
  -- (17) the direct-injection residual: tl.remote + remote.<n>.url supplied
  --      entirely by a hostile ~/.gitconfig, NO url rewrite. The push follows
  --      the injected remote to the decoy; a rewrite-only check reports ok, so
  --      the scope-origin check must catch it.
  let g := tmp / "grepo"
  let gReal := tmp / "g-real.git"
  let gDecoy := tmp / "g-decoy.git"
  IO.FS.createDirAll g
  git tmp ["init", "-q", g.toString]
  git tmp ["init", "--bare", "-q", gReal.toString]
  git tmp ["init", "--bare", "-q", gDecoy.toString]
  git g ["remote", "add", "origin", gReal.toString]
  git g ["config", "protocol.file.allow", "always"]
  let _ ← spawn ["init"] [] (some g)
  let _ ← spawn ["create", "inject probe"] [] (some g)
  let gHome := tmp / "g-home"
  IO.FS.createDirAll gHome
  IO.FS.writeFile (gHome / ".gitconfig")
    ("[tl]\n\tremote = evil\n[remote \"evil\"]\n\turl = " ++ gDecoy.toString ++ "\n")
  let s17 ← spawn ["sync", "--json"] [("HOME", some gHome.toString)] (some g)
  let s17d ← spawn ["doctor", "--json"] [("HOME", some gHome.toString)] (some g)
  o := o ++
    [check "residual: injected tl.remote redirects the push to the decoy"
       (s17.exitCode == 0 && (← hasTlRef gDecoy) && !(← hasTlRef gReal)) s17.stdout,
     check "residual: doctor discloses injected tl.remote (scope-origin check)"
       (s17d.exitCode == 0 && (s17d.stdout.splitOn "\"externalPushConfig\"").length > 1
         && (s17d.stdout.splitOn "tl.remote").length > 1
         && (s17d.stdout.splitOn "~/.gitconfig").length > 1) s17d.stdout]
  -- and a deliberate REPO-LOCAL tl.remote is not flagged (local overrides global)
  git g ["config", "tl.remote", "origin"]
  let s17b ← spawn ["doctor", "--json"] [] (some g)
  o := o ++
    [check "a repo-local tl.remote is not flagged as external"
       (s17b.exitCode == 0 && (s17b.stdout.splitOn "\"externalPushConfig\":[]").length > 1) s17b.stdout]
  -- (18) a multi-valued pushurl: git pushes to EVERY configured pushurl, so a
  --      global decoy pushurl added ALONGSIDE a legit local one is a real extra
  --      push target — a last-value origin check would miss it (local wins the
  --      single read), so the get-all check must flag the global value even
  --      though a local pushurl exists.
  let mv := tmp / "multi"
  let mvReal := tmp / "mv-real.git"
  let mvDecoy := tmp / "mv-decoy.git"
  IO.FS.createDirAll mv
  git tmp ["init", "-q", mv.toString]
  git tmp ["init", "--bare", "-q", mvReal.toString]
  git tmp ["init", "--bare", "-q", mvDecoy.toString]
  git mv ["remote", "add", "origin", mvReal.toString]
  git mv ["config", "protocol.file.allow", "always"]
  git mv ["config", "remote.origin.pushurl", mvReal.toString]  -- a legit local pushurl
  let _ ← spawn ["init"] [] (some mv)
  let mvHome := tmp / "mv-home"
  IO.FS.createDirAll mvHome
  IO.FS.writeFile (mvHome / ".gitconfig")
    ("[remote \"origin\"]\n\tpushurl = " ++ mvDecoy.toString ++ "\n")
  let s18 ← spawn ["doctor", "--json"] [("HOME", some mvHome.toString)] (some mv)
  o := o ++
    [check "a global pushurl added beside a local one is flagged (multi-valued)"
       (s18.exitCode == 0 && (s18.stdout.splitOn "\"externalPushConfig\"").length > 1
         && (s18.stdout.splitOn mvDecoy.toString).length > 1) s18.stdout]
  -- (18b) a rewrite of a NON-FIRST local pushurl: git pushes to every one, so
  --       a HOME insteadOf that only moves the middle target is invisible to a
  --       single-URL resolver — the all-URLs comparison must catch it, and it
  --       must NOT false-positive when multiple local pushurls are legit.
  let mid := tmp / "midrewrite"
  let midReal := tmp / "mid-real.git"
  let midOther := tmp / "mid-other.git"
  let midDecoy := tmp / "mid-decoy.git"
  IO.FS.createDirAll mid
  git tmp ["init", "-q", mid.toString]
  git tmp ["init", "--bare", "-q", midReal.toString]
  git tmp ["init", "--bare", "-q", midOther.toString]
  git tmp ["init", "--bare", "-q", midDecoy.toString]
  git mid ["remote", "add", "origin", midReal.toString]
  git mid ["config", "--add", "remote.origin.pushurl", midReal.toString]
  git mid ["config", "--add", "remote.origin.pushurl", midOther.toString]  -- the middle, to be rewritten
  git mid ["config", "--add", "remote.origin.pushurl", midReal.toString]
  let _ ← spawn ["init"] [] (some mid)
  -- first, an ordinary env: multiple legit local pushurls must not warn
  let s18c ← spawn ["doctor", "--json"] [] (some mid)
  o := o ++
    [check "multiple legit local pushurls do not false-positive as a rewrite"
       (s18c.exitCode == 0 && (s18c.stdout.splitOn "\"remoteRewrite\":null").length > 1) s18c.stdout]
  let midHome := tmp / "mid-home"
  IO.FS.createDirAll midHome
  IO.FS.writeFile (midHome / ".gitconfig")
    ("[url \"" ++ midDecoy.toString ++ "\"]\n\tinsteadOf = " ++ midOther.toString ++ "\n")
  let s18d ← spawn ["doctor", "--json"] [("HOME", some midHome.toString)] (some mid)
  o := o ++
    [check "a rewrite of a non-first pushurl is disclosed (all-URLs comparison)"
       (s18d.exitCode == 0 && (s18d.stdout.splitOn "\"remoteRewrite\"").length > 1
         && (s18d.stdout.splitOn midDecoy.toString).length > 1) s18d.stdout]
  -- (19) the branch.<current>.remote selector injected from global (tl.remote
  --      unset) redirects the remote choice — the selector chain must check it
  let br := tmp / "branchsel"
  let brDecoy := tmp / "br-decoy.git"
  IO.FS.createDirAll br
  git tmp ["init", "-q", br.toString]
  git tmp ["init", "--bare", "-q", brDecoy.toString]
  git br ["remote", "add", "origin", (tmp / "br-real.git").toString]
  git br ["config", "protocol.file.allow", "always"]
  -- a commit so there is a current branch to key branch.<b>.remote on
  IO.FS.writeFile (br / "f") "x\n"
  git br ["add", "f"]
  git br ["-c", "commit.gpgsign=false", "-c", "user.email=ci@x.test", "-c", "user.name=ci",
          "commit", "-q", "--no-verify", "-m", "seed"]
  let curBranch := ((← IO.Process.output { cmd := "git", args := #["-C", br.toString, "symbolic-ref", "--short", "HEAD"] }).stdout).trimAscii
  let _ ← spawn ["init"] [] (some br)
  let brHome := tmp / "br-home"
  IO.FS.createDirAll brHome
  IO.FS.writeFile (brHome / ".gitconfig")
    (s!"[branch \"{curBranch}\"]\n\tremote = decoy\n[remote \"decoy\"]\n\turl = " ++ brDecoy.toString ++ "\n")
  let s19 ← spawn ["doctor", "--json"] [("HOME", some brHome.toString)] (some br)
  o := o ++
    [check "an injected branch.<current>.remote selector is flagged"
       (s19.exitCode == 0 && (s19.stdout.splitOn s!"branch.{curBranch}.remote").length > 1) s19.stdout]
  return o

/-- Spawned-binary hostile-environment matrix. Fixture git calls throw, so a
    setup failure (a global `commit.gpgsign` with no usable key, a
    `core.hooksPath`) surfaces as one clear row instead of crashing the suite
    far from its cause. -/
def cliGitEnvTests : IO (List Outcome) := do
  let exe := (← IO.currentDir) / ".lake" / "build" / "bin" / "tl"
  unless ← exe.pathExists do
    return [{ name := "binary present", passed := false,
              msg := "run `lake build` first: .lake/build/bin/tl missing" }]
  match ← (gitEnvMatrixRows exe).toBaseIO with
  | .ok rows => return rows
  | .error e =>
    return [{ name := "git-env hostile-environment matrix", passed := false,
              msg := s!"fixture setup failed: {e}" }]

/-- A canonical line for a crafted segment. The stamp's replica is the
    segment stem's decoded value — the decode-side owner check (segments are
    per-replica authored, ADR-0001) refuses anything else. -/
private def foreignLine (op : WireOp) (hlc : Nat) (stem : String) (actor : String)
    (nonce : Nat := 1) : String :=
  renderLine { v := supportedVersion, op,
               stamp := ⟨hlc, (ofCrockford? stem).getD 0, nonce⟩, actor := some actor }

def cliReviewTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- sanitization reaches the payloads (ADR-0014)
  let dir ← freshDir
  let esc := String.singleton (Char.ofNat 0x1b)
  let zwsp := String.singleton (Char.ofNat 0x200B)
  o := o ++
    [← expectData "create echo sanitizes the title"
      ["create", "Red " ++ esc ++ "[31mtext" ++ zwsp ++ "!", "--dir", dir, "--actor", "t"]
      (fun j => jStr j "title" == some "Red text!")]
  -- `tl log` human output sanitizes the (attacker-controllable, ADR-0014 T1) actor
  -- field: a foreign op whose actor carries an OSC title-set escape must not reach a
  -- terminal raw (the human render must match the --json arm, which already wraps it).
  let dirLog ← freshDir
  let _ ← mkIssue dirLog "Mine"
  let evilActor := esc ++ "]0;pwn" ++ String.singleton (Char.ofNat 0x07)
  IO.FS.writeFile (System.FilePath.mk dirLog / "log" / "1zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbccccdddd" { title := some "F" }) 50 "1zzzzzzzzzzzz" evilActor ++ "\n")
  let logRes ← run' ["log", "--dir", dirLog]
  o := o ++ [match logRes with
    | .ok out =>
      check "tl log human output strips the actor field's escape bytes (ADR-0014)"
        (!((out.render.map (· Style.plain)).getD out.human).contains (Char.ofNat 0x1b))
        ((out.render.map (· Style.plain)).getD out.human)
    | .error e =>
      { name := "tl log over a seeded escape-actor segment succeeds", passed := false,
        msg := e.message }]
  -- claim --sync post-reload fallback (reloadOrFallback): a throwing reload yields
  -- the fallback view + a disclosure note (never a thrown error — a durable claim
  -- must not report failure); a succeeding reload yields the reloaded view, no note.
  -- Two views with distinct issue counts (fallback=1, reload=2) prove which is used.
  let dFb ← freshDir; let _ ← mkIssue dFb "fallback-only"
  let dRe ← freshDir; let _ ← mkIssue dRe "r1"; let _ ← mkIssue dRe "r2"
  let rFb ← (loadView (some dFb)).run
  let rRe ← (loadView (some dRe)).run
  match rFb, rRe with
  | .ok vFb, .ok vRe =>
    let onThrow ← (reloadOrFallback (throw (.mk' .internal "boom")) vFb "tl-x").run
    let onOk ← (reloadOrFallback (pure vRe) vFb "tl-x").run
    o := o ++ [
      check "reloadOrFallback: a throwing reload returns the fallback view + a disclosure note"
        (match onThrow with
         | .ok (vf, notes) => vf.present.length == 1
             && notes.any (fun n => (n.splitOn "reload failed").length > 1)
         | .error _ => false) "threw instead of falling back",
      check "reloadOrFallback: a succeeding reload returns the reloaded view, no note"
        (match onOk with
         | .ok (vf, notes) => vf.present.length == 2 && notes.isEmpty
         | .error _ => false) "did not return the reloaded view"]
  | _, _ => o := o ++ [check "reloadOrFallback setup: both views load" false "loadView failed"]
  -- '=' in flag values, both spellings
  let a ← mkIssue dir "EqTarget"
  o := o ++
    [← expectData "--title=a=b keeps the embedded '='"
      ["update", "tl-" ++ a, "--dir", dir, "--title=a=b", "--actor", "t"]
      (fun j => jStr j "title" == some "a=b"),
     ← expectData "--title a=b keeps the embedded '=' (two-token form)"
      ["update", "tl-" ++ a, "--dir", dir, "--title", "x=y", "--actor", "t"]
      (fun j => jStr j "title" == some "x=y")]
  -- uppercase TL- discriminates as an id
  let upper := "TL-" ++ String.ofList (a.toList.map Char.toUpper)
  o := o ++
    [← expectData "uppercase TL- token resolves as an id" ["show", upper, "--dir", dir]
      (fun j => jStr j "id" == some ("tl-" ++ a))]
  -- why omits blockedBy when blockers are not the reason (an epic)
  let epic ← mkIssue dir "Epic"
  let _ ← mkIssue dir "Child" ["--parent", "tl-" ++ epic]
  o := o ++
    [← expectData "why omits an empty blockedBy (omit-empty)"
      ["why", "tl-" ++ epic, "--dir", dir]
      (fun j => jBool j "ready" == some false && jBool j "isEpic" == some true
        && (jGet j "blockedBy").isNone)]
  -- trailing-slash --dir binds the same state
  o := o ++
    [← expectData "trailing-slash --dir binds the same state"
      ["list", "--dir", dir ++ "/", "--limit", "0"]
      (fun j => (jNat j "count").getD 0 ≥ 3)]
  -- partial init: an empty .tl is completed, a file in the way teaches
  let root2 ← IO.FS.createTempDir
  IO.FS.createDirAll (root2 / ".tl")
  o := o ++
    [← expectData "init completes a partial (empty) .tl"
      ["init", "--dir", (root2 / ".tl").toString]
      (fun j => jBool j "created" == some true)]
  let root3 ← IO.FS.createTempDir
  IO.FS.writeFile (root3 / ".tl") "not a dir"
  o := o ++
    [← expectErr "init over a file named .tl teaches the fix"
      ["init", "--dir", (root3 / ".tl").toString] .usage]
  -- a hostile foreign segment: skip-bad folds around it; writes disclose it
  let dir2 ← freshDir
  let _ ← mkIssue dir2 "Mine"
  let foreignOk := foreignLine (.create "aaaabbbbccccdddd" { title := some "Foreign" }) 99 "1zzzzzzzzzzzz" "eve"
  IO.FS.writeFile (System.FilePath.mk dir2 / "log" / "1zzzzzzzzzzzz.jsonl")
    (foreignOk ++ "
GARBAGE
")
  o := o ++
    [← expectData "bare read folds around the refused foreign segment"
      ["list", "--dir", dir2, "--limit", "0"]
      (fun j => jNat j "count" == some 1),
     ← expectData "--skip-bad folds the foreign segment's good lines"
      ["list", "--dir", dir2, "--limit", "0", "--skip-bad"]
      (fun j => jNat j "count" == some 2)]
  -- write verbs disclose the refusal on stderr (CmdOut.notes)
  let wres ← run' ["create", "another", "--dir", dir2, "--actor", "t"]
  o := o ++ [match wres with
    | .ok out =>
      check "write verbs disclose the foreign refusal"
        ((out.notes.any (fun n => (n.splitOn "refused").length > 1)))
        (String.intercalate "|" out.notes)
    | .error e =>
      { name := "write verbs disclose the foreign refusal", passed := false,
        msg := e.message }]
  -- own-segment damage: bare read fails, --skip-bad succeeds with disclosure
  let ownSeg := System.FilePath.mk dir2 / "log"
  let segs ← ownSeg.readDir
  for ent in segs do
    unless ent.fileName == "1zzzzzzzzzzzz.jsonl" do
      let prev ← IO.FS.readFile ent.path
      IO.FS.writeFile ent.path ("BROKEN LINE
" ++ prev)
  o := o ++
    [← expectErr "own-segment damage fails the bare read" ["list", "--dir", dir2]
       .malformedLine,
     ← expectData "--skip-bad reads through own-segment damage"
       ["list", "--dir", dir2, "--limit", "0", "--skip-bad"]
       (fun j => (jNat j "count").getD 0 ≥ 2)]
  -- superseded claim: a foreign claim at a later HLC wins LWW
  let dir3 ← freshDir
  let target ← mkIssue dir3 "Contested"
  let _ ← run' ["claim", "tl-" ++ target, "--dir", dir3, "--actor", "carol"]
  -- a sibling's concurrent claim, later than ours but within the skew window
  -- (ADR-0007: a far-future HLC would be deferred, not treated as "later")
  let laterHlc := ((← nowMs) + 60000) * 2 ^ 16
  let foreignClaim := foreignLine (.claim target "eve") laterHlc "2zzzzzzzzzzzz" "eve"
  IO.FS.writeFile (System.FilePath.mk dir3 / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignClaim ++ "
")
  o := o ++
    [← expectData "a later foreign claim supersedes (replica-relative signal)"
      ["show", "tl-" ++ target, "--dir", dir3]
      (fun j => jStr j "assignee" == some "eve"
        && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "superseded")]
  -- the claim command itself discloses supersession in its human line (parity
  -- with close): a higher-stamped foreign reopen clears the assignee and sets
  -- the issue Open (so it is ready), and that reopen outranks the fresh local
  -- claim on both the status and assignee LWW — current ≠ actor, so "Claimed …"
  -- would be a lie (ADR-0013: reopen clears assignee)
  let dir3b ← freshDir
  let tgt2 ← mkIssue dir3b "Reassigned"
  let base ← nowMs
  let seg := foreignLine (.claim tgt2 "eve") ((base + 20000) * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 1 ++ "\n"
          ++ foreignLine (.reopen tgt2) ((base + 40000) * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 2 ++ "\n"
  IO.FS.writeFile (System.FilePath.mk dir3b / "log" / "2zzzzzzzzzzzz.jsonl") seg
  match ← run' ["claim", "tl-" ++ tgt2, "--dir", dir3b, "--actor", "carol"] with
  | .error e => o := o ++ [check "superseded claim is reachable via the command" false s!"unexpected: {e.message}"]
  | .ok out =>
    let outc := (jGet out.data "claim").bind (fun c => jStr c "outcome")
    o := o ++
      [check "claim command reports superseded in JSON" (outc == some "superseded") s!"outcome={outc}",
       check "claim command discloses supersession in the human line"
         ((out.human.splitOn "superseded").length == 2) out.human]
  -- a foreign close outstamping the claim: the assignee register alone still
  -- reads carol (a close never writes assignee), but the claim did NOT hold —
  -- the status register was lost to the close, so the outcome derives from
  -- BOTH registers and reads superseded on the (truthfully done) issue
  let dirFC ← freshDir
  let tgtFC ← mkIssue dirFC "ClosedUnderTheClaim"
  let _ ← run' ["claim", "tl-" ++ tgtFC, "--dir", dirFC, "--actor", "carol"]
  let closeHlc := ((← nowMs) + 60000) * 2 ^ 16
  IO.FS.writeFile (System.FilePath.mk dirFC / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.close tgtFC .Done) closeHlc "2zzzzzzzzzzzz" "eve" ++ "\n")
  o := o ++ [← expectData "a foreign close outstamping the claim supersedes it (both-register outcome)"
      ["show", "tl-" ++ tgtFC, "--dir", dirFC]
      (fun j => jStr j "status" == some "done"
        && jStr j "assignee" == some "carol"
        && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "superseded")]
  -- the partial win through the claim command itself: a foreign `create` dated
  -- ahead (within the skew window) seeds status=(high stamp, open), so the
  -- issue is claimable, but the fresh claim's lower-stamped status write loses
  -- while its assignee write survives — assignee-only would read "won"; the
  -- both-register outcome is superseded, and the human line explains the
  -- partial survival instead of a bare verdict
  let dirPW ← freshDir
  -- a local write first, so the persisted HLC is seeded at wall-clock now and
  -- the upcoming claim does NOT reseed from (and outstamp) the foreign segment
  let _ ← mkIssue dirPW "WarmTheClock"
  let pwId := "aaaabbbbccccff00"
  let pwHlc := ((← nowMs) + 60000) * 2 ^ 16
  IO.FS.writeFile (System.FilePath.mk dirPW / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create pwId { title := some "SeededAhead" }) pwHlc "2zzzzzzzzzzzz" "eve" ++ "\n")
  match ← run' ["claim", "tl-" ++ pwId, "--dir", dirPW, "--actor", "carol"] with
  | .error e => o := o ++ [check "partial claim win is reachable via the command" false s!"unexpected: {e.message}"]
  | .ok out =>
    let outc := (jGet out.data "claim").bind (fun c => jStr c "outcome")
    o := o ++
      [check "partial claim win reports superseded in JSON (binary wire outcome)"
         (outc == some "superseded") s!"outcome={outc}",
       check "partial claim win keeps the truthful issue payload (open + assigned)"
         (jStr out.data "status" == some "open" && jStr out.data "assignee" == some "carol")
         out.data.compress,
       check "partial claim win's human line explains the split, not a bare verdict"
         ((out.human.splitOn "still holds the assignee").length == 2
          && (out.human.splitOn "superseded").length == 2) out.human]
  -- the show claim block agrees on the partial case (same both-register derivation)
  o := o ++ [← expectData "show's claim block reads the partial win as superseded"
      ["show", "tl-" ++ pwId, "--dir", dirPW]
      (fun j => ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "superseded")]
  -- a claim ended by this replica's OWN later close is history, not a lost
  -- race: show's block reads "ended" (never "superseded" — every normally
  -- completed task would read like a contest), with the factual payload
  -- (done + still-assigned) alongside
  let dirSC ← freshDir
  let tgtSC ← mkIssue dirSC "ClaimedThenSelfClosed"
  let _ ← run' ["claim", "tl-" ++ tgtSC, "--dir", dirSC, "--actor", "carol"]
  let _ ← run' ["close", "tl-" ++ tgtSC, "--dir", dirSC, "--as", "done", "--actor", "carol"]
  o := o ++ [← expectData "own close after own claim reads ended, not superseded"
      ["show", "tl-" ++ tgtSC, "--dir", dirSC]
      (fun j => jStr j "status" == some "done"
        && jStr j "assignee" == some "carol"
        && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "ended")]
  match ← run' ["show", "tl-" ++ tgtSC, "--dir", dirSC] with
  | .error e => o := o ++ [check "show human after own close stays non-contest" false e.message]
  | .ok out => o := o ++
      [check "show human discloses the claim outcome (human/JSON parity): 'claim: ended'"
        ((out.human.splitOn "claim: ended").length == 2) out.human,
       check "show human after own close stays non-contest (no 'superseded' wording)"
        ((out.human.splitOn "superseded").length == 1) out.human]
  -- ... and the same reading after this replica's own reopen (the other own
  -- status-writing successor): the old claim is over, not out-raced
  let _ ← run' ["reopen", "tl-" ++ tgtSC, "--dir", dirSC, "--actor", "carol"]
  o := o ++ [← expectData "own reopen after own claim also reads ended"
      ["show", "tl-" ++ tgtSC, "--dir", dirSC]
      (fun j => jStr j "status" == some "open"
        && (jGet j "assignee").isNone
        && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "ended")]
  -- ended never MASKS a lost race: carol's claim is outstamped by dave's
  -- foreign claim, then carol closes with an even higher stamp. Her own close
  -- is the winning status write, but dave took the assignee in between — the
  -- verdict stays superseded (an assignee winner that is not the claimant
  -- blocks the ended reading)
  let dirMask ← freshDir
  let tgtMask ← mkIssue dirMask "LostThenSelfClosed"
  let _ ← run' ["claim", "tl-" ++ tgtMask, "--dir", dirMask, "--actor", "carol"]
  -- dave's claim lands just a few ms ahead — above carol's claim, below her
  -- upcoming close (the sleep lets wall-clock pass it, so the close outstamps
  -- dave's claim and genuinely wins the status LWW)
  let daveHlc := ((← nowMs) + 20) * 2 ^ 16
  IO.FS.writeFile (System.FilePath.mk dirMask / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.claim tgtMask "dave") daveHlc "2zzzzzzzzzzzz" "dave" ++ "\n")
  o := o ++ [← expectData "an interleaved foreign claim reads superseded before the close"
      ["show", "tl-" ++ tgtMask, "--dir", dirMask]
      (fun j => ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "superseded")]
  IO.sleep 60
  let _ ← run' ["close", "tl-" ++ tgtMask, "--dir", dirMask, "--as", "done", "--actor", "carol"]
  o := o ++ [← expectData "carol's later own close does not mask the lost race (still superseded)"
      ["show", "tl-" ++ tgtMask, "--dir", dirMask]
      (fun j => jStr j "status" == some "done"
        && jStr j "assignee" == some "dave"
        && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "superseded")]
  -- shared replica, two actors: alice claims, bob closes with --actor bob.
  -- The winning status write is this replica's — but not the CLAIMANT's: the
  -- envelope actor distinguishes them (provenance, not authentication), so
  -- alice's view reads superseded, not "her own" history
  let dirSH ← freshDir
  let tgtSH ← mkIssue dirSH "SharedReplica"
  let _ ← run' ["claim", "tl-" ++ tgtSH, "--dir", dirSH, "--actor", "alice"]
  let _ ← run' ["close", "tl-" ++ tgtSH, "--dir", dirSH, "--as", "done", "--actor", "bob"]
  o := o ++ [← expectData "another actor's close on the same replica reads superseded, not ended"
      ["show", "tl-" ++ tgtSH, "--dir", dirSH]
      (fun j => jStr j "status" == some "done"
        && jStr j "assignee" == some "alice"
        && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "superseded")]
  -- a re-claim by the SAME actor from another replica: after convergence the
  -- actor's current claim holds both registers at one (later) stamp, so this
  -- replica still reads won — its actor holds the issue, just via a newer op
  let dirRR ← freshDir
  let tgtRR ← mkIssue dirRR "ReclaimedElsewhere"
  let _ ← run' ["claim", "tl-" ++ tgtRR, "--dir", dirRR, "--actor", "carol"]
  -- a few-ms lead (not tens of seconds): the later own close below must be
  -- able to outstamp the re-claim once wall-clock passes it
  let baseRR ← nowMs
  let segRR := foreignLine (.reopen tgtRR) ((baseRR + 10) * 2 ^ 16) "2zzzzzzzzzzzz" "carol" 1 ++ "\n"
            ++ foreignLine (.claim tgtRR "carol") ((baseRR + 20) * 2 ^ 16) "2zzzzzzzzzzzz" "carol" 2 ++ "\n"
  IO.FS.writeFile (System.FilePath.mk dirRR / "log" / "2zzzzzzzzzzzz.jsonl") segRR
  o := o ++ [← expectData "the same actor's cross-replica re-claim still reads won"
      ["show", "tl-" ++ tgtRR, "--dir", dirRR]
      (fun j => jStr j "assignee" == some "carol"
        && jStr j "status" == some "in_progress"
        && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won")]
  -- ... and the claimant's own close on top of that re-claim ends it: the
  -- assignee winner is still carol (the re-claim) and the status winner is
  -- carol's close — ended, by actor, across replicas
  IO.sleep 60
  let _ ← run' ["close", "tl-" ++ tgtRR, "--dir", dirRR, "--as", "done", "--actor", "carol"]
  o := o ++ [← expectData "own close over the same actor's re-claim reads ended"
      ["show", "tl-" ++ tgtRR, "--dir", dirRR]
      (fun j => jStr j "status" == some "done"
        && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "ended")]
  -- exhaustive enum pin: across the scenario dirs above, the outcome value
  -- set is exactly {won, ended, superseded} — a fourth value or a typo'd
  -- branch cannot ship silently. (dirRR was just closed: re-derive a won dir.)
  let dirWon ← freshDir
  let tgtWon ← mkIssue dirWon "CleanClaim"
  let _ ← run' ["claim", "tl-" ++ tgtWon, "--dir", dirWon, "--actor", "carol"]
  let mut outcomes : List String := []
  for (d, t) in [(dirWon, tgtWon), (dirSC, tgtSC), (dirMask, tgtMask), (dirSH, tgtSH), (dirRR, tgtRR)] do
    match ← run' ["show", "tl-" ++ t, "--dir", d] with
    | .ok out => outcomes := outcomes ++ ((jGet out.data "claim").bind (fun c => jStr c "outcome")).toList
    | .error _ => pure ()
  let allowed := ["won", "ended", "superseded"]
  o := o ++ [check "claim outcome enum is exactly {won, ended, superseded}"
    (outcomes.length == 5 && outcomes.all allowed.contains && allowed.all outcomes.contains)
    (String.intercalate "," outcomes)]
  -- partialClaimMessage rows (unit — reaching the rarer status winners through
  -- the command needs a mid-command concurrent fold): every status wording is
  -- self-consistent; the in_progress winner never yields the contradictory
  -- "in_progress, not in_progress" and drops the reopen/re-claim remedy
  for st in [Status.Open, Status.InProgress, Status.Done, Status.Cancelled] do
    let msg := partialClaimMessage "aaaabbbbccccdd77" "carol" st
    let base := (msg.splitOn "superseded").length == 2
      && (msg.splitOn "still holds the assignee").length == 2
    let shaped :=
      if st == Status.InProgress then
        (msg.splitOn "not in_progress").length == 1
          && (msg.splitOn "already in_progress").length == 2
      else
        (msg.splitOn s!"{statusWire st}, not in_progress").length == 2
    o := o ++ [check s!"partial-claim wording is self-consistent for status {statusWire st}"
      (base && shaped) msg]
  -- reopen clears the assignee (ADR-0013): a claimed-then-reopened issue is Open
  -- AND unassigned (the prior claim ended with the close the reopen reverses).
  -- omit-empty ⇒ the assignee field is absent once cleared.
  let dirRC ← freshDir
  let tgtRC ← mkIssue dirRC "ClaimedThenReopened"
  let baseRC ← nowMs
  let segRC := foreignLine (.claim tgtRC "frank") ((baseRC + 20000) * 2 ^ 16) "2zzzzzzzzzzzz" "frank" 1 ++ "\n"
            ++ foreignLine (.reopen tgtRC) ((baseRC + 40000) * 2 ^ 16) "2zzzzzzzzzzzz" "frank" 2 ++ "\n"
  IO.FS.writeFile (System.FilePath.mk dirRC / "log" / "2zzzzzzzzzzzz.jsonl") segRC
  o := o ++ [← expectData "reopen clears the assignee: a reopened claimed issue is Open and unassigned"
      ["show", "tl-" ++ tgtRC, "--dir", dirRC, "--json"]
      (fun j => jStr j "status" == some "open" && (jGet j "assignee").isNone)]
  -- open+assigned IS reachable by an LWW race (NOT "unreachable by construction"):
  -- `status` and `assignee` are independent registers, so a `claim` stamped BELOW
  -- its `create` (clock skew / a crafted segment) loses the status LWW (the higher
  -- create wins status=open) but wins the assignee LWW. The value-equality reopen
  -- guard is genuinely needed: it fires on this open-but-assigned state (not a
  -- no-op) and restores open+unassigned.
  let dirLww ← freshDir
  IO.FS.createDirAll (System.FilePath.mk dirLww / "log")
  let lwwId := "aaaabbbbcccceeee"
  IO.FS.writeFile (System.FilePath.mk dirLww / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create lwwId { title := some "skewed" }) 4000 "2zzzzzzzzzzzz" "eve" 2 ++ "\n"
     ++ foreignLine (.claim lwwId "alice") 2000 "2zzzzzzzzzzzz" "eve" 1 ++ "\n")
  o := o ++ [← expectData "open+assigned is reachable by an LWW race (claim stamped below create)"
      ["show", "tl-" ++ lwwId, "--dir", dirLww, "--json"]
      (fun j => jStr j "status" == some "open" && jStr j "assignee" == some "alice")]
  let _ ← run' ["reopen", "tl-" ++ lwwId, "--dir", dirLww, "--actor", "dev"]
  o := o ++ [← expectData "reopen (value-equality guard) restores open+unassigned from the LWW open+assigned"
      ["show", "tl-" ++ lwwId, "--dir", dirLww, "--json"]
      (fun j => jStr j "status" == some "open" && (jGet j "assignee").isNone)]
  -- doctor survives store damage as a failing check
  let dir4 ← freshDir
  let _ ← mkIssue dir4 "Healthy"
  let log4 := System.FilePath.mk dir4 / "log"
  let segs4 ← log4.readDir
  for ent in segs4 do
    IO.FS.removeFile ent.path
    let out ← IO.Process.output { cmd := "ln", args := #["-s", "/nonexistent", ent.path.toString] }
    unless out.exitCode == 0 do throw (IO.userError "ln failed")
  o := o ++
    [← expectData "doctor reports a symlinked segment as a failing check"
      ["doctor", "--dir", dir4]
      (fun j => jBool j "healthy" == some false
        && (jArr j "checks").any (fun c =>
             jStr c "name" == some "log" && jStr c "status" == some "fail"))]
  return o

/-- The ADR-0017 §8 description precedence on `create`. The stdin leg needs
    a real process boundary (a pipe), so those rows spawn the binary via
    `sh -c`. -/
def cliDescriptionTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  o := o ++
    [← expectData "create --description sets the body"
      ["create", "Titled", "--dir", dir, "--actor", "t",
       "--description", "line one\nline two"]
      (fun j => jStr j "description" == some "line one\nline two"),
     -- a trailing `-` and `--description <text>` name two body sources: a usage
     -- conflict, caught before any IO (so it never reaches stdin)
     ← expectErr "a trailing - with --description <text> is a usage conflict"
       ["create", "X", "--dir", dir, "--actor", "t", "--description", "text", "-"] .usage]
  let exe := (← IO.currentDir) / ".lake" / "build" / "bin" / "tl"
  unless ← exe.pathExists do
    return o ++ [{ name := "binary present for stdin rows", passed := false,
                   msg := "run `lake build` first" }]
  let sh (script : String) : IO IO.Process.Output :=
    IO.Process.output { cmd := "sh", args := #["-c", script] }
  let q (s : String) : String := "'" ++ s ++ "'"
  let hasDesc (out body : String) : Bool := (out.splitOn s!"\"description\":\"{body}\"").length == 2
  let noDesc (out : String) : Bool := (out.splitOn "\"description\"").length == 1
  -- ADR-0017 §8: without the `-` sentinel, stdin is not
  -- read — the body stays absent even with data on the pipe. The regression
  -- guard for the hang: an unrequested stdin is never consumed.
  let nodash ← sh s!"printf 'from\nstdin' | {q exe.toString} create NoDash --dir {q dir} --actor t --json"
  o := o ++ [check "no sentinel: piped stdin is NOT read (body absent)" (noDesc nodash.stdout) nodash.stdout]
  -- `--description -` reads the body from stdin
  let viaFlag ← sh s!"printf 'from\nstdin' | {q exe.toString} create ViaFlag --dir {q dir} --actor t --description - --json"
  o := o ++ [check "--description - reads the body from stdin" (hasDesc viaFlag.stdout "from\\nstdin") viaFlag.stdout]
  -- a trailing `-` reads the body from stdin (same request as --description -)
  let viaDash ← sh s!"printf 'from\nstdin' | {q exe.toString} create ViaDash --dir {q dir} --actor t --json -"
  o := o ++ [check "a trailing - reads the body from stdin" (hasDesc viaDash.stdout "from\\nstdin") viaDash.stdout]
  -- `--description <text>` is the literal body; stdin is left untouched
  let lit ← sh s!"printf 'ignored' | {q exe.toString} create Lit --dir {q dir} --actor t --description flagged --json"
  o := o ++ [check "--description <text> is the body; stdin untouched" (hasDesc lit.stdout "flagged") lit.stdout]
  -- `-` with empty stdin leaves the description absent
  let emptyDash ← sh s!": | {q exe.toString} create EmptyDash --dir {q dir} --actor t --json -"
  o := o ++ [check "- with empty stdin leaves the body absent" (noDesc emptyDash.stdout) emptyDash.stdout]
  -- the hang guard: a held-open, non-EOF stdin without `-` must not block — tl
  -- returns promptly without reading it. On a regression it would block until
  -- the 5s holder closes the write end; the timing bound catches that.
  let fifo := s!"{dir}-holdpipe"
  let t0 ← IO.monoMsNow
  let held ← sh s!"mkfifo {q fifo}; sleep 5 > {q fifo} 2>/dev/null & {q exe.toString} create Held --dir {q dir} --actor t --json < {q fifo}; rm -f {q fifo}"
  let elapsed := (← IO.monoMsNow) - t0
  o := o ++
    [check s!"held-open non-EOF stdin without - does not block ({elapsed}ms)"
      (held.exitCode == 0 && noDesc held.stdout && elapsed < 3000)
      s!"exit={held.exitCode} elapsed={elapsed}ms out={held.stdout}"]
  return o

/-- The consistency batch: stamp-ordered provenance ties, mode-scoped
    `--of`, segment-owner validation, junk stems, hardened enumeration. (The
    ownership *refusal* itself needs a second uid and stays untestable here;
    its mechanism rides every open via the shim walk.) -/
def cliConsistencyTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  -- --of is mode-scoped: only --as duplicate
  let x ← mkIssue dir "OfGuard"
  o := o ++ [← expectErr "--of without --as duplicate is usage"
    ["close", "tl-" ++ x, "--dir", dir, "--as", "done", "--of", "tl-" ++ x] .usage]
  -- same-HLC cross-replica lifecycle ties: the projection must agree with
  -- the LWW state in both directions (the bare-hlc comparison bug class)
  let a ← mkIssue dir "TieA"
  let b ← mkIssue dir "TieB"
  -- later than the local creates, within the skew window (ADR-0007)
  let h := ((← nowMs) + 60000) * 2 ^ 16
  let log := System.FilePath.mk dir / "log"
  IO.FS.writeFile (log / "1zzzzzzzzzzzz.jsonl")
    (foreignLine (.close a .Done) h "1zzzzzzzzzzzz" "eve" 1 ++ "\n"
      ++ foreignLine (.reopen b) h "1zzzzzzzzzzzz" "eve" 2 ++ "\n")
  IO.FS.writeFile (log / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.reopen a) h "2zzzzzzzzzzzz" "mallory" 1 ++ "\n"
      ++ foreignLine (.close b .Done) h "2zzzzzzzzzzzz" "mallory" 2 ++ "\n")
  o := o ++
    [← expectData "same-hlc reopen wins by stamp order: open, no closedAt"
      ["show", "tl-" ++ a, "--dir", dir]
      (fun j => jStr j "status" == some "open" && (jStr j "closedAt").isNone),
     ← expectData "same-hlc close wins by stamp order: done, closedAt present"
      ["show", "tl-" ++ b, "--dir", dir]
      (fun j => jStr j "status" == some "done" && (jStr j "closedAt").isSome)]
  -- a record stamped by another replica refuses its segment
  let dir2 ← freshDir
  let _ ← mkIssue dir2 "Mine"
  IO.FS.writeFile (System.FilePath.mk dir2 / "log" / "1zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbccccdddd" { title := some "smuggled" }) 99
       "2zzzzzzzzzzzz" "eve" ++ "\n")
  o := o ++
    [← expectData "a mis-assembled segment (wrong stamp replica) is refused"
      ["list", "--dir", dir2, "--limit", "0"]
      (fun j => jNat j "count" == some 1)]
  -- junk .jsonl stems are disclosed and never folded
  IO.FS.writeFile (System.FilePath.mk dir2 / "log" / "not-a-replica.jsonl") "GARBAGE\n"
  let junkRes ← run' ["list", "--dir", dir2, "--limit", "0"]
  o := o ++ [match junkRes with
    | .ok out =>
      check "junk .jsonl stem is disclosed, not folded"
        (out.notes.any (fun n => (n.splitOn "not a replica segment").length > 1))
        (String.intercalate "|" out.notes)
    | .error e =>
      { name := "junk .jsonl stem is disclosed, not folded", passed := false,
        msg := e.message }]
  -- a symlinked log/ refuses the listing (not just the later per-file opens)
  let dir3 ← freshDir
  let _ ← mkIssue dir3 "X"
  let realLog ← IO.FS.createTempDir
  IO.FS.removeDirAll (System.FilePath.mk dir3 / "log")
  let ln ← IO.Process.output
    { cmd := "ln", args := #["-s", realLog.toString, dir3 ++ "/log"] }
  o := o ++
    [check "ln -s for the log-dir fixture" (ln.exitCode == 0) ln.stderr,
     ← expectErr "a symlinked log/ refuses the listing" ["list", "--dir", dir3]
       .unsafePath]
  return o

/-- The xhigh-review batch: clock monotonicity vs a stale/zeroed clock,
    init not zeroing an existing clock, strict argv, TL_DIR-init, ceiling
    realpath, error-message sanitization, and the meta-key collision. -/
def cliReviewBatchTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let esc := String.singleton (Char.ofNat 0x1b)
  -- (1) a stale present clock is floored by the own-segment max: craft an own
  -- segment with a high HLC, set the clock file far below it, then a write
  -- must mint above the own max (no own-replica LWW regression).
  let dir ← freshDir
  -- the project's own replica id, so the crafted segment counts as own
  let realReplica := (← IO.FS.readFile (System.FilePath.mk dir / "local" / "replica")).trimAscii.toString
  let high := 0x0000700000000000
  IO.FS.createDirAll (System.FilePath.mk dir / "log")
  IO.FS.writeFile (System.FilePath.mk dir / "log" / (realReplica ++ ".jsonl"))
    (foreignLine (.create "aaaabbbbccccdddd" { title := some "old" }) high realReplica "t" ++ "\n")
  IO.FS.writeFile (System.FilePath.mk dir / "local" / "clock") "0000000000000001\n"
  o := o ++
    [← expectData "a stale clock is floored by the own-segment max (no regression)"
      ["create", "new", "--dir", dir, "--actor", "t"]
      (fun j => ((jStr j "createdAt").isSome))]
  -- read it back: the new create's stamp must exceed the old high HLC, i.e.
  -- the issue materializes (folded above) — verify via list count = 2
  o := o ++
    [← expectData "the stale-clock write folded (monotonic over own segment)"
      ["list", "--dir", dir, "--limit", "0"]
      (fun j => jNat j "count" == some 2)]
  -- (2) init must not zero an existing clock on partial-init completion
  let dir2 ← freshDir
  IO.FS.writeFile (System.FilePath.mk dir2 / "local" / "clock") "0000700000000abc\n"
  IO.FS.removeFile (System.FilePath.mk dir2 / "local" / "replica")
  let _ ← run' ["init", "--dir", dir2]
  let clockAfter := (← IO.FS.readFile (System.FilePath.mk dir2 / "local" / "clock")).trimAscii.toString
  o := o ++
    [check "init completes a partial .tl without zeroing an existing clock"
      (clockAfter == "0000700000000abc") clockAfter]
  -- (3) strict argv — surplus positionals and duplicate single-value flags
  let dir3 ← freshDir
  let x ← mkIssue dir3 "Strict"
  o := o ++
    [← expectErr "surplus positional is usage" ["close", "tl-" ++ x, "extra", "--dir", dir3, "--as", "done"] .usage,
     ← expectErr "ready with a positional is usage" ["ready", "extra", "--dir", dir3] .usage,
     ← expectErr "duplicate single-value flag is usage"
       ["update", "tl-" ++ x, "--dir", dir3, "--title", "a", "--title", "b"] .usage,
     ← expectData "create's repeatable edge flags are NOT rejected"
       ["create", "child", "--dir", dir3, "--blocked-by", "tl-" ++ x, "--blocked-by", "tl-" ++ x, "--actor", "t"]
       (fun j => (jArr j "dependencies").length ≥ 1)]
  -- (7) meta-key collision: two keys differing only in a control char both
  -- survive the --json projection (no silent mkObj collapse)
  let dir4 ← freshDir
  let m ← mkIssue dir4 "Meta"
  let k1 := "k" ++ String.singleton (Char.ofNat 1)
  let k2 := "k" ++ String.singleton (Char.ofNat 2)
  let realReplica4 := (← IO.FS.readFile (System.FilePath.mk dir4 / "local" / "replica")).trimAscii.toString
  let metaSeg := System.FilePath.mk dir4 / "log" / (realReplica4 ++ ".jsonl")
  -- append the two metaSet ops to the own segment (mkIssue already wrote the
  -- create there — overwriting would delete the issue)
  let prev ← IO.FS.readFile metaSeg
  IO.FS.writeFile metaSeg
    (prev ++ foreignLine (.metaSet m k1 (some "v1")) 0x100 realReplica4 "t" 3 ++ "\n"
      ++ foreignLine (.metaSet m k2 (some "v2")) 0x101 realReplica4 "t" 4 ++ "\n")
  o := o ++
    [← (do
       -- the own segment now has the meta ops; show --json must keep both keys
       match ← run' ["show", "tl-" ++ m, "--dir", dir4] with
       | .ok out =>
         let metaCount := match jGet out.data "meta" with
           | some (Json.obj kvs) => kvs.toArray.size
           | _ => 0
         pure (check "two control-char meta keys both survive the projection"
           (metaCount == 2) s!"meta member count {metaCount}")
       | .error e => pure { name := "meta keys both survive", passed := false, msg := e.message })]
  -- (#12) a close that loses LWW to a later foreign write echoes
  -- consistently: status not closed and unblocked empty (no "Closed" lie)
  let dir5 ← freshDir
  let blkr ← mkIssue dir5 "blocker"
  let _ ← mkIssue dir5 "dependent" ["--blocked-by", "tl-" ++ blkr]
  -- a foreign segment reopens the blocker at a far-future stamp
  let realReplica5 := (← IO.FS.readFile (System.FilePath.mk dir5 / "local" / "replica")).trimAscii.toString
  let _ := realReplica5
  -- the reopen is later than the local close, within the skew window (ADR-0007)
  let reopenHlc := ((← nowMs) + 60000) * 2 ^ 16
  IO.FS.writeFile (System.FilePath.mk dir5 / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create blkr { title := some "blocker" }) 0x10 "2zzzzzzzzzzzz" "eve" 1 ++ "\n"
      ++ foreignLine (.reopen blkr) reopenHlc "2zzzzzzzzzzzz" "eve" 2 ++ "\n")
  o := o ++
    [← expectData "a superseded close echoes consistently (not closed, nothing freed)"
      ["close", "tl-" ++ blkr, "--dir", dir5, "--as", "done", "--actor", "t"]
      (fun j => jStr j "status" != some "done" && (jArr j "unblocked").isEmpty)]
  -- spawn rows: TL_DIR-init, ceiling realpath, error sanitization
  let exe := (← IO.currentDir) / ".lake" / "build" / "bin" / "tl"
  unless ← exe.pathExists do return o
  let spawn (args : List String) (env : List (String × Option String) := [])
      (cwd : Option System.FilePath := none) : IO IO.Process.Output :=
    IO.Process.output { cmd := exe.toString, args := args.toArray, env := env.toArray, cwd }
  -- (4) TL_DIR is honored by init (the init+work-loop pair binds one dir)
  let root ← IO.FS.createTempDir
  let envState := (root / "state").toString
  let i1 ← spawn ["init", "--json"] [("TL_DIR", some envState)]
  let c1 ← spawn ["create", "x", "--json"] [("TL_DIR", some envState)]
  o := o ++
    [check "TL_DIR tl init initializes the env dir" (i1.exitCode == 0) i1.stdout,
     check "the following create binds the SAME TL_DIR dir" (c1.exitCode == 0) c1.stdout]
  -- (5) a logical (un-realpath'd) ceiling still stops discovery (macOS /var
  -- vs /private/var; the realpath canonicalization matches them)
  IO.FS.createDirAll (root / "proj" / "sub")
  let _ ← spawn ["init", "--dir", (root / "proj" / ".tl").toString]
  let ceiled ← spawn ["list", "--json"]
    [("TL_DIR", none), ("GIT_CEILING_DIRECTORIES", some (root / "proj").toString)]
    (some (root / "proj" / "sub"))
  o := o ++
    [check "a logical ceiling entry still stops discovery (realpath-matched)"
      (ceiled.exitCode == 3) ceiled.stdout]
  -- (6) a refused segment's error message is ANSI-stripped before surfacing
  let sdir ← spawn ["init", "--json"]
  let _ := sdir
  let sandbox ← IO.FS.createTempDir
  let _ ← spawn ["init", "--dir", (sandbox / ".tl").toString]
  let sreplica := (← IO.FS.readFile (sandbox / ".tl" / "local" / "replica")).trimAscii.toString
  -- own-segment damage carrying an ANSI escape in a malformed line
  IO.FS.createDirAll (sandbox / ".tl" / "log")
  IO.FS.writeFile (sandbox / ".tl" / "log" / (sreplica ++ ".jsonl"))
    ("GARBAGE " ++ esc ++ "[31mhostile\n")
  let refused ← spawn ["list", "--json", "--dir", (sandbox / ".tl").toString]
  o := o ++
    [check "the refused-segment error envelope is ANSI-stripped on stdout"
      (refused.exitCode == 7 && (refused.stdout.splitOn esc).length == 1)
      refused.stdout]
  return o

/-- The free read/lifecycle verbs added in the agent-surface batch:
    reopen, stats, log. -/
def cliFreeVerbTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let a ← mkIssue dir "Task A" ["-p", "1"]
  let b ← mkIssue dir "Task B" ["--blocked-by", "tl-" ++ a]
  -- reopen: a closed issue returns to open and clears the resolution
  let _ ← run' ["close", "tl-" ++ a, "--dir", dir, "--as", "done", "--actor", "t"]
  o := o ++
    [← expectData "reopen returns a closed issue to open, clearing resolution"
      ["reopen", "tl-" ++ a, "--dir", dir, "--actor", "t"]
      (fun j => jStr j "status" == some "open" && (jStr j "closeResolution").isNone),
     -- idempotent: reopening an already-open issue is a disclosed no-op
     ← expectData "reopen of an already-open issue is a no-op"
       ["reopen", "tl-" ++ a, "--dir", dir, "--actor", "t"]
       (fun j => jStr j "status" == some "open")]
  -- stats: the pinned counts
  o := o ++
    [← expectData "stats counts by state + ready/blocked/cycles"
      ["stats", "--dir", dir]
      (fun j => jNat j "total" == some 2 && jNat j "open" == some 2
        && jNat j "ready" == some 1 && jNat j "blocked" == some 1
        && jNat j "cycles" == some 0)]
  -- §7: green marks the workable (ready) count, not the stored-open count
  -- (which includes the blocked issue). Assert the colored render directly.
  let escSeq := String.singleton (Char.ofNat 0x1b)
  match ← run' ["stats", "--dir", dir] with
  | .error e => o := o ++ [check "stats colored render reachable" false e.message]
  | .ok out =>
    let colored := match out.render with | some f => f ⟨.on, .ascii⟩ | none => ""
    o := o ++
      [check "stats paints the ready count green (§7 workable)"
        ((colored.splitOn (escSeq ++ "[32mready ")).length == 2) colored,
       check "stats leaves the stored-open count neutral (not green)"
        ((colored.splitOn (escSeq ++ "[32mopen ")).length == 1) colored]
  -- stats counts effective status and splits open into epics vs tasks: a
  -- rolled-up epic (stored open, all children closed) counts as done, not open,
  -- matching `list` (ADR-0020 §stats).
  let dir2 ← freshDir
  let p ← mkIssue dir2 "Epic P" []
  let c ← mkIssue dir2 "Child C" ["--parent", "tl-" ++ p]
  let _ ← mkIssue dir2 "Task T" []
  o := o ++
    [← expectData "stats: open splits into epics vs tasks (effective status)"
      ["stats", "--dir", dir2]
      (fun j => jNat j "total" == some 3 && jNat j "open" == some 3
        && jNat j "openEpics" == some 1 && jNat j "openTasks" == some 2)]
  let _ ← run' ["close", "tl-" ++ c, "--dir", dir2, "--as", "done", "--actor", "t"]
  o := o ++
    [← expectData "stats: a rolled-up epic counts as done, not open (effective, not stored)"
      ["stats", "--dir", dir2]
      (fun j => jNat j "open" == some 1 && jNat j "openEpics" == some 0
        && jNat j "openTasks" == some 1 && jNat j "done" == some 2)]
  -- slug: create/update set the display handle, which resolves like an id
  let dirS ← freshDir
  let sId ← mkIssue dirS "Sluggable" ["--slug", "my-slug"]
  o := o ++
    [← expectData "create --slug sets the slug" ["show", "tl-" ++ sId, "--dir", dirS]
      (fun j => jStr j "slug" == some "my-slug"),
     ← expectData "the slug resolves like an id" ["show", "my-slug", "--dir", dirS]
      (fun j => jStr j "id" == some ("tl-" ++ sId)),
     ← expectData "update --slug replaces it"
        ["update", "tl-" ++ sId, "--slug", "new-slug", "--dir", dirS, "--actor", "t"]
      (fun j => jStr j "slug" == some "new-slug")]
  -- meta: the opaque side-channel — set/get/list/clear round-trip
  let dirMeta ← freshDir
  let mId ← mkIssue dirMeta "Has meta" []
  o := o ++
    [← expectData "meta set writes a key"
        ["meta", "set", "tl-" ++ mId, "ext:jira", "PROJ-1", "--dir", dirMeta, "--actor", "t"]
      (fun j => jStr j "status" == some "set" && jStr j "value" == some "PROJ-1"),
     ← expectData "meta get reads it back" ["meta", "get", "tl-" ++ mId, "ext:jira", "--dir", dirMeta]
      (fun j => jStr j "value" == some "PROJ-1"),
     ← expectData "meta list counts the issue's keys" ["meta", "list", "tl-" ++ mId, "--dir", dirMeta]
      (fun j => jNat j "count" == some 1),
     ← expectData "meta clear retracts it"
        ["meta", "clear", "tl-" ++ mId, "ext:jira", "--dir", dirMeta, "--actor", "t"]
      (fun j => jStr j "status" == some "cleared"),
     ← expectData "meta get after clear is null" ["meta", "get", "tl-" ++ mId, "ext:jira", "--dir", dirMeta]
      (fun j => (jStr j "value").isNone)]
  -- CLI conveniences: -v/--version and -h aliases; did-you-mean on a typo
  o := o ++
    [← expectData "--version is a version alias" ["--version"] (fun _ => true),
     ← expectData "-v is a version alias" ["-v"] (fun _ => true),
     ← expectData "-h is a help alias" ["-h"] (fun j => (jArr j "commands").length > 0),
     ← expectErr "an unknown command suggests the closest" ["creat", "x"] .usage
       (fun e => (e.message.splitOn "did you mean").length > 1)]
  -- list defaults to open-only; --all includes closed
  let _ ← run' ["close", "tl-" ++ b, "--dir", dir, "--as", "done", "--actor", "t"]
  o := o ++
    [← expectData "list hides closed issues by default"
       ["list", "--dir", dir, "--limit", "0"]
       (fun j => (jArr j "items").all (fun r => jStr r "id" != some ("tl-" ++ b))),
     ← expectData "list --all includes closed issues"
       ["list", "--all", "--dir", dir, "--limit", "0"]
       (fun j => (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ b)))]
  -- log: newest-first entries, the per-issue filter, the targets array
  o := o ++
    [← expectData "log lists ops newest-first with targets"
      ["log", "--dir", dir, "--limit", "0"]
      (fun j => (jNat j "count").getD 0 ≥ 4
        && (match (jArr j "entries").head? with
            | some e => (jStr e "op").isSome && (jArr e "targets").length ≥ 1
                && (jStr e "timestamp").isSome
            | none => false)),
     ← expectData "log <id> filters to ops touching that issue"
       ["log", "tl-" ++ b, "--dir", dir, "--limit", "0"]
       (fun j =>
         -- B's create + the depAdd that touches B (the close/reopen were on A)
         (jArr j "entries").all (fun e =>
           (jArr e "targets").any (fun t => t.getStr?.toOption == some ("tl-" ++ b))))]
  return o

/-- The ADR-0017 rich human rendering: glyphs, per-token color, the show
    detail view, the footer/legend, and the independent color/glyph/plain
    surfaces. Drives each cmd's `render` closure with explicit styles (the
    in-process path), plus a spawned color/plain check (the flag/TTY
    resolution path). -/
def cliRenderTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let esc := Char.ofNat 27
  let dir ← freshDir
  let a ← mkIssue dir "Render me" ["-p", "0"]
  -- ready: one-line format styled vs plain
  match ← run' ["ready", "--dir", dir] with
  | .ok out =>
    let colored := (out.render.map (· ⟨.on, .unicode⟩)).getD ""
    let plain := (out.render.map (· Style.plain)).getD out.human
    o := o ++
      [check "ready emits ANSI under color=on" (colored.contains esc) "no ESC",
       check "ready is ANSI-free under plain" (!plain.contains esc) plain,
       check "ready uses a unicode glyph under glyphs=unicode" (colored.contains '○') colored,
       check "ready uses an ascii glyph under plain" (plain.contains 'o') plain,
       check "ready footer carries summary + legend"
         (((plain.splitOn "Ready:").length > 1) && ((plain.splitOn "in_progress").length > 1)) plain]
  | .error e => o := o ++ [{ name := "ready render", passed := false, msg := e.message }]
  -- show: the detail view (multi-line, status word, relationships), not the one-liner
  let b ← mkIssue dir "Blocked one" ["--blocked-by", "tl-" ++ a, "--description", "the body here"]
  match ← run' ["show", "tl-" ++ b, "--dir", dir] with
  | .ok out =>
    let plain := (out.render.map (· Style.plain)).getD out.human
    o := o ++
      [check "show detail is multi-line (a detail view, not the one-liner)"
         ((plain.splitOn "\n").length > 2) plain,
       check "show detail renders the DESCRIPTION fence"
         ((plain.splitOn "DESCRIPTION").length > 1) plain,
       check "show detail lists the blocker relationship"
         ((plain.splitOn "blocked by").length > 1) plain]
  | .error e => o := o ++ [{ name := "show render", passed := false, msg := e.message }]
  -- list renders the hierarchy tree by default (ADR-0017 §2); --flat opts into
  -- one-line rows; --json stays the flat items array either way
  let dirT ← freshDir
  let epic ← mkIssue dirT "An epic"
  let _ ← mkIssue dirT "A child" ["--parent", "tl-" ++ epic]
  let _ ← mkIssue dirT "An orphan"
  match ← run' ["list", "--dir", dirT, "--limit", "0"] with
  | .ok out =>
    let plain := (out.render.map (· Style.plain)).getD out.human
    o := o ++
      [check "default list marks the epic" ((plain.splitOn "[epic]").length > 1) plain,
       check "default list indents the child with a connector"
         ((plain.splitOn "\\-- ").length > 1 || (plain.splitOn "+-- ").length > 1) plain,
       check "the child line sits below its epic line"
         (((plain.splitOn "An epic").head?.getD "").length < ((plain.splitOn "A child").head?.getD "").length) plain]
  | .error e => o := o ++ [{ name := "list default tree", passed := false, msg := e.message }]
  match ← run' ["list", "--flat", "--dir", dirT, "--limit", "0"] with
  | .ok out =>
    let plain := (out.render.map (· Style.plain)).getD out.human
    o := o ++
      [check "list --flat has no tree connectors"
         ((plain.splitOn "\\-- ").length == 1 && (plain.splitOn "+-- ").length == 1) plain,
       check "list --flat still shows every visible issue"
         (((plain.splitOn "A child").length > 1) && ((plain.splitOn "An orphan").length > 1)) plain]
  | .error e => o := o ++ [{ name := "list --flat", passed := false, msg := e.message }]
  o := o ++
    [← expectData "default list --json keeps the flat items array"
       ["list", "--dir", dirT, "--limit", "0"]
       (fun j => (jArr j "items").length == 3
         && (jArr j "items").all (fun r => (jStr r "id").isSome))]
  -- spawned: the flag/TTY resolution path (--color=always vs --plain)
  let exe := (← IO.currentDir) / ".lake" / "build" / "bin" / "tl"
  if ← exe.pathExists then
    let spawn (args : List String) : IO String := do
      let out ← IO.Process.output { cmd := exe.toString, args := args.toArray }
      pure out.stdout
    let always ← spawn ["ready", "--dir", dir, "--color=always"]
    let plainOut ← spawn ["ready", "--dir", dir, "--plain"]
    o := o ++
      [check "--color=always emits ANSI on stdout" (always.contains esc) "no ESC",
       check "--plain emits no ANSI on stdout" (!plainOut.contains esc) plainOut]
  return o

/-- Read-time refresh end-to-end (ADR-0016 §3): two state dirs sharing one
    repo's `refs/tl/log` (the worktree model). A creates + syncs; B *only
    reads* and still sees A's task — no explicit `tl sync` on B's side. -/
def cliReadRefreshTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let root ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] } : IO _)
  let aDir := (root / ".tl").toString
  let bDir := (root / ".tlB").toString
  let _ ← run' ["init", "--dir", aDir]
  let _ ← run' ["init", "--dir", bDir]
  let aId ← match ← run' ["create", "shared via read-refresh", "--dir", aDir, "--actor", "a"] with
    | .ok out => pure ((jStr out.data "id").getD "")
    | .error e => throw (IO.userError s!"create failed: {e.message}")
  let _ ← run' ["sync", "--dir", aDir]  -- A publishes; B never syncs
  o := o ++ [← expectData "a read absorbs a sibling's published task without an explicit sync"
    ["list", "--dir", bDir, "--json"]
    (fun j => jNat j "count" == some 1 && (jArr j "items").any (fun it => jStr it "id" == some aId))]
  -- the refresh left A's segment + the ref-mark in B's own state dir
  o := o ++ [check "B's read materialized A's segment into its own .tl/log"
      ((← (root / ".tlB" / "log").readDir).size == 1),
    check "B's read wrote the ref-mark"
      (← (root / ".tlB" / "local" / "ref-mark").pathExists)]
  -- a second read with the ref unmoved still works (the unchanged-skip path)
  o := o ++ [← expectData "a second read with nothing new still sees the task"
    ["list", "--dir", bDir, "--json"] (fun j => jNat j "count" == some 1)]
  return o

/-- Degraded-refresh disclosure (ADR-0008 loud-not-silent × ADR-0016 §3): when a
    read-time refresh cannot run (here, B's log dir is read-only so the foreign
    materialize fails), the read still serves — a moment stale — and discloses
    the degrade as a note, rather than silently serving the stale view. Root
    bypasses directory permissions, so the degrade branch is asserted only for a
    non-root user; the always-true invariant (the read succeeds) holds for both. -/
def cliDegradedRefreshTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let root ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] } : IO _)
  let aDir := (root / ".tl").toString
  let bDir := (root / ".tlB").toString
  let _ ← run' ["init", "--dir", aDir]
  let _ ← run' ["init", "--dir", bDir]
  let _ ← run' ["create", "first task", "--dir", aDir, "--actor", "a"]
  let _ ← run' ["sync", "--dir", aDir]
  -- B reads once: this materializes A's segment, creating B's log dir + ref-mark.
  let _ ← run' ["list", "--dir", bDir, "--json"]
  -- the ref moves again; now B's mark trails the tip, so B's next read must
  -- materialize — but with B's log dir read-only the writeback fails and the
  -- refresh degrades (read the ref, can't write the segment).
  let _ ← run' ["create", "second task", "--dir", aDir, "--actor", "a"]
  let _ ← run' ["sync", "--dir", aDir]
  let uid ← (IO.Process.output { cmd := "id", args := #["-u"] } : IO _)
  let isRoot := uid.stdout.trimAscii.toString == "0"
  let bLog := (root / ".tlB" / "log").toString
  let _ ← (IO.Process.output { cmd := "chmod", args := #["0500", bLog] } : IO _)
  let listed ← run' ["list", "--dir", bDir, "--json"]
  o := o ++ [(match listed with
    | .ok out => check "a read whose refresh cannot run succeeds and discloses the degrade"
        (if isRoot then true
         else out.notes.any (fun n => (n.splitOn "moment-stale").length > 1))
        ("notes=" ++ String.intercalate "|" out.notes)
    | .error e => { name := "degraded read succeeds", passed := false,
                    msg := s!"read failed with {e.code.wire}: {e.message}" })]
  let _ ← (IO.Process.output { cmd := "chmod", args := #["0700", bLog] } : IO _)
  return o

/-- Auto-sync (ADR-0021): the post-`transact` hook publishes a write into the
    shared `refs/tl/log` when `tl.autosync` is on, so a worktree sibling sees it
    with no explicit `tl sync`; off by default; best-effort (a publish failure
    is disclosed, never fails the write); a no-op outside a git repo. -/
def cliAutoSyncTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let root ← IO.FS.createTempDir
  let gitC (args : List String) : IO _ :=
    IO.Process.output { cmd := "git", args := #["-C", root.toString] ++ args.toArray }
  let _ ← gitC ["init", "-q"]
  let aDir := (root / ".tl").toString
  let bDir := (root / ".tlB").toString
  let _ ← run' ["init", "--dir", aDir]
  let _ ← run' ["init", "--dir", bDir]
  -- (a) auto-sync unset (default off in a main worktree): A's write is not
  -- published, so a sibling that only reads sees nothing.
  let _ ← run' ["create", "off by default", "--dir", aDir, "--actor", "a"]
  o := o ++ [← expectData "auto-sync off: a sibling does not see an unpublished write"
    ["list", "--dir", bDir, "--json"] (fun j => jNat j "count" == some 0)]
  -- (b) auto-sync on: the next write auto-publishes; B sees it with no `tl sync`.
  let _ ← gitC ["config", "tl.autosync", "true"]
  let onId ← match ← run' ["create", "on, auto-published", "--dir", aDir, "--actor", "a"] with
    | .ok out => pure ((jStr out.data "id").getD "")
    | .error e => throw (IO.userError s!"create failed: {e.message}")
  o := o ++ [← expectData "auto-sync on: a sibling sees the write with no explicit sync"
    ["list", "--dir", bDir, "--json"]
    (fun j => (jArr j "items").any (fun it => jStr it "id" == some onId))]
  -- (c) a publish failure is disclosed and never fails the write (ADR-0021 §4):
  -- the object store is read-only, so update-ref fails but the append already
  -- landed. Root bypasses permissions, so only assert the survive-invariant there.
  let uid ← (IO.Process.output { cmd := "id", args := #["-u"] } : IO _)
  let isRoot := uid.stdout.trimAscii.toString == "0"
  let _ ← (IO.Process.output { cmd := "chmod", args := #["-R", "0500", (root / ".git").toString] } : IO _)
  let res ← run' ["create", "write outlives a failed publish", "--dir", aDir, "--actor", "a"]
  o := o ++ [(match res with
    | .ok out => check "a write succeeds and discloses when auto-sync's publish fails"
        ((jStr out.data "id").isSome
         && (isRoot || out.notes.any (fun n => (n.splitOn "auto-sync skipped").length > 1)))
        ("notes=" ++ String.intercalate "|" out.notes)
    | .error e => { name := "write outlives a failed publish", passed := false,
                    msg := s!"write failed: {e.code.wire}: {e.message}" })]
  let _ ← (IO.Process.output { cmd := "chmod", args := #["-R", "0700", (root / ".git").toString] } : IO _)
  -- (d) no-git degrade: a write in a non-repo dir succeeds with no auto-sync
  -- note (syncLocal is a silent no-op when there is no shared ref).
  let solo ← IO.FS.createTempDir
  let _ ← run' ["init", "--dir", (solo / ".tl").toString]
  o := o ++ [(match ← run' ["create", "no repo here", "--dir", (solo / ".tl").toString] with
    | .ok out => check "a write outside a git repo succeeds with no auto-sync note"
        ((jStr out.data "id").isSome && !out.notes.any (fun n => (n.splitOn "auto-sync").length > 1))
        ("notes=" ++ String.intercalate "|" out.notes)
    | .error e => { name := "non-repo write succeeds", passed := false, msg := e.message })]
  return o

/-- Pre-transact absorb (ADR-0016 write-path freshness): a directed write by id refreshes
    from the shared ref before its guards run, so it finds a task that exists
    only on a sibling's published segment — closing the stale-directed-write gap
    (without it, this `close` by id would fail not-found). -/
def cliPreWriteAbsorbTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let root ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] } : IO _)
  let aDir := (root / ".tl").toString
  let bDir := (root / ".tlB").toString
  let _ ← run' ["init", "--dir", aDir]
  let _ ← run' ["init", "--dir", bDir]
  let aId ← match ← run' ["create", "made by A", "--dir", aDir, "--actor", "a"] with
    | .ok out => pure ((jStr out.data "id").getD "")
    | .error e => throw (IO.userError s!"create failed: {e.message}")
  let _ ← run' ["sync", "--dir", aDir]  -- A publishes; B has never read or synced
  let closed ← run' ["close", aId, "--as", "done", "--dir", bDir]
  o := o ++ [(match closed with
    | .ok _ => check "a directed write absorbs the shared ref before its guards (finds a sibling-only task)"
        true ""
    | .error e => { name := "pre-transact absorb finds a sibling-only task", passed := false,
                    msg := s!"close by id failed: {e.code.wire}: {e.message}" })]
  o := o ++ [← expectData "the directed close took effect against the absorbed state"
    ["show", aId, "--dir", bDir, "--json"] (fun j => jStr j "effectiveStatus" == some "done")]
  return o

/-- Read-time refresh × the refused-segment policy (ADR-0008 × ADR-0016 §3):
    refresh now routinely materializes sibling segments, so a single corrupt
    sibling segment must be disclosed, not fail a worktree whose own state is
    fine/empty — the all-refused throw only fires with no own replica to anchor
    a partial read. -/
def cliRefreshRefusalTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let root ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] } : IO _)
  let bDir := (root / ".tl").toString
  let _ ← run' ["init", "--dir", bDir]  -- B: own replica minted, no own segment
  -- a sibling publishes a corrupt segment into the shared ref
  let badRid := (Tl.Clock.Replica.ofNat 13).id
  let dB : Tl.Store.Dirs := { base := root.toString, tlRel := ".tl" }
  let _ ← (Tl.Sync.writeRef dB [⟨badRid, "this is not json\n".toUTF8⟩] [] none).run
  -- B reads: refresh materializes the corrupt sibling, and the read discloses
  -- the foreign refusal and succeeds (exit 0) rather than failing the command
  let listed ← run' ["list", "--dir", bDir, "--json"]
  o := o ++ [(match listed with
    | .ok out => check "an all-foreign-refused read discloses and succeeds (does not fail)"
        (jNat out.data "count" == some 0 && out.notes.any (fun n => (n.splitOn "refused").length > 1))
        (out.data.compress ++ " notes=" ++ String.intercalate "|" out.notes)
    | .error e => { name := "all-foreign-refused read succeeds", passed := false, msg := s!"read failed with {e.code.wire}: {e.message}" })]
  return o

/-- Clock-skew surfacing (ADR-0007): a far-future foreign op is deferred — a
    read discloses it (held-back note) and `doctor`'s clockSkew check warns. -/
def cliDoctorSkewTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let beyond := ((← nowMs) + 2 * skewWindowMs) * 2 ^ 16  -- well past the 1h window
  IO.FS.createDirAll (System.FilePath.mk dir / "log")
  IO.FS.writeFile (System.FilePath.mk dir / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbccccdddd" { title := some "from the future" })
       beyond "2zzzzzzzzzzzz" "eve" ++ "\n")
  -- a read folds nothing (the future op is deferred) and discloses it
  let listed ← run' ["list", "--dir", dir, "--json"]
  o := o ++ [(match listed with
    | .ok out => check "a read defers the future op (count 0) and discloses it"
        (jNat out.data "count" == some 0
          && out.notes.any (fun n => (n.splitOn "held back").length > 1))
        (out.data.compress ++ " notes=" ++ String.intercalate "|" out.notes)
    | .error e => { name := "read discloses deferred op", passed := false, msg := e.message })]
  -- doctor's clockSkew check warns, naming the deferred count, and reports the
  -- real lead (over deferred ops too — maxHlc alone would understate it)
  o := o ++ [← expectData "doctor warns on clock skew with the real ahead-of-now lead"
    ["doctor", "--json", "--dir", dir]
    (fun j => (jArr j "checks").any (fun c =>
      jStr c "name" == some "clockSkew" && jStr c "status" == some "warn"
        && (jNat c "deferredOps").getD 0 ≥ 1
        && (jNat c "clockLeadMs").getD 0 ≥ skewWindowMs))]
  -- a write against the deferred foreign op discloses it too (not only reads)
  let wrote ← run' ["create", "local work", "--dir", dir, "--actor", "t"]
  o := o ++ [(match wrote with
    | .ok out => check "a write whose guard fold dropped a deferred op discloses it"
        (out.notes.any (fun n => (n.splitOn "held back").length > 1))
        (String.intercalate "|" out.notes)
    | .error e => { name := "write discloses deferred", passed := false, msg := e.message })]
  -- a clock notably ahead but within the 24h window: its op folds (count 1, not
  -- deferred) yet doctor still warns — the warn threshold is decoupled from the
  -- deferral window, so a 9h-style TZ misconfig is flagged (not silent)
  let dir2 ← freshDir
  let ahead := ((← nowMs) + 2 * skewWarnMs) * 2 ^ 16  -- ~2h ahead: > warn, < window
  IO.FS.createDirAll (System.FilePath.mk dir2 / "log")
  IO.FS.writeFile (System.FilePath.mk dir2 / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "bbbbccccddddeeee" { title := some "ahead but folded" })
       ahead "2zzzzzzzzzzzz" "eve" ++ "\n")
  o := o ++ [← expectData "a folded-but-notably-ahead clock still warns (not deferred)"
    ["doctor", "--json", "--dir", dir2]
    (fun j => (jArr j "checks").any (fun c =>
      jStr c "name" == some "clockSkew" && jStr c "status" == some "warn"
        && (jNat c "deferredOps").getD 1 == 0
        && (jNat c "clockLeadMs").getD 0 > skewWarnMs))]
  o := o ++ [← expectData "the notably-ahead op folds (it is not hidden)"
    ["list", "--dir", dir2, "--json"] (fun j => jNat j "count" == some 1)]
  return o

/-- Labels (ADR-0002 OR-Set): add (idempotent), remove (noop when absent),
    the `label list` vocabulary, and the `tl list --label` facet (conjunctive across
    repeats). -/
def cliLabelTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let a ← mkIssue dir "alpha"
  let b ← mkIssue dir "beta"
  o := o ++ [← expectData "label add echoes added"
    ["label", "add", "tl-" ++ a, "feature", "--dir", dir]
    (fun j => jStr j "status" == some "added" && jStr j "label" == some "feature")]
  o := o ++ [← expectData "label add is idempotent (noop on a present label)"
    ["label", "add", "tl-" ++ a, "feature", "--dir", dir] (fun j => jStr j "status" == some "noop")]
  o := o ++ [← expectErr "an empty label is a usage error"
    ["label", "add", "tl-" ++ a, "", "--dir", dir] .usage]
  o := o ++ [← expectData "show reflects the label"
    ["show", "tl-" ++ a, "--dir", dir]
    (fun j => (jArr j "labels").any (fun l => l.getStr?.toOption == some "feature"))]
  let _ ← run' ["label", "add", "tl-" ++ a, "parser", "--dir", dir]
  let _ ← run' ["label", "add", "tl-" ++ b, "feature", "--dir", dir]
  o := o ++ [← expectData "label list is the vocabulary with issue counts"
    ["label", "list", "--dir", dir]
    (fun j => jNat j "count" == some 2
      && (jArr j "labels").any (fun r => jStr r "label" == some "feature" && jNat r "count" == some 2)
      && (jArr j "labels").any (fun r => jStr r "label" == some "parser" && jNat r "count" == some 1))]
  o := o ++ [← expectData "list --label filters to carriers"
    ["list", "--label", "feature", "--dir", dir, "--json"] (fun j => jNat j "count" == some 2)]
  o := o ++ [← expectData "list --label is AND across repeats"
    ["list", "--label", "feature", "--label", "parser", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1 && (jArr j "items").any (fun it => jStr it "id" == some ("tl-" ++ a)))]
  o := o ++ [← expectData "label remove echoes removed"
    ["label", "remove", "tl-" ++ a, "parser", "--dir", dir] (fun j => jStr j "status" == some "removed")]
  o := o ++ [← expectData "label remove is a noop when the label is absent"
    ["label", "remove", "tl-" ++ a, "parser", "--dir", dir] (fun j => jStr j "status" == some "noop")]
  o := o ++ [← expectErr "label remove rejects an empty label (parity with add)"
    ["label", "remove", "tl-" ++ a, "", "--dir", dir] .usage]
  return o

/-- The tree render on a multi-parent diamond stays linear (the old walk
    re-walked the shared subtree under every parent — exponential on chained
    diamonds, reachable from one `create --parent --parent`): the shared node
    expands once, later encounters render the already-shown marker. -/
def cliTreeDiamondTests : IO (List Outcome) := do
  let dir ← freshDir
  -- distinctive titles, not ids: human rows now render short ids (whose length
  -- depends on prefix collisions), so count the stable title token instead — it
  -- renders on both the first expansion and the shared-node "(shown above)" line.
  let a ← mkIssue dir "Anode"
  let b ← mkIssue dir "Bnode" ["--parent", "tl-" ++ a]
  let c ← mkIssue dir "Cnode" ["--parent", "tl-" ++ a]
  let d ← mkIssue dir "Dnode" ["--parent", "tl-" ++ b, "--parent", "tl-" ++ c]
  let _e ← mkIssue dir "Enode" ["--parent", "tl-" ++ d]
  match ← run' ["list", "--dir", dir] with
  | .ok out =>
    let h := out.human
    let count (needle : String) : Nat := (h.splitOn needle).length - 1
    return [
      check "the shared diamond node renders under both parents" (count "Dnode" == 2)
        s!"Dnode appearances: {count "Dnode"} in:\n{h}",
      check "the shared node's subtree expands exactly once" (count "Enode" == 1)
        s!"Enode appearances: {count "Enode"} in:\n{h}",
      check "the second encounter carries the already-shown marker"
        (count "(shown above)" == 1) h]
  | .error err => return [{ name := "tree diamond render", passed := false, msg := err.message }]

/-- Tree-skeleton coloring (ADR-0017 §7): the vertical-continuation prefix
    (`│`/`|`) ahead of a nested node is part of the skeleton and must be painted
    the same dim `2` as the connectors — an un-painted bar renders in the
    terminal default (brighter) and stands out. Regression for the bare-bar bug:
    a non-last branch (`B`) with a child (`sub`) gives `sub` a `|   `
    continuation, which must come through painted when color is on. -/
def cliTreePrefixDimTests : IO (List Outcome) := do
  let dir ← freshDir
  let a ← mkIssue dir "A"
  let b ← mkIssue dir "B" ["--parent", "tl-" ++ a]
  let c ← mkIssue dir "C" ["--parent", "tl-" ++ a]
  -- nest under both siblings: whichever renders non-last yields a `|   `
  -- continuation, independent of the sibling ordering
  let _ ← mkIssue dir "subB" ["--parent", "tl-" ++ b]
  let _ ← mkIssue dir "subC" ["--parent", "tl-" ++ c]
  match ← run' ["list", "--dir", dir] with
  | .ok out =>
    let esc := String.singleton (Char.ofNat 27)
    let s := (out.render.map (fun f => f (⟨.on, .ascii⟩ : Style))).getD ""
    let lines := s.splitOn "\n"
    return [
      -- the scenario must actually produce a `|` continuation (not vacuous)
      check "the tree has a painted vertical continuation"
        ((s.splitOn (esc ++ "[2m|")).length > 1) s,
      -- and with color on, no skeleton line is a bare (unpainted, brighter) bar
      check "no continuation prefix is a bare bright bar — all dim-painted"
        (lines.all (fun l => !l.startsWith "|")) s]
  | .error err => return [{ name := "tree prefix dim", passed := false, msg := err.message }]

/-- The hoisted edge views feeding issueObj/doctor agree with the spec helpers
    they replaced (the lingering non-hoisted scans): a multi-parent child's
    `show --json` still reports a canonical `parent` (issueObj via
    `canonicalParentE`), and `doctor` still counts exactly the one multi-parent
    issue (the graph row over the hoisted `pedges`, not a per-issue `parentsOf`
    rescan). -/
def cliHoistedHelperTests : IO (List Outcome) := do
  let dir ← freshDir
  let a ← mkIssue dir "A"
  let b ← mkIssue dir "B" ["--parent", "tl-" ++ a]
  let c ← mkIssue dir "C" ["--parent", "tl-" ++ a]
  let d ← mkIssue dir "D" ["--parent", "tl-" ++ b, "--parent", "tl-" ++ c]
  return [
    ← expectData "show reports a canonical parent for a multi-parent child"
      ["show", "tl-" ++ d, "--dir", dir]
      (fun j => jStr j "parent" == some ("tl-" ++ b) || jStr j "parent" == some ("tl-" ++ c)),
    ← expectData "doctor counts exactly the one multi-parent issue (hoisted parent view)"
      ["doctor", "--dir", dir]
      (fun j => (jArr j "checks").any (fun ch =>
         jStr ch "name" == some "graph" && jNat ch "multiParent" == some 1))]

/-- The batched provenance map agrees with the per-id scan on every issue —
    including same-target ops interleaved out of order (the sort-grouped
    build must preserve within-target order, like the scan's walk). -/
def provenanceAgreementTests : List Outcome :=
  let stem := "0123456789abc"
  let rv := (ofCrockford? stem).getD 0
  let mk (idx : Nat) (op : WireOp) : ParsedOp :=
    { v := supportedVersion, op, stamp := ⟨1000000 + idx * 7, rv, 500 + idx⟩,
      actor := some s!"a{idx % 3}" }
  let ids := ["a000000000000000", "b000000000000000", "c000000000000000"]
  let pick (k : Nat) : IssueId := ids.getD (k % 3) ""
  let ops := (List.range 40).map (fun k =>
    let i := pick k
    match k % 9 with
    | 0 => mk k (.create i { title := some s!"t{k}" })
    | 1 => mk k (.update i { description := some (some s!"d{k}") })
    | 2 => mk k (.claim i s!"who{k}")
    | 3 => mk k (.close i .Done)
    | 4 => mk k (.reopen i)
    | 5 => mk k (.defer i (2000000 + k))
    | 6 => mk k (.undefer i)
    -- non-provenance verbs must be inert in both forms
    | 7 => mk k (.labelAdd i "x")
    | _ => mk k (.depAdd (i, pick (k + 1), EdgeKind.Blocks)))
  let m := provenanceMap ops
  let s := ops.foldl (fun st p => Tl.Kernel.apply st p.kernelOp) State.empty
  ids.map (fun i =>
    let a := provOf m i
    let b := provenanceOf ops i
    check s!"provenance map ≡ per-id scan for {i}"
      (a.createdAt == b.createdAt && a.updatedAt == b.updatedAt
        && a.closedAt == b.closedAt && a.claimedAt == b.claimedAt
        && a.createdBy == b.createdBy && a.createdReplica == b.createdReplica
        -- cmdList sorts on Prov.createdAt instead of the O(N) createdAtOf find;
        -- for a present issue they must coincide (both = the min create-tag HLC)
        && (!s.presentIssues.contains i || a.createdAt == some (s.createdAtOf i))))

/-- Tree rendering on graphs the CLI cannot create but a merge can (ADR-0003:
    cycles are reported, tolerated at read): a parent cycle renders the "↺"
    marker — distinct from the diamond's already-shown marker — and a root
    re-encountered inside an earlier root's subtree is marked, not re-walked.
    Built directly over a folded kernel state (no store). -/
def treeCycleRenderTests : List Outcome :=
  let stA := (⟨10, 7, 1⟩ : Tl.Crdt.Stamp)
  let stB := (⟨11, 7, 2⟩ : Tl.Crdt.Stamp)
  let stE1 := (⟨12, 7, 3⟩ : Tl.Crdt.Stamp)
  let stE2 := (⟨13, 7, 4⟩ : Tl.Crdt.Stamp)
  let a := "a000000000000000"
  let b := "b000000000000000"
  let mkView (s : State) : View :=
    { dirs := ⟨"", ".tl"⟩
      loaded := { state := s, ops := [], refused := [], skipped := [], deferred := [],
                  maxHlc := 0, maxDeferredHlc := 0, warnings := [], segmentCount := 0 }
      now := 0, replica := none
      rollup := s.effStatusAll, present := s.presentIssues, edges := s.presentEdges, pedges := s.parentEdges
      prov := Tl.Crdt.AMap.empty
      idx := ViewIndex.of s.data s.effStatusAll s.presentIssues s.presentEdges s.parentEdges Tl.Crdt.AMap.empty s.edges.adds.toList }
  -- a 2-cycle: a parent-of b, b parent-of a
  let sCyc := Tl.Kernel.fold [
    Op.create a stA { title := some "A" }, Op.create b stB { title := some "B" },
    Op.edgeAdd (a, b, .Parent) stE1, Op.edgeAdd (b, a, .Parent) stE2]
  let vCyc := mkView sCyc
  let cycOut := String.intercalate "\n" (treeForest Style.plain vCyc [a] (fun _ => true) vCyc.kids)
  -- a shared root: r1 and r2 both roots, r2 also a child of r1
  let r1 := "c000000000000000"
  let r2 := "d000000000000000"
  let sShared := Tl.Kernel.fold [
    Op.create r1 stA { title := some "R1" }, Op.create r2 stB { title := some "R2" },
    Op.edgeAdd (r1, r2, .Parent) stE1]
  let vShared := mkView sShared
  let sharedOut := String.intercalate "\n" (treeForest Style.plain vShared [r1, r2] (fun _ => true) vShared.kids)
  -- the same renderer over the blocks-blocker accessor (`why`'s direction): a
  -- transitive blocker nests under its direct blocker. Chain a → b → c (a blocks
  -- b, b blocks c); `why c`'s roots are c's blockers ([b]), b's blockers ([a]).
  let c := "e000000000000000"
  let stC := (⟨14, 7, 5⟩ : Tl.Crdt.Stamp)
  let stEc1 := (⟨15, 7, 6⟩ : Tl.Crdt.Stamp)
  let stEc2 := (⟨16, 7, 7⟩ : Tl.Crdt.Stamp)
  let sChain := Tl.Kernel.fold [
    Op.create a stA { title := some "A" }, Op.create b stB { title := some "B" },
    Op.create c stC { title := some "C" },
    Op.edgeAdd (a, b, .Blocks) stEc1, Op.edgeAdd (b, c, .Blocks) stEc2]
  let vChain := mkView sChain
  let chainOut := String.intercalate "\n"
    (treeForest Style.plain vChain (vChain.blockers c) (fun _ => true) vChain.blockers)
  [ check "a parent cycle renders the ↺ marker, not the diamond marker"
      (((cycOut.splitOn "↺").length - 1 ≥ 1) && !(cycOut.splitOn "(shown above)").length.blt 0) cycOut,
    check "the cycle marker is distinct from the already-shown marker"
      (!((cycOut.splitOn "(shown above)").length - 1 ≥ 1)) cycOut,
    check "a root already shown in an earlier subtree renders one marked line"
      (((sharedOut.splitOn "(shown above)").length - 1 == 1)
        && ((sharedOut.splitOn "R2").length - 1 == 2)) sharedOut,
    check "the blocker tree nests a transitive blocker under its direct blocker"
      ((chainOut.splitOn "\\-- ").length - 1 == 1) chainOut,
    check "the blocker tree shows both the direct and the transitive blocker"
      (((chainOut.splitOn "A").length - 1 ≥ 1) && ((chainOut.splitOn "B").length - 1 ≥ 1)) chainOut ]

/-- The canonical-parent LWW tie-break: with two surviving parent edges the
    display parent is the one whose greatest add-tag is LWW-greater — on both
    the spec form and the hoisted-view form. -/
def canonicalParentTieTests : List Outcome :=
  let pOld := "e000000000000000"
  let pNew := "f000000000000000"
  let child := "g000000000000000"
  let s := Tl.Kernel.fold [
    Op.create pOld ⟨10, 7, 1⟩ { title := some "old" },
    Op.create pNew ⟨11, 7, 2⟩ { title := some "new" },
    Op.create child ⟨12, 7, 3⟩ { title := some "kid" },
    Op.edgeAdd (pOld, child, .Parent) ⟨20, 7, 4⟩,
    Op.edgeAdd (pNew, child, .Parent) ⟨21, 7, 5⟩]
  let v : View :=
    { dirs := ⟨"", ".tl"⟩
      loaded := { state := s, ops := [], refused := [], skipped := [], deferred := [],
                  maxHlc := 0, maxDeferredHlc := 0, warnings := [], segmentCount := 0 }
      now := 0, replica := none
      rollup := s.effStatusAll, present := s.presentIssues, edges := s.presentEdges, pedges := s.parentEdges
      prov := Tl.Crdt.AMap.empty
      idx := ViewIndex.of s.data s.effStatusAll s.presentIssues s.presentEdges s.parentEdges Tl.Crdt.AMap.empty s.edges.adds.toList }
  -- a parent edge to an absent child (dangling): parentEdges drops it, so the
  -- fast presence-filter must too
  let sDangling := Tl.Kernel.fold [
    Op.create pOld ⟨10, 7, 1⟩ { title := some "p" },
    Op.edgeAdd (pOld, child, .Parent) ⟨20, 7, 4⟩,
    Op.edgeAdd (pOld, "h000000000000000", .Parent) ⟨21, 7, 5⟩]  -- child & h absent
  [ check "canonicalParent picks the LWW-greatest surviving parent edge"
      (canonicalParent s child == some pNew),
    check "canonicalParentE agrees with the spec form"
      (canonicalParentE v child == canonicalParent s child),
    -- the loadView optimization: parentEdgesFast = State.parentEdges (same list),
    -- so v.pedges stays exactly the spec list every kernel function expects
    check "parentEdgesFast = parentEdges (present children)"
      (parentEdgesFast s == s.parentEdges),
    check "parentEdgesFast = parentEdges (drops dangling-child edges)"
      (parentEdgesFast sDangling == sDangling.parentEdges
        && sDangling.parentEdges.isEmpty) ]

/-- The indexed-view row accessors (ADR-0024) equal — pointwise, on every present
    issue — the spec accessors they replace, over a folded state exercising an
    epic, a done child, a blocked issue, a deferred issue, a multi-parent child,
    and a `duplicate-of`. The per-issue bridges are proved in the kernel
    (`issueDataH_eq`/`isReadyFastH_eq`/`blocksByTarget_eq`/…); this is the
    shell-tier pin that the CLI's `View` helpers compose them faithfully (the
    per-row Θ(N²)/Θ(N·E) → O(N) routing of `issueRow`/`issueObj`/`styledLine`/
    `list`/`stats`/`doctor`). -/
def rowAccessorAgreementTests : List Outcome :=
  let st (n : Nat) : Tl.Crdt.Stamp := ⟨n, 7, n⟩
  let a := "a000000000000000"; let b := "b000000000000000"; let c := "c000000000000000"
  let d := "d000000000000000"; let e := "e000000000000000"; let f := "f000000000000000"
  let g := "g000000000000000"; let h := "h000000000000000"
  let now := 1000000
  let s := Tl.Kernel.fold [
    Op.create a (st 1) { title := some "epic A" },
    Op.create b (st 2) { title := some "B" },
    Op.create c (st 3) { title := some "C" },
    Op.create d (st 4) { title := some "D" },
    Op.create e (st 5) { title := some "E" },
    Op.create f (st 6) { title := some "F" },
    Op.create g (st 7) { title := some "epic G" },
    Op.create h (st 8) { title := some "H" },
    Op.edgeAdd (a, b, .Parent) (st 9),
    Op.edgeAdd (a, c, .Parent) (st 10),
    Op.edgeAdd (a, f, .Parent) (st 11),
    Op.edgeAdd (g, f, .Parent) (st 12),       -- f is multi-parent (a and g)
    Op.edgeAdd (b, d, .Blocks) (st 13),       -- b blocks d (b open ⇒ d blocked)
    Op.setFields c (st 14) { status := some .Done },
    Op.setFields e (st 15) { deferUntil := some (some 2000000) },  -- 2000000 > now ⇒ deferred
    Op.metaSet h (st 16) "duplicate-of" (some a)]
  let rollup := s.effStatusAll
  let edges := s.presentEdges
  let pedges := s.parentEdges
  -- a non-empty prov so `v.provFor` (reads the provH hash copy) is checked
  -- against `provOf` (reads the AMap) on populated entries, not a vacuous
  -- both-default-{} match: `a` carries created/updated/close, `d` a claim.
  let prov : Tl.Crdt.AMap IssueId Prov :=
    (Tl.Crdt.AMap.empty.insert a
        { created := some (⟨100, 7, 5⟩, some "alice"), updated := some ⟨200, 7, 6⟩,
          lastClose := some ⟨300, 7, 7⟩ }).insert d
        { created := some (⟨150, 8, 9⟩, some "bob"), lastClaim := some ⟨400, 8, 10⟩ }
  let v : View :=
    { dirs := ⟨"", ".tl"⟩
      loaded := { state := s, ops := [], refused := [], skipped := [], deferred := [],
                  maxHlc := 0, maxDeferredHlc := 0, warnings := [], segmentCount := 0 }
      now, replica := none
      rollup, present := s.presentIssues, edges, pedges, prov
      idx := ViewIndex.of s.data rollup s.presentIssues edges pedges prov s.edges.adds.toList }
  s.presentIssues.map (fun i =>
    let dh := v.issueData i
    let ds := s.issueData i
    let pa := v.provFor i
    let pb := provOf prov i
    check s!"row accessors ≡ spec for {i}"
      (  (dh.statusOf == ds.statusOf)
      && (dh.priorityOf == ds.priorityOf)
      && (dh.deferUntilOf == ds.deferUntilOf)
      && (dh.title.value == ds.title.value)
      && (v.effStatus i == State.effStatusWith rollup s i)
      && (v.effClosed i == State.effClosedWith rollup s i)
      && (v.isEpic i == !(State.kidsOfEdges pedges i).isEmpty)
      && (v.kids i == State.kidsOfEdges pedges i)
      && (v.ready i == State.isReadyFast rollup edges pedges s now i)
      && (v.blocked i == blockedOf rollup edges s i)
      && (v.deferred i == deferredOf s now i)
      && (v.blockers i == State.blockersOfE edges i)
      && (v.dependents i == State.dependentsOfE edges i)
      && (v.has i == decide (s.hasIssue i))
      && (v.duplicateOf i == duplicateOf s i)
      && (canonicalParentE v i == canonicalParent s i)
      && (pa.createdAt == pb.createdAt && pa.updatedAt == pb.updatedAt
          && pa.closedAt == pb.closedAt && pa.claimedAt == pb.claimedAt
          && pa.createdBy == pb.createdBy && pa.createdReplica == pb.createdReplica)))

/-- The default `--limit` is 50 (was 10) for `ready` and `list`: 11 plain issues
    — all open, unblocked, top-level — must all show with no explicit flag. Under
    the old default of 10 the items array would cap at 10; the literal 50 lives in
    `Tl/Cli/Main.lean`. `count` always reports the true total. -/
def cliDefaultLimitTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  for k in [0:11] do
    let _ ← mkIssue dir s!"issue {k}"
  o := o ++ [← expectData "ready default limit shows all 11 (>10)" ["ready", "--dir", dir]
    (fun j => jNat j "count" == some 11 && (jArr j "items").length == 11)]
  o := o ++ [← expectData "list default limit shows all 11 (>10)" ["list", "--dir", dir]
    (fun j => jNat j "count" == some 11 && (jArr j "items").length == 11)]
  -- the tree view caps rendered rows, not roots: one epic + 6 children is 7 rows
  -- under a single root, so `--limit 3` shows 3 rows + a truncation footer — not
  -- the whole subtree (which the old root-capping would have rendered in full).
  let dirT ← freshDir
  let epic ← mkIssue dirT "Epic root"
  for k in [0:6] do
    let _ ← mkIssue dirT s!"kid {k}" ["--parent", "tl-" ++ epic]
  match ← run' ["list", "--dir", dirT, "--limit", "3"] with
  | .ok out =>
    let plain := (out.render.map (· Style.plain)).getD out.human
    o := o ++
      [check "tree --limit caps rows and discloses truncation"
         ((plain.splitOn "Showing 3 of 7").length > 1) plain,
       check "tree --limit renders exactly the capped rows (epic + 2 kids)"
         ((plain.splitOn "kid ").length == 3) plain]
  | .error e => o := o ++ [{ name := "tree limit rows", passed := false, msg := e.message }]
  return o

/-- Short display ids (ADR-0017/0018): human one-line rows render `tl-` + the
    shortest prefix unambiguous over the present set (floor `shortIdFloor`), JSON
    keeps the full id, and a rendered short id resolves as a command argument. -/
def cliShortIdTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- the pure prefix-length algorithm: floor honored, collisions extend, and
  -- every emitted prefix is unique over the set (so it resolves)
  let ids := ["aaaa0zzz", "aaaa1zzz", "bcde0000"]
  let lens := shortIdLens ids
  let prefixOf := fun (i : IssueId) => String.ofList (i.toList.take ((lens[i]?).getD i.length))
  o := o ++
    [check "shortIdLens floors a lone-prefix id at shortIdFloor"
       ((lens["bcde0000"]?).getD 0 == shortIdFloor) s!"got {(lens["bcde0000"]?).getD 0}",
     check "shortIdLens extends past the floor on a shared prefix"
       ((lens["aaaa0zzz"]?).getD 0 == 5 && (lens["aaaa1zzz"]?).getD 0 == 5)
       s!"a0={(lens["aaaa0zzz"]?).getD 0} a1={(lens["aaaa1zzz"]?).getD 0}",
     check "every shortIdLens prefix is unambiguous over the set"
       (ids.all (fun i => (ids.filter (·.startsWith (prefixOf i))).length == 1)) "a prefix matched >1 id"]
  -- a single-issue repo: the human row drops the full id for the floor-length
  -- prefix, and that prefix resolves back to the full id
  let dir ← freshDir
  let a ← mkIssue dir "Solo issue"
  let floorPref := "tl-" ++ String.ofList (a.toList.take shortIdFloor)
  match ← run' ["list", "--dir", dir] with
  | .ok out =>
    let plain := (out.render.map (· Style.plain)).getD out.human
    o := o ++
      [check "human list omits the full id (shortened)" ((plain.splitOn ("tl-" ++ a)).length == 1) plain,
       check "human list shows the floor-length prefix" ((plain.splitOn floorPref).length > 1) plain]
  | .error e => o := o ++ [{ name := "short id list render", passed := false, msg := e.message }]
  o := o ++ [← expectData "a rendered short id resolves as a command arg"
    ["show", floorPref, "--dir", dir] (fun j => jStr j "id" == some ("tl-" ++ a))]
  o := o ++ [← expectData "--json keeps the full id" ["list", "--dir", dir]
    (fun j => (jArr j "items").any (fun it => jStr it "id" == some ("tl-" ++ a)))]
  return o

/-- Sync posture (ADR-0011 §2): `doctor` owns a local-only sync row (upstream /
    lastSync / ahead, no remote contact), and `ready` shows a staleness advisory
    when behind/never-synced. `--sync` (= sync-then-run) reconciles first and
    suppresses the advisory. No remote is contacted except by an explicit sync. -/
def cliSyncPostureTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let syncRow := fun (out : CmdOut) => (jArr out.data "checks").find? (fun c => jStr c "name" == some "sync")
  -- (1) outside a git repo / no remote: doctor sync row = no-upstream, ready clean
  let dir ← freshDir
  let _ ← mkIssue dir "Solo task"
  match ← run' ["doctor", "--dir", dir] with
  | .ok out =>
    o := o ++
      [check "doctor has a sync row" (syncRow out).isSome "no sync row",
       check "no remote ⇒ upstream null" ((syncRow out).bind (fun c => jGet c "upstream") == some Json.null)
         (toString ((syncRow out).map (·.compress)))]
  | .error e => o := o ++ [{ name := "doctor sync row (no remote)", passed := false, msg := e.message }]
  o := o ++ [← expectData "ready: no advisory without a remote" ["ready", "--dir", dir]
    (fun j => jGet j "staleness" == some Json.null)]
  -- (2) a git repo with a bare remote, never synced
  let root ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] }
  let tldir := (root / ".tl").toString
  let _ ← run' ["init", "--dir", tldir]
  let bare ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", bare.toString, "init", "-q", "--bare"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "remote", "add", "origin", bare.toString] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "config", "protocol.file.allow", "always"] }
  let _ ← run' ["create", "Remote task", "--dir", tldir, "--actor", "t"]
  match ← run' ["doctor", "--dir", tldir] with
  | .ok out =>
    o := o ++
      [check "doctor: upstream resolves to origin" ((syncRow out).bind (jStr · "upstream") == some "origin")
         (toString ((syncRow out).map (·.compress))),
       check "doctor: never-synced warns" ((syncRow out).bind (jStr · "status") == some "warn") "",
       check "doctor: lastSync null before any sync" ((syncRow out).bind (fun c => jGet c "lastSync") == some Json.null) ""]
  | .error e => o := o ++ [{ name := "doctor sync row (remote)", passed := false, msg := e.message }]
  o := o ++ [← expectData "ready: never-synced advisory" ["ready", "--dir", tldir]
    (fun j => match jStr j "staleness" with | some s => (s.splitOn "never synced").length > 1 | none => false)]
  -- (3) after a sync: lastSync recorded, ahead 0, doctor ok, ready clean.
  -- A recording sink pins the progress-notice wiring (`syncProgressSink`):
  -- the sync fires it exactly once with the resolved remote name.
  let fired ← IO.mkRef ([] : List String)
  syncProgressSink.set (fun rm => fired.modify (· ++ [rm]))
  let _ ← run' ["sync", "--dir", tldir]
  o := o ++ [check "sync fires the progress sink once with the resolved remote"
    ((← fired.get) == ["origin"]) (String.intercalate "," (← fired.get))]
  -- a local-only sync (no git repo ⇒ no remote resolves) must not fire the sink
  fired.set []
  let _ ← run' ["sync", "--dir", dir]
  o := o ++ [check "a local-only sync does not fire the progress sink"
    ((← fired.get).isEmpty) (String.intercalate "," (← fired.get))]
  syncProgressSink.set (fun _ => pure ())  -- restore the suite's silent sink
  match ← run' ["doctor", "--dir", tldir] with
  | .ok out =>
    o := o ++
      [check "doctor: lastSync set after sync" ((syncRow out).bind (jStr · "lastSync")).isSome "",
       check "doctor: ahead 0 right after sync" ((syncRow out).bind (jNat · "ahead") == some 0) out.data.compress,
       check "doctor: ok after sync" ((syncRow out).bind (jStr · "status") == some "ok") ""]
  | .error e => o := o ++ [{ name := "doctor sync row (post-sync)", passed := false, msg := e.message }]
  o := o ++ [← expectData "ready: advisory cleared after sync" ["ready", "--dir", tldir]
    (fun j => jGet j "staleness" == some Json.null)]
  -- (3b) a local write after sync ⇒ segment-based ahead > 0 (the main-repo fix:
  -- writes don't advance refs/tl/log, so a commit-count would read a false 0)
  let _ ← mkIssue tldir "Written after sync"
  match ← run' ["doctor", "--dir", tldir] with
  | .ok out =>
    o := o ++
      [check "doctor: ahead counts unsynced local ops" (((syncRow out).bind (jNat · "ahead")).getD 0 > 0) out.data.compress,
       check "doctor: warns on unsynced ops" ((syncRow out).bind (jStr · "status") == some "warn") "",
       check "doctor: no degenerate behind field" ((syncRow out).bind (fun c => jGet c "behind")).isNone ""]
  | .error e => o := o ++ [{ name := "doctor ahead>0", passed := false, msg := e.message }]
  o := o ++ [← expectData "ready: unsynced-ops advisory" ["ready", "--dir", tldir]
    (fun j => match jStr j "staleness" with | some s => (s.splitOn "local change").length > 1 | none => false)]
  -- (4) stale-by-time: re-sync (ahead→0), then age the marker keeping the real
  -- tip, so the time branch (not the ahead branch) drives the advisory
  let _ ← run' ["sync", "--dir", tldir]
  let tipOut ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "rev-parse", "refs/tl/log"] }
  IO.FS.writeFile (root / ".tl" / "local" / "last-sync") s!"1000 {tipOut.stdout.trimAscii.toString}\n"
  o := o ++ [← expectData "ready: stale-by-time advisory" ["ready", "--dir", tldir]
    (fun j => match jStr j "staleness" with | some s => (s.splitOn "ago").length > 1 | none => false)]
  -- (5) --sync reconciles first: advisory suppressed, doctor reports the reconcile
  o := o ++ [← expectData "ready --sync suppresses the advisory" ["ready", "--dir", tldir, "--sync"]
    (fun j => jGet j "staleness" == some Json.null)]
  match ← run' ["doctor", "--dir", tldir, "--sync"] with
  | .ok out =>
    o := o ++
      [check "doctor --sync refreshes lastSync" ((syncRow out).bind (jStr · "lastSync")).isSome "",
       check "doctor --sync reports the reconcile result" ((syncRow out).bind (jBool · "reconciled") == some true) out.data.compress,
       check "doctor --sync names the reconcile" (((((syncRow out).bind (jStr · "message")).getD "").splitOn "reconciled").length > 1) ""]
  | .error e => o := o ++ [{ name := "doctor --sync", passed := false, msg := e.message }]
  return o

/-- claim freshness (ADR-0001 §5): `--sync` reconciles around the take (fetch,
    claim, push), `--verify` re-checks against the freshest reachable state first
    (warn-and-degrade with no remote). Both keep the not-claimable guard. -/
def cliClaimSyncTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- git repo + bare remote + a ready issue
  let root ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] }
  let tldir := (root / ".tl").toString
  let _ ← run' ["init", "--dir", tldir]
  let bare ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", bare.toString, "init", "-q", "--bare"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "remote", "add", "origin", bare.toString] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "config", "protocol.file.allow", "always"] }
  let a ← mkIssue tldir "Claimable"
  match ← run' ["claim", "tl-" ++ a, "--dir", tldir, "--sync", "--actor", "ann"] with
  | .ok out =>
    o := o ++ [check "claim --sync wins the take"
                 ((jGet out.data "claim").bind (jStr · "outcome") == some "won") out.data.compress]
  | .error e => o := o ++ [{ name := "claim --sync", passed := false, msg := e.message }]
  let ls ← IO.Process.output { cmd := "git", args := #["-c", "protocol.file.allow=always", "ls-remote", bare.toString, "refs/tl/log"] }
  o := o ++ [check "claim --sync published to the remote" (!ls.stdout.trimAscii.isEmpty) ls.stdout]
  -- --verify with no remote: succeeds and warns it degraded to local
  let dir ← freshDir
  let b ← mkIssue dir "Local claimable"
  match ← run' ["claim", "tl-" ++ b, "--dir", dir, "--verify", "--actor", "ann"] with
  | .ok out =>
    o := o ++
      [check "claim --verify succeeds with no remote"
         ((jGet out.data "claim").bind (jStr · "outcome") == some "won") out.data.compress,
       check "claim --verify warns it could not verify against a remote"
         (out.notes.any (fun n => (n.splitOn "verified against local state only").length > 1)) (toString out.notes)]
  | .error e => o := o ++ [{ name := "claim --verify (no remote)", passed := false, msg := e.message }]
  -- the not-claimable guard still holds through the sync path
  let c ← mkIssue dir "a blocker"
  let blk ← mkIssue dir "blocked one" ["--blocked-by", "tl-" ++ c]
  o := o ++ [← expectErr "claim --sync still refuses a non-ready item"
    ["claim", "tl-" ++ blk, "--dir", dir, "--sync", "--actor", "ann"] .notClaimable]
  return o

/-- Two clones over a bare remote: a sync that pulls a new replica from the
    remote reports it in `absorbed` (the post-remote second local leg), and
    `doctor`'s refMark check warns when a materialized foreign segment is deleted
    on disk while the ref-mark stays put. -/
def cliSyncTwoCloneTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let refMarkRow := fun (out : CmdOut) => (jArr out.data "checks").find? (fun c => jStr c "name" == some "refMark")
  let mkClone : IO String := do
    let root ← IO.FS.createTempDir
    let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] }
    pure root.toString
  let bare ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", bare.toString, "init", "-q", "--bare"] }
  -- clone A: create an issue and push it
  let rootA ← mkClone
  let tlA := rootA ++ "/.tl"
  let _ ← run' ["init", "--dir", tlA]
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootA, "remote", "add", "origin", bare.toString] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootA, "config", "protocol.file.allow", "always"] }
  let _ ← mkIssue tlA "From clone A"
  let _ ← run' ["sync", "--dir", tlA]
  -- clone B: a sync pulls A's replica from the remote
  let rootB ← mkClone
  let tlB := rootB ++ "/.tl"
  let _ ← run' ["init", "--dir", tlB]
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootB, "remote", "add", "origin", bare.toString] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootB, "config", "protocol.file.allow", "always"] }
  let mut absorbedRep := ""
  match ← run' ["sync", "--dir", tlB] with
  | .ok out =>
    let absorbed := jArr ((jGet out.data "local").getD Json.null) "absorbed"
    absorbedRep := (absorbed.head?.bind (·.getStr?.toOption)).getD ""
    o := o ++ [check "sync reports a remote-pulled replica in absorbed (not [])" (!absorbed.isEmpty) out.data.compress]
  | .error e => o := o ++ [{ name := "B sync absorb", passed := false, msg := e.message }]
  -- doctor refMark: ok while disk matches, warn after the foreign segment is deleted
  match ← run' ["doctor", "--dir", tlB] with
  | .ok out => o := o ++ [check "doctor refMark ok when on-disk matches the marker"
      ((refMarkRow out).bind (jStr · "status") == some "ok") out.data.compress]
  | .error e => o := o ++ [{ name := "refMark ok", passed := false, msg := e.message }]
  if absorbedRep != "" then
    IO.FS.removeFile (rootB ++ "/.tl/log/" ++ absorbedRep ++ ".jsonl")
    match ← run' ["doctor", "--dir", tlB] with
    | .ok out => o := o ++ [check "doctor refMark warns when a marked foreign segment is gone on disk"
        ((refMarkRow out).bind (jStr · "status") == some "warn") out.data.compress]
    | .error e => o := o ++ [{ name := "refMark warn", passed := false, msg := e.message }]
  return o

/-- An unreachable (configured-but-broken) remote: read `--sync` degrades and
    never fails, `doctor --sync` never fails, `claim --sync` records the take and
    discloses, but `claim --verify` fails with `verify-failed` (the strict gate). -/
def cliSyncDegradeTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let syncRow := fun (out : CmdOut) => (jArr out.data "checks").find? (fun c => jStr c "name" == some "sync")
  let root ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] }
  let dir := (root / ".tl").toString
  let _ ← run' ["init", "--dir", dir]
  -- a configured remote whose URL is not a git repo ⇒ fetch/push error (not a hang)
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "remote", "add", "origin", "/no/such/tl/remote"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "config", "protocol.file.allow", "always"] }
  let _ ← mkIssue dir "Workable"
  match ← run' ["ready", "--dir", dir, "--sync"] with
  | .ok out => o := o ++
      [check "ready --sync degrades (no failure) on an unreachable remote"
         (out.notes.any (fun n => (n.splitOn "could not reconcile").length > 1)) (toString out.notes),
       check "ready --sync still reports staleness when the sync failed"
         (jStr out.data "staleness").isSome out.data.compress]
  | .error e => o := o ++ [{ name := "ready --sync degrade", passed := false, msg := s!"failed instead of degrading: {e.message}" }]
  match ← run' ["doctor", "--dir", dir, "--sync"] with
  | .ok out => o := o ++
      [check "doctor --sync never fails on an unreachable remote" ((syncRow out).isSome) "",
       check "doctor --sync warns + discloses the reconcile failure"
         ((syncRow out).bind (jStr · "status") == some "warn"
          && ((((syncRow out).bind (jStr · "message")).getD "").splitOn "failed").length > 1) out.data.compress]
  | .error e => o := o ++ [{ name := "doctor --sync degrade", passed := false, msg := s!"failed: {e.message}" }]
  let vid ← mkIssue dir "verify target"
  o := o ++ [← expectErr "claim --verify fails verify-failed on an unreachable remote"
    ["claim", "tl-" ++ vid, "--dir", dir, "--verify", "--actor", "t"] .verifyFailed]
  let sid ← mkIssue dir "sync target"
  match ← run' ["claim", "tl-" ++ sid, "--dir", dir, "--sync", "--actor", "t"] with
  | .ok out => o := o ++
      [check "claim --sync still records the take on an unreachable remote"
         ((jGet out.data "claim").bind (jStr · "outcome") == some "won") out.data.compress,
       check "claim --sync discloses the reconcile/publish failure"
         (out.notes.any (fun n => (n.splitOn "could not").length > 1)) (toString out.notes)]
  | .error e => o := o ++ [{ name := "claim --sync degrade", passed := false, msg := s!"failed instead of degrading: {e.message}" }]
  return o

/-- A push rejected (a pre-receive hook) after the local CAS advanced the ref
    self-heals — the failed sync left the local ref ahead, and a later sync (hook
    removed) recovers and converges the remote. Plus: a remote-leg timeout
    surfaces as a clear error, never misclassified as a push-rejected race. -/
def cliSyncRecoveryTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let bare ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", bare.toString, "init", "-q", "--bare"] }
  let hook := (bare / "hooks" / "pre-receive").toString
  IO.FS.writeFile hook "#!/bin/sh\nexit 1\n"
  let _ ← IO.Process.output { cmd := "chmod", args := #["+x", hook] }
  -- pin the receiving repo's hooks dir in its own config: a developer's global
  -- `core.hooksPath` would otherwise send receive-pack elsewhere, the decline
  -- would never fire, and the rejection this row exists to test would not happen
  let hooksDir := (bare / "hooks").toString
  let _ ← IO.Process.output { cmd := "git", args := #["-C", bare.toString, "config", "core.hooksPath", hooksDir] }
  let root ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] }
  let dir := (root / ".tl").toString
  let _ ← run' ["init", "--dir", dir]
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "remote", "add", "origin", bare.toString] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "config", "protocol.file.allow", "always"] }
  let _ ← mkIssue dir "Recover me"
  match ← run' ["sync", "--dir", dir] with
  | .error _ =>
    let lt ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "rev-parse", "refs/tl/log"] }
    o := o ++ [check "a hook-rejected push fails the sync but the local ref still advanced"
      (!lt.stdout.trimAscii.isEmpty) lt.stdout]
  | .ok out => o := o ++ [{ name := "hook-rejected sync should fail", passed := false, msg := out.data.compress }]
  IO.FS.removeFile hook
  match ← run' ["sync", "--dir", dir] with
  | .ok _ =>
    let ls ← IO.Process.output { cmd := "git", args := #["-c", "protocol.file.allow=always", "ls-remote", bare.toString, "refs/tl/log"] }
    o := o ++ [check "the next sync recovers and converges the remote" (!ls.stdout.trimAscii.isEmpty) ls.stdout]
  | .error e => o := o ++ [{ name := "sync recovery", passed := false, msg := e.message }]
  -- G-adjacent: a remote timeout surfaces as a clear error, not a misclassified
  -- race. A fresh repo with the 1ms remote timeout set before its first git call
  -- (the timeout is memoized per repo per process — fine for the one-shot CLI).
  let root2 ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root2.toString, "init", "-q"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root2.toString, "config", "tl.gitRemoteTimeoutMs", "1"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root2.toString, "remote", "add", "origin", bare.toString] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", root2.toString, "config", "protocol.file.allow", "always"] }
  let dir2 := (root2 / ".tl").toString
  let _ ← run' ["init", "--dir", dir2]
  let _ ← mkIssue dir2 "timeout target"
  match ← run' ["sync", "--dir", dir2] with
  | .error e => o := o ++ [check "a remote timeout is a clear error, not a misclassified race"
      (e.code != .pushRejected) s!"got {e.code.wire}: {e.message}"]
  | .ok _ => o := o ++ [{ name := "remote timeout should error", passed := false, msg := "succeeded under a 1ms remote timeout" }]
  return o

/-- Posture must not falsely report "clean": (A) sync an empty repo with a remote
    then create a task — the unsynced op shows as ahead>0 / a staleness advisory;
    (B) a local-only sync (no remote) does not record lastSync, so after a remote
    is added the view reads "never synced", not clean. -/
def cliSyncFalseCleanTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let syncRow := fun (out : CmdOut) => (jArr out.data "checks").find? (fun c => jStr c "name" == some "sync")
  let bare ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", bare.toString, "init", "-q", "--bare"] }
  -- (A) sync an empty repo (with a remote), then create the first task
  let rootA ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootA.toString, "init", "-q"] }
  let dirA := (rootA / ".tl").toString
  let _ ← run' ["init", "--dir", dirA]
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootA.toString, "remote", "add", "origin", bare.toString] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootA.toString, "config", "protocol.file.allow", "always"] }
  let _ ← run' ["sync", "--dir", dirA]
  let _ ← mkIssue dirA "First task after an empty sync"
  match ← run' ["doctor", "--dir", dirA] with
  | .ok out => o := o ++
      [check "empty-sync-then-create: ahead counts the unsynced op"
         (((syncRow out).bind (jNat · "ahead")).getD 0 > 0) out.data.compress,
       check "empty-sync-then-create: the row warns (not falsely ok)"
         ((syncRow out).bind (jStr · "status") == some "warn") ""]
  | .error e => o := o ++ [{ name := "false-clean A doctor", passed := false, msg := e.message }]
  o := o ++ [← expectData "empty-sync-then-create: ready advises staleness" ["ready", "--dir", dirA]
    (fun j => (jStr j "staleness").isSome)]
  -- (B) a local-only sync (no remote), then a remote is added
  let rootB ← IO.FS.createTempDir
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootB.toString, "init", "-q"] }
  let dirB := (rootB / ".tl").toString
  let _ ← run' ["init", "--dir", dirB]
  let _ ← mkIssue dirB "Task before any remote"
  let _ ← run' ["sync", "--dir", dirB]
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootB.toString, "remote", "add", "origin", bare.toString] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", rootB.toString, "config", "protocol.file.allow", "always"] }
  match ← run' ["doctor", "--dir", dirB] with
  | .ok out => o := o ++ [check "local-only sync then add-remote: the row is not falsely ok"
      ((syncRow out).bind (jStr · "status") == some "warn") out.data.compress]
  | .error e => o := o ++ [{ name := "false-clean B doctor", passed := false, msg := e.message }]
  o := o ++ [← expectData "local-only sync then add-remote: ready advises 'never synced'" ["ready", "--dir", dirB]
    (fun j => match jStr j "staleness" with | some s => (s.splitOn "never synced").length > 1 | none => false)]
  return o

/-- The doctor `gitRouting` split-brain row (ADR-0012 / ADR-0014 T7): the
    pure-core branches (ok / inherited-vars warn / toplevel-mismatch warn /
    both / non-repo ok — none fails health), and the end-to-end row against
    real repos in both the aligned and the `--dir`-into-a-subdir shapes. The
    inherited-variable condition itself needs a process boundary and lives
    with the spawned-binary rows (`cliGitEnvTests`). -/
def cliDoctorRoutingTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- pure-core branches
  let rw : RemoteRewrite :=
    { remote := "origin", configured := "/real.git", effective := "/decoy.git" }
  let ext : List ExternalPushConfig :=
    [{ key := "tl.remote", value := "evil" }, { key := "remote.evil.url", value := "/decoy.git" }]
  let okRow := gitRoutingRow [] "/repo" (some "/repo") none []
  -- use only repo-rerouting vars, as production does (cmdDoctor filters to
  -- repoRoutingVars) — passing a config-relocation var here would test a state
  -- production cannot construct and mask the routingVars/repoRoutingVars split
  let varsRow := gitRoutingRow ["GIT_DIR", "GIT_WORK_TREE"] "/repo" (some "/repo") none []
  let misRow := gitRoutingRow [] "/repo/sub" (some "/repo") none []
  let bothRow := gitRoutingRow ["GIT_DIR"] "/repo/sub" (some "/repo") none []
  let noRepoRow := gitRoutingRow [] "/somewhere" none none []
  let rwRow := gitRoutingRow [] "/repo" (some "/repo") (some rw) []
  let extRow := gitRoutingRow [] "/repo" (some "/repo") none ext
  let status := fun (r : Json × Bool) => (jStr r.1 "status").getD "?"
  let msg := fun (r : Json × Bool) => (jStr r.1 "message").getD ""
  let nullAt := fun (j : Json) (k : String) =>
    match jGet j k with | some .null => true | _ => false
  o := o ++
    [check "gitRouting: aligned repo is ok" (status okRow == "ok") (msg okRow),
     check "gitRouting: inherited repo-routing vars warn and name themselves"
       (status varsRow == "warn" && (msg varsRow |>.splitOn "GIT_WORK_TREE").length > 1
         && (msg varsRow |>.splitOn "tl ignores it").length > 1) (msg varsRow),
     check "gitRouting: toplevel mismatch warns and teaches placement"
       (status misRow == "warn" && (msg misRow |>.splitOn "toplevel").length > 1) (msg misRow),
     check "gitRouting: both conditions compose into one message"
       (status bothRow == "warn" && (msg bothRow |>.splitOn "tl ignores it").length > 1
         && (msg bothRow |>.splitOn "toplevel").length > 1) (msg bothRow),
     check "gitRouting: outside a repo is ok (null toplevel)"
       (status noRepoRow == "ok" && nullAt noRepoRow.1 "repoToplevel") "",
     -- the carried residual (ADR-0012 / ADR-0014 T7): an insteadOf rewrite
     -- really does redirect the push, so the row must name both URLs
     check "gitRouting: an insteadOf remote rewrite warns and names both URLs"
       (status rwRow == "warn" && (msg rwRow |>.splitOn "/real.git").length > 1
         && (msg rwRow |>.splitOn "/decoy.git").length > 1
         && (msg rwRow |>.splitOn "insteadOf").length > 1) (msg rwRow),
     check "gitRouting: no rewrite reports remoteRewrite null"
       (nullAt okRow.1 "remoteRewrite") "",
     -- the direct-injection face: push-destination keys sourced from global
     check "gitRouting: global-sourced push config warns and names the keys"
       (status extRow == "warn" && (msg extRow |>.splitOn "tl.remote=evil").length > 1
         && (msg extRow |>.splitOn "~/.gitconfig").length > 1) (msg extRow),
     check "gitRouting: no external config reports an empty externalPushConfig"
       ((jArr okRow.1 "externalPushConfig").isEmpty) "",
     check "gitRouting: no branch fails health"
       (!okRow.2 && !varsRow.2 && !misRow.2 && !bothRow.2 && !noRepoRow.2
         && !rwRow.2 && !extRow.2) ""]
  -- end-to-end: aligned (init at a repo toplevel) → ok with the real toplevel
  let findCheck (data : Json) (nm : String) : Option Json :=
    (jArr data "checks").find? (fun c => jStr c "name" == some nm)
  let root ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] } : IO _)
  let dir := (root / ".tl").toString
  let _ ← run' ["init", "--dir", dir]
  let realRoot ← IO.FS.realPath root
  o := o ++ [← expectData "doctor gitRouting: aligned repo reports ok"
    ["doctor", "--json", "--dir", dir]
    (fun j => (findCheck j "gitRouting").any (fun c =>
      jStr c "status" == some "ok" && jStr c "repoToplevel" == some realRoot.toString))]
  -- end-to-end: state dir in a repo subdir → warn (split placement disclosed)
  IO.FS.createDirAll (root / "sub")
  let subDir := (root / "sub" / ".tl").toString
  let _ ← run' ["init", "--dir", subDir]
  o := o ++ [← expectData "doctor gitRouting: subdir state warns on the toplevel mismatch"
    ["doctor", "--json", "--dir", subDir]
    (fun j => (findCheck j "gitRouting").any (fun c =>
      jStr c "status" == some "warn" && jBool j "healthy" == some true))]
  -- the mismatch message names the actual state directory, not a hard-coded
  -- `.tl` (custom-named --dir): "move .tl to the toplevel" would misdirect
  o := o ++ [← expectData "doctor gitRouting: mismatch message names the real state dir, not `.tl`"
    ["doctor", "--json", "--dir", subDir]
    (fun j => (findCheck j "gitRouting").any (fun c =>
      match jStr c "message" with
      | some m => (m.splitOn "state directory").length > 1 && (m.splitOn "move .tl").length == 1
      | none => false))]
  -- end-to-end: non-git state → ok, null toplevel
  let plain ← freshDir
  o := o ++ [← expectData "doctor gitRouting: non-git state is ok with null toplevel"
    ["doctor", "--json", "--dir", plain]
    (fun j => (findCheck j "gitRouting").any (fun c =>
      jStr c "status" == some "ok" && nullAt c "repoToplevel"))]
  return o

/-- `doctor`'s staleClaims check is driven entirely by the `tl.staleAfter` git
    config (a compact duration) — there is no hardcoded default. Unset ⇒ the row
    is omitted; a set window flags in-progress claims older than it; an
    unparseable value teaches the format. -/
def cliDoctorStaleTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let findCheck (data : Json) (nm : String) : Option Json :=
    (jArr data "checks").find? (fun c => jStr c "name" == some nm)
  -- (1) unset ⇒ no staleClaims row at all (freshDir is not a git repo, so the
  --     config is unset) — the headline of removing the hardcoded default
  let bare ← freshDir
  let _ ← mkIssue bare "open work"
  o := o ++ [← expectData "doctor omits staleClaims when tl.staleAfter is unset"
    ["doctor", "--json", "--dir", bare]
    (fun j => (findCheck j "staleClaims").isNone)]
  -- a git-backed project so `tl.staleAfter` is readable; inject a foreign
  -- create+claim both ~2h in the past (the claim must out-stamp its own create
  -- to leave the issue InProgress, so both are dated old)
  let root ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] } : IO _)
  let dir := (root / ".tl").toString
  let _ ← run' ["init", "--dir", dir]
  IO.FS.createDirAll (System.FilePath.mk dir / "log")
  let base := (← nowMs) - 2 * 3600 * 1000   -- 2h ago, in ms
  let issueId := "aaaabbbbccccdddd"
  IO.FS.writeFile (System.FilePath.mk dir / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create issueId { title := some "claimed long ago" }) (base * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 1 ++ "\n"
     ++ foreignLine (.claim issueId "eve") ((base + 1000) * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 2 ++ "\n")
  -- (2) window 1h ⇒ the 2h-old claim is stale; row carries window + count + ids and
  --     an actionable next-step naming `claim --steal` (ADR-0013; the signal no
  --     longer dead-ends)
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "config", "tl.staleAfter", "1h"] } : IO _)
  o := o ++ [← expectData "doctor flags a claim older than tl.staleAfter, naming the window and the --steal fix"
    ["doctor", "--json", "--dir", dir]
    (fun j => match findCheck j "staleClaims" with
      | some c => jStr c "status" == some "warn" && jNat c "count" == some 1
          && jStr c "window" == some "1h"
          && (jArr c "ids").any (fun x => x.getStr?.toOption == some ("tl-" ++ issueId))
          && (((jStr c "message").getD "").splitOn "--steal").length == 2
      | none => false)]
  -- (3) window 3h ⇒ the same 2h-old claim is within the window (ok, count 0)
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "config", "tl.staleAfter", "3h"] } : IO _)
  o := o ++ [← expectData "a claim younger than the window is not stale"
    ["doctor", "--json", "--dir", dir]
    (fun j => match findCheck j "staleClaims" with
      | some c => jStr c "status" == some "ok" && jNat c "count" == some 0
      | none => false)]
  -- (4) an unparseable tl.staleAfter ⇒ a row that teaches the format
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "config", "tl.staleAfter", "soon"] } : IO _)
  o := o ++ [← expectData "an invalid tl.staleAfter yields a teaching row"
    ["doctor", "--json", "--dir", dir]
    (fun j => match findCheck j "staleClaims" with
      | some c => jStr c "status" == some "warn"
          && (((jStr c "message").getD "").splitOn "valid duration").length == 2
      | none => false)]
  return o

/-- `tl claim <id> --steal` (ADR-0013): take over an already-claimed item only
    when its claim is stale (an inline `--stale <dur>` or `tl.staleAfter`, no
    default). A local courtesy guard, never merge-enforced. Covers: the usage
    guards (no window / --stale without --steal / bad duration), not-stale-yet,
    the takeover (won + reassigned + the "Took over … from" human line), the
    config-supplied window, and --steal as a plain claim on a ready / own item. -/
def cliClaimStealTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- a git-backed project with three issues each created + claimed by eve ~2h ago
  -- (the claim out-stamps its create so the issue is InProgress, and stale)
  let root ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] } : IO _)
  let dir := (root / ".tl").toString
  let _ ← run' ["init", "--dir", dir]
  IO.FS.createDirAll (System.FilePath.mk dir / "log")
  let base := (← nowMs) - 2 * 3600 * 1000   -- 2h ago, in ms
  let mkStale (iid : String) (n1 n2 : Nat) : String :=
    foreignLine (.create iid { title := some "stale work" }) (base * 2 ^ 16) "2zzzzzzzzzzzz" "eve" n1 ++ "\n"
    ++ foreignLine (.claim iid "eve") ((base + 1000) * 2 ^ 16) "2zzzzzzzzzzzz" "eve" n2 ++ "\n"
  let issA := "aaaabbbbcccc0001"
  let issB := "aaaabbbbcccc0002"
  let issC := "aaaabbbbcccc0003"
  IO.FS.writeFile (System.FilePath.mk dir / "log" / "2zzzzzzzzzzzz.jsonl")
    (mkStale issA 1 2 ++ mkStale issB 3 4 ++ mkStale issC 5 6)
  -- (tl.staleAfter is unset for the usage/not-stale cases below)
  -- (a) --steal with no window at all (no --stale, no config) is usage
  o := o ++ [← expectErr "claim --steal without any staleness window is usage"
      ["claim", "tl-" ++ issB, "--dir", dir, "--steal", "--actor", "bob"] .usage
      (fun e => (e.message.splitOn "staleness window").length == 2)]
  -- (b) --stale without --steal is usage (a typo never silently plain-claims)
  o := o ++ [← expectErr "claim --stale without --steal is usage"
      ["claim", "tl-" ++ issB, "--dir", dir, "--stale", "1h", "--actor", "bob"] .usage]
  -- (c) --steal --stale <unparseable> is usage
  o := o ++ [← expectErr "claim --steal --stale with a bad duration is usage"
      ["claim", "tl-" ++ issB, "--dir", dir, "--steal", "--stale", "later", "--actor", "bob"] .usage]
  -- (d) --steal --stale 3h: the 2h-old claim is within the window ⇒ not-claimable
  o := o ++ [← expectErr "claim --steal --stale 3h on a 2h-old claim is not-claimable (not stale yet)"
      ["claim", "tl-" ++ issB, "--dir", dir, "--steal", "--stale", "3h", "--actor", "bob"] .notClaimable
      (fun e => (e.message.splitOn "not stale yet").length == 2)]
  -- (e) --steal --stale 1h: the 2h-old claim IS stale ⇒ takeover (won + reassigned)
  o := o ++ [← expectData "claim --steal --stale 1h takes over a stale claim (won, reassigned)"
      ["claim", "tl-" ++ issA, "--dir", dir, "--steal", "--stale", "1h", "--actor", "bob"]
      (fun j => ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won"
        && ((jGet j "claim").bind (fun c => jStr c "currentAssignee")) == some "bob")]
  -- the human line discloses the takeover and the prior holder
  o := o ++ [← (do match ← run' ["claim", "tl-" ++ issC, "--dir", dir, "--steal", "--stale", "1h", "--actor", "carol"] with
    | .ok out => pure (check "claim --steal human line says 'Took over … from eve'"
        ((out.human.splitOn "Took over").length == 2 && (out.human.splitOn "from eve").length == 2) out.human)
    | .error e => pure { name := "steal human line", passed := false, msg := e.message })]
  -- (f) the tl.staleAfter config supplies the window when --stale is absent (issB
  --     is still eve's untouched 2h-old claim — the (a)-(d) cases all errored)
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "config", "tl.staleAfter", "1h"] } : IO _)
  o := o ++ [← expectData "claim --steal uses the tl.staleAfter window when --stale is omitted"
      ["claim", "tl-" ++ issB, "--dir", dir, "--steal", "--actor", "dave"]
      (fun j => ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won"
        && ((jGet j "claim").bind (fun c => jStr c "currentAssignee")) == some "dave")]
  -- (g) --steal on an unclaimed (ready) item is just a plain claim — no window read
  let fresh ← freshDir
  let r1 ← mkIssue fresh "ready one"
  o := o ++ [← expectData "claim --steal on an unclaimed ready item just claims it (won)"
      ["claim", "tl-" ++ r1, "--dir", fresh, "--steal", "--actor", "bob"]
      (fun j => ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won")]
  -- (h) --steal on your OWN in-progress item re-claims it (no window needed)
  let r2 ← mkIssue fresh "own one"
  let _ ← run' ["claim", "tl-" ++ r2, "--dir", fresh, "--actor", "alice"]
  o := o ++ [← expectData "claim --steal on your own in-progress item re-claims it (won, no window)"
      ["claim", "tl-" ++ r2, "--dir", fresh, "--steal", "--actor", "alice"]
      (fun j => ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won")]
  -- (i) a plain claim (no --steal) of a READY item that merely retains a stale
  -- assignee (open + assignee, reachable via claim→close→reopen) must say
  -- "Claimed", never a false "Took over … stale" — no staleness test ran here
  let fresh2 ← freshDir
  let ra ← mkIssue fresh2 "retained-assignee"
  let _ ← run' ["claim", "tl-" ++ ra, "--dir", fresh2, "--actor", "alice"]
  let _ ← run' ["close", "tl-" ++ ra, "--dir", fresh2, "--as", "done", "--actor", "alice"]
  let _ ← run' ["reopen", "tl-" ++ ra, "--dir", fresh2, "--actor", "alice"]
  o := o ++ [← (do match ← run' ["claim", "tl-" ++ ra, "--dir", fresh2, "--actor", "bob"] with
    | .ok out => pure (check "a plain claim of a ready open+assigned item says Claimed, not a false takeover"
        ((out.human.splitOn "Claimed").length == 2 && (out.human.splitOn "Took over").length == 1) out.human)
    | .error e => pure { name := "no false takeover", passed := false, msg := e.message })]
  -- (j) a malformed tl.staleAfter must NOT block --steal on a ready item (no window
  -- is needed there); only the take-over path reports the bad config
  let root2 ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root2.toString, "init", "-q"] } : IO _)
  let dir2 := (root2 / ".tl").toString
  let _ ← run' ["init", "--dir", dir2]
  IO.FS.createDirAll (System.FilePath.mk dir2 / "log")
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root2.toString, "config", "tl.staleAfter", "whenever"] } : IO _)
  let rb ← mkIssue dir2 "ready under a bad config"
  o := o ++ [← expectData "a malformed tl.staleAfter does not block --steal on a ready item"
      ["claim", "tl-" ++ rb, "--dir", dir2, "--steal", "--actor", "bob"]
      (fun j => ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won")]
  -- (k) but taking over a stale claim with a malformed config reports it (teaches)
  let base2 := (← nowMs) - 2 * 3600 * 1000
  IO.FS.writeFile (System.FilePath.mk dir2 / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbcccc9999" { title := some "stale" }) (base2 * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 1 ++ "\n"
     ++ foreignLine (.claim "aaaabbbbcccc9999" "eve") ((base2 + 1000) * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 2 ++ "\n")
  o := o ++ [← expectErr "--steal over a stale claim with a malformed tl.staleAfter reports the bad config"
      ["claim", "tl-aaaabbbbcccc9999", "--dir", dir2, "--steal", "--actor", "bob"] .usage
      (fun e => (e.message.splitOn "not a valid duration").length == 2)]
  return o

/-- `tl list --stale <duration>` (ADR-0011): a mandatory-window read
    facet showing only stale claims (in-progress, claimed longer ago than the
    window), via the same `claimStaleDeadlineMs` as doctor / claim --steal. No
    default; a bad value is usage; open and freshly-claimed items are excluded. -/
def cliListStaleTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  -- an open (unclaimed) item and a freshly-claimed (not stale) item
  let _open ← mkIssue dir "open work"
  let freshId ← mkIssue dir "fresh claim"
  let _ ← run' ["claim", "tl-" ++ freshId, "--dir", dir, "--actor", "alice"]
  -- a foreign claim ~2h ago (the claim out-stamps its create ⇒ InProgress + stale)
  let base := (← nowMs) - 2 * 3600 * 1000
  let staleId := "aaaabbbbcccc7777"
  IO.FS.writeFile (System.FilePath.mk dir / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create staleId { title := some "claimed long ago" }) (base * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 1 ++ "\n"
     ++ foreignLine (.claim staleId "eve") ((base + 1000) * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 2 ++ "\n")
  -- (1) --stale 1h ⇒ only the 2h-old claim (open + fresh-claim excluded)
  o := o ++ [← expectData "list --stale 1h shows only the stale claim"
      ["list", "--stale", "1h", "--json", "--dir", dir]
      (fun j => jNat j "count" == some 1 && (jArr j "items").length == 1
        && ((jArr j "items").head?.bind (fun e => jStr e "id")) == some ("tl-" ++ staleId))]
  -- (2) --stale 3h ⇒ the 2h-old claim is within the window ⇒ nothing stale
  o := o ++ [← expectData "list --stale 3h shows nothing (the claim is younger than the window)"
      ["list", "--stale", "3h", "--json", "--dir", dir]
      (fun j => jNat j "count" == some 0)]
  -- (3) a bad --stale value is a usage error (no default, no silent full list)
  o := o ++ [← expectErr "list --stale with a bad duration is usage"
      ["list", "--stale", "soon", "--dir", dir] .usage
      (fun e => (e.message.splitOn "valid duration").length == 2)]
  -- (4) plain list (no --stale) shows all open work (open + both claims)
  o := o ++ [← expectData "plain list shows all open work, not just stale"
      ["list", "--json", "--dir", dir]
      (fun j => jNat j "count" == some 3)]
  -- (5) a stale-claimed EPIC that rolled up to done (raw in_progress, all children
  -- closed) must still appear under --stale — that lingering claim is exactly what
  -- to surface, doctor lists it (raw status, no effClosed gate), and --all must not
  -- change the stale set. Regression for the effClosed-gate bypass.
  let epicId := "aaaabbbbcccc8888"
  let kidId := "aaaabbbbcccc8889"
  IO.FS.writeFile (System.FilePath.mk dir / "log" / "3zzzzzzzzzzzz.jsonl")
    (foreignLine (.create epicId { title := some "epic claimed long ago" }) (base * 2 ^ 16) "3zzzzzzzzzzzz" "eve" 1 ++ "\n"
     ++ foreignLine (.claim epicId "eve") ((base + 1000) * 2 ^ 16) "3zzzzzzzzzzzz" "eve" 2 ++ "\n"
     ++ foreignLine (.create kidId { title := some "kid" }) ((base + 2000) * 2 ^ 16) "3zzzzzzzzzzzz" "eve" 3 ++ "\n"
     ++ foreignLine (.depAdd (epicId, kidId, EdgeKind.Parent)) ((base + 3000) * 2 ^ 16) "3zzzzzzzzzzzz" "eve" 4 ++ "\n"
     ++ foreignLine (.close kidId CloseResolution.Done) ((base + 4000) * 2 ^ 16) "3zzzzzzzzzzzz" "eve" 5 ++ "\n")
  let staleHasEpic (allFlag : Bool) : IO Bool := do
    match ← run' (["list", "--stale", "1h", "--json", "--dir", dir] ++ (if allFlag then ["--all"] else [])) with
    | .ok out => pure ((jArr out.data "items").any (fun e => jStr e "id" == some ("tl-" ++ epicId)))
    | .error _ => pure false
  o := o ++
    [check "list --stale surfaces a rolled-up-done epic with a stale claim (mirrors doctor, no effClosed gate)"
       (← staleHasEpic false) "the stale epic is missing under --stale",
     check "list --stale --all gives the same stale set (the epic is present either way)"
       (← staleHasEpic true) "the stale epic is missing under --stale --all"]
  -- (human) the stale render is non-empty and carries the stale-claim summary
  o := o ++ [← (do match ← run' ["list", "--stale", "1h", "--dir", dir] with
    | .ok out => pure (check "list --stale human render shows the stale-claim summary, not 'no issues'"
        ((out.human.splitOn "stale claim").length ≥ 2 && (out.human.splitOn "no issues").length == 1) out.human)
    | .error e => pure { name := "stale human render", passed := false, msg := e.message })]
  return o

/-- The git runtime-floor check (ADR-0006): the `git --version` parser, the floor
    comparison, the doctor row builder (incl. the below-floor warn — pure, so it is
    covered without an actually-old git), and the doctor/init integration on the
    live git (≥ 2.17 ⇒ ok / no note). -/
def cliGitFloorTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- (1) parseGitVersion: canonical X.Y.Z, a build suffix, two-component, garbage
  o := o ++
    [check "parseGitVersion: canonical X.Y.Z" (Tl.Sync.parseGitVersion "git version 2.17.1" == some (2, 17)) "",
     check "parseGitVersion: Apple build suffix" (Tl.Sync.parseGitVersion "git version 2.39.3 (Apple Git-145)" == some (2, 39)) "",
     check "parseGitVersion: two-component X.Y" (Tl.Sync.parseGitVersion "git version 2.9" == some (2, 9)) "",
     check "parseGitVersion: trailing newline tolerated" (Tl.Sync.parseGitVersion "git version 2.37.2\n" == some (2, 37)) "",
     check "parseGitVersion: windows suffix X.Y.Z.windows.N" (Tl.Sync.parseGitVersion "git version 2.45.2.windows.1" == some (2, 45)) "",
     check "parseGitVersion: a banner line before the version is scanned past" (Tl.Sync.parseGitVersion "warning: setlocale\ngit version 2.40.0" == some (2, 40)) "",
     check "parseGitVersion: non-git output → none" (Tl.Sync.parseGitVersion "not a git line" == none) "",
     check "parseGitVersion: missing minor → none" (Tl.Sync.parseGitVersion "git version 2" == none) ""]
  -- (2) gitMeetsFloor: at, below, above the 2.17 floor (major and minor)
  o := o ++
    [check "gitMeetsFloor: exactly 2.17 meets" (Tl.Sync.gitMeetsFloor (2, 17) == true) "",
     check "gitMeetsFloor: 2.16 is below" (Tl.Sync.gitMeetsFloor (2, 16) == false) "",
     check "gitMeetsFloor: 2.39 is above" (Tl.Sync.gitMeetsFloor (2, 39) == true) "",
     check "gitMeetsFloor: 1.99 (older major) is below" (Tl.Sync.gitMeetsFloor (1, 99) == false) "",
     check "gitMeetsFloor: 3.0 (newer major) is above" (Tl.Sync.gitMeetsFloor (3, 0) == true) ""]
  -- (3) gitVersionRow: below-floor warns + teaches; at-floor ok; unreadable warns;
  --     never fails doctor (warn, not fail — ADR-0008)
  let rowStatus (v : Option (Nat × Nat)) : Option String := jStr (gitVersionRow v).1 "status"
  let rowSaysFloor (v : Option (Nat × Nat)) : Bool := (((jStr (gitVersionRow v).1 "message").getD "").splitOn "2.17").length ≥ 2
  o := o ++
    [check "gitVersionRow: below floor → warn + teaching message"
       (rowStatus (some (2, 16)) == some "warn" && rowSaysFloor (some (2, 16))) "",
     check "gitVersionRow: at floor → ok" (rowStatus (some (2, 17)) == some "ok") "",
     check "gitVersionRow: unreadable git (none) → warn + message"
       (rowStatus none == some "warn" && rowSaysFloor none) "",
     check "gitVersionRow: never fails doctor (warn, not fail)"
       ((gitVersionRow (some (2, 16))).2 == false && (gitVersionRow none).2 == false) ""]
  -- (4) doctor integration: the gitVersion row is present and ok on the live git
  let dir ← freshDir
  let _ ← mkIssue dir "x"
  o := o ++ [← expectData "doctor reports a gitVersion check, ok on the live (≥2.17) git"
      ["doctor", "--json", "--dir", dir]
      (fun j => match (jArr j "checks").find? (fun c => jStr c "name" == some "gitVersion") with
        | some c => jStr c "status" == some "ok" && (jStr c "version").isSome
        | none => false)]
  -- (5) init integration: no git-floor note on the live git
  let root ← IO.FS.createTempDir
  o := o ++ [← (do match ← run' ["init", "--dir", (root / ".tl").toString] with
    | .ok out => pure (check "init emits no git-floor note on the live (≥2.17) git"
        (out.notes.all (fun n => (n.splitOn "below the required floor").length == 1))
        (String.intercalate " | " out.notes))
    | .error e => pure { name := "init git-floor note", passed := false, msg := e.message })]
  return o

/-- `tl log --since <cursor>`: the resumable change-feed. Covers empty/zero
    cursor ⇒ full history, the post-cursor delta, idempotent re-read, malformed
    cursors, human/json parity, and the distinguishing version-vector regression
    — a late foreign op below another replica's max is still delivered (a scalar
    high-water-mark cursor would drop it). -/
def cliLogSinceTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let _ ← mkIssue dir "one"
  let _ ← mkIssue dir "two"
  -- (1) an empty cursor is the full history; every log reports a resumable cursor
  o := o ++ [← expectData "log --since '' returns the full history with a cursor"
      ["log", "--since", "", "--json", "--dir", dir]
      (fun j => jNat j "count" == some 2 && ((jSub j "cursor" "since").getD "").length > 0)]
  -- capture the current frontier from a plain log
  let frontier ← (do match ← run' ["log", "--json", "--dir", dir] with
    | .ok out => pure ((jSub out.data "cursor" "since").getD "")
    | .error _ => pure "")
  -- (2) idempotent re-read: --since <frontier> right away is empty, cursor stable
  o := o ++ [← expectData "log --since <frontier> just after is empty and stable (idempotent)"
      ["log", "--since", frontier, "--json", "--dir", dir]
      (fun j => jNat j "count" == some 0 && jSub j "cursor" "since" == some frontier)]
  -- (3) post-cursor delta: a new op appears exactly once
  let _ ← mkIssue dir "three"
  o := o ++ [← expectData "log --since <frontier> after a change shows exactly the new op"
      ["log", "--since", frontier, "--json", "--dir", dir]
      (fun j => jNat j "count" == some 1 && (jArr j "entries").length == 1
        && ((jArr j "entries").head?.bind (fun e => jStr e "op")) == some "create")]
  -- (4) a malformed cursor is a clean usage error (never a silent full dump)
  o := o ++
    [← expectErr "log --since with a token that is not a replica:hlc:nonce triple is usage"
       ["log", "--since", "garbage", "--dir", dir] .usage,
     ← expectErr "log --since with a non-numeric hlc is usage"
       ["log", "--since", "1zzzzzzzzzzzz:notanum:1", "--dir", dir] .usage,
     ← expectErr "log --since with a non-numeric nonce is usage"
       ["log", "--since", "1zzzzzzzzzzzz:256:nope", "--dir", dir] .usage,
     ← expectErr "log --since with a non-Crockford replica is usage"
       ["log", "--since", "!!!:256:1", "--dir", dir] .usage,
     ← expectErr "log --since with an empty replica is usage"
       ["log", "--since", ":256:1", "--dir", dir] .usage,
     ← expectErr "log --since with an over-long (non-13-char) replica is usage"
       ["log", "--since", "00000000000000000000:256:1", "--dir", dir] .usage,
     ← expectErr "log --since with a >=2^64 replica is usage (first char above 'f')"
       ["log", "--since", "zzzzzzzzzzzzz:256:1", "--dir", dir] .usage,
     ← expectErr "log --since with stray commas is usage, never a silent full dump"
       ["log", "--since", ",,,", "--dir", dir] .usage,
     ← expectErr "log --since with a trailing comma is usage"
       ["log", "--since", "1zzzzzzzzzzzz:256:1,", "--dir", dir] .usage,
     ← expectErr "log --since with an hlc >= 2^64 is usage"
       ["log", "--since", "1zzzzzzzzzzzz:18446744073709551616:1", "--dir", dir] .usage,
     ← expectErr "log --since with a nonce >= 2^128 is usage"
       ["log", "--since", "1zzzzzzzzzzzz:256:340282366920938463463374607431768211456", "--dir", dir] .usage]
  -- (5) the distinguishing regression: a late-arriving foreign op whose HLC is
  -- below the own replica's max is still delivered under the per-replica version
  -- vector — a scalar high-water-mark cursor would drop it (count 0, not 1).
  let dirR ← freshDir
  let _ ← mkIssue dirR "own"           -- own replica at a real (high) HLC
  let frontierA ← (do match ← run' ["log", "--json", "--dir", dirR] with
    | .ok out => pure ((jSub out.data "cursor" "since").getD "")
    | .error _ => pure "")
  -- a foreign replica authored an op long ago (HLC 0x100, below the own max) that
  -- has only now synced into this clone
  IO.FS.writeFile (System.FilePath.mk dirR / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbccccdddd" { title := some "late" }) 0x100 "2zzzzzzzzzzzz" "mallory" ++ "\n")
  o := o ++
    [← expectData "a late foreign op below the own max is still delivered (version vector, not scalar)"
       ["log", "--since", frontierA, "--json", "--dir", dirR]
       (fun j => jNat j "count" == some 1 && (jArr j "entries").length == 1),
     ← expectData "the advanced cursor spans both replicas once the late op is folded"
       ["log", "--since", frontierA, "--json", "--dir", dirR]
       (fun j => (((jSub j "cursor" "since").getD "").splitOn ",").length == 2)]
  -- (5b) two ops from one replica at the same HLC, split only by nonce (ADR-0007),
  -- must each be delivered exactly once: a (replica → HLC) cursor skips the second
  -- on resume; the (HLC, nonce) frontier does not.
  let dirT ← freshDir
  IO.FS.createDirAll (System.FilePath.mk dirT / "log")
  IO.FS.writeFile (System.FilePath.mk dirT / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbcccc0001" { title := some "a" }) 256 "2zzzzzzzzzzzz" "m" 1 ++ "\n"
      ++ foreignLine (.create "aaaabbbbcccc0002" { title := some "b" }) 256 "2zzzzzzzzzzzz" "m" 2 ++ "\n")
  let tp1 ← run' ["log", "--since", "", "--limit", "1", "--json", "--dir", dirT]
  let (te1, tc1) := match tp1 with
    | .ok out => ((jArr out.data "entries").length, (jSub out.data "cursor" "since").getD "")
    | .error _ => (0, "")
  let tp2 ← run' ["log", "--since", tc1, "--limit", "1", "--json", "--dir", dirT]
  let (te2, tc2) := match tp2 with
    | .ok out => ((jArr out.data "entries").length, (jSub out.data "cursor" "since").getD "")
    | .error _ => (0, "")
  o := o ++
    [check "same-HLC page 1 delivers one op" (te1 == 1) s!"entries={te1} cursor={tc1}",
     check "same-HLC page 2 delivers the nonce-tiebroken op, not empty (no skip)"
       (te2 == 1 && tc2 != tc1) s!"entries={te2} c1={tc1} c2={tc2}"]
  -- (5c) a valid (HLC, nonce) = (0, 0) op is decodable; an empty cursor must
  -- still return it (the absent-threshold bottom sentinel, not a (0,0) default
  -- under strict >).
  let dirZ ← freshDir
  IO.FS.createDirAll (System.FilePath.mk dirZ / "log")
  IO.FS.writeFile (System.FilePath.mk dirZ / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbcccc0000" { title := some "z" }) 0 "2zzzzzzzzzzzz" "m" 0 ++ "\n")
  o := o ++ [← expectData "log --since '' returns a (0,0)-stamped op (empty cursor is full history)"
      ["log", "--since", "", "--json", "--dir", dirZ]
      (fun j => jNat j "count" == some 1 && (jArr j "entries").length == 1)]
  -- (6) human/json parity: --since reports the cursor in the human output too
  o := o ++ [← (do match ← run' ["log", "--since", "", "--dir", dir] with
    | .ok out => pure (check "human log --since prints a cursor line (parity with --json)"
        ((out.human.splitOn "cursor:").length > 1) out.human)
    | .error e => pure { name := "human cursor parity", passed := false, msg := e.message })]
  -- (7) --limit paginates the feed and the cursor advances by exactly the page,
  -- so a resume never skips — pins advanceCursor over the delivered page (capped),
  -- not over all matching ops (a capped→matching mutation drops page 2 to empty)
  let dirP ← freshDir
  let _ ← mkIssue dirP "p1"
  let _ ← mkIssue dirP "p2"
  let page1 ← run' ["log", "--since", "", "--limit", "1", "--json", "--dir", dirP]
  let (e1, c1) := match page1 with
    | .ok out => ((jArr out.data "entries").length, (jSub out.data "cursor" "since").getD "")
    | .error _ => (0, "")
  let page2 ← run' ["log", "--since", c1, "--limit", "1", "--json", "--dir", dirP]
  let (e2, c2) := match page2 with
    | .ok out => ((jArr out.data "entries").length, (jSub out.data "cursor" "since").getD "")
    | .error _ => (0, "")
  o := o ++
    [check "log --since --limit 1 delivers one op for the first page" (e1 == 1) s!"page1 entries={e1}",
     check "the next page resumes from the page cursor without skipping (capped advance)"
       (e2 == 1 && c2 != c1) s!"page2 entries={e2} c1={c1} c2={c2}"]
  -- (8) --since combined with an <id> filter scopes the feed to that issue's ops
  let dirF ← freshDir
  let i1 ← mkIssue dirF "f1"
  let _ ← mkIssue dirF "f2"
  let _ ← run' ["update", "tl-" ++ i1, "--title", "f1b", "--dir", dirF]
  o := o ++ [← expectData "log <id> --since '' returns only that issue's ops, with a cursor"
      ["log", "tl-" ++ i1, "--since", "", "--json", "--dir", dirF]
      (fun j => jNat j "count" == some 2 && ((jSub j "cursor" "since").getD "").length > 0)]
  return o

/-- `tl log` human output shows each target's current title (ADR-0025), sanitized
    (ADR-0014) and id-keyed-fallback for a dangling/untitled target; the `--json`
    entry stays id-keyed with NO title (the deliberate human/json divergence). -/
def cliLogTitleTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let humanOf (out : CmdOut) : String := (out.render.map (· Style.plain)).getD out.human
  let dir ← freshDir
  let id ← mkIssue dir "Write the parser"
  -- (1) the human line carries the title immediately after the target id
  o := o ++ [← (do match ← run' ["log", "--dir", dir] with
    | .ok out => pure (check "tl log human line shows the title right after the target id"
        (((humanOf out).splitOn ("tl-" ++ id ++ " Write the parser")).length ≥ 2) (humanOf out))
    | .error e => pure { name := "log title human", passed := false, msg := e.message })]
  -- (2) the --json entry stays id-keyed with NO title key (deliberate divergence)
  o := o ++ [← expectData "tl log --json entries carry no title (an id-keyed op feed)"
      ["log", "--json", "--dir", dir]
      (fun j => match (jArr j "entries").head? with
        | some e => (jGet e "title").isNone && (jArr e "targets").length == 1
        | none => false)]
  -- (3) a dangling target (op on a never-created issue) renders as the bare id with
  --     no title; an attacker-controlled title is sanitized on the human line
  let dir2 ← freshDir
  IO.FS.createDirAll (System.FilePath.mk dir2 / "log")
  let evil := String.singleton (Char.ofNat 0x1b) ++ "]0;x" ++ String.singleton (Char.ofNat 0x07)
  IO.FS.writeFile (System.FilePath.mk dir2 / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbcccc1234" { title := some ("Esc" ++ evil ++ "End") }) 100 "2zzzzzzzzzzzz" "eve" 1 ++ "\n"
     ++ foreignLine (.metaSet "ffffffffffffffff" "k" (some "v")) 200 "2zzzzzzzzzzzz" "eve" 2 ++ "\n")
  o := o ++ [← (do match ← run' ["log", "--dir", dir2] with
    | .ok out =>
      let h := humanOf out
      pure (check "log title: dangling target → bare id; attacker title sanitized"
        (!h.contains (Char.ofNat 0x1b)
          && (h.splitOn "tl-ffffffffffffffff").length ≥ 2
          && (h.splitOn "EscEnd").length ≥ 2) h)
    | .error e => pure { name := "log title dangling/sanitize", passed := false, msg := e.message })]
  -- (4) a long title is truncated to 48 chars + an ellipsis (the 49th char is dropped)
  let dir3 ← freshDir
  let _ ← mkIssue dir3 (String.ofList (List.replicate 60 'A'))
  o := o ++ [← (do match ← run' ["log", "--dir", dir3] with
    | .ok out =>
      let h := humanOf out
      pure (check "tl log truncates a >48-char title to 48 chars + ellipsis"
        ((h.splitOn "…").length ≥ 2
          && (h.splitOn (String.ofList (List.replicate 48 'A'))).length ≥ 2
          && (h.splitOn (String.ofList (List.replicate 49 'A'))).length == 1) h)
    | .error e => pure { name := "log title truncation", passed := false, msg := e.message })]
  -- (5) a title that sanitizes to empty renders as the bare id — no trailing space
  let dir4 ← freshDir
  IO.FS.createDirAll (System.FilePath.mk dir4 / "log")
  IO.FS.writeFile (System.FilePath.mk dir4 / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbcccc5555" { title := some evil }) 100 "2zzzzzzzzzzzz" "eve" 1 ++ "\n")
  o := o ++ [← (do match ← run' ["log", "--dir", dir4] with
    | .ok out =>
      let h := humanOf out
      pure (check "a title that sanitizes to empty renders as the bare id, no trailing space"
        ((h.splitOn "tl-aaaabbbbcccc5555").length ≥ 2
          && (h.splitOn "tl-aaaabbbbcccc5555 ").length == 1) h)
    | .error e => pure { name := "log title empty-sanitize", passed := false, msg := e.message })]
  return o

/-- `tl log --until <cursor>` (ADR-0025): backward history browsing and the
    dual-edge `{since, until}` cursor. Covers full-history-newest-first with both
    edges, backward paging that telescopes without overlap and terminates, the
    shared-HLC boundary tie-break across two replicas (each op delivered exactly
    once paging back — an HLC-only edge would skip or re-deliver the second), a
    bounded `--since C1 --until C2` window, the default page size (pages, not
    drains), and the edge-named malformed-cursor usage error. -/
def cliLogUntilTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let entryTarget (out : CmdOut) : Option String :=
    ((jArr out.data "entries").head?.bind (fun e => (jArr e "targets").head?)).bind (fun t => t.getStr?.toOption)
  -- (1) --until '' is the full history, newest-first, and reports both edges
  let dir ← freshDir
  let _a ← mkIssue dir "a"
  let _b ← mkIssue dir "b"
  let c ← mkIssue dir "c"
  o := o ++ [← expectData "log --until '' is full history newest-first with both cursor edges"
      ["log", "--until", "", "--json", "--dir", dir]
      (fun j => jNat j "count" == some 3
        -- both edges present AND populated (not the always-present empty-string key)
        && ((jSub j "cursor" "since").getD "").length > 0 && ((jSub j "cursor" "until").getD "").length > 0
        && (((jArr j "entries").head?.bind (fun e => (jArr e "targets").head?)).bind
              (fun t => t.getStr?.toOption)) == some ("tl-" ++ c))]
  -- (2) backward paging telescopes via cursor.until: pages are disjoint, then drains
  let pageTargets (out : CmdOut) : List String :=
    (jArr out.data "entries").filterMap (fun e => (jArr e "targets").head?.bind (fun t => t.getStr?.toOption))
  let p1 ← run' ["log", "--until", "", "--limit", "2", "--json", "--dir", dir]
  let (t1, u1) := match p1 with
    | .ok out => (pageTargets out, (jSub out.data "cursor" "until").getD "")
    | .error _ => ([], "")
  let p2 ← run' ["log", "--until", u1, "--limit", "2", "--json", "--dir", dir]
  let (t2, u2) := match p2 with
    | .ok out => (pageTargets out, (jSub out.data "cursor" "until").getD "")
    | .error _ => ([], "")
  let p3 ← run' ["log", "--until", u2, "--limit", "2", "--json", "--dir", dir]
  let n3 := match p3 with | .ok out => (jArr out.data "entries").length | .error _ => 99
  let overlap := t1.filter t2.contains
  o := o ++
    [check "backward page 1 delivers the newest 2 of 3" (t1.length == 2) s!"t1={t1}",
     check "backward page 2 telescopes to the remaining 1, disjoint from page 1"
       (t2.length == 1 && overlap.isEmpty) s!"t1={t1} t2={t2} overlap={overlap}",
     check "the two pages together cover all 3 ops with no repeat" ((t1 ++ t2).eraseDups.length == 3) s!"t1={t1} t2={t2}",
     check "backward paging terminates (page 3 is empty)" (n3 == 0) s!"n3={n3} u2={u2}"]
  -- (3) boundary tie-break: two replicas author an op at the SAME hlc; backward
  -- --limit 1 pages deliver each exactly once. The per-replica until edge splits
  -- them by the (hlc, replica, nonce) tie-break — an HLC-only edge skips or
  -- re-delivers the second; a non-accumulating until edge re-delivers on page 3.
  let dirB ← freshDir
  IO.FS.createDirAll (System.FilePath.mk dirB / "log")
  IO.FS.writeFile (System.FilePath.mk dirB / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbcccc000a" { title := some "A" }) 256 "2zzzzzzzzzzzz" "m" 1 ++ "\n")
  IO.FS.writeFile (System.FilePath.mk dirB / "log" / "3zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbcccc000b" { title := some "B" }) 256 "3zzzzzzzzzzzz" "m" 1 ++ "\n")
  let b1 ← run' ["log", "--until", "", "--limit", "1", "--json", "--dir", dirB]
  let (bn1, bt1, bu1) := match b1 with
    | .ok out => ((jArr out.data "entries").length, entryTarget out, (jSub out.data "cursor" "until").getD "")
    | .error _ => (0, none, "")
  let b2 ← run' ["log", "--until", bu1, "--limit", "1", "--json", "--dir", dirB]
  let (bn2, bt2, bu2) := match b2 with
    | .ok out => ((jArr out.data "entries").length, entryTarget out, (jSub out.data "cursor" "until").getD "")
    | .error _ => (0, none, "")
  let b3 ← run' ["log", "--until", bu2, "--limit", "1", "--json", "--dir", dirB]
  let bn3 := match b3 with | .ok out => (jArr out.data "entries").length | .error _ => 99
  o := o ++
    [check "same-HLC backward page 1 delivers one op" (bn1 == 1) s!"bn1={bn1}",
     check "same-HLC backward page 2 delivers the OTHER op (tie-break, no skip)"
       (bn2 == 1 && bt1.isSome && bt2.isSome && bt2 != bt1) s!"bt1={bt1} bt2={bt2}",
     check "same-HLC backward paging terminates without re-delivery" (bn3 == 0) s!"bn3={bn3} bu2={bu2}"]
  -- (4) a bounded window: --since C1 --until C3 keeps only ops strictly between
  let dirW ← freshDir
  let _w1 ← mkIssue dirW "w1"
  let c1 ← (do match ← run' ["log", "--json", "--dir", dirW] with
    | .ok out => pure ((jSub out.data "cursor" "since").getD "") | .error _ => pure "")
  let _w2 ← mkIssue dirW "w2"
  let _w3 ← mkIssue dirW "w3"
  let c3 ← (do match ← run' ["log", "--json", "--dir", dirW] with
    | .ok out => pure ((jSub out.data "cursor" "since").getD "") | .error _ => pure "")
  o := o ++ [← expectData "log --since C1 --until C3 is the bounded window (just the middle op)"
      ["log", "--since", c1, "--until", c3, "--json", "--dir", dirW]
      (fun j => jNat j "count" == some 1)]
  -- (4b) a windowed FORWARD feed with --limit loses no op: the undelivered remainder
  -- is reached by cursor.since (not cursor.until). Guards the resume-back edge against
  -- a future "fix" that mistakes the since-mode degenerate edge for a skip.
  let dirN ← freshDir
  let _n1 ← mkIssue dirN "n1"
  let cLo ← (do match ← run' ["log", "--limit", "1", "--since", "", "--json", "--dir", dirN] with
    | .ok out => pure ((jSub out.data "cursor" "since").getD "") | .error _ => pure "")
  let _n2 ← mkIssue dirN "n2"
  let _n3 ← mkIssue dirN "n3"
  let _n4 ← mkIssue dirN "n4"
  let cHi ← (do match ← run' ["log", "--json", "--dir", dirN] with
    | .ok out => pure ((jSub out.data "cursor" "since").getD "") | .error _ => pure "")
  -- window (cLo, cHi) = {n2, n3}; drain it forward one op at a time
  let q1 ← run' ["log", "--since", cLo, "--until", cHi, "--limit", "1", "--json", "--dir", dirN]
  let (qt1, qs1) := match q1 with
    | .ok out => (pageTargets out, (jSub out.data "cursor" "since").getD "")
    | .error _ => ([], "")
  let q2 ← run' ["log", "--since", qs1, "--until", cHi, "--limit", "1", "--json", "--dir", dirN]
  let qt2 := match q2 with | .ok out => pageTargets out | .error _ => []
  o := o ++
    [check "windowed forward page 1 delivers one op" (qt1.length == 1) s!"qt1={qt1}",
     check "windowed forward page 2 reaches the remainder via cursor.since (no op lost)"
       (qt2.length == 1 && (qt1.filter qt2.contains).isEmpty) s!"qt1={qt1} qt2={qt2}"]
  -- (5) a malformed --until cursor is a usage error whose message names --until
  -- (the edge param's whole point) — never a silent dump
  o := o ++
    [← expectErr "log --until bad segment is usage, and the message names --until"
       ["log", "--until", "garbage", "--dir", dir] .usage
       (fun e => (e.message.splitOn "--until").length > 1),
     ← expectErr "log --until with a non-numeric hlc is usage"
       ["log", "--until", "1zzzzzzzzzzzz:notanum:1", "--dir", dir] .usage]
  -- (5b) a hand-edited --until cursor repeating a replica collapses to the MIN
  -- (the conservative upper bound), not the max: the higher triple must not widen
  -- the window. With one own op at stamp S, `--until <S-as-(hlc,big-nonce)>,<S>`
  -- must exclude S (min picks the lower), i.e. deliver nothing.
  let dirD ← freshDir
  let _d1 ← mkIssue dirD "d1"
  let sCur ← (do match ← run' ["log", "--json", "--dir", dirD] with
    | .ok out => pure ((jSub out.data "cursor" "until").getD "") | .error _ => pure "")
  -- sCur is "<replica>:<hlc>:<nonce>" of d1; pair it with a higher-hlc triple for the
  -- same replica (append a digit ⇒ ×10, still < 2^64; the nonce is already near 2^128
  -- so it cannot be grown without tripping the bound). min collapses to the real hlc.
  let dup := match sCur.splitOn ":" with
    | [r, h, n] => s!"{r}:{h}0:{n},{r}:{h}:{n}"
    | _ => sCur
  o := o ++ [← expectData "log --until with a duplicate-replica cursor uses the MIN bound (excludes the op)"
      ["log", "--until", dup, "--json", "--dir", dirD]
      (fun j => jNat j "count" == some 0)]
  -- (6) --until's default --limit pages (like plain log, 10) and does not drain
  let dirP ← freshDir
  for k in [0:12] do let _ ← mkIssue dirP s!"i{k}"
  o := o ++ [← expectData "log --until '' defaults to a 10-entry page (count discloses the full 12)"
      ["log", "--until", "", "--json", "--dir", dirP]
      (fun j => jNat j "count" == some 12 && (jArr j "entries").length == 10)]
  return o

/-- `tl log` time selectors (ADR-0025): `--since`/`--until` accepting a duration,
    date, timestamp, or `all` alongside the cursor, plus `--last N`. Time bounds
    are best-effort over wall-clock; the rows stay deterministic by using `all`,
    a `1h` window (every just-created op is within the last hour), and far
    past/future absolute bounds whose verdict no timezone can flip. The cursor
    regression row pins that a version-vector value still routes to the exact path. -/
def cliLogTimeTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  for k in [0:4] do let _ ← mkIssue dir s!"t{k}"   -- 4 create ops
  o := o ++ [← expectData "log --since all returns the full history (oldest-first)"
    ["log", "--since", "all", "--json", "--dir", dir]
    (fun j => jNat j "count" == some 4 && (jArr j "entries").length == 4)]
  o := o ++ [← expectData "log --since 1h includes every recent op and emits a resume cursor"
    ["log", "--since", "1h", "--json", "--dir", dir]
    (fun j => jNat j "count" == some 4 && ((jSub j "cursor" "since").getD "").length > 0)]
  o := o ++ [← expectData "log --since a far-future date is empty"
    ["log", "--since", "2099-01-01", "--json", "--dir", dir]
    (fun j => jNat j "count" == some 0)]
  -- a time-started --since must return the skipped frontier, not an empty cursor:
  -- resuming with it continues from the query point, never replays the history
  let resumeRow ← (match ← run' ["log", "--since", "2099-01-01", "--json", "--dir", dir] with
    | .ok out => do
      let cur := (jSub out.data "cursor" "since").getD ""
      let r ← run' ["log", "--since", cur, "--json", "--dir", dir]
      pure (if cur.isEmpty then
              check "resuming a time-started --since does not replay the skipped history" false
                "cursor.since was empty (an empty cursor replays the whole log)"
            else match r with
              | .ok rr => check "resuming a time-started --since does not replay the skipped history"
                  (jNat rr.data "count" == some 0) rr.data.compress
              | .error e => { name := "time --since resume", passed := false, msg := e.message })
    | .error e => pure { name := "time --since cursor", passed := false, msg := e.message })
  o := o ++ [resumeRow]
  o := o ++
    [← expectData "log --until a far-future date includes all"
       ["log", "--until", "2099-01-01", "--json", "--dir", dir]
       (fun j => jNat j "count" == some 4),
     ← expectData "log --until a far-past date is empty"
       ["log", "--until", "2000-01-01", "--json", "--dir", dir]
       (fun j => jNat j "count" == some 0),
     ← expectData "log --until a far-future timestamp (explicit offset) includes all"
       ["log", "--until", "2099-01-01T00:00:00Z", "--json", "--dir", dir]
       (fun j => jNat j "count" == some 4)]
  o := o ++ [← expectData "log --last 2 returns the newest 2 (count discloses the full 4)"
    ["log", "--last", "2", "--json", "--dir", dir]
    (fun j => jNat j "count" == some 4 && (jArr j "entries").length == 2)]
  o := o ++ [← expectData "log --last 0 returns all (mirrors --limit 0)"
    ["log", "--last", "0", "--json", "--dir", dir]
    (fun j => (jArr j "entries").length == 4)]
  o := o ++ [← expectData "log --since all --last 2 tails the newest 2 of the window"
    ["log", "--since", "all", "--last", "2", "--json", "--dir", dir]
    (fun j => jNat j "count" == some 4 && (jArr j "entries").length == 2)]
  -- a version-vector value still routes to the exact frontier path (regression)
  let cursorRow ← (match ← run' ["log", "--json", "--dir", dir] with
    | .ok out => do
      let cur := (jSub out.data "cursor" "since").getD ""
      match ← run' ["log", "--since", cur, "--json", "--dir", dir] with
      | .ok r => pure (check "a cursor value still routes to the exact path (no ops after the full frontier)"
          (jNat r.data "count" == some 0) r.data.compress)
      | .error e => pure { name := "cursor regression resume", passed := false, msg := e.message }
    | .error e => pure { name := "cursor regression precondition", passed := false, msg := e.message })
  o := o ++ [cursorRow]
  o := o ++
    [← expectErr "log --since junk is usage" ["log", "--since", "soon", "--dir", dir] .usage,
     ← expectErr "log --last a non-number is usage" ["log", "--last", "abc", "--dir", dir] .usage,
     ← expectErr "log --limit together with --last is usage"
       ["log", "--limit", "5", "--last", "3", "--dir", dir] .usage,
     -- a bad-offset timestamp (has '-') teaches the bound forms, not a cursor error
     ← expectErr "log --since a bad-offset timestamp teaches the forms (not a cursor error)"
       ["log", "--since", "2026-06-20T12:00:00+25:00", "--dir", dir] .usage
       (fun e => (e.message.splitOn "recognized bound").length > 1),
     -- a cursor-shaped token (':' and no '-') still gets the cursor-specific error
     ← expectErr "log --since a malformed cursor still gets the cursor error"
       ["log", "--since", "notareplica:1:2", "--dir", dir] .usage
       (fun e => (e.message.splitOn "cursor").length > 1
                 && (e.message.splitOn "recognized bound").length == 1)]
  return o

/-- `tl init --stealth` (ADR-0001 §7): local-only state with zero repo-visible
    trace. Pins the marker, the suppressed discovery pointer, that writes still
    work, that `tl sync` fails closed with `stealth-mode`, the creation-fixed mode
    (re-init neither converts nor un-stealths), the marker-removal un-stealth, and
    that auto-sync never publishes even when `tl.autosync` is set by hand. -/
def cliStealthTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- (1) stealth init: created, marked, no sharing affordances
  let root ← IO.FS.createTempDir
  let dir := (root / ".tl").toString
  o := o ++ [(match ← run' ["init", "--stealth", "--dir", dir] with
    | .ok out => check "init --stealth reports stealth, notes local-only, suppresses the discovery pointer"
        (jBool out.data "stealth" == some true
          && out.notes.any (fun n => (n.splitOn "local-only").length > 1)
          && !out.notes.any (fun n => (n.splitOn "discoverable").length > 1))
        (String.intercalate " | " out.notes)
    | .error e => { name := "init --stealth", passed := false, msg := e.message })]
  o := o ++ [check "init --stealth wrote the gitignored stealth marker"
    (← (root / ".tl" / "local" / "stealth").pathExists)]
  -- (2) writes work in stealth (the CRDT degenerates to a single-replica fold)
  let sid ← mkIssue dir "stealth work"
  o := o ++ [← expectData "a stealth repo still creates and lists issues" ["ready", "--dir", dir]
    (fun j => (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ sid)))]
  -- (3) tl sync is refused with the stable stealth-mode code, not a silent
  -- no-op — and the message teaches the whole conversion: the marker path,
  -- that nothing migrates, and where the local guide lives
  o := o ++ [← expectErr "tl sync in a stealth repo is stealth-mode" ["sync", "--dir", dir] .stealthMode
    (fun e => (e.message.splitOn ".tl/local/stealth").length > 1
      && (e.message.splitOn "migrates nothing").length > 1
      && (e.message.splitOn ".tl/README.md").length > 1)]
  -- the generated primer carries the un-stealth guide the error points at
  let primer ← IO.FS.readFile (root / ".tl" / "README.md")
  o := o ++ [check "the .tl/README.md primer teaches the un-stealth conversion"
    ((primer.splitOn "local/stealth").length > 1
      && (primer.splitOn "unchanged").length > 1) primer]
  -- the taught paths are the REAL ones: under a custom --dir the marker and
  -- primer do not live under `.tl`, and an error naming `.tl/...` would send
  -- the user to a path that does not exist
  let customRoot ← IO.FS.createTempDir
  let customDir := (customRoot / "custom-state").toString
  let _ ← run' ["init", "--stealth", "--dir", customDir]
  o := o ++ [← expectErr "a custom --dir stealth repo is still stealth-mode"
    ["sync", "--dir", customDir] .stealthMode
    (fun e => (e.message.splitOn (customDir ++ "/local/stealth")).length > 1
      && (e.message.splitOn (customDir ++ "/README.md")).length > 1
      && (e.message.splitOn "`.tl/local/stealth`").length == 1)]
  o := o ++ [(match ← run' ["init", "--stealth", "--dir", customDir] with
    | .ok out => check "the custom --dir init note names the real marker path"
        (out.notes.any (fun n => (n.splitOn (customDir ++ "/local/stealth")).length > 1)
          && !out.notes.any (fun n => (n.splitOn "`.tl/local/stealth`").length > 1))
        (String.intercalate " | " out.notes)
    | .error e => { name := "custom --dir init note", passed := false, msg := e.message })]
  -- (4) the mode is fixed at creation: re-init --stealth is idempotent, a plain
  -- re-init does not un-stealth
  o := o ++
    [← expectData "re-init --stealth stays stealth (created false)" ["init", "--stealth", "--dir", dir]
       (fun j => jBool j "stealth" == some true && jBool j "created" == some false),
     ← expectData "a plain re-init does not un-stealth" ["init", "--dir", dir]
       (fun j => jBool j "stealth" == some true)]
  -- (5) un-stealth = remove the marker; sync no longer reports stealth-mode
  IO.FS.removeFile (root / ".tl" / "local" / "stealth")
  o := o ++ [(match ← run' ["sync", "--dir", dir] with
    | .ok _ => check "after removing the marker, sync runs (no stealth-mode)" true ""
    | .error e => check "after removing the marker, sync is not stealth-mode"
        (e.code != .stealthMode) e.code.wire)]
  -- (6) control: a normal init is not stealth and offers the discovery pointer
  let root2 ← IO.FS.createTempDir
  IO.FS.writeFile (root2 / "AGENTS.md") "# p\n"
  let nDir := (root2 / ".tl").toString
  o := o ++ [(match ← run' ["init", "--dir", nDir] with
    | .ok out => check "a normal init is not stealth and offers the discovery pointer"
        (jBool out.data "stealth" == some false
          && out.notes.any (fun n => (n.splitOn "discoverable").length > 1))
        (String.intercalate " | " out.notes)
    | .error e => { name := "normal init control", passed := false, msg := e.message })]
  o := o ++ [← expectData "--stealth on an existing non-stealth repo is ignored (mode fixed at creation)"
    ["init", "--stealth", "--dir", nDir] (fun j => jBool j "stealth" == some false)]
  -- (7) auto-sync gate: in a git repo with tl.autosync set by hand, a stealth
  -- write still does not publish, so a sibling clone sees nothing
  let groot ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", groot.toString, "init", "-q"] } : IO _)
  let aDir := (groot / ".tl").toString
  let bDir := (groot / ".tlB").toString
  let _ ← run' ["init", "--stealth", "--dir", aDir]
  let _ ← run' ["init", "--dir", bDir]
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", groot.toString, "config", "tl.autosync", "true"] } : IO _)
  let _ ← run' ["create", "stealth write must not publish", "--dir", aDir, "--actor", "a"]
  o := o ++ [← expectData "stealth write does not auto-publish even with tl.autosync on"
    ["list", "--dir", bDir, "--json"] (fun j => jNat j "count" == some 0)]
  -- (8) no --sync/--verify bracket reaches refs/tl/log: exercise every sync-bearing
  -- path in the stealth repo, then assert the shared ref was never created
  let _ ← run' ["ready", "--sync", "--dir", aDir]
  let _ ← run' ["doctor", "--sync", "--dir", aDir]
  let _ ← run' ["create", "via preWriteRefresh", "--dir", aDir, "--actor", "a"]
  let refLs ← (IO.Process.output { cmd := "git", args := #["-C", groot.toString, "rev-parse", "--verify", "--quiet", "refs/tl/log"] } : IO _)
  o := o ++ [check "no --sync path ever creates refs/tl/log in a stealth repo"
    (refLs.exitCode != 0) s!"refs/tl/log exists: {refLs.stdout}"]
  -- the best-effort --sync bracket discloses the skip rather than silently sharing
  o := o ++ [(match ← run' ["ready", "--sync", "--dir", aDir] with
    | .ok out => check "ready --sync in stealth discloses the skip"
        (out.notes.any (fun n => (n.splitOn "stealth").length > 1)) (String.intercalate " | " out.notes)
    | .error e => { name := "ready --sync in stealth", passed := false, msg := e.message })]
  return o

/-- `tl list --deferred` (ADR-0010): the read facet over the `v.deferred` view —
    only open issues whose `deferUntil` is still in the future. Pins that a
    future-deferred issue appears, a past-deferUntil one does not (it auto-resumed),
    a plain open one does not, undefer drops it, and the rows carry `deferred:true`. -/
def cliListDeferredTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let a ← mkIssue dir "plain open"
  let b ← mkIssue dir "deferred future"
  let c ← mkIssue dir "deferred past"
  let _ ← run' ["defer", "tl-" ++ b, "--until", "2099-01-01", "--dir", dir, "--actor", "t"]
  let _ ← run' ["defer", "tl-" ++ c, "--until", "2000-01-01", "--dir", dir, "--actor", "t"]
  o := o ++ [← expectData "list --deferred shows only the open + future-deferUntil issue"
    ["list", "--deferred", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").all (fun r => jBool r "deferred" == some true)
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ b))
      && !(jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ a))
      && !(jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ c)))]
  -- the list row carries the wake-up deferUntil (triage; human/json parity with show)
  o := o ++ [← expectData "an actively-deferred list row carries the deferUntil wake-up time"
    ["list", "--deferred", "--flat", "--dir", dir, "--json"]
    (fun j => (jArr j "items").all (fun r => (jStr r "deferUntil").isSome))]
  let _ ← run' ["undefer", "tl-" ++ b, "--dir", dir, "--actor", "t"]
  o := o ++ [← expectData "after undefer, list --deferred is empty"
    ["list", "--deferred", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 0)]
  let _ ← run' ["defer", "tl-" ++ a, "--for", "48h", "--dir", dir, "--actor", "t"]
  let humanRow ← (match ← run' ["list", "--deferred", "--dir", dir] with
    | .ok out => pure (check "list --deferred human summary names the facet"
        ((out.human.splitOn "deferred issue").length > 1) out.human)
    | .error e => pure { name := "list --deferred human", passed := false, msg := e.message })
  o := o ++ [humanRow]
  -- tree mode (the default render): a facet must hide a non-matching child of a
  -- matching parent — the tree shows exactly the filtered rows the count reports
  let dir3 ← freshDir
  let e ← mkIssue dir3 "deferred epic Etitle"
  let _ ← mkIssue dir3 "child Tnotdeferred" ["--parent", "tl-" ++ e]
  let _ ← run' ["defer", "tl-" ++ e, "--for", "72h", "--dir", dir3, "--actor", "t"]
  let treeRow ← (match ← run' ["list", "--deferred", "--dir", dir3] with
    | .ok out => pure (check "list --deferred (tree) shows the deferred epic but hides its non-deferred child"
        ((out.human.splitOn "Etitle").length > 1 && (out.human.splitOn "Tnotdeferred").length == 1) out.human)
    | .error e => pure { name := "list --deferred tree", passed := false, msg := e.message })
  o := o ++ [treeRow]
  -- composes with --label (AND): only deferred issues carrying the label
  let dir4 ← freshDir
  let p ← mkIssue dir4 "deferred labeled"
  let q ← mkIssue dir4 "deferred unlabeled"
  let _ ← run' ["label", "add", "tl-" ++ p, "area:x", "--dir", dir4, "--actor", "t"]
  let _ ← run' ["defer", "tl-" ++ p, "--until", "2099-01-01", "--dir", dir4, "--actor", "t"]
  let _ ← run' ["defer", "tl-" ++ q, "--until", "2099-01-01", "--dir", dir4, "--actor", "t"]
  o := o ++ [← expectData "list --deferred --label composes as AND (only the labeled deferred issue)"
    ["list", "--deferred", "--label", "area:x", "--flat", "--dir", dir4, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ p))
      && !(jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ q)))]
  return o

/-- `tl list --status` (ADR-0020): repeatable ⇒ OR over effectiveStatus;
    a named closed status self-includes (bypasses the default open-only gate); a
    bad spelling is a usage error; the match is on effectiveStatus, not raw status. -/
def cliListStatusTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let openId ← mkIssue dir "open task"
  let inProgId ← mkIssue dir "in-progress task"
  let doneId ← mkIssue dir "done task"
  let cancId ← mkIssue dir "cancelled task"
  let _ ← run' ["claim", "tl-" ++ inProgId, "--dir", dir, "--actor", "alice"]
  let _ ← run' ["close", "tl-" ++ doneId, "--as", "done", "--dir", dir, "--actor", "alice"]
  let _ ← run' ["close", "tl-" ++ cancId, "--as", "cancelled", "--dir", dir, "--actor", "alice"]
  o := o ++ [← expectData "list --status open keeps only the open issue"
    ["list", "--status", "open", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ openId))
      && (jArr j "items").all (fun r => jStr r "effectiveStatus" == some "open"))]
  o := o ++ [← expectData "list --status repeats compose as OR (open or in_progress)"
    ["list", "--status", "open", "--status", "in_progress", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 2
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ inProgId)))]
  -- the facets inherit the uniform parser: the `--flag=value` form is accepted
  -- (ADR-0020 — frozen intentionally, not a facet-specific rule)
  o := o ++ [← expectData "list --status=open (the = value form) is accepted"
    ["list", "--status=open", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1)]
  o := o ++ [← expectData "list --status done self-includes closed (no --all needed)"
    ["list", "--status", "done", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ doneId)))]
  o := o ++ [← expectData "list --status done --status cancelled OR-includes both closed"
    ["list", "--status", "done", "--status", "cancelled", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 2
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ doneId))
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ cancId)))]
  o := o ++ [← expectErr "list --status with a bad value is usage"
    ["list", "--status", "stuck", "--dir", dir] .usage]
  -- matches effectiveStatus, not raw status: an epic rolled up to done by its
  -- only child matches --status done and is excluded from --status open
  let dir2 ← freshDir
  let epic ← mkIssue dir2 "rolled-up epic"
  let kid ← mkIssue dir2 "only child" ["--parent", "tl-" ++ epic]
  let _ ← run' ["close", "tl-" ++ kid, "--as", "done", "--dir", dir2, "--actor", "t"]
  o := o ++ [← expectData "list --status done matches an epic rolled up to done (effectiveStatus)"
    ["list", "--status", "done", "--flat", "--dir", dir2, "--json"]
    (fun j => (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ epic)))]
  o := o ++ [← expectData "list --status open excludes the rolled-up-done epic"
    ["list", "--status", "open", "--flat", "--dir", dir2, "--json"]
    (fun j => !(jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ epic)))]
  let humanRow ← (match ← run' ["list", "--status", "open", "--flat", "--dir", dir] with
    | .ok out => pure (check "list --status human summary names the facet"
        ((out.human.splitOn "filtered by status open").length > 1) out.human)
    | .error e => pure { name := "list --status human", passed := false, msg := e.message })
  o := o ++ [humanRow]
  -- composes with another facet as AND (status AND priority)
  let dir3 ← freshDir
  let _ ← mkIssue dir3 "open p0" ["-p", "0"]
  let openP2 ← mkIssue dir3 "open p2"
  o := o ++ [← expectData "list --status open --priority 2 composes as AND"
    ["list", "--status", "open", "--priority", "2", "--flat", "--dir", dir3, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ openP2)))]
  return o

/-- `tl list --assignee` (ADR-0013): repeatable ⇒ OR; exact, case-sensitive (an
    identity is discrete); `me` resolves to the current actor. -/
def cliListAssigneeTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let a ← mkIssue dir "alice work"
  let b ← mkIssue dir "bob work"
  let _ ← mkIssue dir "unassigned work"
  let _ ← run' ["claim", "tl-" ++ a, "--dir", dir, "--actor", "alice"]
  let _ ← run' ["claim", "tl-" ++ b, "--dir", dir, "--actor", "bob"]
  o := o ++ [← expectData "list --assignee alice keeps only alice's issue"
    ["list", "--assignee", "alice", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ a)))]
  o := o ++ [← expectData "list --assignee repeats compose as OR (alice or bob)"
    ["list", "--assignee", "alice", "--assignee", "bob", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 2)]
  o := o ++ [← expectData "list --assignee with no holder matches nothing"
    ["list", "--assignee", "carol", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 0)]
  o := o ++ [← expectData "list --assignee is case-sensitive (Alice ≠ alice)"
    ["list", "--assignee", "Alice", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 0)]
  -- `me` resolves to the current actor: claim without --actor, then filter by me —
  -- both resolve through the same actor chain, so they agree regardless of env
  let dir2 ← freshDir
  let mine ← mkIssue dir2 "my work"
  let _ ← mkIssue dir2 "not claimed"
  let _ ← run' ["claim", "tl-" ++ mine, "--dir", dir2]
  o := o ++ [← expectData "list --assignee me resolves to the current actor"
    ["list", "--assignee", "me", "--flat", "--dir", dir2, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ mine)))]
  -- the human summary echoes the raw `me` token, not the resolved actor (no
  -- identity/email leaked into the headline)
  let meHuman ← (match ← run' ["list", "--assignee", "me", "--flat", "--dir", dir2] with
    | .ok out => pure (check "list --assignee me echoes `me` in the summary, not the resolved actor"
        ((out.human.splitOn "filtered by assignee me").length > 1) out.human)
    | .error e => pure { name := "list --assignee me human", passed := false, msg := e.message })
  o := o ++ [meHuman]
  -- a closed-but-still-assigned issue: --assignee refines the open set (hidden by
  -- the default gate), --all surfaces it (close does not clear the assignee register)
  let dir3 ← freshDir
  let ca ← mkIssue dir3 "closed but assigned"
  let _ ← run' ["claim", "tl-" ++ ca, "--dir", dir3, "--actor", "alice"]
  let _ ← run' ["close", "tl-" ++ ca, "--as", "done", "--dir", dir3, "--actor", "alice"]
  o := o ++ [← expectData "list --assignee alice hides a closed-but-assigned issue (open gate)"
    ["list", "--assignee", "alice", "--flat", "--dir", dir3, "--json"]
    (fun j => jNat j "count" == some 0)]
  o := o ++ [← expectData "list --assignee alice --all surfaces the closed-but-assigned issue"
    ["list", "--assignee", "alice", "--all", "--flat", "--dir", dir3, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ ca)))]
  -- the summary echoes untrusted assignee text: a control byte in the matched
  -- assignee must be stripped from the human footer (Tl/Cli/Sanitize.lean contract)
  let esc := Char.ofNat 27
  let evil := String.ofList [esc, 'r', 'e', 'd']
  let dir4 ← freshDir
  let ev ← mkIssue dir4 "evil assignee work"
  let _ ← run' ["claim", "tl-" ++ ev, "--dir", dir4, "--actor", evil]
  let sanRow ← (match ← run' ["list", "--assignee", evil, "--flat", "--dir", dir4] with
    | .ok out => pure (check "list --assignee strips control bytes from the human summary"
        (!out.human.toList.contains esc) out.human)
    | .error e => pure { name := "list --assignee sanitize", passed := false, msg := e.message })
  o := o ++ [sanRow]
  return o

/-- `tl list --priority` (ADR-0020): repeatable ⇒ OR; exact 0–4; a
    non-0–4 value is a usage error; it refines the open set (no gate bypass). -/
def cliListPriorityTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let p0 ← mkIssue dir "p0 work" ["-p", "0"]
  let p2 ← mkIssue dir "p2 work"
  let p4 ← mkIssue dir "p4 work" ["-p", "4"]
  o := o ++ [← expectData "list --priority 0 keeps only p0"
    ["list", "--priority", "0", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ p0)))]
  -- the global `-p` ⇒ `--priority` alias also reaches the facet (ADR-0020 —
  -- frozen intentionally; the facets add no parsing rules of their own)
  o := o ++ [← expectData "list -p 0 (the global -p alias) works for the facet"
    ["list", "-p", "0", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ p0)))]
  o := o ++ [← expectData "list --priority repeats compose as OR (0 or 4)"
    ["list", "--priority", "0", "--priority", "4", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 2
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ p0))
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ p4)))]
  o := o ++ [← expectData "list --priority 2 matches the default-priority issue"
    ["list", "--priority", "2", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ p2)))]
  o := o ++ [← expectErr "list --priority out of range is usage"
    ["list", "--priority", "9", "--dir", dir] .usage]
  o := o ++ [← expectErr "list --priority non-number is usage"
    ["list", "--priority", "high", "--dir", dir] .usage]
  -- refines the open set: a done p1 is hidden unless --all (no closed-gate bypass)
  let dir2 ← freshDir
  let donep1 ← mkIssue dir2 "done p1" ["-p", "1"]
  let _ ← run' ["close", "tl-" ++ donep1, "--as", "done", "--dir", dir2, "--actor", "t"]
  o := o ++ [← expectData "list --priority 1 hides a closed match (no gate bypass)"
    ["list", "--priority", "1", "--flat", "--dir", dir2, "--json"]
    (fun j => jNat j "count" == some 0)]
  o := o ++ [← expectData "list --priority 1 --all surfaces the closed match"
    ["list", "--priority", "1", "--all", "--flat", "--dir", dir2, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ donep1)))]
  let prioHuman ← (match ← run' ["list", "--priority", "0", "--flat", "--dir", dir] with
    | .ok out => pure (check "list --priority human summary names the facet"
        ((out.human.splitOn "filtered by priority 0").length > 1) out.human)
    | .error e => pure { name := "list --priority human", passed := false, msg := e.message })
  o := o ++ [prioHuman]
  -- `--priority` repeats only on `list`; making it repeatable there must NOT relax
  -- the single-value duplicate guard on create/update (per-command repeatable scope)
  o := o ++ [← expectErr "create rejects a duplicate --priority (single-value flag)"
    ["create", "dup prio", "--priority", "1", "--priority", "2", "--dir", dir] .usage]
  o := o ++ [← expectErr "update rejects a duplicate --priority (single-value flag)"
    ["update", "tl-" ++ p0, "--priority", "1", "--priority", "2", "--dir", dir] .usage]
  return o

/-- `tl list --blocked`: open issues with ≥1 unclosed blocker (the derived
    `blocked` view); closing the blocker discharges it. -/
def cliListBlockedTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let blocker ← mkIssue dir "the blocker"
  let blockedId ← mkIssue dir "the dependent" ["--blocked-by", "tl-" ++ blocker]
  let _ ← mkIssue dir "free work"
  o := o ++ [← expectData "list --blocked keeps only the blocked issue"
    ["list", "--blocked", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ blockedId))
      && (jArr j "items").all (fun r => jBool r "blocked" == some true))]
  let _ ← run' ["close", "tl-" ++ blocker, "--as", "done", "--dir", dir, "--actor", "t"]
  o := o ++ [← expectData "list --blocked is empty after the blocker closes"
    ["list", "--blocked", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 0)]
  -- human summary names the blocked facet via the `filtered by` suffix — a token
  -- the legend ("! blocked") and the row's `[blocked]` flag do NOT carry, so this
  -- actually proves the suffix is emitted (not just any "blocked" on the page)
  let dir2 ← freshDir
  let bk ← mkIssue dir2 "bk"
  let _ ← mkIssue dir2 "bd" ["--blocked-by", "tl-" ++ bk]
  let humanRow ← (match ← run' ["list", "--blocked", "--flat", "--dir", dir2] with
    | .ok out => pure (check "list --blocked human summary names the facet"
        ((out.human.splitOn "filtered by blocked").length > 1) out.human)
    | .error e => pure { name := "list --blocked human", passed := false, msg := e.message })
  o := o ++ [humanRow]
  return o

/-- Cross-facet composition (ADR-0020: different facets compose with
    AND): the gate-bypassing / AND-within facets (`--deferred`/`--label`) combined
    with the new single-valued facets still narrow to the intersection. -/
def cliListFacetComposeTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- --deferred (gate-bypassing) AND --priority (open-set refinement)
  let dir ← freshDir
  let dp0 ← mkIssue dir "deferred p0" ["-p", "0"]
  let dp2 ← mkIssue dir "deferred p2"
  let _ ← run' ["defer", "tl-" ++ dp0, "--until", "2099-01-01", "--dir", dir, "--actor", "t"]
  let _ ← run' ["defer", "tl-" ++ dp2, "--until", "2099-01-01", "--dir", dir, "--actor", "t"]
  o := o ++ [← expectData "list --deferred --priority 0 composes as AND"
    ["list", "--deferred", "--priority", "0", "--flat", "--dir", dir, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ dp0))
      && !(jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ dp2)))]
  -- --label (AND-within) AND a closed --status: the label refines the closed set
  -- that --status surfaced (both bypass/extend the open gate, and still intersect)
  let dir2 ← freshDir
  let ld ← mkIssue dir2 "labeled done"
  let ud ← mkIssue dir2 "unlabeled done"
  let _ ← run' ["label", "add", "tl-" ++ ld, "x", "--dir", dir2, "--actor", "t"]
  let _ ← run' ["close", "tl-" ++ ld, "--as", "done", "--dir", dir2, "--actor", "t"]
  let _ ← run' ["close", "tl-" ++ ud, "--as", "done", "--dir", dir2, "--actor", "t"]
  o := o ++ [← expectData "list --label x --status done composes as AND (label refines the closed set)"
    ["list", "--label", "x", "--status", "done", "--flat", "--dir", dir2, "--json"]
    (fun j => jNat j "count" == some 1
      && (jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ ld))
      && !(jArr j "items").any (fun r => jStr r "id" == some ("tl-" ++ ud)))]
  return o

/-- `tl import` (ADR-0005) — the differential test: import the committed
    fixture `Tests/fixtures/import-sample.jsonl`, then assert the materialized
    state matches the records' fields, statuses, and edges, and `ready`
    matches the unblocked set the graph implies. Plus determinism (byte-stable
    re-import), the two safety gates, and the fail-closed malformed-line
    paths. The fixture is read from the repo checkout (cwd-relative, like the
    imports/doc-grammar suites) and copied into a temp dir before importing,
    so import behavior itself stays temp-dir hermetic. -/
def cliImportTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let fixturePath : System.FilePath := "Tests" / "fixtures" / "import-sample.jsonl"
  if !(← fixturePath.pathExists) then
    return [check "import: committed fixture present at cwd" false
      s!"could not find {fixturePath} under cwd {(← IO.currentDir)} — run tltest from the repo root"]
  let fixture? ← try pure (some (← IO.FS.readFile fixturePath)) catch e => do
    o := o ++ [check "import: committed fixture readable" false s!"{fixturePath}: {e}"]
    pure none
  let some fixture := fixture? | return o
  let root ← IO.FS.createTempDir
  let fpath := (root / "in.jsonl").toString
  IO.FS.writeFile (root / "in.jsonl") fixture
  let dir := (root / ".tl").toString
  let idOf (src : String) : String := "tl-" ++ Tl.Import.importIssueId "import" src
  -- import: 5 issues, the priority clamp + the dangling edge both disclosed
  o := o ++ [← expectData "import seeds the issues and discloses the clamp + the dangling edge"
    ["import", fpath, "--dir", dir]
    (fun j => jNat j "issues" == some 5 && jNat j "ops" != some 0
      && (jArr j "disclosures").any (fun d => ((d.getStr?.toOption.getD "").splitOn "clamped").length > 1)
      && (jArr j "disclosures").any (fun d => ((d.getStr?.toOption.getD "").splitOn "not in the import").length > 1))]
  -- differential oracle: each record materializes to its fields/status
  o := o ++
    [← expectData "imported in_progress issue: status / assignee / priority / labels"
       ["show", idOf "PROJ-42", "--dir", dir]
       (fun j => jStr j "status" == some "in_progress" && jStr j "assignee" == some "alice"
         && jNat j "priority" == some 1 && (jArr j "labels").length == 1),
     ← expectData "imported done issue is closed done"
       ["show", idOf "PROJ-7", "--dir", dir] (fun j => jStr j "status" == some "done"),
     ← expectData "an imported issue reports provenance.source = imported (not native)"
       ["show", idOf "PROJ-42", "--dir", dir]
       (fun j => ((jGet j "provenance").bind (fun p => jStr p "source")) == some "imported"),
     ← expectData "imported epic is an epic (rolled up over its children)"
       ["show", idOf "PROJ-1", "--dir", dir] (fun j => jBool j "isEpic" == some true),
     ← expectData "imported issue: out-of-range priority clamped to 4, deferred set"
       ["show", idOf "PROJ-9", "--dir", dir]
       (fun j => jNat j "priority" == some 4 && jBool j "deferred" == some true && (jStr j "deferUntil").isSome),
     ← expectData "imported duplicate is cancelled"
       ["show", idOf "PROJ-3", "--dir", dir] (fun j => jStr j "status" == some "cancelled")]
  -- edges: blocks (blocker done ⇒ not blocked), parent, related all present
  o := o ++ [← expectData "imported edges: blocks + parent + related, not blocked (blocker is done)"
    ["show", idOf "PROJ-42", "--dir", dir]
    (fun j => jBool j "blocked" == some false
      && (jArr j "dependencies").any (fun e => jStr e "type" == some "blocks")
      && (jArr j "dependencies").any (fun e => jStr e "type" == some "parent")
      && (jArr j "dependencies").any (fun e => jStr e "type" == some "related"))]
  -- ready matches the import graph: nothing workable (done / in_progress / deferred / epic)
  o := o ++ [← expectData "ready matches the unblocked set the import implies (none)"
    ["ready", "--dir", dir] (fun j => jNat j "count" == some 0)]
  -- determinism: a re-import into a fresh repo yields a byte-identical segment
  let readSeg (dpath : String) : IO String := do
    let entries ← (System.FilePath.mk dpath / "log").readDir
    let parts ← entries.toList.mapM (fun e => IO.FS.readFile e.path)
    pure (String.join parts)
  let root2 ← IO.FS.createTempDir
  IO.FS.writeFile (root2 / "in.jsonl") fixture
  let dir2 := (root2 / ".tl").toString
  let _ ← run' ["import", (root2 / "in.jsonl").toString, "--dir", dir2]
  o := o ++ [check "re-import is byte-stable (identical seed segment)"
    ((← readSeg dir) == (← readSeg dir2)) "segment bytes differ across imports"]
  -- the --force gate: a non-empty log refuses, --force proceeds
  o := o ++
    [← expectErr "import into a non-empty log needs --force"
       ["import", fpath, "--dir", dir] .forceRequired,
     ← expectData "import --force re-seeds the non-empty log"
       ["import", fpath, "--dir", dir, "--force"] (fun j => jNat j "issues" == some 5)]
  -- the bounds gate (separate from --force): over --max refuses, --allow-large proceeds
  let root3 ← IO.FS.createTempDir
  IO.FS.writeFile (root3 / "in.jsonl") fixture
  let dir3 := (root3 / ".tl").toString
  o := o ++
    [← expectErr "import over the size bound needs --allow-large or a raised --max"
       ["import", (root3 / "in.jsonl").toString, "--dir", dir3, "--max", "10"] .forceRequired,
     ← expectData "import --allow-large proceeds past the bound"
       ["import", (root3 / "in.jsonl").toString, "--dir", dir3, "--max", "10", "--allow-large"]
       (fun j => jNat j "issues" == some 5)]
  -- fail-closed malformed-line paths
  let badDir ← IO.FS.createTempDir
  let writeBad (name content : String) : IO String := do
    IO.FS.writeFile (badDir / name) content; pure (badDir / name).toString
  o := o ++
    [← expectErr "invalid JSON is malformed-line"
       ["import", (← writeBad "a.jsonl" "{not json}\n"), "--dir", (badDir / "a").toString] .malformedLine,
     ← expectErr "a missing title is malformed-line"
       ["import", (← writeBad "b.jsonl" "{\"id\":\"X\"}\n"), "--dir", (badDir / "b").toString] .malformedLine,
     ← expectErr "an unknown status is malformed-line"
       ["import", (← writeBad "c.jsonl" "{\"id\":\"X\",\"title\":\"t\",\"status\":\"wat\"}\n"), "--dir", (badDir / "c").toString] .malformedLine,
     ← expectErr "a duplicate source id is malformed-line"
       ["import", (← writeBad "d.jsonl" "{\"id\":\"X\",\"title\":\"a\"}\n{\"id\":\"X\",\"title\":\"b\"}\n"), "--dir", (badDir / "d").toString] .malformedLine]
  return o

/-- `tl defer` / `tl undefer` (ADR-0010): the `--for`/`--until` value grammar,
    the ready exclusion + auto-resume on a past instant, idempotent re-defer and
    undefer, and the teaching usage errors on bad input. The offset-timestamp row
    pins the UTC normalization; bare-date offset interpretation is exercised at
    the pure-parser tier (`Tests.TimeTests`, deterministic), so these rows stay
    independent of the test host's timezone by using far past/future dates. -/
def cliDeferTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let id ← mkIssue dir "deferrable task"
  let tid := "tl-" ++ id
  -- --for: deferred, deferUntil set, dropped from ready
  o := o ++ [← expectData "defer --for marks the issue deferred"
    ["defer", tid, "--for", "36h", "--dir", dir, "--actor", "t"]
    (fun j => jBool j "deferred" == some true && (jStr j "deferUntil").isSome
              && jBool j "ready" == some false)]
  o := o ++ [← expectData "a deferred issue drops out of ready" ["ready", "--dir", dir]
    (fun j => (jArr j "items").all (fun r => jStr r "id" != some tid))]
  -- undefer: cleared, back in ready
  o := o ++ [← expectData "undefer clears the deferral"
    ["undefer", tid, "--dir", dir, "--actor", "t"]
    (fun j => jBool j "deferred" == some false && (jStr j "deferUntil").isNone
              && jBool j "ready" == some true)]
  o := o ++ [← expectData "undefer returns the issue to ready" ["ready", "--dir", dir]
    (fun j => (jArr j "items").any (fun r => jStr r "id" == some tid))]
  -- --until a far-future date: deferred (timezone-independent)
  o := o ++ [← expectData "defer --until a future date defers"
    ["defer", tid, "--until", "2099-01-01", "--dir", dir, "--actor", "t"]
    (fun j => jBool j "deferred" == some true && jBool j "ready" == some false)]
  -- --until a far-past date: the instant is already gone, so it is NOT deferred
  -- (auto-resume — the conjunct holds vacuously once now ≥ deferUntil)
  o := o ++ [← expectData "defer --until a past date is not deferred (already elapsed)"
    ["defer", tid, "--until", "2000-01-01", "--dir", dir, "--actor", "t"]
    (fun j => jBool j "deferred" == some false && jBool j "ready" == some true)]
  -- --until a timestamp with an explicit offset, normalized to UTC
  o := o ++ [← expectData "defer --until an offset timestamp normalizes to UTC"
    ["defer", tid, "--until", "2099-01-01T00:00:00+02:00", "--dir", dir, "--actor", "t"]
    (fun j => jStr j "deferUntil" == some "2098-12-31T22:00:00Z" && jBool j "deferred" == some true)]
  -- re-defer to the identical instant is an idempotent no-op
  o := o ++ [(match ← run' ["defer", tid, "--until", "2099-01-01T00:00:00+02:00",
                            "--dir", dir, "--actor", "t"] with
    | .ok out => check "re-defer to the same instant is an idempotent no-op"
        ((out.human.splitOn "already deferred").length > 1) out.human
    | .error e => { name := "re-defer to the same instant is an idempotent no-op",
                    passed := false, msg := e.message })]
  -- undefer twice: the second is an idempotent no-op with an honest message
  let _ ← run' ["undefer", tid, "--dir", dir, "--actor", "t"]
  o := o ++ [(match ← run' ["undefer", tid, "--dir", dir, "--actor", "t"] with
    | .ok out => check "undefer on a non-deferred issue is a no-op"
        ((out.human.splitOn "is not deferred").length > 1) out.human
    | .error e => { name := "undefer on a non-deferred issue is a no-op",
                    passed := false, msg := e.message })]
  -- usage / not-found errors, each a teaching message behind a stable code
  o := o ++
    [← expectErr "defer with neither flag is usage"
       ["defer", tid, "--dir", dir, "--actor", "t"] .usage,
     ← expectErr "defer with both flags is usage"
       ["defer", tid, "--until", "2099-01-01", "--for", "1h", "--dir", dir, "--actor", "t"] .usage,
     ← expectErr "defer --until junk is usage"
       ["defer", tid, "--until", "soon", "--dir", dir, "--actor", "t"] .usage,
     ← expectErr "defer --until an invalid date is usage"
       ["defer", tid, "--until", "2026-13-40", "--dir", dir, "--actor", "t"] .usage,
     ← expectErr "defer --until a bare datetime (no offset) is usage"
       ["defer", tid, "--until", "2099-01-01T09:00:00", "--dir", dir, "--actor", "t"] .usage,
     ← expectErr "defer --for zero is usage"
       ["defer", tid, "--for", "0h", "--dir", dir, "--actor", "t"] .usage,
     ← expectErr "defer --for a bare number is usage"
       ["defer", tid, "--for", "10", "--dir", dir, "--actor", "t"] .usage,
     -- a --for so large the instant exceeds the canonical wire range is rejected
     -- (rendering a 5-digit year would make the next read refuse our own segment)
     ← expectErr "defer --for beyond the representable range (year 9999) is usage"
       ["defer", tid, "--for", "3000000d", "--dir", dir, "--actor", "t"] .usage,
     ← expectErr "defer an unknown id is not-found"
       ["defer", "tl-zzzzzzzzzzzzzzzz", "--for", "1h", "--dir", dir, "--actor", "t"] .notFound]
  -- the rejected over-range defer left the own segment readable (no corrupt write)
  o := o ++ [← expectData "a rejected over-range defer does not corrupt the own segment"
    ["show", tid, "--dir", dir] (fun j => (jStr j "id").isSome)]
  return o

/-- ADR-0020 shape pins for the later-built verbs (`defer`/`undefer`,
    `reopen`, `dep relate`/`unrelate`/`path`/`critical`, `unblocks`, the
    `meta` family, `import`): exact top-level key sets plus the pinned enum
    values and orderings — the freeze the ADR's per-command sections state.
    Value-level behavior is covered by the per-verb groups; these rows guard
    the *shape*. -/
def cliShapePinTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let hub ← mkIssue dir "Design the AST"
  let leaf ← mkIssue dir "Write the parser" ["--blocked-by", "tl-" ++ hub]
  let mid ← mkIssue dir "Name the fields" ["--blocked-by", "tl-" ++ hub]
  let sub ← mkIssue dir "Parse digits" ["--blocked-by", "tl-" ++ leaf]
  let solo ← mkIssue dir "Wire the CLI"
  -- the issueObj echo for a titled, undescribed, unclaimed native create:
  -- every always-present field plus title and timestamps, nothing else
  let echoKeys : List String :=
    ["blocked", "createdAt", "deferred", "dependencies", "effectiveStatus",
     "id", "isEpic", "labels", "meta", "priority", "provenance", "ready",
     "status", "title", "updatedAt"]
  -- unblocks: {count, freed, id}; each freed row {effectiveStatus, id, status, title}
  o := o ++ [← expectData "unblocks pins {count, freed, id}"
      ["unblocks", "tl-" ++ hub, "--dir", dir]
    (fun j => jKeys j == ["count", "freed", "id"]
      && jNat j "count" == some 2
      && (jArr j "freed").all (fun r =>
           jKeys r == ["effectiveStatus", "id", "status", "title"]
           && jStr r "status" == some "open" && jStr r "effectiveStatus" == some "open")
      && (let ids := (jArr j "freed").filterMap (fun r => jStr r "id")
          ids.length == 2 && ids.contains ("tl-" ++ leaf) && ids.contains ("tl-" ++ mid))),
   ← expectData "unblocks keeps the shape when freed is empty"
      ["unblocks", "tl-" ++ solo, "--dir", dir]
    (fun j => jKeys j == ["count", "freed", "id"] && jNat j "count" == some 0)]
  -- dep path: {found, from, path, to}, all four present in both answers
  o := o ++ [← expectData "dep path pins {found, from, path, to}"
      ["dep", "path", "tl-" ++ hub, "tl-" ++ sub, "--dir", dir]
    (fun j => jKeys j == ["found", "from", "path", "to"]
      && jBool j "found" == some true
      && (jArr j "path").map (·.getStr?.toOption)
           == [some ("tl-" ++ hub), some ("tl-" ++ leaf), some ("tl-" ++ sub)]),
   ← expectData "dep path keeps all four fields when no path exists"
      ["dep", "path", "tl-" ++ sub, "tl-" ++ hub, "--dir", dir]
    (fun j => jKeys j == ["found", "from", "path", "to"]
      && jBool j "found" == some false && (jArr j "path").isEmpty)]
  -- dep critical: {count, items}; rows {id, status, title, weight},
  -- weight-descending, status = the (necessarily open) effective status
  o := o ++ [← expectData "dep critical pins {count, items} and the row shape"
      ["dep", "critical", "--dir", dir]
    (fun j => jKeys j == ["count", "items"]
      && jNat j "count" == some 2
      && (jArr j "items").all (fun r =>
           jKeys r == ["id", "status", "title", "weight"]
           && jStr r "status" == some "open")
      && ((jArr j "items").map (fun r => jStr r "id"))
           == [some ("tl-" ++ hub), some ("tl-" ++ leaf)]
      && ((jArr j "items").map (fun r => jNat r "weight")) == [some 3, some 1])]
  -- dep relate / unrelate: {from, status, to, type}; relate is always
  -- "added" (add-wins, no noop), unrelate is removed-then-noop
  o := o ++ [← expectData "dep relate pins the related ack"
      ["dep", "relate", "tl-" ++ leaf, "tl-" ++ solo, "--dir", dir, "--actor", "t"]
    (fun j => jKeys j == ["from", "status", "to", "type"]
      && jStr j "type" == some "related" && jStr j "status" == some "added"
      && jStr j "from" == some ("tl-" ++ leaf) && jStr j "to" == some ("tl-" ++ solo)),
   ← expectData "re-relating (swapped args) still answers added, echoing argument order"
      ["dep", "relate", "tl-" ++ solo, "tl-" ++ leaf, "--dir", dir, "--actor", "t"]
    (fun j => jStr j "status" == some "added"
      && jStr j "from" == some ("tl-" ++ solo) && jStr j "to" == some ("tl-" ++ leaf)),
   ← expectData "dep unrelate answers removed"
      ["dep", "unrelate", "tl-" ++ leaf, "tl-" ++ solo, "--dir", dir, "--actor", "t"]
    (fun j => jKeys j == ["from", "status", "to", "type"]
      && jStr j "status" == some "removed"),
   ← expectData "unrelating an unrelated pair is the noop"
      ["dep", "unrelate", "tl-" ++ leaf, "tl-" ++ solo, "--dir", dir, "--actor", "t"]
    (fun j => jStr j "status" == some "noop"),
   ← expectData "self-unrelate is the noop"
      ["dep", "unrelate", "tl-" ++ solo, "tl-" ++ solo, "--dir", dir, "--actor", "t"]
    (fun j => jStr j "status" == some "noop"),
   ← expectErr "self-relate is a usage refusal"
      ["dep", "relate", "tl-" ++ solo, "tl-" ++ solo, "--dir", dir, "--actor", "t"] .usage]
  -- defer / undefer / reopen: the bare issue echo — deferUntil is the only
  -- key the deferral adds, and closing/reopening adds/removes exactly
  -- {closeResolution, closedAt, unblocked}
  o := o ++ [← expectData "defer echoes the issue plus deferUntil only"
      ["defer", "tl-" ++ solo, "--until", "2098-06-01", "--dir", dir, "--actor", "t"]
    (fun j => jKeys j
        == ["blocked", "createdAt", "deferUntil", "deferred", "dependencies",
            "effectiveStatus", "id", "isEpic", "labels", "meta", "priority",
            "provenance", "ready", "status", "title", "updatedAt"]
      && jBool j "deferred" == some true && (jStr j "deferUntil").isSome),
   ← expectData "undefer drops deferUntil and nothing else"
      ["undefer", "tl-" ++ solo, "--dir", dir, "--actor", "t"]
    (fun j => jKeys j == echoKeys && jBool j "deferred" == some false),
   ← expectData "close adds exactly closeResolution/closedAt/unblocked"
      ["close", "tl-" ++ solo, "--as", "done", "--dir", dir, "--actor", "t"]
    (fun j => jKeys j
        == ["blocked", "closeResolution", "closedAt", "createdAt", "deferred",
            "dependencies", "effectiveStatus", "id", "isEpic", "labels", "meta",
            "priority", "provenance", "ready", "status", "title",
            "unblocked", "updatedAt"]),
   ← expectData "reopen restores the bare echo (no closeResolution/closedAt)"
      ["reopen", "tl-" ++ solo, "--dir", dir, "--actor", "t"]
    (fun j => jKeys j == echoKeys && jStr j "status" == some "open"),
   ← expectData "reopening an open issue is the idempotent no-op, same echo"
      ["reopen", "tl-" ++ solo, "--dir", dir, "--actor", "t"]
    (fun j => jKeys j == echoKeys)]
  -- meta: set/clear acks, keyed and keyless get, per-id and global list
  o := o ++ [← expectData "meta set pins {id, key, status, value}"
      ["meta", "set", "tl-" ++ solo, "owner", "carol", "--dir", dir, "--actor", "t"]
    (fun j => jKeys j == ["id", "key", "status", "value"]
      && jStr j "status" == some "set" && jStr j "value" == some "carol"),
   ← expectData "re-setting a set key still answers set (an LWW write is never a noop)"
      ["meta", "set", "tl-" ++ solo, "owner", "carol", "--dir", dir, "--actor", "t"]
    (fun j => jStr j "status" == some "set" && jStr j "value" == some "carol")]
  let _ ← run' ["meta", "set", "tl-" ++ solo, "area", "kernel", "--dir", dir, "--actor", "t"]
  o := o ++ [← expectData "keyed meta get pins {id, key, value}"
      ["meta", "get", "tl-" ++ solo, "owner", "--dir", dir]
    (fun j => jKeys j == ["id", "key", "value"] && jStr j "value" == some "carol"),
   ← expectData "keyed meta get of an absent key answers value:null"
      ["meta", "get", "tl-" ++ solo, "nope", "--dir", dir]
    (fun j => jKeys j == ["id", "key", "value"]
      && (match jGet j "value" with | some Json.null => true | _ => false)),
   ← expectData "keyless meta get pins {count, id, meta}, key-ascending rows"
      ["meta", "get", "tl-" ++ solo, "--dir", dir]
    (fun j => jKeys j == ["count", "id", "meta"] && jNat j "count" == some 2
      && (jArr j "meta").all (fun r => jKeys r == ["key", "value"])
      && (jArr j "meta").map (fun r => jStr r "key") == [some "area", some "owner"]),
   ← expectData "per-id meta list pins {count, id, keys} with string keys"
      ["meta", "list", "tl-" ++ solo, "--dir", dir]
    (fun j => jKeys j == ["count", "id", "keys"]
      && (jArr j "keys").map (·.getStr?.toOption) == [some "area", some "owner"]),
   ← expectData "global meta list pins key-ascending rows with per-key counts"
      ["meta", "list", "--dir", dir]
    (fun j => jNat j "count" == some 2
      && (jArr j "keys").map (fun r => jStr r "key") == [some "area", some "owner"]
      && (jArr j "keys").map (fun r => jNat r "count") == [some 1, some 1]),
   ← expectData "meta clear pins {id, key, status} — no value field"
      ["meta", "clear", "tl-" ++ solo, "owner", "--dir", dir, "--actor", "t"]
    (fun j => jKeys j == ["id", "key", "status"] && jStr j "status" == some "cleared"),
   ← expectData "clearing a clear key is the noop"
      ["meta", "clear", "tl-" ++ solo, "owner", "--dir", dir, "--actor", "t"]
    (fun j => jStr j "status" == some "noop"),
   ← expectData "global meta list pins {count, keys} with {count, key} rows"
      ["meta", "list", "--dir", dir]
    (fun j => jKeys j == ["count", "keys"] && jNat j "count" == some 1
      && (jArr j "keys").all (fun r => jKeys r == ["count", "key"])
      && (jArr j "keys").map (fun r => jStr r "key") == [some "area"])]
  -- import: the five-field summary; disclosures duplicate into envelope notes
  let importRoot ← IO.FS.createTempDir
  let batch := importRoot / "batch.jsonl"
  IO.FS.writeFile batch
    ("{\"id\":\"EXT-1\",\"title\":\"Imported epic\",\"status\":\"open\"}\n"
      ++ "{\"id\":\"EXT-2\",\"title\":\"Imported leaf\",\"status\":\"open\",\"blockedBy\":[\"GHOST-1\"]}\n")
  let dir2 ← freshDir
  match ← run' ["import", batch.toString, "--source", "ext", "--dir", dir2] with
  | .ok out =>
    o := o ++
      [check "import pins {disclosures, issues, ops, replica, source}"
        (jKeys out.data == ["disclosures", "issues", "ops", "replica", "source"])
        out.data.compress,
       check "import counts the records and echoes the source tag"
        (jNat out.data "issues" == some 2 && jStr out.data "source" == some "ext")
        out.data.compress,
       check "the dangling-edge disclosure rides data and the envelope notes"
        ((jArr out.data "disclosures").length == 1
          && out.notes.any (fun n => (n.splitOn "GHOST-1").length > 1))
        (String.intercalate " | " out.notes)]
  | .error e =>
    o := o ++ [check "import pins {disclosures, issues, ops, replica, source}"
      false s!"{e.code.wire}: {e.message}"]
  -- past-instant defer: deferUntil stays in the echo, the issue stays
  -- workable, and the elapsed deferral is disclosed as a top-level note
  let past ← mkIssue dir "Sort the imports"
  match ← run' ["defer", "tl-" ++ past, "--until", "2000-01-01", "--dir", dir, "--actor", "t"] with
  | .ok out =>
    o := o ++
      [check "a past defer keeps deferUntil in the echo and stays workable"
        (jKeys out.data
            == ["blocked", "createdAt", "deferUntil", "deferred", "dependencies",
                "effectiveStatus", "id", "isEpic", "labels", "meta", "priority",
                "provenance", "ready", "status", "title", "updatedAt"]
          && jBool out.data "deferred" == some false
          && jBool out.data "ready" == some true)
        out.data.compress,
       check "a past defer discloses the elapsed deferral in the envelope notes"
        (out.notes.any (fun n => (n.splitOn "already past").length > 1))
        (String.intercalate " | " out.notes)]
  | .error e =>
    o := o ++ [check "a past defer keeps deferUntil in the echo and stays workable"
      false s!"{e.code.wire}: {e.message}"]
  -- untitled rows (reachable only via merge): a freed row omits title, a
  -- dep critical row carries the empty title
  let dirU ← freshDir
  let victim ← mkIssue dirU "Titled blocker"
  let victim2 ← mkIssue dirU "Downstream leaf"
  IO.FS.writeFile (System.FilePath.mk dirU / "log" / "1zzzzzzzzzzzz.jsonl")
    (foreignLine (.create "aaaabbbbccccdddd" {}) 50 "1zzzzzzzzzzzz" "eve" ++ "\n")
  let _ ← run' ["dep", "add", "tl-aaaabbbbccccdddd", "tl-" ++ victim, "--dir", dirU, "--actor", "t"]
  let _ ← run' ["dep", "add", "tl-" ++ victim2, "tl-aaaabbbbccccdddd", "--dir", dirU, "--actor", "t"]
  o := o ++ [← expectData "an untitled freed row omits the title key"
      ["unblocks", "tl-" ++ victim, "--dir", dirU]
    (fun j => jNat j "count" == some 1
      && (jArr j "freed").all (fun r => jKeys r == ["effectiveStatus", "id", "status"])),
   ← expectData "an untitled dep critical row carries the empty title"
      ["dep", "critical", "--dir", dirU]
    (fun j => (jArr j "items").any (fun r =>
        jStr r "id" == some "tl-aaaabbbbccccdddd" && jStr r "title" == some ""
        && jKeys r == ["id", "status", "title", "weight"]))]
  -- dep critical tie-break: equal weights order by id ascending
  let dirT ← freshDir
  let hubA ← mkIssue dirT "First hub"
  let hubB ← mkIssue dirT "Second hub"
  let _ ← mkIssue dirT "Leaf one" ["--blocked-by", "tl-" ++ hubA]
  let _ ← mkIssue dirT "Leaf two" ["--blocked-by", "tl-" ++ hubB]
  let tieOrder := if hubA ≤ hubB then [some ("tl-" ++ hubA), some ("tl-" ++ hubB)]
                  else [some ("tl-" ++ hubB), some ("tl-" ++ hubA)]
  o := o ++ [← expectData "dep critical breaks weight ties by id ascending"
      ["dep", "critical", "--dir", dirT]
    (fun j => ((jArr j "items").map (fun r => jStr r "id")) == tieOrder
      && ((jArr j "items").map (fun r => jNat r "weight")) == [some 1, some 1])]
  -- fail-closed import: '-' is a filename, and a malformed line writes nothing
  let mixedBatch := importRoot / "mixed.jsonl"
  IO.FS.writeFile mixedBatch
    ("{\"id\":\"EXT-1\",\"title\":\"Good line\",\"status\":\"open\"}\nnot json at all\n")
  let dir4 ← freshDir
  o := o ++ [← expectErr "import of the literal filename '-' is not-found"
      ["import", "-", "--dir", dir4] .notFound,
   ← expectErr "a malformed line rejects the whole batch"
      ["import", mixedBatch.toString, "--dir", dir4] .malformedLine,
   ← expectData "the rejected batch wrote nothing"
      ["list", "--all", "--dir", dir4]
    (fun j => jNat j "count" == some 0)]
  let cleanBatch := importRoot / "clean.jsonl"
  IO.FS.writeFile cleanBatch "{\"id\":\"EXT-9\",\"title\":\"Imported solo\",\"status\":\"open\"}\n"
  let dir3 ← freshDir
  o := o ++ [← expectData "a clean import keeps the shape with empty disclosures"
      ["import", cleanBatch.toString, "--source", "ext", "--dir", dir3]
    (fun j => jKeys j == ["disclosures", "issues", "ops", "replica", "source"]
      && (jArr j "disclosures").isEmpty)]
  return o

/-- Init/import placement boundaries (ADR-0012): a bare repository — any
    gitdir layout — refuses with a teaching usage error, from its root, from
    inside it, and through `import`'s implicit init; a normal repo subdir
    still places at the toplevel; `--dir` into anywhere is never refused.
    The `GIT_CEILING_DIRECTORIES` placement stop needs a process boundary
    and lives with the spawned-binary rows (`cliGitEnvTests`). -/
def cliInitBoundaryTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let prev ← IO.currentDir
  let tmp ← IO.FS.createTempDir
  let bare := tmp / "mirror.git"
  let mk ← IO.Process.output { cmd := "git", args := #["init", "--bare", "-q", bare.toString] }
  if mk.exitCode != 0 then
    return [{ name := "git init --bare available", passed := false, msg := mk.stderr }]
  try
    IO.Process.setCurrentDir bare
    o := o ++ [← expectErr "init refuses a bare repository" ["init"] .usage]
    o := o ++ [← (do
      match ← run' ["init"] with
      | .error e => pure (check "the bare-init refusal teaches worktree / --dir / remote"
          ((e.message.splitOn "worktree").length > 1 && (e.message.splitOn "--dir").length > 1
            && (e.message.splitOn "sync remote").length > 1) e.message)
      | .ok _ => pure { name := "the bare-init refusal teaches worktree / --dir / remote",
                        passed := false, msg := "init unexpectedly succeeded" })]
    IO.Process.setCurrentDir (bare / "hooks")
    o := o ++ [← expectErr "init refuses from inside a bare repository" ["init"] .usage]
    -- import's implicit init shares the placement walk and the refusal
    let src := tmp / "seed.jsonl"
    IO.FS.writeFile src "{\"id\":\"EXT-1\",\"title\":\"Seeded\",\"status\":\"open\"}\n"
    IO.Process.setCurrentDir bare
    o := o ++ [← expectErr "import's implicit init refuses a bare repository"
        ["import", src.toString] .usage]
    -- --dir stays the deliberate escape hatch: an explicit target inside the
    -- bare directory is honored, never walked or refused
    o := o ++ [← expectData "init --dir into a bare directory is honored"
        ["init", "--dir", (bare / ".tl").toString]
        (fun j => jBool j "created" == some true)]
    -- a normal repo subdir still places at the toplevel
    let repo := tmp / "proj"
    IO.FS.createDirAll (repo / "src")
    let mk2 ← IO.Process.output { cmd := "git", args := #["init", "-q", repo.toString] }
    if mk2.exitCode != 0 then
      o := o ++ [{ name := "git init available", passed := false, msg := mk2.stderr }]
    else
      IO.Process.setCurrentDir (repo / "src")
      o := o ++ [← expectData "init from a subdir places .tl at the repo toplevel" ["init"]
          (fun j => (jStr j "root").isSome
            && ((jStr j "root").getD "").endsWith "proj/.tl")]
      o := o ++ [check "init created .tl at the toplevel, not the subdir"
        ((← (repo / ".tl").isDir) && !(← (repo / "src" / ".tl").pathExists))]
      -- fuel exhaustion (a >256-deep nest): the placement walk gives up and
      -- falls to the repo-less cwd arm with the local-only note — it does
      -- not throw, and it does not reach the (too-distant) toplevel
      let deep := (List.range 260).foldl (fun p _ => p / "d") repo
      IO.FS.createDirAll deep
      IO.Process.setCurrentDir deep
      o := o ++ [(match ← run' ["init"] with
        | .ok out => check "a depth-exhausted placement walk falls to the cwd arm"
            (((jStr out.data "root").getD "").endsWith "d/.tl"
              && out.notes.any (fun n => (n.splitOn "local-only").length > 1))
            (String.intercalate "|" out.notes)
        | .error e => { name := "a depth-exhausted placement walk falls to the cwd arm",
                        passed := false, msg := e.message })]
    return o
  finally
    IO.Process.setCurrentDir prev

def cliTests : IO (List Outcome) := do
  return (← cliBasicTests) ++ (← cliWorkLoopTests) ++ (← cliCloseGuardTests)
    ++ (← cliDepTests) ++ (← cliReparentTests) ++ (← cliResolutionTests) ++ (← cliUsageTests)
    ++ (← cliReviewTests) ++ (← cliDescriptionTests) ++ (← cliConsistencyTests)
    ++ (← cliReviewBatchTests) ++ (← cliFreeVerbTests) ++ (← cliRenderTests)
    ++ (← cliReadRefreshTests) ++ (← cliDegradedRefreshTests) ++ (← cliRefreshRefusalTests)
    ++ (← cliAutoSyncTests) ++ (← cliPreWriteAbsorbTests)
    ++ (← cliDoctorSkewTests) ++ (← cliDoctorRoutingTests) ++ (← cliDoctorStaleTests) ++ (← cliClaimStealTests) ++ (← cliListStaleTests) ++ (← cliGitFloorTests) ++ (← cliLabelTests) ++ (← cliDefaultLimitTests)
    ++ provenanceAgreementTests
    ++ treeCycleRenderTests ++ canonicalParentTieTests ++ rowAccessorAgreementTests
    ++ (← cliTreeDiamondTests) ++ (← cliTreePrefixDimTests) ++ (← cliHoistedHelperTests)
    ++ (← cliShortIdTests) ++ (← cliSyncPostureTests) ++ (← cliClaimSyncTests)
    ++ (← cliSyncTwoCloneTests) ++ (← cliSyncDegradeTests) ++ (← cliSyncRecoveryTests)
    ++ (← cliSyncFalseCleanTests) ++ (← cliLogSinceTests) ++ (← cliLogUntilTests) ++ (← cliLogTitleTests) ++ (← cliLogTimeTests) ++ (← cliDeferTests) ++ (← cliStealthTests) ++ (← cliListDeferredTests)
    ++ (← cliListStatusTests) ++ (← cliListAssigneeTests) ++ (← cliListPriorityTests) ++ (← cliListBlockedTests) ++ (← cliListFacetComposeTests) ++ (← cliImportTests) ++ (← cliInitBoundaryTests) ++ (← cliShapePinTests) ++ (← cliBinaryTests) ++ (← cliGitEnvTests)

end Tl.Tests
