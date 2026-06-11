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
  match ← run' (["create", title, "--dir", dir, "--assignee", "tester"] ++ extra) with
  | .ok out => return ((jStr out.data "id").getD "").drop 3 |>.toString
  | .error e => throw (IO.userError s!"create failed: {e.message}")

def cliBasicTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- version
  o := o ++ [← expectData "version payload" ["version"]
    (fun j => jStr j "version" == some "0.1.0" && jNat j "logFormat" == some 1)]
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
  -- create echo (ADR-0020): display id, defaults, provenance, dependencies
  let dir ← freshDir
  o := o ++ [← expectData "create echoes the full issue"
    ["create", "Design the AST", "--dir", dir, "-p", "0", "--assignee", "carol"]
    (fun j =>
      ((jStr j "id").getD "").startsWith "tl-"
      && jStr j "status" == some "open" && jStr j "effectiveStatus" == some "open"
      && jNat j "priority" == some 0 && jBool j "ready" == some true
      && jBool j "isEpic" == some false
      && ((jGet j "provenance").bind (fun p => jStr p "createdBy")) == some "carol"
      && (jStr j "createdAt").isSome && (jStr j "updatedAt").isSome)]
  -- default priority is 2
  o := o ++ [← expectData "create defaults priority 2" ["create", "x", "--dir", dir, "--assignee", "t"]
    (fun j => jNat j "priority" == some 2)]
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
  -- claim refusals: not-ready target, with blockedBy reasons
  o := o ++ [← expectErr "claim of a blocked issue is not-claimable"
    ["claim", "tl-" ++ blocked, "--dir", dir, "--assignee", "carol"] .notClaimable
    (fun e => e.context.any (fun (k, v) =>
      k == "reasons" && ((jGet v "blockedBy").isSome)))]
  -- claim the ready one: outcome won, assignee set
  o := o ++ [← expectData "claim wins and echoes the claim block"
    ["claim", "tl-" ++ blocker, "--dir", dir, "--assignee", "carol"]
    (fun j => jStr j "assignee" == some "carol" && jStr j "status" == some "in_progress"
      && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won")]
  -- show now carries the recent-claim block
  o := o ++ [← expectData "show carries the recent claim block"
    ["show", "tl-" ++ blocker, "--dir", dir]
    (fun j => ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "won")]
  -- already-claimed target refuses with assignee reason
  o := o ++ [← expectErr "claim of an in-progress issue is not-claimable"
    ["claim", "tl-" ++ blocker, "--dir", dir, "--assignee", "dana"] .notClaimable
    (fun e => e.context.any (fun (k, v) =>
      k == "reasons" && ((jGet v "assignee").isSome || (jGet v "status").isSome)))]
  -- close: unblocked carries the freed dependent
  o := o ++ [← expectData "close frees the dependent (unblocked)"
    ["close", "tl-" ++ blocker, "--dir", dir, "--as", "done", "--assignee", "carol"]
    (fun j => jStr j "closeResolution" == some "done" && (jStr j "closedAt").isSome
      && (jArr j "unblocked").any (fun x => x.getStr?.toOption == some ("tl-" ++ blocked)))]
  -- idempotent re-close: succeeds, empty unblocked, still closed
  o := o ++ [← expectData "re-close with the same resolution is a no-op"
    ["close", "tl-" ++ blocker, "--dir", dir, "--as", "done", "--assignee", "carol"]
    (fun j => jStr j "status" == some "done" && (jArr j "unblocked").isEmpty)]
  -- different resolution is a plain rewrite
  o := o ++ [← expectData "re-close with a different resolution rewrites"
    ["close", "tl-" ++ blocker, "--dir", dir, "--as", "cancelled", "--assignee", "carol"]
    (fun j => jStr j "closeResolution" == some "cancelled" && jStr j "status" == some "cancelled")]
  -- update echo
  o := o ++
    [← expectData "update rewrites the title"
      ["update", "tl-" ++ blocked, "--dir", dir, "--title", "Parser v2", "--assignee", "t"]
      (fun j => jStr j "title" == some "Parser v2"),
     ← expectErr "update without flags is usage"
       ["update", "tl-" ++ blocked, "--dir", dir] .usage]
  return o

def cliCloseGuardTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let dir ← freshDir
  let epic ← mkIssue dir "The epic"
  let child ← mkIssue dir "The child" ["--parent", "tl-" ++ epic]
  -- epic --as done refused with openChildren context
  o := o ++ [← expectErr "epic close --as done is not-closeable"
    ["close", "tl-" ++ epic, "--dir", dir, "--as", "done", "--assignee", "t"] .notCloseable
    (fun e => e.context.any (fun (k, v) =>
      k == "reasons" && (jGet v "openChildren").isSome))]
  -- --as cancelled is allowed on an epic
  o := o ++ [← expectData "epic close --as cancelled is allowed"
    ["close", "tl-" ++ epic, "--dir", dir, "--as", "cancelled", "--assignee", "t"]
    (fun j => jStr j "status" == some "cancelled")]
  -- duplicate: stored canonical target renders in display form
  let canonical ← mkIssue dir "The canonical"
  let dupe ← mkIssue dir "The dupe"
  o := o ++
    [← expectErr "self-duplicate is not-closeable"
      ["close", "tl-" ++ dupe, "--dir", dir, "--as", "duplicate", "--of", "tl-" ++ dupe,
       "--assignee", "t"] .notCloseable
      (fun e => e.context.any (fun (k, v) =>
        k == "reasons" && (jGet v "selfDuplicate").isSome)),
     ← expectData "close --as duplicate records the canonical target"
       ["close", "tl-" ++ dupe, "--dir", dir, "--as", "duplicate", "--of", "tl-" ++ canonical,
        "--assignee", "t"]
       (fun j => jStr j "status" == some "cancelled"
         && jStr j "closeResolution" == some "duplicate"
         && ((jGet j "meta").bind (fun m => jStr m "duplicate-of")) == some ("tl-" ++ canonical)),
     ← expectData "duplicate re-close with the same target is a no-op"
       ["close", "tl-" ++ dupe, "--dir", dir, "--as", "duplicate", "--of", "tl-" ++ canonical,
        "--assignee", "t"]
       (fun j => jStr j "closeResolution" == some "duplicate"),
     ← expectData "child close completes the epic by rollup"
       (["close", "tl-" ++ child, "--dir", dir, "--as", "done", "--assignee", "t"])
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
      ["dep", "add", "tl-" ++ a, "tl-" ++ b, "--dir", dir, "--assignee", "t"]
      (fun j => jStr j "type" == some "blocks" && jStr j "from" == some ("tl-" ++ b)
        && jStr j "to" == some ("tl-" ++ a) && jStr j "status" == some "added"),
     ← expectData "dep remove acks removal"
      ["dep", "remove", "tl-" ++ a, "tl-" ++ b, "--dir", dir, "--assignee", "t"]
      (fun j => jStr j "status" == some "removed"),
     ← expectData "second dep remove is a disclosed noop"
      ["dep", "remove", "tl-" ++ a, "tl-" ++ b, "--dir", dir, "--assignee", "t"]
      (fun j => jStr j "status" == some "noop")]
  -- a cycle: A blocked by B, B blocked by A
  let _ ← run' ["dep", "add", "tl-" ++ a, "tl-" ++ b, "--dir", dir, "--assignee", "t"]
  let _ ← run' ["dep", "add", "tl-" ++ b, "tl-" ++ a, "--dir", dir, "--assignee", "t"]
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
     ← expectErr "missing flag value is usage" ["ready", "--dir"] .usage]
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
      (out.stdout == "{\"schemaVersion\":1,\"ok\":true,\"data\":{\"logFormat\":1,\"version\":\"0.1.0\"}}\n")
      out.stdout,
     check "version exits 0" (out.exitCode == 0)]
  -- usage error honors --json anywhere in argv: envelope on stdout, exit 2
  let bad ← spawn ["frobnicate", "--json"]
  o := o ++
    [check "usage error emits the error envelope on stdout"
      (bad.stdout.startsWith "{\"schemaVersion\":1,\"ok\":false,\"error\":{\"code\":\"usage\"")
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
  return o

/-- A canonical foreign-segment line built through the real codec. -/
private def foreignLine (op : WireOp) (hlc : Nat) (actor : String) : String :=
  renderLine { v := supportedVersion, op, stamp := ⟨hlc, 1, 1⟩, actor := some actor }

def cliReviewTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  -- sanitization reaches the payloads (ADR-0014)
  let dir ← freshDir
  let esc := String.singleton (Char.ofNat 0x1b)
  let zwsp := String.singleton (Char.ofNat 0x200B)
  o := o ++
    [← expectData "create echo sanitizes the title"
      ["create", "Red " ++ esc ++ "[31mtext" ++ zwsp ++ "!", "--dir", dir, "--assignee", "t"]
      (fun j => jStr j "title" == some "Red text!")]
  -- '=' in flag values, both spellings
  let a ← mkIssue dir "EqTarget"
  o := o ++
    [← expectData "--title=a=b keeps the embedded '='"
      ["update", "tl-" ++ a, "--dir", dir, "--title=a=b", "--assignee", "t"]
      (fun j => jStr j "title" == some "a=b"),
     ← expectData "--title a=b keeps the embedded '=' (two-token form)"
      ["update", "tl-" ++ a, "--dir", dir, "--title", "x=y", "--assignee", "t"]
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
  let foreignOk := foreignLine (.create "aaaabbbbccccdddd" { title := some "Foreign" }) 99 "eve"
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
  let wres ← run' ["create", "another", "--dir", dir2, "--assignee", "t"]
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
  let _ ← run' ["claim", "tl-" ++ target, "--dir", dir3, "--assignee", "carol"]
  let farFuture := 0x7000000000000000
  let foreignClaim := foreignLine (.claim target "eve") farFuture "eve"
  IO.FS.writeFile (System.FilePath.mk dir3 / "log" / "2zzzzzzzzzzzz.jsonl")
    (foreignClaim ++ "
")
  o := o ++
    [← expectData "a later foreign claim supersedes (replica-relative signal)"
      ["show", "tl-" ++ target, "--dir", dir3]
      (fun j => jStr j "assignee" == some "eve"
        && ((jGet j "claim").bind (fun c => jStr c "outcome")) == some "superseded")]
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

def cliTests : IO (List Outcome) := do
  return (← cliBasicTests) ++ (← cliWorkLoopTests) ++ (← cliCloseGuardTests)
    ++ (← cliDepTests) ++ (← cliResolutionTests) ++ (← cliUsageTests)
    ++ (← cliReviewTests) ++ (← cliBinaryTests)

end Tl.Tests
