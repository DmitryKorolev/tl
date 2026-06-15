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
  -- discovery (ADR-0011 §3): init writes the gitignored primer and SUGGESTS
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
     -- deliberately allowed (the pinned `close --as duplicate [--of <id>]`
     -- surface): a targetless duplicate closes as cancelled/duplicate and
     -- records NO duplicate-of meta — not an oversight
     ← (do
       let loner ← mkIssue dir "Targetless dupe"
       expectData "targetless --as duplicate is allowed (pinned contract)"
         ["close", "tl-" ++ loner, "--dir", dir, "--as", "duplicate", "--assignee", "t"]
         (fun j => jStr j "status" == some "cancelled"
           && jStr j "closeResolution" == some "duplicate"
           && ((jGet j "meta").bind (fun m => jStr m "duplicate-of")).isNone)),
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
    ["parent", "set", "tl-" ++ t, "tl-" ++ e1, "--dir", dir, "--assignee", "t"]
    (fun j => jStr j "parent" == some ("tl-" ++ e1)
      && ((jGet j "reparent").bind (fun c => jStr c "status")) == some "set"
      && ((jGet j "reparent").map (fun c => (jArr c "replaced").isEmpty)) == some true)]
  -- reparent to a second epic replaces the first (replaced lists the old parent)
  o := o ++ [← expectData "parent set replaces the current parent"
    ["parent", "set", "tl-" ++ t, "tl-" ++ e2, "--dir", dir, "--assignee", "t"]
    (fun j => jStr j "parent" == some ("tl-" ++ e2)
      && ((jGet j "reparent").bind (fun c => jStr c "status")) == some "set"
      && ((jGet j "reparent").map (fun c => (jArr c "replaced").any
            (fun x => x.getStr?.toOption == some ("tl-" ++ e1)))) == some true)]
  -- idempotent: already under e2 → noop, appends nothing
  o := o ++ [← expectData "parent set to the current parent is a noop"
    ["parent", "set", "tl-" ++ t, "tl-" ++ e2, "--dir", dir, "--assignee", "t"]
    (fun j => ((jGet j "reparent").bind (fun c => jStr c "status")) == some "noop")]
  -- self-parent is a courtesy usage refusal
  o := o ++ [← expectErr "a task cannot be its own parent"
    ["parent", "set", "tl-" ++ t, "tl-" ++ t, "--dir", dir, "--assignee", "t"] .usage]
  -- detach: parent remove drops the edge; the child becomes a root (no parent)
  o := o ++ [← expectData "parent remove detaches the child (now a root)"
    ["parent", "remove", "tl-" ++ t, "tl-" ++ e2, "--dir", dir, "--assignee", "t"]
    (fun j => ((jGet j "reparent").bind (fun c => jStr c "status")) == some "removed"
      && (jGet j "parent").isNone)]
  o := o ++ [← expectData "a second parent remove is a disclosed noop"
    ["parent", "remove", "tl-" ++ t, "tl-" ++ e2, "--dir", dir, "--assignee", "t"]
    (fun j => ((jGet j "reparent").bind (fun c => jStr c "status")) == some "noop")]
  -- multi-parent: a child born under two epics is reported by doctor (never
  -- rejected); a local `parent set` collapses it to a single parent
  let m ← freshDir
  let me1 ← mkIssue m "M epic one"
  let me2 ← mkIssue m "M epic two"
  let kid ← match ← run' ["create", "multi kid", "--dir", m, "--assignee", "t",
                          "--parent", "tl-" ++ me1, "--parent", "tl-" ++ me2] with
    | .ok out => pure ((jStr out.data "id").getD "")
    | .error e => throw (IO.userError s!"create failed: {e.message}")
  o := o ++ [← expectData "doctor reports a born multi-parent" ["doctor", "--dir", m]
    (fun j => (jArr j "checks").any (fun c =>
      jStr c "name" == some "graph" && jNat c "multiParent" == some 1))]
  let _ ← run' ["parent", "set", kid, "tl-" ++ me1, "--dir", m, "--assignee", "t"]
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
  -- a sibling's concurrent claim, later than ours but WITHIN the skew window
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
  -- the claim COMMAND itself discloses supersession in its human line (parity
  -- with close): a reopened issue keeps its assignee, so it is ready (status
  -- Open) yet a higher-stamped foreign claim outranks the fresh one on the
  -- assignee LWW — current ≠ actor, so "Claimed …" would be a lie
  let dir3b ← freshDir
  let tgt2 ← mkIssue dir3b "Reassigned"
  let base ← nowMs
  let seg := foreignLine (.claim tgt2 "eve") ((base + 20000) * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 1 ++ "\n"
          ++ foreignLine (.reopen tgt2) ((base + 40000) * 2 ^ 16) "2zzzzzzzzzzzz" "eve" 2 ++ "\n"
  IO.FS.writeFile (System.FilePath.mk dir3b / "log" / "2zzzzzzzzzzzz.jsonl") seg
  match ← run' ["claim", "tl-" ++ tgt2, "--dir", dir3b, "--assignee", "carol"] with
  | .error e => o := o ++ [check "superseded claim is reachable via the command" false s!"unexpected: {e.message}"]
  | .ok out =>
    let outc := (jGet out.data "claim").bind (fun c => jStr c "outcome")
    o := o ++
      [check "claim command reports superseded in JSON" (outc == some "superseded") s!"outcome={outc}",
       check "claim command discloses supersession in the human line"
         ((out.human.splitOn "superseded").length == 2) out.human]
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
      ["create", "Titled", "--dir", dir, "--assignee", "t",
       "--description", "line one\nline two"]
      (fun j => jStr j "description" == some "line one\nline two"),
     -- a trailing `-` AND `--description <text>` name two body sources: a usage
     -- conflict, caught before any IO (so it never reaches stdin)
     ← expectErr "a trailing - with --description <text> is a usage conflict"
       ["create", "X", "--dir", dir, "--assignee", "t", "--description", "text", "-"] .usage]
  let exe := (← IO.currentDir) / ".lake" / "build" / "bin" / "tl"
  unless ← exe.pathExists do
    return o ++ [{ name := "binary present for stdin rows", passed := false,
                   msg := "run `lake build` first" }]
  let sh (script : String) : IO IO.Process.Output :=
    IO.Process.output { cmd := "sh", args := #["-c", script] }
  let q (s : String) : String := "'" ++ s ++ "'"
  let hasDesc (out body : String) : Bool := (out.splitOn s!"\"description\":\"{body}\"").length == 2
  let noDesc (out : String) : Bool := (out.splitOn "\"description\"").length == 1
  -- ADR-0017 §8 (amended 2026-06-14): WITHOUT the `-` sentinel, stdin is NOT
  -- read — the body stays absent even with data on the pipe. The regression
  -- guard for the hang: an unrequested stdin is never consumed.
  let nodash ← sh s!"printf 'from\nstdin' | {q exe.toString} create NoDash --dir {q dir} --assignee t --json"
  o := o ++ [check "no sentinel: piped stdin is NOT read (body absent)" (noDesc nodash.stdout) nodash.stdout]
  -- `--description -` reads the body from stdin
  let viaFlag ← sh s!"printf 'from\nstdin' | {q exe.toString} create ViaFlag --dir {q dir} --assignee t --description - --json"
  o := o ++ [check "--description - reads the body from stdin" (hasDesc viaFlag.stdout "from\\nstdin") viaFlag.stdout]
  -- a trailing `-` reads the body from stdin (same request as --description -)
  let viaDash ← sh s!"printf 'from\nstdin' | {q exe.toString} create ViaDash --dir {q dir} --assignee t --json -"
  o := o ++ [check "a trailing - reads the body from stdin" (hasDesc viaDash.stdout "from\\nstdin") viaDash.stdout]
  -- `--description <text>` is the literal body; stdin is left untouched
  let lit ← sh s!"printf 'ignored' | {q exe.toString} create Lit --dir {q dir} --assignee t --description flagged --json"
  o := o ++ [check "--description <text> is the body; stdin untouched" (hasDesc lit.stdout "flagged") lit.stdout]
  -- `-` with empty stdin leaves the description absent
  let emptyDash ← sh s!": | {q exe.toString} create EmptyDash --dir {q dir} --assignee t --json -"
  o := o ++ [check "- with empty stdin leaves the body absent" (noDesc emptyDash.stdout) emptyDash.stdout]
  -- the hang guard: a held-open, non-EOF stdin WITHOUT `-` must not block — tl
  -- returns promptly without reading it. On a regression it would block until
  -- the 5s holder closes the write end; the timing bound catches that.
  let fifo := s!"{dir}-holdpipe"
  let t0 ← IO.monoMsNow
  let held ← sh s!"mkfifo {q fifo}; sleep 5 > {q fifo} 2>/dev/null & {q exe.toString} create Held --dir {q dir} --assignee t --json < {q fifo}; rm -f {q fifo}"
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
  -- the LWW state in BOTH directions (the bare-hlc comparison bug class)
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
  -- a symlinked log/ refuses the LISTING (not just the later per-file opens)
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
  -- (1) a STALE present clock is floored by the own-segment max: craft an own
  -- segment with a high HLC, set the clock file far below it, then a write
  -- must mint ABOVE the own max (no own-replica LWW regression).
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
      ["create", "new", "--dir", dir, "--assignee", "t"]
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
       ["create", "child", "--dir", dir3, "--blocked-by", "tl-" ++ x, "--blocked-by", "tl-" ++ x, "--assignee", "t"]
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
       -- the own segment now has the meta ops; show --json must keep BOTH keys
       match ← run' ["show", "tl-" ++ m, "--dir", dir4] with
       | .ok out =>
         let metaCount := match jGet out.data "meta" with
           | some (Json.obj kvs) => kvs.toArray.size
           | _ => 0
         pure (check "two control-char meta keys both survive the projection"
           (metaCount == 2) s!"meta member count {metaCount}")
       | .error e => pure { name := "meta keys both survive", passed := false, msg := e.message })]
  -- (#12) a close that loses LWW to a later foreign write echoes
  -- consistently: status NOT closed and unblocked empty (no "Closed" lie)
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
      ["close", "tl-" ++ blkr, "--dir", dir5, "--as", "done", "--assignee", "t"]
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
  let _ ← run' ["close", "tl-" ++ a, "--dir", dir, "--as", "done", "--assignee", "t"]
  o := o ++
    [← expectData "reopen returns a closed issue to open, clearing resolution"
      ["reopen", "tl-" ++ a, "--dir", dir, "--assignee", "t"]
      (fun j => jStr j "status" == some "open" && (jStr j "closeResolution").isNone),
     -- idempotent: reopening an already-open issue is a disclosed no-op
     ← expectData "reopen of an already-open issue is a no-op"
       ["reopen", "tl-" ++ a, "--dir", dir, "--assignee", "t"]
       (fun j => jStr j "status" == some "open")]
  -- stats: the pinned counts
  o := o ++
    [← expectData "stats counts by state + ready/blocked/cycles"
      ["stats", "--dir", dir]
      (fun j => jNat j "total" == some 2 && jNat j "open" == some 2
        && jNat j "ready" == some 1 && jNat j "blocked" == some 1
        && jNat j "cycles" == some 0)]
  -- §7: green marks the workable (ready) count, NOT the stored-open count
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
  -- list defaults to open-only; --all includes closed
  let _ ← run' ["close", "tl-" ++ b, "--dir", dir, "--as", "done", "--assignee", "t"]
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
  let aId ← match ← run' ["create", "shared via read-refresh", "--dir", aDir, "--assignee", "a"] with
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
    materialize fails), the read still serves — a moment stale — AND discloses
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
  let _ ← run' ["create", "first task", "--dir", aDir, "--assignee", "a"]
  let _ ← run' ["sync", "--dir", aDir]
  -- B reads once: this materializes A's segment, creating B's log dir + ref-mark.
  let _ ← run' ["list", "--dir", bDir, "--json"]
  -- the ref moves AGAIN; now B's mark trails the tip, so B's next read must
  -- materialize — but with B's log dir read-only the writeback fails and the
  -- refresh degrades (read the ref, can't write the segment).
  let _ ← run' ["create", "second task", "--dir", aDir, "--assignee", "a"]
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
  let _ ← run' ["create", "off by default", "--dir", aDir, "--assignee", "a"]
  o := o ++ [← expectData "auto-sync off: a sibling does not see an unpublished write"
    ["list", "--dir", bDir, "--json"] (fun j => jNat j "count" == some 0)]
  -- (b) auto-sync on: the next write auto-publishes; B sees it with no `tl sync`.
  let _ ← gitC ["config", "tl.autosync", "true"]
  let onId ← match ← run' ["create", "on, auto-published", "--dir", aDir, "--assignee", "a"] with
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
  let res ← run' ["create", "write outlives a failed publish", "--dir", aDir, "--assignee", "a"]
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

/-- Pre-transact absorb (ADR-0016 §3 amendment): a directed write by id refreshes
    from the shared ref BEFORE its guards run, so it finds a task that exists
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
  let aId ← match ← run' ["create", "made by A", "--dir", aDir, "--assignee", "a"] with
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
    refresh now routinely materializes sibling segments, so a single CORRUPT
    sibling segment must be DISCLOSED, not fail a worktree whose own state is
    fine/empty — the all-refused throw only fires with no own replica to anchor
    a partial read. -/
def cliRefreshRefusalTests : IO (List Outcome) := do
  let mut o : List Outcome := []
  let root ← IO.FS.createTempDir
  let _ ← (IO.Process.output { cmd := "git", args := #["-C", root.toString, "init", "-q"] } : IO _)
  let bDir := (root / ".tl").toString
  let _ ← run' ["init", "--dir", bDir]  -- B: own replica minted, no own segment
  -- a sibling publishes a CORRUPT segment into the shared ref
  let badRid := (Tl.Clock.Replica.ofNat 13).id
  let dB : Tl.Store.Dirs := { base := root.toString, tlRel := ".tl" }
  let _ ← (Tl.Sync.writeRef dB [⟨badRid, "this is not json\n".toUTF8⟩] none).run
  -- B reads: refresh materializes the corrupt sibling, and the read DISCLOSES
  -- the foreign refusal and SUCCEEDS (exit 0) rather than failing the command
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
  -- a WRITE against the deferred foreign op discloses it too (not only reads)
  let wrote ← run' ["create", "local work", "--dir", dir, "--assignee", "t"]
  o := o ++ [(match wrote with
    | .ok out => check "a write whose guard fold dropped a deferred op discloses it"
        (out.notes.any (fun n => (n.splitOn "held back").length > 1))
        (String.intercalate "|" out.notes)
    | .error e => { name := "write discloses deferred", passed := false, msg := e.message })]
  -- a clock notably ahead but WITHIN the 24h window: its op FOLDS (count 1, not
  -- deferred) yet doctor still WARNS — the warn threshold is decoupled from the
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
    the `label list` vocabulary, and the `tl list --label` facet (AND across
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
  -- distinctive titles, not ids: human rows now render SHORT ids (whose length
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
  -- nest under BOTH siblings: whichever renders non-last yields a `|   `
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
  let cycOut := String.intercalate "\n" (treeForest Style.plain vCyc [a] (fun _ => true))
  -- a shared root: r1 and r2 both roots, r2 also a child of r1
  let r1 := "c000000000000000"
  let r2 := "d000000000000000"
  let sShared := Tl.Kernel.fold [
    Op.create r1 stA { title := some "R1" }, Op.create r2 stB { title := some "R2" },
    Op.edgeAdd (r1, r2, .Parent) stE1]
  let vShared := mkView sShared
  let sharedOut := String.intercalate "\n" (treeForest Style.plain vShared [r1, r2] (fun _ => true))
  [ check "a parent cycle renders the ↺ marker, not the diamond marker"
      (((cycOut.splitOn "↺").length - 1 ≥ 1) && !(cycOut.splitOn "(shown above)").length.blt 0) cycOut,
    check "the cycle marker is distinct from the already-shown marker"
      (!((cycOut.splitOn "(shown above)").length - 1 ≥ 1)) cycOut,
    check "a root already shown in an earlier subtree renders one marked line"
      (((sharedOut.splitOn "(shown above)").length - 1 == 1)
        && ((sharedOut.splitOn "R2").length - 1 == 2)) sharedOut ]

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
  -- a parent edge to an ABSENT child (dangling): parentEdges drops it, so the
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
  -- a NON-EMPTY prov so `v.provFor` (reads the provH hash copy) is checked
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
  -- the tree view caps rendered ROWS, not roots: one epic + 6 children is 7 rows
  -- under a single root, so `--limit 3` shows 3 rows + a truncation footer — NOT
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

def cliTests : IO (List Outcome) := do
  return (← cliBasicTests) ++ (← cliWorkLoopTests) ++ (← cliCloseGuardTests)
    ++ (← cliDepTests) ++ (← cliReparentTests) ++ (← cliResolutionTests) ++ (← cliUsageTests)
    ++ (← cliReviewTests) ++ (← cliDescriptionTests) ++ (← cliConsistencyTests)
    ++ (← cliReviewBatchTests) ++ (← cliFreeVerbTests) ++ (← cliRenderTests)
    ++ (← cliReadRefreshTests) ++ (← cliDegradedRefreshTests) ++ (← cliRefreshRefusalTests)
    ++ (← cliAutoSyncTests) ++ (← cliPreWriteAbsorbTests)
    ++ (← cliDoctorSkewTests) ++ (← cliLabelTests) ++ (← cliDefaultLimitTests)
    ++ provenanceAgreementTests
    ++ treeCycleRenderTests ++ canonicalParentTieTests ++ rowAccessorAgreementTests
    ++ (← cliTreeDiamondTests) ++ (← cliTreePrefixDimTests) ++ (← cliHoistedHelperTests)
    ++ (← cliShortIdTests) ++ (← cliBinaryTests)

end Tl.Tests
