/-
`Tests.CrossTests` — the cross-checks that tie the proofs to the bytes
(ADR-0004, overview §Tested), and the registry recording what each one is
evidence *about*.

Every row samples the *compiled* code. What differs between rows is what a green
sample establishes, and ADR-0004 separates three kinds:

- `proved` — a statement proved over `Tl/Kernel`'s source, re-checked against the
  compiled function. A disagreement means compilation stopped preserving the
  theorem; it is never evidence about the property itself.
- `tested` — a delegation the kernel makes to the shell, which no theorem
  discharges: that the canonical wire strings compare bytewise in the order the
  kernel proves over the decoded `(hlc, replica, nonce)` triple.
- `observed` — which branch the compiled code took: that the SCC certificate is
  accepted, so the fast path ran and the proved fallback is not what produced
  the answer.

`sampledProperties` pairs each sampled property with one of those, and a `proved`
row names its statement as an elaboration-resolved `Name`, so a renamed or
retired theorem fails this build instead of leaving a claim to a proof that is
gone. `crossEvidenceTests` then checks that registry against the
`tl:cross-evidence` block in ADR-0004 in both directions: the ADR carries the
properties and their kinds, this file carries the names, and neither holds a
second copy of the other.

What this file must keep covering — the property list, the crafted fixtures that
stay alongside the seeded corpus, and the rule that strengthening is additive
while *narrowing* is an ADR edit — is stated in ADR-0004 under "The
compiled-kernel cross-check, as a contract". The numeric parameters stay here and
are named there: `seeds`, `genOps`, `idPool`, `sampleStamps`. Renaming one of
those, or dropping a fixture class, means editing that section in the same
change; a cross-check quietly reduced to the cases that still pass is the failure
the contract exists to prevent.
-/
import Tl.Format.Codec
import Tl.Kernel.Apply
import Tl.Kernel.Ready
import Tl.Kernel.Theorems
import Tl.Kernel.Ranking
import Tl.Kernel.Unblocks
import Tl.Kernel.Rollup
import Tl.Kernel.Cycles
import Tl.Kernel.RollupFast
import Tl.Kernel.ReadyFast
import Tl.Kernel.CyclesFast
import Tests.Harness

namespace Tl.Tests

open System (FilePath)
open Lean (Name)
open Tl.Format
open Tl.Kernel
open Tl.Crdt

/-! ## The evidence a sample carries -/

/-- What one sampled row is evidence *about*. Three kinds, because ADR-0004
    separates three; calling all of them `proved` is the drift this registry
    replaces. -/
inductive Evidence where
  /-- A re-check of a statement proved over `Tl/Kernel`'s source. The name is
      resolved at elaboration (``` ``name ```), so retiring or renaming the
      statement fails the build rather than leaving a claim to a proof that is
      gone. For a totality claim the named statement is the definition itself:
      Lean accepts only total definitions, so its elaboration *is* the proof and
      there is no separate theorem to name. -/
  | proved (statement : Name)
  /-- A delegation the kernel makes to the shell, which no theorem discharges. -/
  | tested (reason : String)
  /-- An observation about which branch the compiled code took. -/
  | observed (reason : String)

/-- The word ADR-0004's evidence block uses for this kind. -/
def Evidence.kind : Evidence → String
  | .proved _ => "proved"
  | .tested _ => "tested"
  | .observed _ => "observed"

/-- The kind and what backs it, for the assertion name — so the one copy of a
    theorem name both pins at compile time and prints in the run. -/
def Evidence.render : Evidence → String
  | .proved statement => s!"proved: {statement}"
  | .tested reason => s!"tested: {reason}"
  | .observed reason => s!"observed: {reason}"

/-! ## 1. The seeded stamp corpus (encoding order-preservation) -/

private def sampleStamps (seed n : Nat) : List Stamp :=
  sample seed n (fun s =>
    let (s1, h) := nextNat s (2 ^ 64)
    let (s2, r) := nextNat s1 (2 ^ 64)
    let (s3, x) := nextNat s2 (2 ^ 128)
    ((⟨h, r, x⟩ : Stamp), s3))

/-- The near-ties that exercise each tie-break level of the stamp order, kept
    alongside the seeded stamps: their *absence* from a random corpus would be
    invisible. -/
private def craftedStamps : List Stamp :=
  [⟨5, 5, 5⟩, ⟨5, 5, 6⟩, ⟨5, 6, 5⟩, ⟨6, 5, 5⟩,
   ⟨5, 5, 2 ^ 128 - 1⟩, ⟨5, 2 ^ 64 - 1, 0⟩, ⟨2 ^ 64 - 1, 0, 0⟩, ⟨0, 0, 0⟩]

/-- Wire order = decoded order on one pair (fixed widths mean the `.` separators
    never decide a comparison). -/
private def wireOrderAgrees (a b : Stamp) : Bool :=
  let sa := tagOfStamp a
  let sb := tagOfStamp b
  (compare sa sb == .lt) == decide (TotalOrd.lt a b)
    && (sa == sb) == decide (a = b)

/-- The pairs on which the wire order and the decoded order disagree. -/
private def wireOrderFailures : List String :=
  let stamps := craftedStamps ++ sampleStamps 0xbeef 60
  stamps.flatMap (fun a => stamps.filterMap (fun b =>
    if wireOrderAgrees a b then none else some s!"pair ({tagOfStamp a}, {tagOfStamp b})"))

/-! ## 2. The seeded op corpus (compiled kernel vs spec) -/

private def idPool : List IssueId :=
  ["a000000000000000", "b000000000000000", "c000000000000000", "d000000000000000",
   "e000000000000000", "f000000000000000", "g000000000000000", "h000000000000000"]

/-- A seeded random op (over a small id pool, so edges/cycles collide often). -/
private def genOp (s : Nat) : Op × Nat :=
  let (s1, kind) := nextNat s 7
  let (s2, i) := nextNat s1 idPool.length
  let (s3, j) := nextNat s2 idPool.length
  let (s4, h) := nextNat s3 1000
  let id := idPool.getD i ""
  let other := idPool.getD j ""
  let st : Stamp := ⟨h, s4 % 5, s4 % 97⟩
  let op := match kind with
    | 0 => Op.create id st {}
    | 1 => Op.setFields id st { status := some (if h % 2 == 0 then .Done else .InProgress) }
    | 2 => Op.edgeAdd (id, other, .Blocks) st
    | 3 => Op.edgeAdd (id, other, .Parent) st
    | 4 => Op.edgeRemove (id, other, .Blocks) (FinSet.singleton st)
    | 5 => Op.labelAdd id "tag" st
    | _ => Op.metaSet id st "k" (some "v")
  (op, s4)

private def genOps (seed n : Nat) : List Op := sample seed n genOp

/-- An observational fingerprint: equal fingerprints ⇔ equal materialized
    behavior on every projection a command reads. -/
private def fingerprint (s : State) : String :=
  let issues := s.presentIssues.map (fun i =>
    let d := s.issueData i
    s!"{i}|{statusWire d.statusOf}|{d.priorityOf.val}|{d.labels.presentElements}|" ++
    s!"{statusWire (s.effectiveStatus i)}")
  let edges := s.presentEdges.map (fun (f, t, k) => s!"{f}->{t}:{edgeKindWire k}")
  String.intercalate ";" issues ++ "#" ++ String.intercalate ";" edges

private def seeds : List Nat := (List.range 25).map (0xc0ffee + 7919 * ·)

/-- One seeded corpus row: the ops, the state they fold to, and the derived
    views the properties read — computed once per seed and shared by every
    property, so adding a property costs one pass and not one corpus. -/
private structure Corpus where
  seed : Nat
  ops : List Op
  s : State
  /-- The first half of the log, for the join laws. -/
  half : State
  now : Nat
  rdy : List IssueId
  rollup : AMap IssueId Status

private def corpora : List Corpus :=
  seeds.map (fun seed =>
    let ops := genOps seed 40
    let s := fold ops
    let now := 500
    { seed, ops, s, half := fold (ops.take 20), now,
      rdy := s.ready now, rollup := s.effStatusAll })

/-- Sortedness by the proved ranking order. -/
private def rankSorted (s : State) : List IssueId → Bool
  | a :: b :: rest => s.readyLe a b && rankSorted s (b :: rest)
  | _ => true

/-! ## 3. The registry: each sampled property and its evidence -/

/-- One sampled property: what it claims, what kind of evidence the sample is,
    and the instances it failed on (empty = it held). -/
structure Sampled where
  /-- The property, in the words ADR-0004's evidence block uses. -/
  key : String
  evidence : Evidence
  /-- The failing instances, given the shared corpus. -/
  failures : List Corpus → List String

/-- A property checked on every corpus row; it reports the seeds it failed on,
    which is enough to reproduce (the corpus is seeded, never random). -/
private def onEverySeed (key : String) (evidence : Evidence)
    (holds : Corpus → Bool) : Sampled :=
  { key, evidence,
    failures := fun cs => (cs.filter (fun c => !holds c)).map (fun c => s!"seed {c.seed}") }

-- The certificate-branch acceptance below reads the production entry points
-- `State.cyclesCertAccepted`/`precCyclesCertAccepted` directly (no hand-rolled
-- successor mirror that silently goes stale when the production wiring changes —
-- a refactor flips these instead).
def sampledProperties : List Sampled :=
  [ onEverySeed "the fold is insensitive to the order ops arrive in"
      (.proved ``fold_perm)
      (fun c => fingerprint (fold c.ops.reverse) == fingerprint c.s),
    onEverySeed "re-delivering the whole log changes nothing"
      (.proved ``fold_append_self)
      (fun c => fingerprint (fold (c.ops ++ c.ops)) == fingerprint c.s),
    onEverySeed "join commutativity, as far as a state fingerprint observes it"
      (.proved ``State.merge_comm)
      (fun c => fingerprint (State.merge c.s c.half) == fingerprint (State.merge c.half c.s)),
    onEverySeed "join idempotence, as far as a state fingerprint observes it"
      (.proved ``State.merge_idem)
      (fun c => fingerprint (State.merge c.s c.s) == fingerprint c.s),
    onEverySeed "every ready issue is present, open, non-epic and unblocked"
      (.proved ``mem_ready_iff)
      (fun c => c.rdy.all (fun i =>
        c.s.presentIssues.contains i
        && (c.s.issueData i).statusOf == .Open
        && !c.s.isEpic i
        && (c.s.blockersOf i).all (c.s.blockerDischarged ·))),
    onEverySeed "the ready queue is sorted by the proved ranking order"
      (.proved ``State.ready_sorted)
      (fun c => rankSorted c.s c.rdy),
    onEverySeed "unblocks is exactly the ready-set difference"
      (.proved ``State.mem_unblocks_iff)
      (fun c => c.s.presentIssues.all (fun i =>
        c.s.unblocks c.now i ==
          ((c.s.withClosed i).ready c.now).filter (fun x => !(c.rdy.contains x)))),
    -- Totality is the definition's own property: evaluating the rollup on
    -- whatever cyclic and dangling graph the generator produced must terminate
    -- and return a status, on every present issue.
    onEverySeed "the rollup is total on cyclic and dangling graphs"
      (.proved ``State.effectiveStatus)
      (fun c => c.s.presentIssues.all (fun i =>
        match c.s.effectiveStatus i with
        | .Open | .InProgress | .Done | .Cancelled => true)),
    onEverySeed "the batched rollup agrees with the spec rollup"
      (.proved ``State.effStatusWith_eq)
      (fun c => c.s.presentIssues.all (fun i =>
        State.effStatusWith c.rollup c.s i == c.s.effectiveStatus i)),
    onEverySeed "the batched readiness check agrees with the spec"
      (.proved ``State.isReadyWith_eq)
      (fun c => c.s.presentIssues.all (fun i =>
        State.isReadyWith c.rollup c.s c.now i == c.s.isReady c.now i)),
    onEverySeed "the fast ready queue agrees with the spec queue"
      (.proved ``State.readyFast_eq)
      (fun c => State.readyFast c.rollup c.s c.now == c.s.ready c.now),
    onEverySeed "the fast unblocks agrees with the spec"
      (.proved ``State.unblocksFast_eq)
      (fun c => c.s.presentIssues.all (fun i =>
        State.unblocksFast c.s c.now i == c.s.unblocks c.now i)),
    onEverySeed "the fast why agrees with the spec"
      (.proved ``State.whyFast_eq)
      (fun c => c.s.presentIssues.all (fun i =>
        State.whyFast c.rollup c.s i == c.s.why i)),
    onEverySeed "the bucketed why the CLI calls agrees with the spec"
      (.proved ``State.whyFastH_eq)
      (fun c => c.s.presentIssues.all (fun i =>
        State.whyFastH (State.blocksByTarget c.s.presentEdges) (hashSetOf c.s.presentIssues)
          (hashAssoc c.rollup.toList) c.s c.s.presentIssues.length i == c.s.why i)),
    onEverySeed "the fast cycle witnesses agree with the spec"
      (.proved ``State.cyclesFast_eq)
      (fun c =>
        State.cyclesFast c.s .Blocks == c.s.cycles .Blocks
        && State.cyclesFast c.s .Parent == c.s.cycles .Parent),
    onEverySeed "the fast readiness-deadlock witnesses agree with the spec"
      (.proved ``State.precCyclesFast_eq)
      (fun c => State.precCyclesFast c.rollup c.s == c.s.precCycles),
    -- The hoisted forms are what the CLI calls with one shared present/edge
    -- scan. `cyclesFast` unfolds to `cyclesFastWith` at these arguments; the
    -- deadlock form additionally swaps the shipped `parentEdgesFast` for
    -- `parentEdges`, which is the named theorem's content.
    onEverySeed "the pre-hoisted view forms agree with the state-derived forms"
      (.proved ``State.parentEdgesFast_eq)
      (fun c =>
        State.cyclesFastWith c.s.presentIssues c.s.presentEdges .Blocks
            == State.cyclesFast c.s .Blocks
        && State.cyclesFastWith c.s.presentIssues c.s.presentEdges .Parent
            == State.cyclesFast c.s .Parent
        && State.precCyclesFastWith c.rollup c.s.presentIssues c.s.presentEdges
            c.s.parentEdges c.s == State.precCyclesFast c.rollup c.s),
    { key := "the canonical wire strings compare in the decoded stamp order"
      evidence := .tested "the encoding is the shell's, and the kernel delegates it"
      failures := fun _ => wireOrderFailures },
    onEverySeed "the cycle certificate accepts Tarjan's partition, so the fast branch runs"
      (.observed "which branch the compiled code took is not a statement any theorem makes")
      (fun c =>
        State.cyclesCertAccepted c.s .Blocks && State.cyclesCertAccepted c.s .Parent
          && State.precCyclesCertAccepted c.rollup c.s) ]

/-- Every registry row, run over the shared corpus. One row per property rather
    than one per seed: a failure then names the property *and* the seeds, where a
    per-seed row conjoining every property named only the seed. -/
def sampledPropertyTests : List Outcome :=
  let cs := corpora
  sampledProperties.map (fun p =>
    let failed := p.failures cs
    check s!"{p.key} [{p.evidence.render}]" failed.isEmpty
      s!"{failed.length} sampled instances disagreed ({String.intercalate ", " (failed.take 4)}); the corpus is seeded, so each replays exactly")

/-! ## 4. SCC fixtures: the certificate fast path on known graphs

`sampledProperties` checks the compiled `cyclesFast`/`precCyclesFast` against
the compiled spec on random multisets; these fixtures additionally pin the
expected witnesses on known graphs (the deterministic-witness contract) and
assert the certificate accepts Tarjan's partition. The fast branch being
taken is covered by tests, never by a proof (SccFast.lean) — a silent
permanent fallback would read as a performance regression with no error. -/

private def fixtureState (ids : List IssueId) (edges : List Edge) : State :=
  let creates := (List.range ids.length).map (fun n =>
    Op.create (ids.getD n "") ⟨n + 1, 0, n⟩ {})
  let adds := (List.range edges.length).map (fun n =>
    Op.edgeAdd (edges.getD n ("", "", .Blocks)) ⟨100 + n, 0, n⟩)
  fold (creates ++ adds)

def sccFixtureTests : List Outcome :=
  -- a 3-cycle with a tail: one witness, the tail outside it
  let ring := fixtureState ["a", "b", "c", "d"]
    [("a", "b", .Blocks), ("b", "c", .Blocks), ("c", "a", .Blocks),
     ("d", "a", .Blocks)]
  -- two 2-cycles joined by a bridge: two witnesses, in present order
  let twin := fixtureState ["a", "b", "c", "d"]
    [("a", "b", .Blocks), ("b", "a", .Blocks),
     ("c", "d", .Blocks), ("d", "c", .Blocks), ("b", "c", .Blocks)]
  -- a self-loop is a cycle; the isolated node is not
  let selfLoop := fixtureState ["a", "b"] [("a", "a", .Blocks)]
  -- a parent 2-cycle: a structural cycle and a readiness deadlock (each
  -- epic waits on the other as its live child)
  let parentCycle := fixtureState ["e", "f"]
    [("e", "f", .Parent), ("f", "e", .Parent)]
  -- mutual blocking: no structural parent cycle, but a ≺-deadlock
  let mutualBlock := fixtureState ["a", "b"]
    [("a", "b", .Blocks), ("b", "a", .Blocks)]
  -- a dangling edge endpoint is inert (ADR-0003 §5): no cycle through it
  let dangling := fixtureState ["a"] [("a", "z", .Blocks), ("z", "a", .Blocks)]
  [check "3-cycle + tail: one Blocks witness [a b c]"
    (State.cyclesFast ring .Blocks == [["a", "b", "c"]]
      && State.cyclesFast ring .Blocks == ring.cycles .Blocks),
   check "two 2-cycles + bridge: witnesses [[a b] [c d]]"
    (State.cyclesFast twin .Blocks == [["a", "b"], ["c", "d"]]
      && State.cyclesFast twin .Blocks == twin.cycles .Blocks),
   check "self-loop: witness [a] only"
    (State.cyclesFast selfLoop .Blocks == [["a"]]
      && State.cyclesFast selfLoop .Blocks == selfLoop.cycles .Blocks),
   check "parent 2-cycle: structural witness [e f]"
    (State.cyclesFast parentCycle .Parent == [["e", "f"]]
      && State.cyclesFast parentCycle .Parent == parentCycle.cycles .Parent),
   check "parent 2-cycle: readiness deadlock [e f]"
    (State.precCyclesFast parentCycle.effStatusAll parentCycle == [["e", "f"]]
      && State.precCyclesFast parentCycle.effStatusAll parentCycle
        == parentCycle.precCycles),
   check "mutual blocking: deadlock witness [a b]"
    (State.precCyclesFast mutualBlock.effStatusAll mutualBlock == [["a", "b"]]
      && State.precCyclesFast mutualBlock.effStatusAll mutualBlock
        == mutualBlock.precCycles),
   check "dangling endpoints are inert: no witnesses"
    (State.cyclesFast dangling .Blocks == ([] : List (List IssueId))
      && State.precCyclesFast dangling.effStatusAll dangling
        == ([] : List (List IssueId))),
   check "certificate accepted on every fixture (fast branch taken)"
    ([ring, twin, selfLoop, parentCycle, mutualBlock, dangling].all (fun s =>
      State.cyclesCertAccepted s .Blocks && State.cyclesCertAccepted s .Parent
        && State.precCyclesCertAccepted s.effStatusAll s))]

/-- The checker must reject wrong candidates — without these the rejection
    branch (and the proved fallback behind it) is dark code in the compiled
    suite, since Tarjan's output is always accepted. -/
private def succOfPairs (pairs : List (IssueId × IssueId)) (i : IssueId) :
    List IssueId :=
  (pairs.filter (·.1 == i)).map (·.2)

def checkerRejectionTests : List Outcome :=
  -- a 3-cycle a→b→c→a with a tail d→a
  let nodes := ["a", "b", "c", "d"]
  let pairs := [("a", "b"), ("b", "c"), ("c", "a"), ("d", "a")]
  let succ := succOfPairs pairs
  -- a 2-chain (no cycle)
  let chainN := ["a", "b"]
  let chainS := succOfPairs [("a", "b")]
  [check "checker rejects a merged component (tail folded into the cycle)"
    (!(sccCertOk nodes succ [["a", "b", "c", "d"]])),
   check "checker rejects an anti-topological component order"
    (!(sccCertOk chainN chainS [["a"], ["b"]])),
   check "checker accepts the emission-ordered chain (rejection control)"
    (sccCertOk chainN chainS [["b"], ["a"]]),
   check "checker rejects missing coverage"
    (!(sccCertOk chainN chainS [["a"]])),
   check "proved fallback path agrees on a known graph"
    (State.sccWitnessesF nodes nodes.length succ == [["a", "b", "c"]])]

def crossTests : List Outcome :=
  sampledPropertyTests ++ sccFixtureTests ++ checkerRejectionTests

/-! ## 5. The registry vs ADR-0004's evidence block

The ADR states which properties this file must keep sampling and what kind of
claim each sample is; the registry above holds the theorem names. This guard
fails when the two disagree in either direction — a property added here and not
recorded there, one recorded there and no longer sampled, or one whose evidence
kind changed on one side only. Nothing reads a copy: the ADR block is parsed, and
the registry is the same list the assertions run through. -/

private def adrPath : FilePath := "docs/adr/ADR-0004-verified-kernel-tcb-boundary.md"

private def hasSubstr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The `tl:cross-evidence` rows of a document, blank lines dropped. The
    boundaries must be the HTML-comment sentinels themselves, not prose that
    mentions the marker text, so the region cannot be hijacked by the document
    around it. -/
private def evidenceRegion (lines : List String) : List String :=
  let afterStart := (lines.dropWhile
    (fun l => !(l.startsWith "<!--" && hasSubstr l "tl:cross-evidence start"))).drop 1
  let region := afterStart.takeWhile
    (fun l => !(l.startsWith "<!--" && hasSubstr l "tl:cross-evidence end"))
  region.filter (fun l => !(l.trimAscii.isEmpty))

/-- One block row: ``- `kind` — property``. Anything else is a malformed row
    rather than a silently skipped one. -/
private def parseEvidenceLine (line : String) : Except String (String × String) :=
  let l := line.trimAscii.toString
  if !(l.startsWith "- `") then
    .error s!"not an evidence row (expected \"- `kind` — property\"): '{line}'"
  else match (l.drop 3).toString.splitOn "` — " with
    | [kind, key] =>
      if ["proved", "tested", "observed"].contains kind then .ok (kind, key.trimAscii.toString)
      else .error s!"unknown evidence kind '{kind}' (proved/tested/observed): '{line}'"
    | _ => .error s!"malformed evidence row (missing the '` — ' separator): '{line}'"

/-- What the block and the registry disagree about. -/
private structure Drift where
  /-- The (kind, property) rows the block recorded. -/
  recorded : List (String × String)
  parseErrors : List String
  /-- Sampled here, absent from the block. -/
  unrecorded : List (String × String)
  /-- Claimed by the block, no longer sampled here. -/
  unsampled : List (String × String)
  duplicated : List (String × String)

/-- Compare a parsed block against a registry. Pure, so the guard's own refusals
    are tested from planted rows rather than from whatever the tree happens to
    hold (`crossEvidenceGuardTests`). -/
private def evidenceDrift (block : List String) (registry : List (String × String)) :
    Drift :=
  let parsed := block.map parseEvidenceLine
  let recorded := parsed.filterMap (fun | .ok v => some v | .error _ => none)
  { recorded
    parseErrors := parsed.filterMap (fun | .error e => some e | .ok _ => none)
    unrecorded := registry.filter (fun r => !(recorded.contains r))
    unsampled := recorded.filter (fun a => !(registry.contains a))
    duplicated := recorded.filter (fun a => (recorded.filter (· == a)).length > 1) }

private def registryEvidence : List (String × String) :=
  sampledProperties.map (fun p => (p.evidence.kind, p.key))

private def renderRow : String × String → String := fun (kind, key) => s!"`{kind}` — {key}"

/-- The rows a drift report yields, shared by the live check and its own tests. -/
private def driftOutcomes (source : String) (d : Drift) : List Outcome :=
  [check s!"{source} carries a tl:cross-evidence block"
    (!(d.recorded.isEmpty))
    s!"no evidence rows parsed from {source} — markers missing, region empty, or not run from the repo root",
   check s!"every tl:cross-evidence row in {source} is well-formed"
    d.parseErrors.isEmpty (String.intercalate "; " d.parseErrors),
   check s!"every sampled property is recorded in {source} with its evidence kind"
    d.unrecorded.isEmpty
    s!"Tests/CrossTests.lean samples {d.unrecorded.map renderRow}, absent from the tl:cross-evidence block — add the rows there (strengthening is additive)",
   check s!"every tl:cross-evidence row in {source} is a property this file still samples"
    d.unsampled.isEmpty
    s!"{source} claims {d.unsampled.map renderRow}, absent from sampledProperties — restore the check, or narrow the contract in the ADR deliberately",
   check s!"no tl:cross-evidence row in {source} is listed twice"
    d.duplicated.isEmpty s!"duplicated: {d.duplicated.map renderRow}"]

/-- The registry and ADR-0004's `tl:cross-evidence` block agree. -/
def crossEvidenceTests : IO (List Outcome) := do
  if !(← adrPath.pathExists) then
    return [check "cross-evidence: ADR-0004 present at cwd" false
      s!"could not find {adrPath} under cwd {(← IO.currentDir)} — run tltest from the repo root"]
  let content ← IO.FS.readFile adrPath
  let block := evidenceRegion (content.splitOn "\n")
  return driftOutcomes "ADR-0004" (evidenceDrift block registryEvidence)

/-! ### The guard's own refusals

A drift guard that cannot fail is a green row and nothing else, so each arm is
exercised from planted rows: the region reader against a document whose prose
merely names the markers, and the comparison against a block that drops, adds,
duplicates, malforms or re-kinds a row. -/

private def planted : List (String × String) :=
  [("proved", "the fold is insensitive to the order ops arrive in"),
   ("tested", "the canonical wire strings compare in the decoded stamp order")]

private def plantedBlock : List String :=
  ["- `proved` — the fold is insensitive to the order ops arrive in",
   "- `tested` — the canonical wire strings compare in the decoded stamp order"]

private def failedNames (outcomes : List Outcome) : List String :=
  (outcomes.filter (fun o => !o.passed)).map (·.name)

def crossEvidenceGuardTests : List Outcome :=
  let region := evidenceRegion
    ["intro prose",
     "<!-- tl:cross-evidence start -->",
     "- `proved` — one",
     "",
     "- `observed` — two",
     "<!-- tl:cross-evidence end -->",
     "- `proved` — outside the region"]
  -- prose *about* the markers is not a marker: only the comment lines delimit
  let hijacked := evidenceRegion
    ["a line mentioning tl:cross-evidence start in prose",
     "- `proved` — smuggled in",
     "<!-- tl:cross-evidence start -->",
     "- `proved` — one",
     "<!-- tl:cross-evidence end -->"]
  let clean := evidenceDrift plantedBlock planted
  let dropped := evidenceDrift [plantedBlock.headD ""] planted
  let extra := evidenceDrift
    (plantedBlock ++ ["- `proved` — a property nobody samples"]) planted
  let dupe := evidenceDrift (plantedBlock ++ [plantedBlock.headD ""]) planted
  let malformed := evidenceDrift (plantedBlock ++ ["the fold is insensitive"]) planted
  let unknownKind := evidenceDrift
    (plantedBlock ++ ["- `assumed` — something else"]) planted
  -- the kind changing on one side only is the drift this registry exists for:
  -- it must read as both an unrecorded sample and an unsampled claim
  let rekinded := evidenceDrift
    ["- `tested` — the fold is insensitive to the order ops arrive in",
     "- `tested` — the canonical wire strings compare in the decoded stamp order"] planted
  [checkEq "region reader takes the fenced rows only, blanks dropped"
    region ["- `proved` — one", "- `observed` — two"],
   checkEq "prose naming the start marker does not open the region"
    hijacked ["- `proved` — one"],
   check "a block that matches the registry reports nothing"
    (failedNames (driftOutcomes "planted" clean)).isEmpty
    s!"{failedNames (driftOutcomes "planted" clean)}",
   checkEq "a dropped row is reported as unrecorded"
    dropped.unrecorded [planted.getD 1 ("", "")],
   checkEq "an added row is reported as unsampled"
    extra.unsampled [("proved", "a property nobody samples")],
   checkEq "a duplicated row is reported"
    dupe.duplicated [planted.getD 0 ("", ""), planted.getD 0 ("", "")],
   check "a row that is not an evidence row is a parse error, not a skip"
    (malformed.parseErrors.length == 1 && malformed.unsampled.isEmpty)
    s!"{malformed.parseErrors}",
   check "an unknown evidence kind is a parse error"
    (unknownKind.parseErrors.length == 1
      && hasSubstr (unknownKind.parseErrors.headD "") "unknown evidence kind")
    s!"{unknownKind.parseErrors}",
   check "changing a row's kind fails in both directions"
    (rekinded.unrecorded == [planted.getD 0 ("", "")]
      && rekinded.unsampled == [("tested", "the fold is insensitive to the order ops arrive in")])
    s!"unrecorded {rekinded.unrecorded}, unsampled {rekinded.unsampled}",
   check "each drift arm has a failing row of its own"
    ([dropped, extra, dupe, malformed, unknownKind, rekinded].all (fun d =>
      !(failedNames (driftOutcomes "planted" d)).isEmpty))
    "a planted drift produced no failing row"]

end Tl.Tests
