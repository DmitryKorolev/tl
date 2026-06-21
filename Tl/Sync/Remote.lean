/-
`Tl.Sync.Remote` — the remote leg of `tl sync` (ADR-0001 §5): reconcile this
clone's `refs/tl/log` with a configured remote by `fetch → union → push`.

Layered atop the shared core (`Ref` plumbing, `Merge` join) and run after the
local-first leg (`Local`), per the ADR-0016 build order. The merge commit is
parented on both the local tip and the fetched-remote tip, so the push
fast-forwards; a non-fast-forward rejection (another clone pushed first)
re-fetches, re-unions and retries once, then surfaces `push-rejected`. With no
remote configured the leg is a reported no-op (`no-upstream`) — it never fails
the command, since the local leg already succeeded (ADR-0016 §1).

Remote resolution (ADR-0001 §5): a `tl.remote` git config wins; else the
current branch's upstream remote; else `origin`; a detached HEAD (no branch)
falls through to `origin`/`tl.remote`. The resolved name must have a URL, else
`no-upstream`. Tested I/O shell; no Mathlib.
-/
import Tl.Sync.Local

namespace Tl.Sync

open Tl.Store

/-- What the remote leg did, for the `tl sync` echo and the tests. -/
structure RemoteOutcome where
  /-- Did a remote resolve? (False ⇒ `no-upstream`, reported, not fatal.) -/
  ran : Bool
  /-- The resolved remote name (`""` when `ran` is false). -/
  remote : String
  /-- Did we push new content to the remote? -/
  pushed : Bool
  /-- Did the remote carry content this clone lacked (now in the local ref)? -/
  pulled : Bool
  /-- The resulting `refs/tl/log` tip. -/
  tip : Option String
deriving Repr, Inhabited

/-- Resolve the remote (ADR-0001 §5): `tl.remote` config wins; else the current
    branch's upstream remote; else `origin`; a detached HEAD falls through to
    `origin`. The name must have a configured URL, else `none` (`no-upstream`). -/
def resolveRemote (d : Dirs) : TlM (Option String) := do
  let candidate ← match ← gitConfig d "tl.remote" with
    | some r => pure r
    | none =>
      match ← currentBranch d with
      | some b => pure ((← gitConfig d s!"branch.{b}.remote").getD "origin")
      | none => pure "origin"
  -- reject an option-injection remote name before it reaches any git command (a name
  -- like `--upload-pack=<cmd>` / `--receive-pack=<cmd>` would otherwise be parsed as a
  -- flag, not a positional, by ls-remote/fetch/push → arbitrary exec). The name comes
  -- from .git/config, below the ADR-0014 trust boundary (config-write already grants
  -- code exec via hooks), so this is defense-in-depth, not a boundary; it covers all
  -- three call sites at the single source.
  if candidate.startsWith "-" then return none
  if ← remoteExists d candidate then return (some candidate) else return none

/-- ADR-0001 §5: try the push, retry once on a non-fast-forward rejection
    (re-fetch + re-union), then `push-rejected`. The same bounded budget also
    absorbs a concurrent local-ref move (CAS loss) before the push. -/
private def maxRemoteAttempts : Nat := 2

/-- `pulledAcc` carries the pull signal across retries: once an attempt absorbs
    remote content into the local ref, a later attempt (whose freshly-read local
    ref already has it) must not report `pulled := false`. `push` is the push
    primitive, injected (default `pushRefLog`) so a test can drive the retry budget
    to exhaustion deterministically — reaching the fuel-0 `push-rejected` arm — by
    returning the non-fast-forward signal on every attempt, instead of a flaky
    concurrent-writer race (the design always builds a fast-forward merge, so a
    single real rejection always recovers). -/
private def reconcileRemote (d : Dirs) (remote : String)
    (push : Dirs → String → String → TlM Bool) (pulledAcc : Bool) :
    Nat → TlM RemoteOutcome
  | 0 => throw (.mk' .pushRejected
      s!"the remote '{remote}' refs/tl/log moved during the push and it was rejected after a retry — run `tl sync` again")
  | fuel + 1 => do
    let (remoteTip, remoteSegs) ← fetchRemoteLog d remote
    let localTip ← refTip d
    let localSegs ← readRef d
    let merged := unionSegments localSegs remoteSegs
    let pulled := pulledAcc || !segsEquiv merged localSegs       -- remote had content we lacked
    -- push only when we have content the remote lacks (never an empty-log churn
    -- commit to a fresh remote when there is nothing to share)
    let needPush := !merged.isEmpty && (remoteTip.isNone || !segsEquiv merged remoteSegs)
    if !pulled && !needPush then
      return { ran := true, remote, pushed := false, pulled := false, tip := localTip }
    -- one merge commit descending from both tips ⇒ a fast-forward push; CAS the
    -- local ref to it (so a future sync sees the union and the pushed ref and
    -- local ref agree), retrying if a concurrent local writer moved it
    let parents := ([localTip, remoteTip].filterMap id).eraseDups
    match ← writeRefMergeCas d merged parents localTip with
    | none => reconcileRemote d remote push pulled fuel  -- local ref moved under us: retry
    | some commit =>
      if needPush then
        if ← push d remote commit then
          return { ran := true, remote, pushed := true, pulled, tip := some commit }
        else
          reconcileRemote d remote push pulled fuel  -- non-fast-forward: re-fetch and retry
      else
        return { ran := true, remote, pushed := false, pulled := true, tip := some commit }

/-- The remote leg: resolve a remote and `fetch → union → push` (ADR-0001 §5).
    No remote ⇒ a reported no-op (`ran := false`, `no-upstream`), never an error
    — the local leg is the success on a remote-less worktree (ADR-0016 §1).

    `announce` is a caller-supplied sink fired once with the resolved remote name
    immediately before the first network call, so an interactive sync over a slow
    remote is not silent. It runs only when a remote actually resolves (a
    no-upstream leg stays quiet). The default is a no-op, so the core stays free
    of any UX/stream policy — the CLI layer injects the (sanitized, stderr) printer.

    `push` is the push primitive, defaulting to the real `pushRefLog`; it is a
    parameter only so a test can force the non-fast-forward retry budget to
    exhaustion (the `push-rejected` throw). Production callers omit it. -/
def syncRemote (d : Dirs) (announce : String → IO Unit := fun _ => pure ())
    (push : Dirs → String → String → TlM Bool := pushRefLog) :
    TlM RemoteOutcome := do
  match ← resolveRemote d with
  | none => return { ran := false, remote := "", pushed := false, pulled := false, tip := none }
  | some remote =>
    announce remote
    reconcileRemote d remote push false maxRemoteAttempts

end Tl.Sync
