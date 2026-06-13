/-
`Tl.Sync.AutoSync` — the write-path freshness bracket (ADR-0016 §3 amendment +
ADR-0021), composed over the sync legs and exposed to the CLI write verbs.

A write verb brackets `Store.transact` with two best-effort, lock-free steps,
both built from the primitives in `Tl.Sync.Local`/`Tl.Sync.Ref`:

  - `preWriteRefresh` — absorb the shared `refs/tl/log` BEFORE the write's
    guards run (the same `refreshFromRef` reads use), so a directed write by id
    sees a sibling's concurrent write and finds a task that exists only on the
    ref, instead of deciding against a stale view (the double-claim /
    not-found gap). Runs before `transact` takes the mutation lock.
  - `autoSyncLocal` — AFTER `transact` released the lock, when `tl.autosync` is
    on, publish this replica's segment into the ref (and absorb siblings) so a
    worktree sibling sees the write with no explicit `tl sync`. Swallows any
    failure into a non-fatal note (the record is already durable — ADR-0021 §4).

`autoSyncInitDefault` is the `tl init` policy that turns the knob on by default
for a linked worktree. The remote leg stays explicit (`tl sync`).

These carry no CLI types — they return `List String` disclosure notes the verbs
fold into their echo. They live in `Sync` (not the CLI) because they are
compositions of the sync legs, peers of `syncLocal`/`syncRemote`; the `Store`
layer cannot host them (it must not import `Sync`). Tested I/O shell; no Mathlib.
-/
import Tl.Sync.Local
import Tl.Sync.Ref
import Tl.Store.Paths

namespace Tl.Sync

open Tl.Store
open Tl.Clock (Replica)

/-- Absorb the shared ref before a write's guards (the pre-transact local
    absorb, ADR-0016 §3 amendment). Returns the located dirs, the loaded replica
    (reused by `autoSyncLocal`), and a degrade note if the refresh could not run
    (the write proceeds a moment stale, never failing). -/
def preWriteRefresh (dirOverride : Option String) :
    TlM (Dirs × Option Replica × List String) := do
  let d ← discover dirOverride
  let replica ← loadReplica d
  let refresh ← refreshFromRef d (replica.map (·.id))
  let notes := refresh.degraded.toList.map (fun r =>
    s!"wrote against a moment-stale view: could not refresh from the shared ref ({r}) — fix git/filesystem access, then `tl sync`")
  return (d, replica, notes)

/-- Auto-sync (ADR-0021): if `tl.autosync` is on, publish this replica's segment
    into the shared ref (and absorb siblings) so a worktree sibling sees the
    write with no explicit `tl sync`. Best-effort and lock-free — runs after the
    write's lock is released; ANY failure (no git, read-only FS, ref contention
    surviving the CAS retry) is swallowed and disclosed as a non-fatal note,
    NEVER failing the write. Catches both thrown `Tl.Error`s and raw
    `IO.Error`s, mirroring `refreshFromRef`. The remote leg stays explicit. -/
def autoSyncLocal (d : Dirs) (replica : Option Replica) : TlM (List String) := do
  if (← gitConfig d "tl.autosync") != some "true" then return []
  match ← ((syncLocal d (replica.map (·.id))).run.toBaseIO : IO _) with
  | .ok (.ok _) => return []
  | .ok (.error e) =>
    return [s!"auto-sync skipped ({e.message}) — run `tl sync` to publish this write to siblings"]
  | .error ioErr =>
    return [s!"auto-sync skipped ({toString ioErr}) — run `tl sync` to publish this write to siblings"]

/-- The `tl init` auto-sync default (ADR-0021 §5 / ADR-0016 §4): turn
    `tl.autosync` ON for a linked worktree (the local leg is free and the whole
    point of cross-worktree sharing), opt-in elsewhere. Never overrides an
    existing value (a re-init is idempotent on the knob too). Returns the
    guidance note to surface from `init`. -/
def autoSyncInitDefault (d : Dirs) : TlM (List String) := do
  if (← gitConfig d "tl.autosync").isSome then return []
  if ← isLinkedWorktree d then
    if ← gitConfigSet d "tl.autosync" "true" then
      return ["auto-sync on (linked worktree): writes publish to siblings automatically; turn off with `git config tl.autosync false` (ADR-0021)"]
    else return []
  else if ← inGitRepo d then
    return ["auto-sync is off; enable publish-on-write to siblings with `git config tl.autosync true` (ADR-0021)"]
  else return []

end Tl.Sync
