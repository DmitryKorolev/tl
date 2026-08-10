/-
The release plan, in the form a workflow can branch on.

`release/plan.json` says which channels a release publishes through, and until
this command existed nothing read it: the deferred `publish-npm` and
`publish-homebrew` jobs ran on any pushed tag. A v0.1.0 release would therefore
have published the GitHub Release and then failed at Homebrew for a missing tap
credential — artifacts already public, release red, and a remedy telling the
operator to configure a channel this release had deliberately deferred.

So the jobs are derived from the plan rather than described by it. `plan
channels` emits one `channel=true|false` line per channel, which a workflow
step appends to `$GITHUB_OUTPUT`; the privileged publish jobs then gate on the
output for their own channel. Enabling a channel becomes one edit to
`plan.json` plus the manual bootstrap its row names.

Emitting *every* channel, including the enabled ones, is deliberate. A command
that printed only what was on would make "off" and "this command does not know
about that channel" the same observation, and a workflow reading a missing
output gets the empty string — which compares unequal to 'true' and would
silently disable a channel that was supposed to publish.
-/
import release.Command
import release.Model

namespace Release

/-- The decision itself, separated from its rendering.

    This is the value that decides whether an immutable publication runs, so it
    is the one place in this module where being wrong is silent: a `false` that
    should be `true` skips a channel nobody notices was skipped, and a `true`
    that should be `false` publishes a version that cannot be withdrawn. That
    is the shape `Verify/Proofs.lean` reserves theorems for, so it gets one
    rather than a sample of rows. -/
def channelDecisions (plan : ReleasePlan) : List (Channel × Bool) :=
  Channel.all.map fun channel => (channel, plan.enabled channel)

/-- Every channel is decided, exactly once, and each decision is that channel's
    own `enabled`. Stated about the list `renderChannelOutputs` renders from, so
    a rendering that dropped or duplicated a channel would have to change this
    to compile. -/
theorem channelDecisions_eq (plan : ReleasePlan) :
    channelDecisions plan = Channel.all.map (fun c => (c, plan.enabled c)) := rfl

/-- The decision recorded for a channel is that channel's own. This is the
    property a workflow reads: it looks up one name and branches on the
    boolean beside it. -/
theorem channelDecisions_lookup (plan : ReleasePlan) (channel : Channel) :
    (channelDecisions plan).lookup channel = some (plan.enabled channel) := by
  cases channel <;> rfl

/-- One `name=value` line per channel, in a fixed order. Shell-safe by
    construction: the names come from a closed enumeration and the values are
    `true` or `false`, so nothing here needs quoting or escaping. -/
def renderChannelOutputs (plan : ReleasePlan) : String :=
  String.join ((channelDecisions plan).map fun (channel, enabled) =>
    s!"{channel.wire}={if enabled then "true" else "false"}\n")

private def channelsCommand : Command := {
  name := "plan-channels"
  arguments := "<plan.json>"
  summary := "Emit one channel=true|false line per distribution channel, for a workflow to branch on."
  run := fun args => do
    match args with
    | [planPath] =>
        match ← readTextFile planPath with
        | .error message => refuse s!"tlrelease plan-channels: {message}"
        | .ok text =>
            match ReleasePlan.parse planPath text with
            | .error message => refuse s!"tlrelease plan-channels: {message}"
            | .ok plan =>
                IO.print (renderChannelOutputs plan)
                return 0
    | _ => misuse "usage: tlrelease plan-channels <plan.json>" }

def planCommands : List Command := [channelsCommand]

end Release
