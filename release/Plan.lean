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

/-- One `name=value` line per channel, in a fixed order. Shell-safe by
    construction: the names are from a closed enumeration and the values are
    `true` or `false`, so nothing here needs quoting or escaping. -/
def renderChannelOutputs (plan : ReleasePlan) : String :=
  String.join (Channel.all.map fun channel =>
    s!"{channel.wire}={if plan.enabled channel then "true" else "false"}\n")

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
