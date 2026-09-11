# Native hermetic runner review

The review examined isolation and process handling, CI/build integration, and
failure-path coverage. It was a single-agent review from those three angles,
supported by mutation tests and real subprocess/container runs.

## Findings addressed

| Finding | Resolution and evidence |
| --- | --- |
| A denied checkout write could be mistaken for a read-only mount. | Require an unambiguous kernel mount entry with the correct, nonconflicting flags for each required mount, then probe writes. Tests mutate missing, duplicate, writable, and conflicting entries. |
| A failed subprocess could lose its stdout diagnostic. | Preserve stdout, stderr, and status for completed commands, including nonzero exits. Real subprocess tests exercise both streams and failure status. |
| Timing out an attached Podman client could leave its evidence container running. | Create a named container, attach within the cleanup scope, and explicitly remove it on success or refusal. Tests cover timeout, nonzero status, missing completion, and removal failures. |
| A log-write failure after successful container creation could bypass cleanup. | Carry logging failure alongside the completed process result and refuse inside the cleanup scope. Tests also ensure a thrown removal error preserves the primary diagnosis. |
| The policy subprocess could exit successfully before completing its gates. | Require its final successful summary to match the number of gates selected by the release plan. Empty, wrong-count, and nonfinal summaries refuse. |
| Linked worktrees could refer to Git metadata outside the checkout mount. | Resolve and mount only the required Git metadata read-only at its existing paths. Tests cover ordinary, linked, separate, malformed, and space-containing paths; the complete native run used a real linked worktree. |

The CI job still invokes the same public native runner. Its authority schema
and exact invocation are checked by the workflow mutation suite. The builder
uses the actual Lake configuration with its release-only option; the launcher
fixture remains byte-identical to the migrated corpus. No Python or Ruby
orchestration was introduced.

## Validation

Implementation and fixes: `2d7b57d` and `059176c`.

- Warning-free full build and verifier build passed.
- Trust verification passed, including independent kernel replay and all 49
  product landmarks.
- The full suite passed 6,518 assertions, including 240 focused runner assertions.
- Strict CI policy passed all eight gates; task-ID lint and whitespace checks passed.
- The native hermetic command passed end to end on macOS through rootless
  Podman, building the Linux static executable and running the restricted
  evidence container from a linked worktree.

New theorem: `Release.Hermetic.completed_iff` characterizes the required
successful status and final completion line.

## Limits

Hosted CI was not rerun for the review fixes. The preceding attempt could not
start jobs because GitHub reported an account billing/spending-limit problem;
this is local validation, not a hosted CI success claim.

Completion markers detect accidental early exits, not deliberate forgery by
the supervised program. The builder's package repositories and normal Lean
toolchain download remain documented build-input assumptions. Abruptly killing
the outer runner itself can prevent cleanup; retained logs name the container
for manual removal. See [ADR-0028](../adr/ADR-0028-release-machinery-architecture.md)
for the isolation and dependency boundaries.
