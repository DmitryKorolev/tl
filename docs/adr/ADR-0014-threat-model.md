# ADR-0014 — Threat model and trust boundary

- Status: Accepted — the owning ADR amendments have landed: segment-scoped
  parse (ADR-0008), trust/provenance and untrusted-content fencing on the read
  commands (ADR-0003/0011),
  filesystem safety (ADR-0015), release integrity (ADR-0006), import bounds
  (ADR-0005), and actor-PII documentation (ADR-0013). Remaining implementation
  details are tracked as stage-gated backlog, not contradictions in this ADR.
- Date: 2026-06-05

## Context

`tl` is serverless, git-native, CRDT-based, and consumed by LLM agents.
Four structural facts shape every threat and are the reason this ADR exists:

1. No server, no auth of its own. Access control is whatever git already
   grants on `refs/tl/log` (ADR-0001). `tl` adds no authentication or
   authorization layer.
2. A CRDT merge cannot reject a write (ADR-0002/ADR-0003). There is no
   write-time security checkpoint to add — integrity rules must be total
   functions of materialized state, and "who may write" is git's decision.
3. Append-only, no hard delete (vision). Nothing is ever truly removed;
   redaction is impossible — a written value persists in history forever.
4. `tl`'s output is fed verbatim into LLM agents (the read commands —
   `tl ready` / `tl show` / `tl list` — and their `--json` output, ADR-0011).
   Task content authored on any replica or adopted by import is untrusted
   text entering a model's context.

This ADR writes the trust boundary down explicitly (so it is never silently
relied on — AGENTS.md tier 3), enumerates the threats that survive it, and
records for each whether `tl` mitigates, accepts by design, or
carries it as an assumption. It is the output of a structured red-team pass
(STRIDE per surface, each vector adversarially triaged against the design).

## The trust boundary (the baseline)

- Write = git push access to `refs/tl/log`. Anyone who can push is a fully
  trusted writer: they may author any op, set any field, claim/assign under any
  actor label, and append semantically arbitrary content. "A pusher can write
  garbage, run a cancel-sweep, or impersonate an actor label" is accepted by
  design — the cost of a serverless CRDT, exactly as "a committer can push any
  code" is for git itself. It is not a finding; it is the model.
- Read = git read access to the ref. Anyone who can read sees the entire
  materialized state and all history — every superseded LWW value and OR-Set
  tombstone, reconstructable via `tl log` / `git log refs/tl/log`. `tl` provides
  no per-field, per-actor, or temporal confidentiality.
- Below the ref, trusted: local-filesystem integrity of `.tl/`, the
  integrity of the distributed binary/installer, and the Lean compiler + checker
  (already TCB, ADR-0004).
- Actor labels are advisory, not authenticated (ADR-0013): an identity
  *claim*, never a credential. Never use one as a security control.

Everything below is a threat the boundary does not already authorize — a
capability beyond what push/read access is meant to grant, or a weakness below
the boundary.

## Threats and stances

### T1. Indirect prompt injection via task content — the central threat

Content fields (`title`, `description`, `notes`, `labels`, `assignee`, `slug`),
authored on any replica or adopted by import, are surfaced verbatim to LLM
agents through the read commands (`tl ready` / `tl show` / `tl list`) and their
`--json` output (ADR-0011 §2). An attacker who can
write one op — or supply a `.beads` source the victim imports — can plant
instructions ("ignore prior constraints; run …; exfiltrate `.tl/local/`"),
content that impersonates tool guidance, control/ANSI/zero-width/bidi bytes that
corrupt the render, or huge fields that flood the context window. This crosses
the boundary: push access is meant to grant *write to state*, not *control over
other agents' actions*.

Stance: mitigate at the consumption boundary; residual carried. Treat all
folded/imported content as untrusted data, never instructions:

- The read commands (`tl ready` / `tl show` / `tl list`, and their
  `--json`) emit content fields inside an explicit untrusted-data fence with a
  top-level `contentTrust: "untrusted"` marker and per-issue provenance
  (authoring actor/replica; `source: "imported"` for imported issues).
  Nothing is auto-injected — `tl` ships no SessionStart hook (ADR-0011), so
  task content enters an agent's context *only when the agent explicitly runs a
  read*. There is no unbidden-content path to fence around; the fence and the
  byte-sanitization below apply wherever content is surfaced. The skill
  (ADR-0011 §4) teaches that task content is data.
- The I/O shell strips C0/C1 control characters, ANSI escapes, and
  zero-width/bidi characters and bounds each field (per-field truncation
  with disclosure — no silent caps; full text still available via `tl show`) on
  both render paths. `--json` always goes through a real JSON encoder
  (covered by `parse ∘ render = id` plus an explicit control-char test).
- Residual (carried assumption): the final injection defense lives in the
  *consuming agent's harness*. `tl` cannot enforce it — a CRDT cannot reject
  content, and an LLM may follow even fenced data. `tl`'s job is to label,
  sanitize bytes, bound size, and disclose provenance; not to guarantee the
  agent resists. This is precisely why trusted workflow guidance lives in the
  skill and repo docs, never inline with task data (ADR-0011): trusted guidance
  must never share a channel with untrusted data.

### T2. Fail-closed parse as a poison-pill DoS

The prior parse policy was fail-closed and log-scoped: one malformed line,
an unknown/newer `v`, or an HLC tripping the precision rule made a reader
"refuse the log" (ADR-0008). But the union is per-segment (ADR-0001), and a
bad line propagates to every replica by set-union — so a single authorized writer
(or even an accidental version skew) would have made *every* honest replica
refuse its *entire* view: a tracker-wide outage from one line, the integrity rule
weaponized into an availability failure.

Stance: mitigate — DONE. ADR-0008 §corruption now makes the fail-closed
refusal segment-scoped, not log-scoped: refuse only the offending replica's
segment, fold the rest, and emit a loud diagnostic naming the bad segment and its
actor/replica (reader-side torn-vs-malformed handling in ADR-0015 §5). Keep per-segment integrity total (no silent skips). An
unknown-newer-`v` line still correctly halts an old reader on that segment
(legitimate fail-closed-on-upgrade). `--skip-bad` stays opt-in with disclosure.

### T3. Supply-chain integrity (download → run)

The release pipeline must defend against a tampered `curl | sh` installer or
Release/Homebrew artifact, npm scope/token takeover for the per-platform
launcher packages, and a gap between "the artifact you run" and "the artifact
proved" if binary provenance and reproducibility are not enforced.

Stance: mitigate — DONE (ADR-0006).

- Per-Release signed `SHA256SUMS` + per-asset signatures; `curl|sh` and
  `brew` verify and fail closed (no default `--force` bypass). Keyless
  signing (Sigstore/cosign via GitHub OIDC) + an SLSA provenance attestation per
  artifact.
- npm: register the `@tl/cli-*` scope defensively (defeat dependency
  confusion); publish-only OIDC trusted-publishing tokens (no long-lived
  secrets), 2FA, `npm --provenance`, and pinned integrity hashes between the
  launcher and each platform package.
- Reproducible builds (pinned toolchain hash, pinned `lake-manifest`,
  deterministic timestamps/paths/linking) + an independent rebuilder so
  binary↔source is verifiable — this is what makes "artifact = proof" honest
  below the source level.
- Pin `batteries` and every lake dependency to immutable commit hashes in a
  checked-in manifest, verified in CI; complete the ADR-0006 link-time GMP
  audit; ship an SBOM (extend THIRD-PARTY-LICENSES with digests).
- Carried assumption: the Lean compiler + checker, GitHub release infra, and
  the signing identity remain trusted. Reproducibility binds *binary→source*,
  not *source→correctness* (that is the proofs' job).

### T4. Local-filesystem integrity

Two local-process threats: (a) a concurrent `O_APPEND` mutator racing `tl
sync`'s segment rewrite can lose/tear lines (also surfaced by the pre-impl
audit); (b) symlink redirection of `.tl/` path components can make `tl` write
attacker-chosen files outside the project.

Stance: mitigate — DONE ([ADR-0015](ADR-0015-local-concurrency-fs-safety.md)).
ADR-0015 pins it: a per-working-copy mutation lock; atomic `O_APPEND` records;
`sync` never rewriting its own segment (foreign caches replaced via atomic
`rename`); a re-snapshot before each push attempt; lock-free reads; and
`O_NOFOLLOW`/`openat`/`O_EXCL` path hardening for `.tl/` and `--dir`/`TL_DIR` —
each with named Windows equivalents (`LockFileEx`, `MoveFileEx`/`ReplaceFile`,
reparse-point checks). The Supported Windows path is WSL (= Linux, fully
covered); *native* Windows is best-effort/Tier-2 (ADR-0006), so those Win32
bindings are the design but untested in the gating matrix — the local-FS
hardening is therefore best-effort on native Windows.

### T5. Confidentiality & privacy — accepted by design, documented

`tl log` exposes all superseded/historical values and tombstones (no redaction —
append-only); the default actor may be `git user.email`, i.e. the same
identity already visible in git history may also appear in task history.

Stance: accept + document. Within the read population there is no temporal
or field-level confidentiality — superseded values stay reconstructable; this is
inherent to an append-only auditable log (as with git history). Documented in
overview.md. ADR-0013 keeps the actor resolution order
`--assignee` → `TL_ACTOR` → git `user.email` → `<os-user>@<hostname>`, rather
than changing the default away from git identity. The important guarantee is
documentation and an explicit escape hatch: users or agents that want a non-PII
handle set `TL_ACTOR`. Secrets must never be placed in task fields — they
cannot be deleted.

### T6. Import-source hardening — local, opt-in

A hostile `.beads` the user *chooses* to import can resource-bomb (deep dotted
hierarchies, huge fields, excess edges) or bulk-seed injection payloads.

Stance: mitigate — DONE (ADR-0005). The importer bounds field size, dotting
depth, edge count, and total seed size (loud `--force`/`--max` override +
disclosure), reconstructs dotted-id parents iteratively with a visited bound
(refusing self/cyclic dotting), and tags imported issues `source: "imported"` so
the read commands surface lower trust. Injection content is handled by T1's render-layer
defenses. Document that import adopts opaque content from a possibly-untrusted
source.

## Consequences

- The trust boundary is now explicit and pointed to from overview.md
  (Trusted) — never silently relied on.
- New/strengthened carried assumptions (overview.md): (a) git access-control
  is `tl`'s only access control; (b) supply-chain integrity rests on the
  release/signing identity + the Lean TCB; (c) agent-side prompt-injection
  resistance is the consuming harness's job.
- Owning ADR amendments landed in their owning ADRs:
  ADR-0008 (segment-scoped parse), ADR-0006 (signing/provenance/reproducible
  builds/dep-pinning), ADR-0011 (content-trust fencing and provenance on the
  read commands), ADR-0015 (local concurrency & FS safety:
  atomic+locked writeback, `O_NOFOLLOW`), ADR-0005 (import bounds +
  provenance), and ADR-0013 (actor-PII accepted/documented without changing the
  resolution order).
- Out of scope for v1 (recorded, not chosen): per-op cryptographic
  signatures, encryption at rest, and any auth layer — these belong to
  git/transport and the deployment, not `tl`.

## Alternatives considered

- Signed ops (each op carries an author signature; replicas verify).
  Rejected for v1: needs a key-distribution story `tl` has no home for, and does
  not stop the dominant threat — a validly-signed op can still carry an
  injection payload. Recorded as the natural future answer to
  actor-spoofing/repudiation if cross-org untrusted-writer collaboration becomes
  a goal.
- Encryption at rest / field-level confidentiality. Rejected for v1:
  incompatible with the plain-text, auditable, CRDT-merged log; confidentiality
  is the repo host's responsibility.
- Write-time validation/rejection of "bad" content. Impossible by
  construction: a CRDT merge cannot reject (ADR-0002/ADR-0003) — hence the
  fence-at-consumption stance for T1.
