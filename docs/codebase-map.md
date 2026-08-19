# Codebase map

> Everything mapped here is built: the verified kernel (`Tl/Crdt/`,
> `Tl/Kernel/`) and the tested shell — `Tl/Error`, `Tl/Format/`, `Tl/Hash/`,
> `Tl/Store/` (with the `ffi/tlsys.c` shim), `Tl/Clock/`, `Tl/Sync/`,
> `Tl/Import/`, and `Tl/Cli/`. The line that matters:
> the verified kernel has no I/O, and everything that touches the world is a
> separate, tested shell.

```
Tl.lean                 -- root module; imports everything under Tl/
VERIFYING.md            -- signed-release verification procedure + identity history
release/identity.json   -- machine-readable current repository/workflow/OIDC/npm pin

Tl/Crdt/                -- generic CRDT pieces (verified; join laws — comm/
                        -- assoc/idem — are proved per structure in each file,
                        -- there is no separate Join.lean)
  Order.lean            --   TotalOrd + the Stamp triple (hlc, replica, nonce)
  Map.lean              --   sorted assoc map (AMap) + FinSet, with join laws
  MapFold.lean          --   batched canonical AMap join (mergeSort + adjacent
                        --   collapse, O(N log N)) = the iterated merge
                        --   (joinFast_eq) — the cold-fold core
  Lww.lean              --   LWW register; key is the triple (HLC, replica, nonce)
                        --   (ADR-0002/0007; wire encodings ADR-0007/0008 — 16-hex HLC, 13/26-char Crockford);
                        --   lifted pointwise over a key map = the `meta` CRDT
  OrSet.lean            --   observed-remove set + join laws; tombstones are
                        --   element-scoped (`removed` mirrors `adds` per
                        --   element), so a remove can never cross elements —
                        --   the basis of the unconditional unrelate frame lemma
  Journal.lean          --   the append-only notes journal (ADR-0027): an OR-Set
                        --   keyed by the add-tag + a tag-keyed payload map;
                        --   join laws, add-wins/re-add/remove-exactness/
                        --   no-resurrection, stamp-ascending rendering, payload
                        --   semilattice (lex-max over (text, handle, actor))

Tl/Kernel/              -- the verified core (no I/O)
  State.lean            --   issues OR-Set, edges OR-Set, per-issue field maps,
                        --   labels OR-Set, the notes Journal (ADR-0027), and a
                        --   per-key-LWW `meta` map (ADR-0002); updatedAtStamp =
                        --   max over scalar-register stamps + journal add-tags
  Op.lean               --   the Op inductive; nine deltas (create, setFields,
                        --   metaSet, edgeAdd, edgeRemove, labelAdd, labelRemove,
                        --   noteAdd, noteRemove) — readable CLI verbs map onto
                        --   these in the shell (ADR-0008/0027)
  ClaimWrites.lean      --   the write-set a `claim` lowers to (status:=InProgress,
                        --   assignee:=actor); its own leaf (imports only Op) so the
                        --   codec's claim lowering and the kernel claim-outcome
                        --   proofs share one definition with no proof-module import
  NotesInvariant.lean   --   fold-level discharge of the journal's SelfTagged /
                        --   PayloadTotal invariants for every materialized state
  Apply.lean            --   apply : State → Op → State  (total reducer + fold)
  Ready.lean            --   ready : State → Now → List Id  (total on cyclic and
                        --   dangling graphs; blocker discharged iff its
                        --   effectiveStatus is done|cancelled — epics by rollup);
                        --   critical-path weight = |reach⁺ over blocks| (total);
                        --   why/unblocks = transitive unclosed blockers / freed-set
                        --   (same reach⁺ machinery; total, proved — ADR-0004 thm 10)
  HashMapView.lean      --   the shared Std.HashMap-backed view primitives
                        --   (upstream of ReadyFast/RollupFast/SccFast):
                        --   bucketBy adjacency, presence-set membership,
                        --   amapOfHashMap materialize in O(N log N), and the
                        --   find = getElem? lookup bridge to the AMap spec
  ReadyFast.lean        --   the shipped queue: hoisted present/edge views,
                        --   rollups through the batched map, one RankKey per
                        --   candidate, sort on cached keys, the O(V+E) frontier
                        --   closure (reachBFS, ReachBFS.lean); refinement bridge
                        --   readyFast_eq / unblocksFast_eq / whyFast_eq — the
                        --   fast forms equal the spec, so thm 4/10 transfer
  Cycles.lean           --   per-kind cycle detection (bounded reachClosure
                        --   iteration — total, no well-founded obligation);
                        --   one canonical witness per cyclic SCC = the SCC's
                        --   sorted node set (ADR-0004 thm 6; proved in SccProps);
                        --   also readiness-deadlock ≺-cycles (mixed blocks+parent,
                        --   ADR-0004 thm 5/6) so no stuck live set is undiagnosed
  Rollup.lean           --   effectiveStatus (the spec: fuel form); reads epic's
                        --   stored status first (manual-cancel precedence), else
                        --   derives from children
  RollupSpec.lean       --   rollup meets its ADR-0003 spec (unconditional
                        --   branches) + live-cycle conservatism (cycle members
                        --   are Open at every fuel — the path-cutoff exactness)
  RollupSat.lean        --   fuel saturation ⇒ the unconditional recurrence
                        --   (no acyclicity hypothesis; ascending-chain
                        --   pigeonhole, Mathlib zone like RollupAcyclic)
  RollupFast.lean       --   the shipped rollup: memoized visiting+memo walk
                        --   over a hoisted parent-edge view (effStatusAll, one
                        --   pass per view) + the refinement bridge — pointwise
                        --   equal to the spec (effStatusWith_eq/isReadyWith_eq),
                        --   so every spec theorem transfers; once-per-pass is
                        --   rollupVisit_find_hit (ADR-0003 rollup recursion shape)
  RollupAcyclic.lean    --   rollup fuel-adequacy on acyclic parent graphs
  Invariant.lean        --   Invariant = valid status enum only; endpoint-existence
                        --   and acyclicity deliberately excluded (tolerated at read)
  Theorems.lean         --   convergence + tracker theorems (ADR-0004/0003);
                        --   liveness is one-directional deadlock-freedom, not a biconditional
  FoldFast.lean         --   the shipped cold fold: foldFast joins the deltas'
                        --   component maps by batched construction (O(N log N))
                        --   + the bridge foldFast_eq_fold — equal to fold, so
                        --   every fold theorem transfers (cold path, ADR-0022)
  Frame.lean            --   frame lemmas: meta/labels/notes/relate/unrelate
                        --   move neither ready nor rollup (all unconditional)
  CloseMono.lean        --   close-monotonicity (ADR-0004 thm 7)
  Reach.lean            --   reach⁺ closure; liveness/deadlock + why (thms 5/6/10;
                        --   the kernel's Mathlib zone starts here, ADR-0009)
  ReachBFS.lean         --   the shipped O(V+E) reachability engine: a Std.HashSet
                        --   frontier/worklist closure (reachBFS), proved list-equal
                        --   to the spec reachClosure (reachBFS_eq, nodup seed) and
                        --   membership-equal unconditionally (mem_reachBFS_iff);
                        --   backs why/weight (ReadyFast) + dep cycles (CyclesFast).
                        --   Reach + HashMapView dependent (ADR-0009 reach zone, 0024)
  ReachFrontier.lean    --   proved "processed-once" structure of the reach engine
                        --   (ADR-0023 provable-shape tier): the BFS frontiers
                        --   (reachFrontier) partition the reachable set — disjoint,
                        --   union = reachClosure, each ⊆ presentIssues — so each node
                        --   lands in exactly one frontier. Work-shape tooth over the
                        --   shipped engine: reachBFSgoTrace_flatten_nodup — reachBFSgo's
                        --   real per-round fold inputs flatten dup-free; a Θ(V·E)
                        --   re-scan recursion (nested closures) fails it. (reachBFSgo_eq
                        --   is output-only.) reachExpandTrace_eq is the reference twin.
  Path.lean             --   blocksPath: a total witness-path extractor over present
                        --   blocks edges (the ordered companion to why's reach⁺ set,
                        --   ADR-0004 thm 10 companion). A parent-recording frontier
                        --   BFS — shipped Std.HashSet visited + Std.HashMap parent
                        --   /depth engine (parentSweepH/bfsPathH), bridged to the
                        --   list/AMap reference (parentSweepH_eq); blocksPath_valid
                        --   / blocksPath_isSome_iff. Reach/ReachBFS dependent
  Tarjan.lean           --   unverified fuel-total iterative Tarjan: proposes the
                        --   SCC partition in emission order; never trusted — its
                        --   output is runtime-validated by SccFast's checker, so
                        --   a bug here costs speed (fallback), never correctness
  SccFast.lean          --   the proved SCC certificate checker: over the
                        --   HashMapView hash views (bucketed adjacency,
                        --   presence set), a sound frontier BFS, and the
                        --   acceptance characterizations — sameSCC = component-
                        --   index equality (cert_sameSCC), onCycle = successor-
                        --   in-my-component (cert_onCycle). Soundness only:
                        --   rejection falls back, acceptance-on-real-runs is
                        --   tested (CrossTests), never assumed
  CyclesFast.lean       --   the shipped diagnostics: certificate path
                        --   (sccWitnessesT = Tarjan + checker + witness
                        --   reconstruction — near-linear detection; grouping
                        --   ∝ cyclic×components, a tracked residual — over
                        --   hash-hoisted successor views), proved
                        --   cached-closure fallback
                        --   (sccWitnessesF); bridge cyclesFast_eq /
                        --   precCyclesFast_eq — equal to the spec, thm 6
                        --   transfers; commands compute each result once
  SccProps.lean         --   SCC-witness enumeration: exactly one witness per cyclic SCC
  CycleRepair.lean      --   the dep cycles → dep remove loop terminates: remove-only
                        --   chain of well-formed removes, edge-count measure;
                        --   no-new-cycle + SCC refinement, per-witness progress,
                        --   in-witness edge bound (ADR-0004 thm 11)
  CanonParent.lean      --   canonical display parent (ADR-0003 §4): rank by
                        --   (greatest live add-tag, parentId), pick the max —
                        --   present-edge winner, maximal live rank, order-
                        --   invariance, existence; shared canonParentSelect +
                        --   Edge-keyed hash probe; bridged to the CLI accessor
                        --   (canonicalParentE_eq, ADR-0024 §3)
  Unblocks.lean         --   unblocks = the ready-set diff; exact and unconditional
  Ranking.lean          --   ready-queue ranking; the queue is proved sorted

Tl/Format/              -- I/O shell: wire encodings + on-disk record (tested)
  Crockford.lean        --   Crockford base32 codec (ids, replica, nonce; ADR-0007)
  Record.lean           --   JSONL record envelope: parse/render, preserve-unknown,
                        --   canonical key order + pinned string escaping
                        --   (ADR-0008 §canonical form)
  Codec.lean            --   the record↔Op codec: ParsedOp = the typed WireOp
                        --   (one constructor per ADR-0008 verb — a verb/payload
                        --   mismatch is unrepresentable) + Stamp + actor +
                        --   unknown bag; the kernel Op is the WireOp.toOp
                        --   projection (the verb→delta table, executable);
                        --   covers the full v1 enum, not just stage-1-emitted
                        --   verbs; strictly canonical decode, fail-closed
                        --   malformed-line/unknown-version (priority clamps,
                        --   disclosed); also homes the id-mint core
                        --   (mintId80/mintIssueId/mintNoteId) so the noteRemove
                        --   decoder can re-derive a note id to enforce its
                        --   own-tag singleton (ADR-0027 finding 2)
  Time.lean             --   strict canonical ISO-8601 UTC ↔ epoch-ms codec
                        --   (deferUntil storage + the --json timestamps)
  Version.lean          --   v fail-closed-on-newer; v=0 is malformed, not older;
                        --   destructive log GC ships behind a v bump carried by
                        --   the compacted markers in trimmed segments, which a
                        --   v1 reader refuses per segment as unknown-version
                        --   (ADR-0008; the non-destructive snapshot is the
                        --   no-bump fold cache)
  Ids.lean              --   the tl- display affix; re-exports the id mints from
                        --   Codec (issue-id: leftmost 80 SHA-256 bits over the
                        --   fixed-width preimage, ADR-0018; note-id: behind the
                        --   "note:" domain prefix, two-block preimage, ADR-0027)

Tl/Error.lean           -- the structured error contract: the closed code enum,
                        -- stable wire strings + exit codes, teaching messages,
                        -- ADR-0020 context fields (below Format/Store/Cli so
                        -- every shell layer fails through one type)

.github/workflows/      -- ci.yml mechanizes the correctness gates; release.yml
                        -- builds, signs, and publishes on a SemVer tag. The
                        -- release workflow's own path is part of the signing
                        -- identity (ADR-0006), so moving it is a rotation
scripts/                -- gates that need no toolchain, each with a --selftest
                        -- arm so a checker that stopped detecting cannot pass
                        -- unnoticed: check-task-ids.sh (no tracker ids in
                        -- tracked artifacts), gen-build-provenance.sh (writes Tl/Build/Stamp.lean;
                        -- fails closed on anything it cannot establish),
                        -- verify-release-artifacts.sh (the VERIFYING.md
                        -- procedure as code, run by the release workflow's
                        -- pre-publish check and by its own selftest, so the
                        -- documented steps are the executed ones;
                        -- --require-signature is the gate mode, where the
                        -- TL_INSTALL_SKIP_SIGNATURE escape is refused rather
                        -- than honoured. install.sh does NOT call it — piped
                        -- from curl it has no checkout — and carries its own
                        -- copy of the pin and the shared helpers; the pin is
                        -- guarded by Tests/ReleaseTests.lean and the helpers by
                        -- the installer corpus in Tests/ReleaseToolTests.lean,
                        -- which runs the script over a planted release),
                        -- tlrelease homebrew-render / homebrew-placeholder /
                        -- homebrew-publish (the whole formula rendered from the
                        -- signed manifest, the tracked placeholder rendered
                        -- from release/identity.json + release/targets.json,
                        -- and one idempotent tap update),
                        -- tlrelease npm-manifests / npm-stage / npm-publish /
                        -- npm-bootstrap / npm-selftest (the five package
                        -- manifests rendered from the identity and the target
                        -- list; staging around the signed binaries with every
                        -- one held to the digest the manifest pins; a survey of
                        -- the whole registry followed by resumable publication,
                        -- launcher last, refusing a version whose contents
                        -- differ; the one-time placeholder bootstrap; and the
                        -- real-npm net over packing, install layout and the
                        -- launcher),
                        -- tlrelease version-consistency (one version across the
                        -- tag, productVersion, the lakefile and the pinned test
                        -- literal — the npm manifests are generated at a
                        -- placeholder version and are not among them),
                        -- tlrelease platform-classification (holds the uname
                        -- mappings install.sh and the npm launcher each carry
                        -- inline to release/Platform.lean, cross-checked
                        -- against release/targets.json),
                        -- check-release-policy.sh (all of the above as one
                        -- command, in two profiles: `ci` adds
                        -- check-channel-policy.sh, whose two gates invoke npm
                        -- and ruby for the deferred channels, and
                        -- `release` — what the release workflow runs against
                        -- the tagged commit — does not have them),
                        -- check-release-runtimes.sh (the release profile again,
                        -- with python, python3, ruby, brew, node and npm
                        -- shimmed to fail, each shim proved to fire first)

scripts/lib/            -- shared by the release scripts
  release-common.sh     --   digests, the SHA256SUMS lookup, the file-mode
                        --   reader, the uname mapping, the stub cosign, and
                        --   the selftest and policy-gate harnesses. install.sh
                        --   and npm/tl/bin/tl carry marked copies of the parts
                        --   they need, because neither can source a file from
                        --   this repository at the moment it runs
release/                -- what a release is, machine-readable; ADR-0028 owns
                        -- the release-machinery boundaries and migration end state
  identity.json         --   the signing pin every verifier checks against
  targets.json          --   the distributed targets and their ADR-0006 tiers,
                        --   read by every consumer instead of being repeated
  plan.json             --   which channels this release actually publishes.
                        --   ADR-0006 describes how each channel works; this
                        --   says which are switched on. The publish jobs
                        --   (via `tlrelease plan-channels`) and the external
                        --   prerequisite audit (via `rc_channel_state`,
                        --   which is why that helper is channel-only) are
                        --   both derived from it: a deferred channel has no
                        --   job to run and no prerequisite to be missing. The
                        --   per-commit gate list in check-release-policy.sh is
                        --   NOT derived from it — those gates are hermetic and
                        --   run over every channel's generator on every commit,
                        --   which is what keeps a deferred channel from
                        --   rotting while it is off

install.sh              -- the curl-pipe installer; embeds its own copy of the
                        -- signing pin because it has no checkout to read
Formula/tl.rb           -- (GENERATED) the Homebrew formula at the placeholder
                        -- release, rendered by `tlrelease
                        -- homebrew-placeholder`. Real brew loads, styles and
                        -- audits it in CI, so what brew judges is what a
                        -- release publishes; the release's own formula comes
                        -- from the signed manifest and is never this file
npm/                    -- the npm packages: tl/ is the launcher (POSIX sh, no
                        -- lifecycle script), platform/<target>/ are the four
                        -- binary packages; the binaries are added at release
                        -- time, never committed

Tl/Build/               -- what source this binary was built from (tested)
  Stamp.lean            --   GENERATED by scripts/gen-build-provenance.sh: the
                        --   commit / dirtiness / toolchain / lake-manifest
                        --   digest compiled in. The checked-in copy is the
                        --   development stamp (no commit); the release
                        --   workflow re-stamps it from the tagged commit
  Provenance.lean       --   what the stamp means: Kind (development / dirty /
                        --   clean) and the record both `tl version` renderings
                        --   are total functions of. No `release` kind — a
                        --   binary cannot attest its own release status; the
                        --   Sigstore identity does (ADR-0006)

Tl/Hash/                -- pure hashing for identity minting (tested)
  Sha256.lean           --   FIPS 180-4 transcription returning the full 32-byte
                        --   digest; consumers slice (ids take the leftmost 80
                        --   bits, import widths differ — ADR-0007/0018); the
                        --   fixed-shape state is Vector-typed (Fin-indexed
                        --   constants/schedule/hash words, digestVec carries
                        --   its 32 bytes in the type); vector-tested (FIPS +
                        --   padding boundaries + the worked mint vector)

Tl/Store/               -- I/O shell: local persistence (tested)
  Paths.lean            --   the .tl/ layout + ADR-0012 discovery (walk-up bounded
                        --   by the .git dir-or-file boundary, a bare-gitdir
                        --   layout (isGitDirLayout), + ceiling dirs (ceilingDirs,
                        --   shared with init/import placement);
                        --   --dir/TL_DIR override; T4 validation → unsafe-path);
                        --   Dirs = (base, rel): the base follows symlinks, the
                        --   .tl components never do (ADR-0015 §6); TlM =
                        --   ExceptT Tl.Error IO is the shell failure channel
  Local.lean            --   .tl/local/ replica + clock files: load/persist,
                        --   auto-mint from OS entropy when absent (ADR-0012),
                        --   corrupt-replica/corrupt-clock fail-closed with the
                        --   remove-and-rerun fix; saturation = corrupt-clock
                        --   reason:"saturated" (ADR-0007)
  Lock.lean             --   the mutation lock (bounded lock-busy poll) and the
                        --   locked critical section `transact`: acquire → load
                        --   replica → materialize through the fold cache
                        --   (ADR-0022; a refused own segment fails the write) → read+advance the HLC (the absent-clock
                        --   arm reseeds from max(all-segments line max, now)
                        --   inside the lock) → build (guards refuse before any
                        --   byte) → append → fsync → persist clock → release
                        --   (ADR-0015 §1)
  Segment.lean          --   segment append/enumerate/read; torn-tail skip;
                        --   crash-fragment closing; one O_APPEND write per
                        --   record + fsync (ADR-0008 §corruption, ADR-0015
                        --   §2/§5); enumeration validates log/ through the
                        --   shim walk before listing and only canonical
                        --   replica-id stems count as segments (junk .jsonl
                        --   disclosed, never silently folded or dropped)
  Materialize.lean      --   records → ops → fold into kernel State; segment-
                        --   scoped fail-closed with --skip-bad disclosures
                        --   (incl. the record/segment owner check — a record
                        --   stamped by another replica is a malformed line);
                        --   line-scoped max-HLC scan (the clock reseed); the
                        --   HLC skew window (ADR-0007) — a FOREIGN op dated
                        --   beyond now+W is deferred from the fold and maxHlc
                        --   (own exempt), so a future HLC neither wins LWW nor
                        --   inflates the reseed (passes `now` only on the
                        --   read/write path; pure-fold default off)
                        --   (Tl/Sync composes Store primitives — own-segment
                        --   snapshot under lock, atomic foreign-cache replace —
                        --   rather than owning segment I/O)
  Cache.lean            --   the materialization fold cache (ADR-0022): the
                        --   folded State persisted in gitignored .tl/local/cache,
                        --   keyed per segment on (byteLen, non-crypto
                        --   hash(prefix), lineCount, refused, deferred lines);
                        --   valid ⇒ reads
                        --   and transact fold only appended suffixes + newly-
                        --   admissible deferred lines on top (fold_append +
                        --   order-insensitivity); stale/corrupt/absent ⇒ rebuilt
                        --   from segments, never repaired; persists best-effort
                        --   via atomic replace (doctor reads, never persists;
                        --   --skip-bad bypasses). Only the fold is cached —
                        --   ops/refusals/deferrals/warnings recompute live
  Sys.lean              --   bindings to the native shim (ffi/tlsys.c): no-follow
                        --   + ownership-checked two-part open (the §6 checks
                        --   ride every component of every open), read/write,
                        --   fsync (F_FULLFSYNC on Darwin), fd lock, OS entropy,
                        --   ownership check — mechanism only (ADR-0019); compiled
                        --   with the host cc (the bundled clang ships no macOS
                        --   system-header sysroot — a recorded ADR-0019 deviation)

Tl/Clock/               -- I/O shell: ordering/identity (tested)
  Hlc.lean              --   hybrid logical clock: pure update rules + hex codec
                        --   (file persistence + the recovery branches live in
                        --   Tl/Store/Local and Lock — ADR-0007 §HLC)
  Replica.lean          --   replica-id validation (canonical width/charset/
                        --   64-bit range); minting + persistence live in
                        --   Tl/Store/Local and draw from the shim's OS CSPRNG
                        --   (ADR-0019)
  Skew.lean             --   proved: the HLC skew-window admission predicate
                        --   (admittedB, the exact one the fold branches on) +
                        --   its monotonicity (admitted_mono_now ⇒ deferral is
                        --   eventual) and filter-identity-past-threshold; pure,
                        --   kernel-free (ADR-0007 skew window)
  SkewConverge.lean     --   proved: skew_converges — composes Skew's filter-
                        --   identity with the kernel fold (fold_eq_of_mem_iff)
                        --   ⇒ replicas converge regardless of clock skew

Tl/Sync/                -- I/O shell: refs/tl/log transport (tested)
  Ref.lean              --   read/write refs/tl/log via git plumbing (built): the
                        --   tree is root-level <replica-id>.jsonl blobs, commits
                        --   parent-chained, fixed neutral tl identity, CAS
                        --   update-ref (writeRefCas distinguishes a lost CAS
                        --   race from a real error); blob content is read/written
                        --   as raw bytes (gitBytes), never a lossy String round-
                        --   trip (ADR-0001 §2 in-ref encoding); every spawn goes
                        --   through runBounded, which scrubs the inherited
                        --   routing/config-injection env (scrubbedGitVars,
                        --   ADR-0012 sanitized-subprocess policy)
  Merge.lean            --   per-segment complete-line set union, canonical
                        --   (sorted/deduped) — the CRDT join (built, ADR-0001 §5)
  Local.lean            --   the local-first worktree leg + read-time refresh
                        --   (built, ADR-0016 §1/§3): syncLocal publishes the own
                        --   segment into the shared ref (CAS-retry) and absorbs
                        --   siblings into .tl/log/ via atomic rename, never the
                        --   own segment (`tl sync`); refreshFromRef is the O(1)
                        --   ref-OID trigger (vs the .tl/local/ref-mark) that
                        --   absorbs siblings — best-effort, lock-free, never
                        --   fails — run before every read fold and before every
                        --   write's guards (pre-transact absorb, ADR-0016 §3)
  Ref.lean              --   git ref/config plumbing: refTip/readRef/writeRef
                        --   (CAS), gitConfig/gitConfigSet, isLinkedWorktree
                        --   (--git-dir ≠ --git-common-dir → auto-sync default-on),
                        --   gitToplevel + effectiveRemoteUrl (doctor's
                        --   split-brain + insteadOf-rewrite disclosure)
  Remote.lean           --   the remote fetch / union / push leg (built, ADR-0001
                        --   §5): resolveRemote (tl.remote > branch-upstream >
                        --   origin; detached-HEAD → origin); syncRemote unions
                        --   local+remote into a commit parented on both tips (so
                        --   the push fast-forwards), retries once on a non-ff
                        --   rejection then push-rejected; no remote → no-upstream
                        --   (reported, not fatal). `tl sync` = local leg → remote
                        --   leg → absorb-pulled
  AutoSync.lean         --   the write-path freshness bracket (ADR-0021 +
                        --   ADR-0016 §3), composed over the legs above:
                        --   preWriteRefresh (absorb before a write's guards),
                        --   autoSyncLocal (gated best-effort publish after),
                        --   autoSyncInitDefault (init's linked-worktree default-
                        --   on). No CLI types — the write verbs just call it

Tl/Import/              -- I/O shell: one-shot bulk import (tested, ADR-0005)
  Bulk.lean             --   JSONL records → a deterministic seed op-log under
                        --   a SHA-256-derived single-writer import replica
                        --   (ids/nonces/fallback timestamps source-derived, so
                        --   re-import is byte-stable); dangling edge endpoints
                        --   skipped + disclosed; two safety gates (--force
                        --   clobber, --allow-large/--max bounds). checkBounds =
                        --   the granular net (fixed per-field byte/count bounds +
                        --   an O(n) parent-depth pass over the functional parent
                        --   graph), collect-all fail-closed / --allow-large
                        --   verbatim; checkSeedSize = the 4x-input derived-seed
                        --   backstop; cycles disclosed, never a violation

Tl/Cli/                 -- I/O shell: command dispatch + JSON output (tested)
  Envelope.lean         --   the --json envelope (schemaVersion/ok/data|error) in
                        --   the deliberate member order, + an omit-empty top-
                        --   level notes[] (machine-readable disclosures, 0020)
  Project.lean          --   the read View + issue projections: the full object
                        --   and trimmed rows (omit-empty, display ids, forced-ms
                        --   timestamps), fold-time provenance (cross-op recency
                        --   compares the full Stamp — the LWW order — never the
                        --   bare HLC), dependencies +
                        --   canonical parent, the provenance trust block
                        --   (ADR-0003/0020). View.ofLoaded is the sole View
                        --   constructor in production — the read path, the
                        --   post-write echo, and doctor all derive the hoisted
                        --   collections and their ViewIndex copies through it,
                        --   so the fields cannot drift from the state they
                        --   summarize and that relationship is proved once
                        --   (View.rollup_ofLoaded/present_ofLoaded/edges_ofLoaded
                        --   /issueData_ofLoaded, the last being the indexed field
                        --   the read facets read). The structure constructor
                        --   stays public: the test suite builds views field-by-
                        --   field, so the "one constructor" rule is a property
                        --   of the production call graph, not of the type
  Sanitize.lean         --   the ADR-0014 render sanitizer (ANSI/control/zero-
                        --   width/bidi stripping; 1 KiB / 64 KiB bounds with
                        --   disclosed truncation) — applied on both render paths
  Render.lean           --   human rendering (ADR-0017): the Style surfaces
                        --   (--color/--glyphs/--plain, NO_COLOR, TTY), the
                        --   one-line glyph/color format, the show detail view
                        --   + children tree (total on cyclic parent graphs),
                        --   footer/legend, stats block — never on the --json path
  Resolve.lean          --   id/slug resolution (tl- discriminator, case-fold +
                        --   symbol aliases, prefix/ambiguity — ADR-0007) and the
                        --   ADR-0013 actor chain
  Grammar.lean          --   commandSpecs: the single source of truth for the verb/
                        --   flag grammar — drives the arg parser, `tl help`, and the
                        --   `--json` help schema (root-imported; GrammarTests covers it)
  Commands.lean         --   the stage-1 verbs + the agent-surface/ergonomics
                        --   verbs (reopen/stats/log, sync, label add/remove/list,
                        --   parent set/remove reparenting); the read filter facets
                        --   are shared between `ready` (--label/--assignee) and
                        --   `list` (those plus --status/--priority/--blocked/
                        --   --deferred/--stale) via labelFacet/assigneeFacet/
                        --   applyFacets/filterSuffix, so the two surfaces cannot
                        --   drift (ADR-0020). That facet algebra is pure and
                        --   total, so it is proved here rather than sampled,
                        --   from one characterization: the fold is exactly a
                        --   List.filter by the conjunction of every active
                        --   facet's predicate (applyFacets_eq_filter), which
                        --   pins membership (mem_applyFacets_iff), order and
                        --   multiplicity (applyFacets_sublist), facet-list-order
                        --   independence (applyFacets_of_perm), and the no-op
                        --   reading of an absent flag at list-identity strength
                        --   (applyFacets_eq_self_of_inactive) with its dual that
                        --   a supplied flag is in play (labelFacet_active_iff /
                        --   assigneeFacet_active_iff). Within-facet AND for
                        --   --label and OR for --assignee
                        --   (labelFacet_pred_eq_true_iff /
                        --   assigneeFacet_pred_eq_true_iff, composed in
                        --   mem_readyFacets_iff); the gate stand-down condition
                        --   (facetsBypassGate_eq_true_iff, discharged per facet
                        --   by labelFacet_no_bypass/assigneeFacet_no_bypass, so
                        --   sharing them with `list` — the gate's only consumer,
                        --   and one whose facet list carries five more of its
                        --   own — cannot introduce a bypass). `ready`'s own
                        --   post-facet queue is the named readyRanked, so the
                        --   cross-layer bounds are about the expression cmdReady
                        --   evaluates, and they characterize membership rather
                        --   than only bounding it: a row is on the queue exactly
                        --   when the kernel calls it ready and every supplied
                        --   facet accepts it (mem_readyRanked_iff, with
                        --   mem_readyRanked_ofLoaded_iff discharging the rollup
                        --   hypothesis from View.rollup_ofLoaded), which rules
                        --   out under-reporting as well as widening
                        --   (readyRanked_cannot_widen is the forward half, via
                        --   State.readyFast_eq). Survivors stay ranked
                        --   (readyRanked_sorted, via ready_sorted), and --limit
                        --   is the named readyPage, a prefix of the queue in
                        --   both branches (readyPage_prefix) whose length the
                        --   cap pins (readyPage_length) — the pair is what says
                        --   "uncapped, or the first limit rows", since the
                        --   prefix law alone admits an empty page and the length
                        --   law alone the bottom limit rows; mem_readyPage_ready
                        --   and readyPage_sorted carry the bound and the ranking
                        --   to the rendered page. The list-only --status/
                        --   --priority facets are inline literals in cmdList and
                        --   stay sampled by the CLI rows.
                        --   Write guards run inside the
                        --   locked transact build (not-claimable, not-closeable,
                        --   the idempotent re-close); doctor's check rows. Each
                        --   write verb brackets transact via Sync.AutoSync
                        --   (preWriteRefresh before guards, autoSyncLocal publish
                        --   after — ADR-0016 §3 / ADR-0021)
  Init.lean             --   tl init (idempotent on an existing replica;
                        --   completes a partial .tl; CSPRNG replica mint;
                        --   repo-toplevel placement lives in Commands.cmdInit)
  Main.lean             --   verb dispatch, arg parsing, streams + exit codes
                        --   (ADR-0008 §--json; the root Main.lean stays the
                        --   thin exe entry)

Tests/                  -- outside-TCB checks, run via `lake exe tltest`
  Harness.lean          --   assertion + seeded-generator harness
  JsonUtil.lean         --   shared option-returning JSON accessors for the
                        --   grammar suites (GrammarTests/DocGrammarTests) —
                        --   one definition so they cannot drift apart
  CrockfordTests.lean   --   encode/decode round-trips
  HlcTests.lean         --   HLC update rules + hex codec branches
  RecordTests.lean      --   envelope round-trip + canonical order
  ErrorTests.lean       --   the (code, wire, exit) table + envelope bytes
  Sha256Tests.lean      --   FIPS/boundary vectors + the worked mint vector
  TimeTests.lean        --   instant-codec vectors + strictness rejections
  CodecTests.lean       --   a canonical line per verb, the escape classes,
                        --   fail-closed rows, the priority clamp, a fold smoke test
  SysTests.lean         --   per-branch shim tests (symlinks, locks, entropy, sync)
  StoreTests.lean       --   discovery, transact, crash/hostile adversity, clock
                        --   and replica recovery, lock contention
  CacheTests.lean       --   fold-cache codec round-trip + fail-closed rows,
                        --   every validity branch (path observed via a poisoned
                        --   marker), the cached≡fresh seeded property, file
                        --   lifecycle (healing, doctor non-persist, skip-bad
                        --   bypass, symlink refusal)
  SyncTests.lean        --   the ref-sync legs (fetch/union/push, push-rejection,
                        --   no-upstream) over a local bare remote — the primary
                        --   cover overview.md leans on for the remote sync claim
  CliTests.lean         --   per-verb contract rows + spawned-binary envelope/
                        --   exit/env tests (TL_DIR, ceiling dirs) + the tree
                        --   diamond/cycle/shared-root tree fixtures (shared
                        --   nodes render once and are marked on re-encounter;
                        --   parent cycles keep the distinct cycle marker)
  GrammarTests.lean     --   the commandSpecs grammar: per-verb spec coverage,
                        --   help-text/`--json` schema generation, flag parsing
  DocGrammarTests.lean  --   docs↔grammar drift guard: the fenced shipped-surface
                        --   block in vision.md must equal commandSpecs (so the
                        --   prose can't silently over-promise/under-document verbs)
  ReleaseTests.lean     --   signed-release identity drift guard: the canonical
                        --   repository/workflow/OIDC/npm pins agree across the
                        --   machine-readable policy, VERIFYING.md, and ADRs;
                        --   plus build provenance — every Kind branch of both
                        --   `tl version` renderings (exercised through explicit
                        --   Provenance values, since the compiled stamp is
                        --   fixed) and a drift guard binding the stamped
                        --   toolchain/manifest pins to the files on disk;
                        --   plus release/plan.json's enabled channels and the
                        --   VERIFYING.md sentence stating them, and the rule
                        --   that every privileged release job needs a pushed
                        --   tag — stated over what makes a job privileged
                        --   (a write permission, a secret, or a protected
                        --   environment), so a privileged job added later is
                        --   covered; and ADR-0028's failure propagation: no
                        --   `continue-on-error` and no status function in an
                        --   `if:`, on every privileged job *and* on every job
                        --   producing an output a privileged job or some
                        --   condition acts on — computed transitively through
                        --   `needs.*.outputs.*`, so moving a policy branch one
                        --   job upstream does not move it out of the guard.
                        --   Quoted control keys are normalized; case-varied or
                        --   bracket-form authority references and YAML aliases
                        --   standing in for failure controls, whole steps or
                        --   output mappings fail closed.
                        --   Stricter than ADR-0028's minimum in one stated
                        --   place: step-level `continue-on-error` is refused on
                        --   every step of a bound job rather than only on
                        --   handoff/authentication/policy/publication steps,
                        --   because classifying those lexically would be a list
                        --   of command spellings. The build matrix's
                        --   Best-effort leg stays allowed: unprivileged, and no
                        --   outputs at all
  ReleaseDriftTests.lean --  the guards over statements kept beside the
                        --   release layer: every backticked invocation of
                        --   `tlrelease` in a tracked .md/.sh/.yml must be one
                        --   the command's own `accepts` takes (name a command
                        --   or write an invocation that works — a fragment is
                        --   what rots), and a script that runs policy gates
                        --   must decide a missing tool through `rc_tool_gate`
                        --   alone. Both read the real tree, and the second uses
                        --   Boundary.lean's own lexer, so a comment explaining
                        --   the rule is not a violation of it. Two more that
                        --   are permanent: no release source may recover a
                        --   native error class by matching formatted text
                        --   (`:E…:`), since that makes a message a contract;
                        --   and the release FFI registry — every extern in the
                        --   loaded release environment pinned by declaring
                        --   module, native symbol and full Lean signature, no
                        --   product-prefixed binding, plus the executable's
                        --   linker inputs and the recipe compiling the shim
                        --   from exactly ffi/tlsys.c, which the trust
                        --   verifier's import audit cannot observe
  ReleaseToolTests.lean --   tlrelease: dispatch, the generated usage, and the
                        --   refusals. Driven in-process against release.Cli;
                        --   a refusal must never share an exit status with
                        --   success, which is the failure the port exists to
                        --   prevent. The SBOM's exact bytes are pinned by
                        --   fixtures/sbom-golden.spdx.json, rendered from the
                        --   two committed inputs beside it, so a change to
                        --   what a release describes is a failing row rather
                        --   than a difference inside a signed asset. The
                        --   boundary's spelling corpus lives here too: one
                        --   table of the ways a command can be written — bare,
                        --   relative, absolute, through env/exec/command, after
                        --   an assignment, quoted, both shebang spellings, on
                        --   CRLF lines, malformed shebangs, and the dynamic
                        --   forms the runtime arm owns — with every row
                        --   asserted through the parser and again through the
                        --   public command over a planted checkout, since a
                        --   parser row alone held while the command never
                        --   reached that code
  PerfTests.lean        --   scaling regression rows: ×4 synthetic ops must
                        --   grow ≤ ×12 on all ratio-asserted paths (cold
                        --   batched fold, warm cached materialize, rollup,
                        --   ready, diagnostics, provenance, sync union)
  CrossTests.lean       --   encoding order-preservation (all pairs) + the
                        --   compiled-kernel-vs-spec property cross-check
  SanitizeTests.lean    --   one row per ADR-0014 sanitizer class
  ImportsTests.lean     --   structural: every `.lean` under Tl/ is imported by the
                        --   root module (guards the "invisible to lake build" class)
  VerifyTests.lean      --   trust-verifier report branches, exact source
                        --   inventory/symlink/checkout boundaries, typed verdict
                        --   evidence, import/supervisor policy, stored-body axiom
                        --   propagation, and semantic replay
  VerifyLoadedTests.lean --  real loaded-environment module/declaration selection,
                        --   provenance, direct-import rows, replay closure, injected
                        --   audit evidence, landmarks, and axiom observation wiring
  Main.lean             --   tltest entry point

Verify/                 -- Lean-native trust gate: `lake exe tlverify`
  Report.lean           --   typed semantic/gate evidence and pure policy
                        --   decisions. The seven-case GateScope indexes
                        --   Observation, so a scope's evidence has a type no
                        --   other scope's fits, its human label is read off
                        --   that type, and the run's seven observations are
                        --   assembled through a structure whose fields all
                        --   differ in type
  Policy.lean           --   axiom allowance, ADR-0009 direct-import allowlist,
                        --   and proved-claim landmarks
  Environment.lean      --   typed audit layout (source paths carry their owning
                        --   scope and derive both claims + expected modules;
                        --   gate roots and inventory findings are derived from
                        --   the same registry by scope), classified inventory,
                        --   symlink boundaries, import/axiom inspection, kernel
                        --   replay. A loaded environment is sealed behind a
                        --   private constructor together with the scope it was
                        --   loaded for, so an observation cannot be minted for
                        --   one scope out of another's environment
  Main.lean             --   dynamically loads production, tests, itself, and
                        --   Lean tooling without initializers; worker verdict
  Supervise.lean        --   the completion protocol and the supervision
                        --   decision applied to a spawned worker. The line a
                        --   worker must print last is derived from the
                        --   protocol's own fields (tool, label, protocol
                        --   version), so it reads as a sentence in a CI log and
                        --   there is no second constant to drift from
  Proofs.lean           --   verdict-logic theorems: GateClean + analyze_clean_iff
                        --   per scope, the gate-wide evidence characterisation,
                        --   the worker's verdict-to-exit decision (status zero
                        --   and the completion marker each iff the evidence is
                        --   empty; report and diagnostics both pinned in both
                        --   arms) composed with that
                        --   characterisation into workerVerdict_marker_iff_clean,
                        --   ADR-0009 traversal completeness and per-edge count,
                        --   stored-body axiom propagation exact in both
                        --   directions (sound + complete over an inductive
                        --   Reaches, at a drained exit),
                        --   the supervision status/marker rule, one replay step
  Launcher.lean         --   minimal supervisor requiring the worker's final verdict
  TestLauncher.lean     --   distinct minimal launcher for the test worker's verdict

VerifyFixture/          -- compiled hostile-initializer fixture; never executed
scripts/GenLicenses.lean -- executable Lean tooling, audited as a separate root
```

The `tlrelease` decision layer is the seventh audited scope, and shares the
`release/` directory with the data it decides over. ADR-0028 owns its
architectural boundary: typed release decisions and channel administration
live here; workflows schedule them; exactly `install.sh`,
`scripts/verify-release-artifacts.sh`, and `npm/tl/bin/tl` remain as standalone
shell adapters after migration. `Formula/tl.rb` remains the channel-required
Ruby DSL and is not release administration.

```
release/                -- `lake exe tlrelease`, and its inputs
  Write.lean            --   what a release-evidence write is, before anything
                        --   performs one: an operator-named output directory, a
                        --   sealed non-empty list of validated relative
                        --   components (no absolute name, no empty component,
                        --   no `.`, `..`, embedded `/` or NUL), and the typed
                        --   observation the mechanism reports — commit and
                        --   durability kept apart, so a directory sync that
                        --   failed *after* a successful rename is disclosed
                        --   rather than reported as a write that did not
                        --   happen. The observation crosses the FFI boundary as
                        --   a nine-slot row of small integers, never as prose a
                        --   caller matches: phase and errno are values, and
                        --   Tests/ReleaseDriftTests refuses the formatted form
                        --   anywhere under release/. decodeRow_encodeRow and
                        --   decodeRow_landed_iff are the characterization —
                        --   nothing but the mechanism's own commit report can
                        --   make a write read as landed. `Mechanism` is the
                        --   seam: the write is a parameter, so every phase
                        --   failure is reachable from a test without a
                        --   filesystem that can produce it, and the outcome's
                        --   predicted destination/staging effects are what a
                        --   real fault test compares the directory against
  Sys.lean              --   release administration's whole native boundary: one
                        --   private `@[extern]`, binding
                        --   `tl_release_write_atomic` in
                        --   ffi/tlsys.c. Deliberately not a `tl_sys_*` symbol —
                        --   release/ is outside the product TCB, and the trust
                        --   verifier audits Lean imports and cannot observe a
                        --   linked symbol, so Tests/ReleaseDriftTests pins the
                        --   declaring module, symbol and full Lean signature
                        --   from the loaded release environment, plus the
                        --   executable's linker inputs and the recipe that
                        --   compiles the shim from exactly ffi/tlsys.c. The
                        --   raw array-taking wire is not callable from another
                        --   release module; the public mechanism accepts only
                        --   Write.lean's sealed capability, component-list path
                        --   and typed observations above.
                        --   Imports no `Tl.*`
  Json.lean             --   typed access (every read returns Except with the
                        --   document and path in the message, where the Python
                        --   it replaces raised tracebacks) and deterministic
                        --   rendering — byte-for-byte Python's
                        --   json.dump(indent=2, sort_keys=True), because the
                        --   manifest and SBOM are hashed into SHA256SUMS and
                        --   signed, so their bytes must be a function of their
                        --   content and nothing else
  Model.lean            --   what a release is: Sha256/Commit/Version opaque
                        --   behind parsers, Tier and Channel closed, a
                        --   PublishedTarget carrying its leg's record by
                        --   construction, ChannelStatus making enabled and
                        --   plannedFor exclusive (and carrying the deferral as
                        --   a parsed Version, so nothing downstream re-parses
                        --   it), Version ordering by full SemVer precedence
                        --   including the prerelease rules, and AuditOutcome
                        --   separating missing from could-not-check
  Cli.lean              --   the subcommand table and dispatch. `help` is
                        --   generated from the same list dispatch reads, so a
                        --   command that exists but is undocumented — or is
                        --   documented but unreachable — is not representable
  Main.lean             --   the three-line root defining `main`, kept separate
                        --   so tests can import the decisions in-process
                        --   (two top-level `main`s cannot share a closure)
  Certificate.lean      --   which certificate identity this project accepts,
                        --   defined structurally (parseSan) and rendered into
                        --   the one Go RE2 expression cosign is given, from
                        --   escaped literals plus the fixed tag grammar. The
                        --   expression stopped being configuration:
                        --   certificateIdentityRegexp is a generated mirror
                        --   held to equal the rendering, so it cannot be
                        --   widened by editing it. identityAccepts_iff is
                        --   about the structure; that cosign reads the emitted
                        --   fragment as documented Go RE2 is a carried
                        --   assumption in overview.md, not a claim here
  Identity.lean         --   writes and drift-guards release/identity.pin: the
                        --   pin in a form a POSIX shell reads without a JSON
                        --   parser, so checking a signature needs no
                        --   interpreter. Refuses to write a pin its own reader
                        --   would reject
  identity.json         --   (data) the signing pin every verifier checks against
  identity.pin          --   (data, GENERATED) the same pin as two inert lines,
                        --   issuer then expression. Never sourced, never
                        --   evaluated; read with `IFS= read -r` from one
                        --   opened descriptor so two reads cannot be handed
                        --   one line each from two different pins
  targets.json          --   (data) the distributed targets and their tiers
  Sbom.lean             --   `sbom` writes the release's SPDX 2.3 document from
                        --   lean-toolchain and lake-manifest.json, the two
                        --   files that already fix the build, so it cannot
                        --   disagree with what was built. No generation
                        --   timestamp and no generated document id: the bytes
                        --   are a function of the release, which is what lets
                        --   two independent generations of one release agree
                        --   after it has been hashed into SHA256SUMS and
                        --   signed. Refuses an input it cannot describe rather
                        --   than describing what did not ship: another Lake
                        --   package's manifest, a dependency Lake did not
                        --   resolve from git, an unpinned revision, a url
                        --   nothing could fetch from, an empty inventory, two
                        --   names colliding in one SPDX identifier, and a
                        --   toolchain naming a channel instead of a pin
  Plan.lean             --   `plan-channels` emits one channel=true|false line
                        --   for the release workflow's gates job to publish as
                        --   outputs, so each deferred channel's publish job is
                        --   derived from the plan rather than expected not to
                        --   run. Every channel is emitted, including enabled
                        --   ones: a missing output reads as the empty string,
                        --   which would disable a channel silently.
                        --   `plan-deferrals` refuses a plan whose deferral
                        --   names a release the one being cut has already
                        --   reached — a deferral that stopped pointing
                        --   forwards is a channel that was forgotten, not one
                        --   that was postponed
  plan.json             --   (data) the channels this release publishes through
  Manifest.lean         --   the one description of a release, written and read
                        --   back whole. `manifest` assembles it from each leg's
                        --   record and the directory's own digests, refusing a
                        --   release this pipeline must not publish; the reader
                        --   parses every section — targets with their platform
                        --   and embedded build record, assets, npm, Homebrew —
                        --   and refuses a document that contradicts itself
                        --   before any channel acts on part of it
                        --   (descriptionCoherent_iff). The platform fields
                        --   travel in the document so a channel projecting a
                        --   release reads no checkout: a working tree's target
                        --   list answers a different question.
                        --   `manifest-verify` is the directory half, and
                        --   manifestAccepts_iff is its characterization
  Homebrew.lean         --   the Homebrew channel, with no template and no
                        --   substitution: `homebrew-render` renders the whole
                        --   formula from the signed manifest,
                        --   `homebrew-placeholder` renders the tracked
                        --   Formula/tl.rb (and the three fixtures real brew
                        --   audits) from release/identity.json +
                        --   release/targets.json, and `homebrew-publish`
                        --   updates the tap once — a prerelease does not push,
                        --   an identical formula is a no-op, and a checkout
                        --   whose origin is not the tap the manifest names is a
                        --   refusal that does not repeat the url. formulaCovers_iff
                        --   is the rule that matters: a stable spec missing a
                        --   url for a Supported target makes Homebrew raise on
                        --   *load*, for every brew command touching the tap.
                        --   tapDisposition_identical_iff is what keeps a
                        --   drifting comparison from reporting a skipped
                        --   publication as success
  Boundary.lean         --   `dependency-boundary` states the four v0.1 entry
                        --   points, walks the first-party scripts they reach,
                        --   and refuses on an invocation of python, python3,
                        --   ruby, brew, node or npm in command position. It
                        --   reads what a script says — comments stripped with
                        --   quote awareness, since these files discuss npm and
                        --   Homebrew throughout, and a gate answered by
                        --   rewording a comment would teach the wrong lesson.
                        --   Deferred channel files and publish jobs leave the
                        --   scan by name and by channel, a missing referenced
                        --   script is a refusal rather than a skip, and a clean
                        --   verdict names the files it read so a walk that
                        --   stopped following references is visible as a short
                        --   list rather than a plausible count. What it cannot
                        --   see — a command name in a variable, or inside the
                        --   string `sh -c` runs — is what
                        --   scripts/check-release-runtimes.sh observes instead.
                        --   Each line is read as what it is: a `#!` goes to the
                        --   parser its own syntax has (the marker, optional
                        --   whitespace, then the interpreter), because read as
                        --   shell `#! /usr/bin/python3` is a command named `#!`
                        --   taking a path — no finding, and a Python helper on
                        --   the release path. Reading a line yields either the
                        --   commands it understood or the reason it could not,
                        --   and the second is a refusal: a parser omission
                        --   costs a release rather than passing as a clean file.
                        --   A backslash escapes as the shell's does, and a
                        --   forbidden path is a finding wherever it is written
                        --   rather than only in command position — a shim
                        --   cannot shadow /usr/bin/python3, so an absolute path
                        --   held in a variable was the one shape neither arm
                        --   saw. What remains uncovered (a path assembled at
                        --   runtime) is pinned by a corpus row, not assumed
```

Each type in `Model.lean` exists because the shell could hold a value that
should not exist and held it silently: uppercase hex compared against lowercase
output and read as tampering, a digest nothing length-checked, "is this a
prerelease" recomputed by searching for `-`, build metadata modelled as an
option and then checked in nine places one of which an empty target list could
skip, and *missing* indistinguishable from *could not check* — the last of
which aborts a legitimate release with a remedy telling the operator to fix
something already correct.

Lowercase, like `scripts/`, and for a stronger reason: the directory already
held this release's machine-readable data, and on a case-insensitive
filesystem a sibling `Release/` *is* `release/`. The trust gate compares claim
paths as strings, so a `Release` claim would scan a directory it had not
claimed and report every module in it as an unclaimed source on macOS while
Linux saw two directories and disagreed — `Tests/VerifyTests.lean` pins that,
stated as "a miscased claim never derives the module name Lake builds" so the
row holds on both filesystems.

Nothing under `release/` may import `Tl.*`: release administration is not part
of the shipped product, and this is enforced rather than asked for — such an
import lands the product modules in the release scope's environment, where the
gate reports them as modules outside the declared scope. Being written in Lean
buys `Except` and totality, not membership in the TCB; almost all of it is
tested I/O-shell code (ADR-0004), with theorems only on the small pure verdict
functions whose failure mode is a silent false negative. It carries no
landmarks and no docs/overview.md row, for the same reason `Verify/Proofs.lean`
does not: landmarks guard the product's proved claims.

Mapping to the boundary: `Tl/Crdt/` and `Tl/Kernel/` are proved
([ADR-0004](adr/ADR-0004-verified-kernel-tcb-boundary.md)); `Tl/Error`,
`Tl/Format`, `Tl/Hash`, `Tl/Store` (+ `ffi/tlsys.c`), `Tl/Clock`, `Tl/Sync`,
`Tl/Import`, `Tl/Cli` are the tested shell outside it — tested at module
granularity, which does not mean no theorem is stated about them: where a piece
of the shell is already a pure total function of data in hand, principle 1 asks
for a proof, and those named proved anchors carry landmarks like the kernel's
own claims do (the per-module blocks above name them). `Verify/` is the
build-time mechanism that checks the proved tier's trust boundary and is
itself inspected as a separate scope. Its tier is split, deliberately:

- The **verdict logic is proved**, in `Verify/Proofs.lean`. `analyze`,
  `AuditedReports.errors`, `GateEvidence.errors`, `gateEvidenceOf`,
  `workerVerdict`, and
  `importViolations` are total pure functions of already-collected evidence, so
  principle 1 applies to them exactly as it applies to the kernel: a
  `GateClean` structure enumerates every condition `analyze` can report, and
  `analyze_clean_iff` proves a scope's finding array is empty if and only if
  all of them hold; `importViolations_isEmpty_iff` and
  `importViolations_size_eq` characterise the ADR-0009 traversal's silence and
  its one-finding-per-rejected-edge count. Example rows cannot establish that,
  because the risk being managed is an arm that stops reporting.
  `workerVerdict` carries the decision to the exit: status zero and the
  completion marker each hold exactly when the evidence is empty
  (`workerVerdict_status_zero_iff`, `workerVerdict_marker_iff`), and both output
  streams are pinned in both arms — `workerVerdict_marker_last` and
  `workerVerdict_report_empty` for the report, `workerVerdict_diagnostics`
  unconditionally for the diagnostics — so `runChecked` needs no branch of its
  own and neither arm can grow an emission no theorem sees.
  `workerVerdict_marker_iff_clean` composes it with `analyze_clean_iff` into the
  whole decision: the marker is printed exactly when all seven scopes are
  `GateClean` and both inventory scans are silent.
- **Stored-body axiom propagation is proved**, in the same file.
  `propagatedAxioms` deliberately reimplements Lean's `collectAxioms` rather
  than trusting the serialized extension summaries — which are data produced by
  the same compilation the gate audits — so a bug in it is a *silent* false
  negative: an ordinary green run with an axiom unreported in a theorem's cone.
  `propagatedAxioms_sound` says every axiom filed under a declaration really is
  an axiom reachable from it along stored-body edges, and
  `propagatedAxioms_complete` the converse, so the axiom rows the
  axiom-dependency arm reports are exactly the reachable set. Both are stated
  over `axiomEdges`, the seam the code walks, and over an *inductive* `Reaches`
  relation rather than a bounded iteration — which is what keeps the section
  batteries-only, since the induction is on a derivation and never asks how
  long a chain is. `Tl/Kernel/Reach.lean` needed Mathlib for exactly the
  argument avoided here, and `Verify/` is outside ADR-0009's escape hatch
  anyway.
  Completeness assumes the drain *finished*: `drainWorklist` returns `Option`
  and refuses on an exhausted bound rather than returning a truncated map,
  which is what makes saturation observable instead of a counting argument.
- Three further functions carry **one-directional** implications, not
  characterisations, and the docs should not be read as claiming more:
  `directImportAllowed_cases` (allowed without the first-party escape implies
  one of the two recorded reasons), `completedSuccessfully_exitZero` plus
  `completedSuccessfully_markerFinal` (an accepted run had status zero *and*
  printed the marker as its last nonempty line), and
  `replayDependencies_superset` with `replayDependencies_inductiveSiblings`
  (one replay step enqueues every constant the stored body uses, plus an
  inductive's mutual siblings — the fixed-point walk in the
  `partial def replayClosure` is not proved).
- **Which scope a piece of evidence belongs to is carried by the types**, and
  so belongs to neither tier. `GateScope` has one case per audited environment
  and indexes `Observation`; `ScopedEnvironment` seals a loaded environment
  together with the scope it was loaded for behind a private constructor, so
  only `loadScope` — which reads that scope's roots out of the registry — can
  mint one; and the run's seven observations are assembled through
  `ScopeObservations`, whose fields all differ in type. The mistakes that would
  leave a scope unaudited while every theorem and every test stayed green —
  passing the tests observation as `production`, auditing one scope twice,
  observing one environment under another scope's name — therefore do not
  elaborate, and the scope word in a finding is derived from the type rather
  than written beside it. What is left is the registry those types are read
  against: which roots and which source directories a scope owns
  (`auditLayout`, `AuditLayout.gateRoots`). That is not silent either — the
  missing- and unexpected-module arms compare each environment's first-party
  imports against its scope's own source inventory — but it is reviewed data,
  and it is what the verifier-bootstrap assumption in the
  [overview](overview.md) now covers.
- The **rest of the collection stays tested**. `Verify/Environment.lean` reads
  Lean's stored module and declaration data, walks the filesystem, and replays
  declarations through the kernel; nothing in `Verify/Proofs.lean` says that
  `o.decls` is a scope's *complete* declaration set or that `replayClosure`
  reached a fixed point. What the axiom-propagation theorems establish is
  relative to the constants they are handed: the propagation is exact over that
  map, not that the map is the right one. `Tests/VerifyTests.lean` and
  `Tests/VerifyLoadedTests.lean` cover those branches and the adversarial
  composition paths described above, together with what the theorems cannot
  see — the wording each finding uses to teach its fix, the truncation
  disclosure, the summarize limit, and that the test file's own base
  observation is clean.

These theorems get **no** entry in `Tl.Verify.landmarkTheorems` and **no** row
in the [overview](overview.md) proved-claims table. Landmarks exist to stop the
*product's* proved claims from silently shrinking; the gate's own internal
correctness is not a product claim, and listing it there would make the
landmark set mean two different things
([ADR-0026](adr/ADR-0026-continuous-integration.md)). They are instead kept from
being silently deleted by `pinnedVerdictLogicTheorems` in
`Tests/VerifyTests.lean`, which names each one so that retiring a theorem is a
compile error. The efficiency tiering
that backs the proved tier (the `*Fast` refinements, `HashMapView`, and the
ratio-asserted regression net) is recorded in
[ADR-0023](adr/ADR-0023-efficiency-tiering-and-prevention.md) and
[ADR-0024](adr/ADR-0024-indexed-views-bridge.md).

## Cross-cutting invariants (load-bearing across modules & ADRs)

A handful of properties thread through many modules and ADRs at once — change one
and several proofs or tests move. A contributor should know these before touching
any single piece (it is also the bus-factor map: the correctness web in one
table).

| Invariant | Relied on by | Enforced / checked by |
|---|---|---|
| `(hlc, replica, nonce)` is a total order | every LWW/OR-Set join (the join is a *function*), issue-id derivation | kernel proof *given* the order; shell mints/validates the triple; nonce-uniqueness is a carried assumption (overview Trusted) governing which write wins and add-wins distinctness only — never join well-definedness, and no longer any frame lemma (element-scoped tombstones made the unrelate case unconditional) — ADR-0002/0007 |
| Clocks / ids / actor are *data* (kernel reads no clock/RNG/env) | convergence being provable at all (the fold stays deterministic) | kernel has no I/O by type (`State → Op → State`); shell mints and freezes them into ops — ADR-0001 §1 / 0007 / 0013 |
| Order/duplicate-insensitivity of the fold | git-as-transport, the segment union, the worktree local-leg, at-least-once delivery | ADR-0004 thm 2 (+ thm 8 inflation/idempotent re-delivery) |
| Dangling `blocks`/`parent` edges are read-time inert | `ready` / `effectiveStatus` / cycle totality; no spurious not-ready | kernel: `Invariant` excludes endpoint-existence; reads treat a nonexistent endpoint as discharged — ADR-0002 / 0003 §5 / 0004 thm 3-4 |
| `actor` is provenance-only (not in the CRDT key) | convergence unaffected by provenance; `createdBy` projection | frame lemma — ADR-0003 / 0004 / 0008 / 0013 |
| `now` is injected; `deferUntil` is a plain instant distinct from the HLC | `ready` determinism + time-monotonicity; "clocks are data" | kernel signature (`Now` param); shell normalizes to an ISO-8601 UTC instant — ADR-0010 / 0004 thm 9 / 0008 |
| Fail-closed parse is *segment*-scoped, not log-scoped | availability under a bad/hostile/`v`-skewed line (one segment can't deny service to all) | shell parser — ADR-0008 §corruption / 0015 §5 / 0014 T2 |

Two reading rules these encode: derive-or-report, never enforce (any
cross-entity rule a merge could break is a total function of state, not a
write-time guard — ADR-0003), and prove the pure core, test the shell, name the
rest as a carried assumption (ADR-0004 / overview Trusted).
