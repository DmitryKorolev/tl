# ADR-0018 — Hand-rolled SHA-256 (pure Lean)

- Status: Accepted
- Date: 2026-06-10

## Context

Several pinned derivations need SHA-256, and nothing in the dependency
closure provides one. ADR-0007 mints issue ids from SHA-256 over the
fixed-width `replica ++ hlc ++ nonce` preimage (80-bit slice); ADR-0005 pins
the import-seed id (`"import:" ++ source-tag ++ ":" ++ source-id`, 80 bits),
the import replica-id (`"import-replica:" ++ …`, 64 bits), and the source
fingerprint (a full digest of the canonical sorted source manifest); the
design-backlog's import-nonce candidate takes a 128-bit slice of the same
hash *function* over its own `"import-nonce:"` preimage (ADR-0005's remaining
record-level hashes reuse the same `Sha256.digest`). Lean core and Std
ship only non-cryptographic 64-bit hashing (the `Hashable` machinery; even
Lake's content-addressed build traces are a `UInt64` with a standing "use a
secure hash" TODO); batteries has none; Mathlib — already in the closure via
the ADR-0009 exception — ships no cryptographic hash either. The wider Lean
ecosystem has no dependency-grade SHA-2: the notable projects are a pure-Lean
SHA-3 *experiments* repo and a McEliece spec that binds OpenSSL and libkeccak
for its fast paths.

The use is cryptographically undemanding in a specific, load-bearing way:
`tl` hashes **public data** (replica ids, HLCs, nonces, import source ids) to
derive identifiers. There is no key material and no secret-dependent
branching, so constant-time execution and side-channel hygiene — the reasons
"never roll your own crypto" exists — do not apply. The only property the
consumers need is byte-exact agreement with FIPS 180-4, which test vectors
check completely. Collision resistance is not a code property at all: it is
already a carried assumption (issue-id uniqueness at the 80-bit truncation,
overview.md Trusted), and no implementation choice here changes it.

So the choice of vehicle is a *dependency and distribution* decision
(ADR-0006/0009 territory), not a security one.

## Decision

Hand-roll SHA-256 in pure Lean, as a direct transcription of FIPS 180-4, in
the tested shell: `Tl/Hash/Sha256.lean` (pure code, tier-2 tested —
ADR-0004).

- **API: the full digest.** `Sha256.digest : ByteArray → ByteArray` returns
  all 32 bytes. Consumers slice: issue ids and import-seed ids take 80 bits,
  the import replica-id 64, the import-nonce candidate 128, and the source
  fingerprint keeps the whole digest — the differing widths are exactly why
  truncation does not belong in the hash module. No streaming/incremental
  API: every message is bytes-in-hand — mint preimages are a single block
  (55 bytes is precisely the one-block padding maximum), import preimages a
  few blocks, and the one large message (the import source manifest) is still
  hashed once, in hand, per one-shot import. A streaming API can be added
  later with a one-shot-equals-folded test.
- **Truncation is pinned here as the NIST convention: the leftmost N bits —
  the first N/8 digest bytes.** This is the reading the `[0..80 bits]` /
  `[0..64 bits]` notation in ADR-0005/0007 already suggests, and the
  convention every SHA-2 variant (SHA-224, SHA-512/256) uses. For issue ids:
  the first 10 digest bytes, read as a big-endian 80-bit integer, encoded
  `toCrockford v 16` (ADR-0007 — its former "low 80 bits" phrasing is
  amended to "leftmost" in this change so the two texts cannot be read as
  opposite ends of the digest). The mint code, not this module, applies the
  slice.
- **Tests ship in the same change** (AGENTS.md DoD: tests in the same
  change): the NIST CAVP short-message vectors plus deliberate boundary
  lengths (0, 1, 55, 56, 63, 64, 65 bytes and a multi-block message — the
  padding edges where SHA-256 implementations actually break), and **one
  worked end-to-end vector**: a concrete `(replica, hlc, nonce)` preimage →
  digest → leftmost-80-bits → 16-char id, so two implementations of the mint
  can never silently diverge. (The import-path vectors — seed id, replica-id,
  fingerprint — land with ADR-0005's differential-import fixtures.) The test
  file documents the one-line external cross-check
  (`printf '%s' … | shasum -a 256`).
- **The transcription *is* the production code.** At one single-block hash
  per `create` there is no hot path; a one-shot import (~10⁵ hashes plus the
  manifest fingerprint) lands sub-second to roughly a second even at the
  pessimistic end of the unoptimized estimate. If an optimized variant is
  ever wanted, it must ship with a proved equivalence to this transcription
  (`fast = spec`) — the AGENTS.md rule applied with the transcription as the
  spec: bridge from the efficient form to the spec, never replace it.
- **No new trust.** This adds no carried assumption: correctness is tier-2
  tested; the 80-bit-truncation collision bound was already in overview.md
  Trusted. Small proof-shaped extras (digest length = 32, padding-length
  lemmas, and the fixed-width preimage injectivity that discharges ADR-0007's
  "unambiguous by fixed width" claim) are welcome but are hardening, not
  gates.

## Consequences

- **Zero new build or distribution surface.** Pure Lean compiles wherever
  `tl` compiles; the ADR-0006 matrix, signing, and reproducible-build story
  gain nothing to vendor, link, or track.
- **Auditable by diff.** A reviewer checks ~120 lines against a frozen
  public standard plus vectors; there is no FFI marshalling layer where an
  integration bug could hide.
- The "rolled our own crypto" objection is answered *here*, once: public
  data, no side channels, vector-verified, collision resistance carried
  explicitly — the one corner of cryptography where hand-rolling is sober.
- The performance ceiling of naive Lean (~10–50× slower than optimized C) is
  accepted and off every hot path; the `fast = spec` rule defines the exit if
  that ever changes.

## Alternatives considered

- **libsodium via FFI** (`crypto_hash_sha256`). Audited — but the risk
  relocates rather than disappears: the new hand-written, less-testable code
  becomes the FFI glue and per-platform build wiring, for a *pure function*
  whose correctness vectors already verify. It adds a permanent
  vendor/static-link burden across every ADR-0006 target, a new supply-chain
  root (ADR-0014 T3), and it violates the FFI policy (ADR-0019: OS primitives
  only). libsodium's own documentation steers new designs to BLAKE2b; we
  would be adopting the whole library for its interoperability shim.
- **OpenSSL via FFI.** The same shape, larger.
- **Vendoring a single-file C SHA-256** into the ADR-0019 shim. Smaller than
  libsodium but still unaudited C in the build with none of pure Lean's
  testability-in-place or potential provability — both options' weaknesses
  combined.
- **Depending on an ecosystem Lean package.** Nothing is dependency-grade
  (experiments and spec repos); ADR-0009's deliberate-dependency stance
  applies doubly to crypto.
- **Switching algorithms (SHA-3, BLAKE2b/3).** No security gain for
  public-data mixing; SHA-256 is already pinned in the ADR-0005/0007
  preimages; its ubiquity is load-bearing (the shell one-liner cross-check,
  the differential-import oracle, every language's stdlib); and it is the
  easiest of the family to transcribe correctly (BLAKE3's tree mode is the
  hardest, and its SIMD wins are unreachable from naive Lean anyway). Ids are
  read as data and never re-derived (ADR-0007), so a future algorithm switch
  for *new* mints stays cheap — future-proofing needs no pre-payment.
- **Waiting for Lean core.** Lake's TODO notwithstanding, core adopting a
  hash for build traces would not oblige a public, stable crypto API on any
  timeline `tl` can plan against.
