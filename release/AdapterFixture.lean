/- Shared declared collaborators for the retained adapters' public-process
corpora. Fixtures validate argv and record per-invocation reachability. -/
import release.Digest

namespace Release.AdapterFixture

structure Outcome where
  name : String
  passed : Bool
  msg : String := ""
  skipped : Bool := false

def check (name : String) (passed : Bool) (msg : String := "") : Outcome :=
  { name, passed, msg }

def checkEq [DecidableEq α] [Repr α] (name : String) (actual expected : α) : Outcome :=
  { name, passed := actual == expected, msg := s!"expected {repr expected}, got {repr actual}" }

def requireResult (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def runTool (cmd : String) (args : Array String) : IO Unit := do
  let _ ← requireResult (← Release.succeeded cmd args)

def cosignFixture : String := r#"#!/bin/sh
set -eu
printf 'cosign\n' >> "$PROBE_EVENTS"
[ "$#" -eq 8 ] && [ "$1" = verify-blob ] && [ "$3" = --bundle ] &&
[ "$5" = --certificate-oidc-issuer ] && [ "$6" = "$PROBE_ISSUER" ] &&
[ "$7" = --certificate-identity-regexp ] && [ "$8" = "$PROBE_IDENTITY" ] || exit 91
blob=$2
[ "$4" = "$blob.sigstore.json" ] && [ -f "$blob" ] && [ -f "$4" ] || exit 92
name=${blob##*/}
printf '%s\n' "$name" >> "$PROBE_SIGNATURES"
case $name in SHA256SUMS|"$PROBE_ASSET"|"${PROBE_SECOND_ASSET-}") ;; *) exit 93 ;; esac
case $PROBE_FAULT in
  signature-SHA256SUMS) [ "$name" != SHA256SUMS ] || { echo 'invalid signature'; exit 1; } ;;
  signature-asset) [ "$name" != "$PROBE_ASSET" ] || { echo 'invalid signature'; exit 1; } ;;
  signature-second) [ "$name" != "${PROBE_SECOND_ASSET-}" ] || { echo 'invalid signature'; exit 1; } ;;
  cosign-broken) echo 'cannot initialize trust root'; exit 1 ;;
esac
"#

def digestFixture : String := r#"#!/bin/sh
set -eu
printf 'digest\n' >> "$PROBE_EVENTS"
if [ "$PROBE_DIGEST_MODE" = shasum ]; then
  [ "$#" -eq 3 ] && [ "$1" = -a ] && [ "$2" = 256 ] || exit 91
  shift 2
fi
[ "$#" -eq 1 ] || exit 92
name=${1##*/}
printf '%s\n' "$name" >> "$PROBE_DIGESTS"
[ "$PROBE_FAULT" != digest-broken ] || exit 1
[ "$PROBE_FAULT" != digest-empty ] || exit 0
if [ "$name" = THIRD-PARTY-LICENSES ] && [ "$PROBE_FAULT" = notice-digest ]; then exit 1; fi
if [ "$PROBE_BACKEND_SHASUM" = 1 ]; then exec "$PROBE_BACKEND" -a 256 "$1"; fi
exec "$PROBE_BACKEND" "$1"
"#

def readLog (path : System.FilePath) : IO (List String) := do
  if ← path.pathExists then
    return ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  return []


end Release.AdapterFixture
