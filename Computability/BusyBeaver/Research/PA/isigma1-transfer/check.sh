#!/usr/bin/env bash
# Compile ConPAISigma1Transfer.lean against the root Lake workspace and report its axioms.
# Optional: IPRA_LEAN_OVERLAY and IPRA_FOUNDATION_OVERLAY, prebuilt object directories that are
# put in front of the search path.
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
out=$(mktemp -d "${TMPDIR:-/tmp}/conpa-isigma1.XXXXXXXX")
trap 'rm -rf "$out"' EXIT
case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*) sep=';' ;; *) sep=':' ;; esac
extra=""
if [ -n "${IPRA_LEAN_OVERLAY:-}" ]; then extra="$(realpath "$IPRA_LEAN_OVERLAY")$sep"; fi
if [ -n "${IPRA_FOUNDATION_OVERLAY:-}" ]; then extra="$extra$(realpath "$IPRA_FOUNDATION_OVERLAY")$sep"; fi
export CONPA_EXTRA="$extra" CONPA_OUT="$out"
lake env bash -c '
set -euo pipefail
lean --version | grep -q "Lean (version 4\.32\.0"
export LEAN_PATH="$CONPA_EXTRA${LEAN_PATH:-}"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/isigma1-transfer/ConPAISigma1Transfer.lean \
  -o "$CONPA_OUT/ConPAISigma1Transfer.olean" | tee "$CONPA_OUT/axioms.log"
'
if grep -q sorryAx "$out/axioms.log"; then echo "sorryAx found" >&2; exit 1; fi
grep -c "depends on axioms" "$out/axioms.log" | grep -qx 3
echo "ConPAISigma1Transfer: checked"
