#!/usr/bin/env bash
# Compile the modules of this directory against the root Lake workspace (Foundation must be
# built there), one lean process at a time.
# Optional: IPRA_LEAN_OVERLAY and IPRA_FOUNDATION_OVERLAY, prebuilt object directories that are
# put in front of the search path.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
cd "$repo"
out=$(mktemp -d "${TMPDIR:-/tmp}/conpa-sequent.XXXXXXXX")
trap 'rm -rf "$out"' EXIT
case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*) sep=';'; outp=$(cygpath -w "$out") ;; *) sep=':'; outp="$out" ;; esac
extra="$outp$sep"
if [ -n "${IPRA_LEAN_OVERLAY:-}" ]; then extra="$extra$(realpath "$IPRA_LEAN_OVERLAY")$sep"; fi
if [ -n "${IPRA_FOUNDATION_OVERLAY:-}" ]; then extra="$extra$(realpath "$IPRA_FOUNDATION_OVERLAY")$sep"; fi
export CONPA_EXTRA="$extra" CONPA_OUT="$out"
lake env bash -c '
set -euo pipefail
lean --version | grep -q "Lean (version 4\.32\.0"
export LEAN_PATH="$CONPA_EXTRA${LEAN_PATH:-}"
d=Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-sequent
for m in ConPASequent ConPASetSequent ConPADerivation; do
  lean -M6000 -j1 $d/$m.lean -o "$CONPA_OUT/$m.olean" | tee -a "$CONPA_OUT/axioms.log"
done
'
if grep -q "sorryAx\|declaration uses" "$out/axioms.log"; then echo "sorry found" >&2; exit 1; fi
grep -c "depends on axioms" "$out/axioms.log" | grep -qx 14
echo "pa194-model-sequent: generic modules checked"
# The instance for the numerical calculus, with every standalone module it imports.
# Arguments of this script are passed on (for example --out DIR to reuse compiled objects).
if command -v py >/dev/null 2>&1; then py=py; else py=python3; fi
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194ModelSequent.lean" --reports 8 "$@"
# The step after the compiler, with the modules of pa194-model-logic and pa194-model-fairness
# that it imports.
"$py" -X utf8 -B "$here/../pa194-model-fairness/check_bridge.py" \
  --top "$here/PA194ModelEndpoint.lean" --reports 6 "$@"
