#!/usr/bin/env bash
# Compile the IΣ₁ transfer and the generic machine layer against the root Lake workspace.
# Optional: IPRA_LEAN_OVERLAY and IPRA_FOUNDATION_OVERLAY, prebuilt object directories that are
# put in front of the search path.
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
out=$(mktemp -d "${TMPDIR:-/tmp}/conpa-machine.XXXXXXXX")
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
d=Computability/BusyBeaver/Research/PA
lean -M6000 -j1 $d/isigma1-transfer/ConPAISigma1Transfer.lean -o "$CONPA_OUT/ConPAISigma1Transfer.olean" > "$CONPA_OUT/transfer.log"
lean -M6000 -j1 $d/isigma1-machine/ConPAMachine.lean -o "$CONPA_OUT/ConPAMachine.olean" | tee "$CONPA_OUT/axioms.log"
lean -M6000 -j1 $d/isigma1-machine/ConPAMachineEndpoint.lean -o "$CONPA_OUT/ConPAMachineEndpoint.olean" | tee -a "$CONPA_OUT/axioms.log"
'
if grep -q sorryAx "$out/axioms.log" "$out/transfer.log"; then echo "sorryAx found" >&2; exit 1; fi
grep -c "depends on axioms" "$out/axioms.log" | grep -qx 2
echo "ConPAMachine, ConPAMachineEndpoint: checked"
