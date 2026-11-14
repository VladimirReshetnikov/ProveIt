#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching iPRA object directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching Foundation object directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
sha256sum -c <<'PINS'
152d1d552b27baca8db0ac05b16092d9083c2ab979bb0b4e7f96a95803d9a9b0  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Zip.lean
5e21edfdc4593f441f46f7fde9f8d0fc467eb1369c03251fe4f3a1a4d17a57de  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRALanguage.lean
f0a5ba7482344477c2c7ca5ec2544f127ede62ec30e60b1101bfaed7be94db74  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean
PINS
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-zip-check.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6"
python3 -B Computability/BusyBeaver/Research/PA/pa194/ipra/generate.py "$repo" "$task_dir"
export LEAN_PATH="$task_dir:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/M6/Zip.olean" Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Zip.lean
lean -R "$task_dir" -M6000 -j1 -o "$task_dir/PA194Literal.olean" "$task_dir/PA194Literal.lean"
lean -R "$task_dir" -M6000 -j1 -o "$task_dir/PA194Rows.olean" "$task_dir/PA194Rows.lean"
lean -M6000 -j1 -o "$task_dir/PA194Bounded.olean" Computability/BusyBeaver/Research/PA/pa194/ipra/PA194Bounded.lean
lean -M6000 -j1 -o "$task_dir/PA194LocalQuotient.olean" Computability/BusyBeaver/Research/PA/pa194-quotient/PA194LocalQuotient.lean
lean -M6000 -j1 -o "$task_dir/PA194AllTape.olean" Computability/BusyBeaver/Research/PA/pa194-all-tape/PA194AllTape.lean
lean -M6000 -j1 -o "$task_dir/PA194ControlData.olean" Computability/BusyBeaver/Research/PA/pa194-control/PA194ControlData.lean
lean -M6000 -j1 -o "$task_dir/PA194Control.olean" Computability/BusyBeaver/Research/PA/pa194-control/PA194Control.lean
lean -M6000 -j1 -o "$task_dir/PA195GenericTrace.olean" Computability/BusyBeaver/Research/PA/pa195-generic-trace/PA195GenericTrace.lean
lean -M6000 -j1 -o "$task_dir/PA194DenseData.olean" Computability/BusyBeaver/Research/PA/pa194-dense/PA194DenseData.lean
lean -M6000 -j1 -o "$task_dir/PA194DenseBinding.olean" Computability/BusyBeaver/Research/PA/pa194-dense/PA194DenseBinding.lean
lean -M6000 -j1 -o "$task_dir/PA194ZipBridge.olean" Computability/BusyBeaver/Research/PA/pa194-zip-bridge/PA194ZipBridge.lean
lean -M6000 -j1 -o "$task_dir/PA194ZipTable.olean" Computability/BusyBeaver/Research/PA/pa194-zip-bridge/PA194ZipTable.lean
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-zip-bridge/PA194ZipRun.lean | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in theorem dependencies' >&2
  exit 1
fi
