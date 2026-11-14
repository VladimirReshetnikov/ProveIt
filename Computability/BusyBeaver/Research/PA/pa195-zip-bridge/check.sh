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
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa195-zip-check.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6"
python3 -B Computability/BusyBeaver/Research/PA/pa195/ipra/generate.py "$repo" "$task_dir"
export LEAN_PATH="$task_dir:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/M6/Zip.olean" Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Zip.lean
lean -R "$task_dir" -M6000 -j1 -o "$task_dir/PA195Literal.olean" "$task_dir/PA195Literal.lean"
lean -R "$task_dir" -M6000 -j1 -o "$task_dir/PA195Rows.olean" "$task_dir/PA195Rows.lean"
lean -M6000 -j1 -o "$task_dir/PA195Bounded.olean" Computability/BusyBeaver/Research/PA/pa195/ipra/PA195Bounded.lean
lean -M6000 -j1 -o "$task_dir/PA195LocalQuotient.olean" Computability/BusyBeaver/Research/PA/pa195-quotient/PA195LocalQuotient.lean
lean -M6000 -j1 -o "$task_dir/PA195AllTape.olean" Computability/BusyBeaver/Research/PA/pa195-all-tape/PA195AllTape.lean
lean -M6000 -j1 -o "$task_dir/PA195ControlData.olean" Computability/BusyBeaver/Research/PA/pa195-control/PA195ControlData.lean
lean -M6000 -j1 -o "$task_dir/PA195Control.olean" Computability/BusyBeaver/Research/PA/pa195-control/PA195Control.lean
lean -M6000 -j1 -o "$task_dir/PA195GenericTrace.olean" Computability/BusyBeaver/Research/PA/pa195-generic-trace/PA195GenericTrace.lean
lean -M6000 -j1 -o "$task_dir/PA195DenseData.olean" Computability/BusyBeaver/Research/PA/pa195-dense/PA195DenseData.lean
lean -M6000 -j1 -o "$task_dir/PA195DenseBinding.olean" Computability/BusyBeaver/Research/PA/pa195-dense/PA195DenseBinding.lean
lean -M6000 -j1 -o "$task_dir/PA195ZipBridge.olean" Computability/BusyBeaver/Research/PA/pa195-zip-bridge/PA195ZipBridge.lean
lean -M6000 -j1 -o "$task_dir/PA195ZipTable.olean" Computability/BusyBeaver/Research/PA/pa195-zip-bridge/PA195ZipTable.lean
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa195-zip-bridge/PA195ZipRun.lean | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in theorem dependencies' >&2
  exit 1
fi
