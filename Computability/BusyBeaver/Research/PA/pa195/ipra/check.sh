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
task_dir=$(mktemp -d "${TMPDIR:-/tmp}/pa195-ipra.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6" "$task_dir/DiophantineConsistency"
for task_dep in "$IPRA_LEAN_OVERLAY"/DiophantineConsistency/*; do
  task_name=${task_dep##*/}
  case "$task_name" in IPRAPA196Consistency.olean*) continue ;; esac
  ln -s "$task_dep" "$task_dir/DiophantineConsistency/$task_name"
done
bridge=Computability/BusyBeaver/Research/PA/pa195/ipra
python3 -B "$bridge/generate.py" "$repo" "$task_dir"
export PA195_TASK_DIR="$task_dir" PA195_TASK_REPO="$repo" IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
lake env bash -c '
set -euo pipefail
lean --version | rg -q "Lean \(version 4\.32\.0"
export LEAN_PATH="$PA195_TASK_DIR:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:${LEAN_PATH:-}"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Zip.lean -o "$PA195_TASK_DIR/M6/Zip.olean"
cd "$PA195_TASK_DIR"
lean -M6000 -j1 PA195Literal.lean -o PA195Literal.olean
lean -M6000 -j1 PA195Rows.lean -o PA195Rows.olean
cd "$PA195_TASK_REPO"
bridge=Computability/BusyBeaver/Research/PA/pa195/ipra
lean -M6000 -j1 "$bridge/PA195Bounded.lean" -o "$PA195_TASK_DIR/PA195Bounded.olean"
lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAPA196Consistency.lean -o "$PA195_TASK_DIR/DiophantineConsistency/IPRAPA196Consistency.olean"
lean -M6000 -j1 "$bridge/PA195BoundedChecks.lean" | tee "$PA195_TASK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA195Endpoint.lean" | tee -a "$PA195_TASK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA195StandardSemantics.lean" | tee -a "$PA195_TASK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA195ForwardGG.lean" | tee -a "$PA195_TASK_DIR/axioms.log"
lean -M6000 -j1 "$bridge/PA195RefutationBridge.lean" | tee -a "$PA195_TASK_DIR/axioms.log"
if rg -q "sorryAx" "$PA195_TASK_DIR/axioms.log"; then
  echo "Unexpected sorryAx in theorem dependencies" >&2
  exit 1
fi
'
