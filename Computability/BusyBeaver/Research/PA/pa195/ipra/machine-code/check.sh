#!/usr/bin/env bash
set -euo pipefail

: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the built iPRA module directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the built Foundation module directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
sha256sum -c <<'PINS'
842453bc52956492e439df8ccadbe00b1c0a2bac547d157b48b13daa045a8946  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAHistoryPairCode.lean
a346cba7ed93b8d495eeca81c85e52510eb45938bf417eb950d9e66b2a0d2f98  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAIsZero.lean
f0a5ba7482344477c2c7ca5ec2544f127ede62ec30e60b1101bfaed7be94db74  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean
5e21edfdc4593f441f46f7fde9f8d0fc467eb1369c03251fe4f3a1a4d17a57de  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRALanguage.lean
2028e9ee96cbf335faaefd878d6cd177bd4ae7c469442977bded19da2e30a89d  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAAddOne.lean
PINS
printf '%s  %s\n' \
  17b5937fcca095d4c3abb51a2e4cb51d7754eb7de1a31f87f8d62936065b3b77 "$IPRA_LEAN_OVERLAY/DiophantineConsistency/PRAHistoryPairCode.olean" \
  aae6176985ffcfadfb94c9681a816443ddd189f39a4a76a89a218c1d8cacb36c "$IPRA_LEAN_OVERLAY/DiophantineConsistency/PRAIsZero.olean" \
  d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e "$IPRA_FOUNDATION_OVERLAY/Init.olean" | sha256sum -c

task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/binary-tape-code.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
export BINARY_TAPE_TASK_DIR="$task_dir" IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
python3 -B Computability/BusyBeaver/Research/PA/pa195/ipra/generate.py "$repo" "$task_dir"
lake env bash -c '
set -euo pipefail
lean --version | rg -q "Lean \(version 4\.32\.0"
export LEAN_PATH="$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:${LEAN_PATH:-}"
lean -M5000 -j1 Computability/BusyBeaver/Research/PA/pa195/ipra/machine-code/BinaryTapeCodes.lean \
  -o "$BINARY_TAPE_TASK_DIR/BinaryTapeCodes.olean" | tee "$BINARY_TAPE_TASK_DIR/axioms.log"
export LEAN_PATH="$BINARY_TAPE_TASK_DIR:$LEAN_PATH"
lean -M5000 -j1 Computability/BusyBeaver/Research/PA/pa195/ipra/machine-code/TapeStepCodes.lean \
  -o "$BINARY_TAPE_TASK_DIR/TapeStepCodes.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -R "$BINARY_TAPE_TASK_DIR" -M5000 -j1 "$BINARY_TAPE_TASK_DIR/PA195Rows.lean" \
  -o "$BINARY_TAPE_TASK_DIR/PA195Rows.olean"
lean -M5000 -j1 Computability/BusyBeaver/Research/PA/pa195/ipra/machine-code/TableDispatch.lean \
  -o "$BINARY_TAPE_TASK_DIR/TableDispatch.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
if rg -q "sorryAx" "$BINARY_TAPE_TASK_DIR/axioms.log"; then
  echo "Unexpected sorryAx in theorem dependencies" >&2
  exit 1
fi
'
