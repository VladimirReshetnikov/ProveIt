#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Foundation object directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
printf '%s  %s\n' \
  4c87d00022da1dd0b75b3d73e184d04458835f362dcdda06e5529574ce2b99cf lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Incompleteness/InductionSchemeDelta1.lean \
  40a30f8715da59e118d4e337dc8ab5969186805af540bcb24300dba2f51e8ba5 "$IPRA_FOUNDATION_OVERLAY/Foundation/FirstOrder/Incompleteness/InductionSchemeDelta1.olean" | sha256sum --strict -c
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-iterated-free.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194IteratedFree.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194IteratedFree.lean | tee "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194OpeningHistory.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194OpeningHistory.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194QVecHistory.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194QVecHistory.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194QVecDistribution.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194QVecDistribution.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194OpeningShape.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194OpeningShape.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194InductionEndpoint.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194InductionEndpoint.lean | tee -a "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in theorem dependencies' >&2
  exit 1
fi
