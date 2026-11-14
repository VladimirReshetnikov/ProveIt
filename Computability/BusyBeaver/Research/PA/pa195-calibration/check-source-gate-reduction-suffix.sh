#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Foundation objects}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project objects}"
: "${PA194_GATE_PREREQ_PATH:?Set PA194_GATE_PREREQ_PATH to ordered colon-separated source and target prerequisite object directories}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-gate-reduction-suffix.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$PA194_GATE_PREREQ_PATH:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for name in PA194SourceGateReduction PA194SourceGateTargetLink; do
  lean -M6000 -j1 -o "$task_dir/$name.olean" "Computability/BusyBeaver/Research/PA/pa195-calibration/$name.lean" | tee -a "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in gate-reduction theorem dependencies' >&2
  exit 1
fi
