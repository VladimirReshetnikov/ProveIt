#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Foundation objects}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project objects}"
: "${PA194_MODELED_GATE_PREREQ_PATH:?Set PA194_MODELED_GATE_PREREQ_PATH to ordered prerequisite object directories}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-modeled-halt-suffix.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$PA194_MODELED_GATE_PREREQ_PATH:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194DistinctGateNumeric.olean" Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-distinct-gate-sound/PA194DistinctGateNumeric.lean | tee "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194ModeledHaltRefutesPA.olean" Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-distinct-gate-sound/PA194ModeledHaltRefutesPA.lean | tee -a "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in theorem dependencies' >&2
  exit 1
fi
