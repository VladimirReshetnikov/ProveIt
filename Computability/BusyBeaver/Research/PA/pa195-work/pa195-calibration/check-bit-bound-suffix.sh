#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Foundation objects}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project objects}"
: "${PA194_BIT_BOUND_PREREQ_PATH:?Set PA194_BIT_BOUND_PREREQ_PATH to the ordered prerequisite object directories}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-bit-bound-suffix.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$PA194_BIT_BOUND_PREREQ_PATH:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194InternalBitBound.olean" Computability/BusyBeaver/Research/PA/pa195-work/pa195-calibration/PA194InternalBitBound.lean | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in theorem dependencies' >&2
  exit 1
fi
