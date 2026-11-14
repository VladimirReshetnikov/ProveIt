#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Foundation object directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
sha256sum --strict -c <<'PINS'
c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120  Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAStandardTheory.lean
66237bbe6f405e2b87fcf598b2fbef074c80264fccc87df11a25773e25756dd8  Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRASuccessorInductionConverse.lean
PINS
printf '%s  %s\n' \
  b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19 "$IPRA_LEAN_OVERLAY/DiophantineConsistency/IPRAStandardTheory.olean" \
  62eb77963e8989f7835d67782cb23ef1d76d706fa0dd91877b6ed0d70481a2a0 "$IPRA_LEAN_OVERLAY/DiophantineConsistency/IPRASuccessorInductionConverse.olean" | sha256sum --strict -c
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-verum-alias-check.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa195-calibration/PA194VerumAlias.lean | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in theorem dependencies' >&2
  exit 1
fi
