#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Foundation object directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
sha256sum --strict -c <<'PINS'
aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84  Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCantor.lean
d7ea33865ce8c7ce192a0abf1bbd7246dee3a00d595491027ac75b711831ac40  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAWitnessTransfer.lean
PINS
printf '%s  %s\n' \
  73992c2c19e098f4e60767aaab2c5dedf37f6a90a81adb561034848fd20f5ab7 "$IPRA_LEAN_OVERLAY/BusyBeaver/ZFC/ArithmeticCantor.olean" \
  c8e29b70f19c4dc4f85fdaf8b3e053f7628a939915cac1be270b4774e6133e0b "$IPRA_LEAN_OVERLAY/DiophantineConsistency/PRAWitnessTransfer.olean" | sha256sum --strict -c
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-tag-code-check.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
export LEAN_PATH="$task_dir:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa195-calibration/PA194TagCode.lean | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in theorem dependencies' >&2
  exit 1
fi
