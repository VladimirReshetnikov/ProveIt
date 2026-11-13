#!/usr/bin/env bash
set -euo pipefail

# The two dependency overlays must have been built from the matching sources;
# see README.md.  This script rebuilds the literal-machine and bridge modules.
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the built iPRA module directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the built Foundation module directory}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"

sha256sum -c <<'PINS'
152d1d552b27baca8db0ac05b16092d9083c2ab979bb0b4e7f96a95803d9a9b0  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Zip.lean
e5ed123ad8e54d431472621d46b6f147a76ed94426efc9e9298f475e8ecca944  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Literal.lean
e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/data/pa196.tm
5e21edfdc4593f441f46f7fde9f8d0fc467eb1369c03251fe4f3a1a4d17a57de  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRALanguage.lean
f0a5ba7482344477c2c7ca5ec2544f127ede62ec30e60b1101bfaed7be94db74  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean
PINS

task_dir=$(mktemp -d "${TMPDIR:-/tmp}/pa196-ipra-check.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6" "$task_dir/PA196"
export PA196_TASK_CHECK_DIR="$task_dir" IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
lake env bash -c '
set -euo pipefail
lean --version | rg -q "Lean \(version 4\.32\.0"
export LEAN_PATH="$PA196_TASK_CHECK_DIR:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:${LEAN_PATH:-}"
upstream=Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196
bridge=Computability/BusyBeaver/Research/PA/pa196-vs-u208/ipra
lean -M6000 -j1 "$upstream/M6/Zip.lean" -o "$PA196_TASK_CHECK_DIR/M6/Zip.olean"
lean -M6000 -j1 "$upstream/PA196/Literal.lean" -o "$PA196_TASK_CHECK_DIR/PA196/Literal.olean"
lean -M6000 -j1 "$bridge/PA196Bounded.lean" -o "$PA196_TASK_CHECK_DIR/PA196Bounded.olean"
lean -M6000 -j1 "$bridge/PA196BoundedChecks.lean" | tee "$PA196_TASK_CHECK_DIR/axioms.log"
if rg -q "sorryAx" "$PA196_TASK_CHECK_DIR/axioms.log"; then
  echo "Unexpected sorryAx in theorem dependencies" >&2
  exit 1
fi
'
