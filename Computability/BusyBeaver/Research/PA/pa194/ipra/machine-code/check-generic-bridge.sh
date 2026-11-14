#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the pinned iPRA build}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the pinned Foundation build}"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
export IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
repo=$(git rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-generic-bridge.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-mark-all.sh" "$task_dir/bridge-mark-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
old='repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
if s.count(old) != 1:
    raise SystemExit('unexpected bridge prerequisite repository discovery')
s=s.replace(old,'repo=$PA194_BRIDGE_REPO',1)
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)[ \t]*$', 'task_dir=$PA194_BRIDGE_TASK_DIR', s, count=1, flags=re.M)
if n != 1:
    raise SystemExit('unexpected bridge prerequisite task directory')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1:
    raise SystemExit('unexpected bridge prerequisite cleanup')
s=s.replace(old,'',1)
Path(sys.argv[2]).write_text(s)
PY
export PA194_BRIDGE_TASK_DIR="$task_dir" PA194_BRIDGE_REPO="$repo"
bash -n "$task_dir/bridge-mark-prerequisites.sh"
bash "$task_dir/bridge-mark-prerequisites.sh"
sha256sum --strict -c <<'PINS'
aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84  Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCantor.lean
d7ea33865ce8c7ce192a0abf1bbd7246dee3a00d595491027ac75b711831ac40  Computability/DiophantineConsistency/Lean/DiophantineConsistency/PRAWitnessTransfer.lean
PINS
printf '%s  %s\n' \
  73992c2c19e098f4e60767aaab2c5dedf37f6a90a81adb561034848fd20f5ab7 "$IPRA_LEAN_OVERLAY/BusyBeaver/ZFC/ArithmeticCantor.olean" \
  c8e29b70f19c4dc4f85fdaf8b3e053f7628a939915cac1be270b4774e6133e0b "$IPRA_LEAN_OVERLAY/DiophantineConsistency/PRAWitnessTransfer.olean" | sha256sum --strict -c
# The history graph requires a writable project overlay. Copy symlinks, then
# replace the rebuilt objects; the pinned input overlay itself is never modified.
cp -as "$IPRA_LEAN_OVERLAY/." "$task_dir/"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for name in PRAWitnessRefutationOuter IPRAPA196Consistency; do
  rm -f "$task_dir/DiophantineConsistency/$name.olean"
  lean -M6000 -j1 -o "$task_dir/DiophantineConsistency/$name.olean" \
    "Computability/DiophantineConsistency/Lean/DiophantineConsistency/$name.lean"
done
for name in PRAHistoryLengthUnique PRAHistorySingletonMembership PRAHistorySingletonSequence PRAHistoryIterator PRAHistoryTrace PRAHistoryResultGraph; do
  rm -f "$task_dir/DiophantineConsistency/$name.olean"
  lean -M6000 -j1 -o "$task_dir/DiophantineConsistency/$name.olean" \
    "Computability/DiophantineConsistency/Lean/DiophantineConsistency/$name.lean"
done
lean -M6000 -j1 -o "$task_dir/PA194UnaryRecursionGraph.olean" \
  Computability/BusyBeaver/Research/PA/pa195-calibration/PA194UnaryRecursionGraph.lean | tee -a "$task_dir/axioms.log"
# The wrapper independently rebuilds the PA witness certificate and the
# generic IΣ₁ transfer from their local sources in a separate private overlay.
IPRA_LEAN_OVERLAY="$task_dir" python3 -B Computability/BusyBeaver/Research/PA/isigma1-machine/check_unconditional.py --out "$task_dir/conpa"
export LEAN_PATH="$task_dir:$task_dir/conpa:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/ConPAMachine.olean" Computability/BusyBeaver/Research/PA/isigma1-machine/ConPAMachine.lean
for mod in PA194HalfDiv PA194GenericBridge PA194Reachable; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$base/$mod.lean" | tee -a "$task_dir/axioms.log"
done
for mod in PA194ForwardGG PA194StandardSemantics; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "Computability/BusyBeaver/Research/PA/pa194/ipra/$mod.lean" | tee -a "$task_dir/axioms.log"
done
lean -M6000 -j1 -o "$task_dir/PA194ExplicitEndpoint.olean" "$base/PA194ExplicitEndpoint.lean" | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA195RefutationBridge.olean" \
  Computability/BusyBeaver/Research/PA/pa195/ipra/PA195RefutationBridge.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 -o "$task_dir/PA194GenericHalt.olean" "$base/PA194GenericHalt.lean" | tee -a "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in bridge theorem dependencies' >&2
  exit 1
fi
