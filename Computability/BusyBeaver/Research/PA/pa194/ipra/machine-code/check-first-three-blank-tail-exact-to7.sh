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
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-first-three-first-split.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-marker-to-increment.sh" "$task_dir/increment-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)[ \t]*$', 'task_dir=$PA194_FIRST_THREE_FIRST_SPLIT_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected prerequisite task directory')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected prerequisite cleanup')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_FIRST_THREE_FIRST_SPLIT_TASK_DIR="$task_dir"
bash -n "$task_dir/increment-prerequisites.sh"
bash "$task_dir/increment-prerequisites.sh"
export LEAN_PATH="$task_dir/result:$task_dir/cycle:$task_dir/decrement:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for module in PA194IncrementHeaderReturn PA194SevenIncrementHeader PA194SeventeenToRootControl PA194SevenToRootControl PA194IncrementOutputEven PA194ContinueIncrementTo24 PA194ContinueTwoDispatch PA194ContinueTwoHeader PA194SevenContinueTwo PA194IncrementContinueTwo PA194MarkerIncrementContinueTwo PA194ZeroFirstReturn PA194ZeroFirstHeader PA194ZeroFirstContinue PA194ZeroIncrementContinue PA194MarkerZeroIncrementContinue PA194AllFirstMarkerContinue PA194NineOdd PA194ZeroSelectedRollback PA194SelectedZeroTo12 PA194ZeroSelectedScan PA194MarkerZeroSelectedTo12 PA194ZeroReturnedFileEven PA194MarkerZeroSelectedTo15 PA194SelectedZeroFifteenReturn PA194SelectedZeroActualReturn PA194SelectedZeroSeventeenTo24 PA194MarkerZeroSelectedTo17 PA194MarkerZeroSelectedTo24 PA194AllSelectedMarkerTo24 PA194FirstFiveTo84 PA194FirstFiveSuccCore PA194FirstFiveSuccTo15 PA194FirstFiveFirstCore PA194FirstFiveFirstTo15 PA194FirstFiveAllTo15 PA194FirstFiveFifteenTo24 PA194FirstFiveAllTo24 PA194FirstSixPositiveHeader PA194FirstSixPositiveTo24 PA194ReturnedFileEven PA194MarkerFirstSixPositiveTo24 PA194FirstSixAllTo24 PA194FirstAtLeastFiveTo24 PA194FirstThreeBoundary PA194FirstThreeFileCases PA194FirstThreeFirstTo42 PA194FirstThreeFirstSplit PA194FirstThreePositiveTo1 PA194FirstThreePositiveScan PA194FirstThreePositiveTo3 PA194CarryThreeFile PA194FirstThreePositiveCarry PA194CarryThreeOddFile PA194ThreeBlankTail PA194FirstThreeBlankTailTo7 PA194CarryThreeExactFile PA194FirstThreeBlankTailExactTo7; do
  lean -M6000 -j1 -o "$task_dir/result/$module.olean" "$base/$module.lean" | tee -a "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in first-three-blank-tail-exact-to7 theorem dependencies' >&2
  exit 1
fi
