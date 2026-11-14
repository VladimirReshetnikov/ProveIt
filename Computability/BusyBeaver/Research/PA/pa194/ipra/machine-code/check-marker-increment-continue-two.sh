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
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-marker-increment-continue-two.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-marker-to-increment.sh" "$task_dir/increment-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)[ \t]*$', 'task_dir=$PA194_MARKER_INCREMENT_CONTINUE_TWO_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected prerequisite task directory')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected prerequisite cleanup')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_MARKER_INCREMENT_CONTINUE_TWO_TASK_DIR="$task_dir"
bash -n "$task_dir/increment-prerequisites.sh"
bash "$task_dir/increment-prerequisites.sh"
export LEAN_PATH="$task_dir/result:$task_dir/cycle:$task_dir/decrement:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for module in PA194IncrementHeaderReturn PA194SevenIncrementHeader PA194SeventeenToRootControl PA194SevenToRootControl PA194IncrementOutputEven PA194ContinueIncrementTo24 PA194ContinueTwoDispatch PA194ContinueTwoHeader PA194SevenContinueTwo PA194IncrementContinueTwo PA194MarkerIncrementContinueTwo; do
  lean -M6000 -j1 -o "$task_dir/result/$module.olean" "$base/$module.lean" | tee -a "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in marker-increment-to-continue-two theorem dependencies' >&2
  exit 1
fi
