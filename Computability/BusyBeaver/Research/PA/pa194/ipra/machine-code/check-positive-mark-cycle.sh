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
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-positive-mark-cycle.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-positive-threshold.sh" "$task_dir/threshold-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)[ \t]*$', 'task_dir=$PA194_CYCLE_TASK_DIR', s, count=1, flags=re.M)
if n != 1:
    raise SystemExit('unexpected threshold prerequisite task directory')
line='\n'+"trap 'rm -rf \"$task_dir\"' EXIT"+'\n'
if s.count(line) != 1:
    raise SystemExit('unexpected threshold prerequisite cleanup')
s=s.replace(line,'\n',1)
Path(sys.argv[2]).write_text(s)
PY
export PA194_CYCLE_TASK_DIR="$task_dir"
bash -n "$task_dir/threshold-prerequisites.sh"
bash "$task_dir/threshold-prerequisites.sh"
export LEAN_PATH="$task_dir:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for mod in PA194ThresholdCycle PA194PositiveMarkCycle; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$base/$mod.lean" | tee -a "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in positive-marker cycle dependencies' >&2
  exit 1
fi
