#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the pinned iPRA build}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the pinned Foundation build}"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
export IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
repo=$(git rev-parse --show-toplevel)
cd "$repo"
export PA194_COMBINED_ROOT="$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-marked-cycle-decrement.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/cycle" "$task_dir/decrement" "$task_dir/result"
python3 - "$base/check-positive-mark-cycle.sh" "$task_dir/cycle.sh" PA194_COMBINED_CYCLE <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)[ \t]*$', 'task_dir=$'+sys.argv[3], s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected cycle task directory')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected cycle cleanup')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
python3 - "$base/check-decrement-choice.sh" "$task_dir/decrement.sh" PA194_COMBINED_DECREMENT <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)[ \t]*$', 'task_dir=$'+sys.argv[3], s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected decrement task directory')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected decrement cleanup')
s=s.replace(old,'',1)
s,n=re.subn(r'^repo=\$\(git -C .* rev-parse --show-toplevel\)$', 'repo=$PA194_COMBINED_ROOT', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected decrement repository discovery')
Path(sys.argv[2]).write_text(s)
PY
export PA194_COMBINED_CYCLE="$task_dir/cycle" PA194_COMBINED_DECREMENT="$task_dir/decrement"
bash -n "$task_dir/cycle.sh"
bash -n "$task_dir/decrement.sh"
bash "$task_dir/cycle.sh"
bash "$task_dir/decrement.sh"
export LEAN_PATH="$task_dir/result:$task_dir/cycle:$task_dir/decrement:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for mod in PA194State59Even PA194State42Boundary PA194ReturnedDecrement PA194MarkedCycleDecrement; do
  lean -M6000 -j1 -o "$task_dir/result/$mod.olean" "$base/$mod.lean" | tee -a "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in marked-cycle decrement dependencies' >&2
  exit 1
fi
