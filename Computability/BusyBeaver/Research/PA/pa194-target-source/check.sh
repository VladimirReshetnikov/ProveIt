#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
repo=$(git rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-target-source.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/source" "$root/scheduler"
export PA194_TARGET_SOURCE_SRC="$root/source" PA194_TARGET_SOURCE_SCHEDULER="$root/scheduler"
export PA194_TARGET_SOURCE_REPO="$repo"
python3 - "$base/pa195-calibration/check-source-diagonal-preservation.sh" "$root/source-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-head6.XXXXXXXX")'
trap='trap \'rm -rf "$task_dir"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected source-diagonal prerequisite wrapper')
repo='repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
if s.count(repo) != 1:
    raise SystemExit('unexpected source-head2 repository discovery')
s=s.replace(repo,'repo=$PA194_TARGET_SOURCE_REPO',1).replace(old,'task_dir=$PA194_TARGET_SOURCE_SRC',1).replace(trap,'',1)
s += '''\nfor module in PA194SourceLineSoundness PA194SourceLineRefutation; do\n  lean -M6000 -j1 -o "$task_dir/$module.olean" "Computability/BusyBeaver/Research/PA/pa195-calibration/$module.lean" | tee -a "$task_dir/axioms.log"\ndone\nif rg -q 'sorryAx' "$task_dir/axioms.log"; then exit 1; fi\n'''
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/source-prerequisites.sh"
bash "$root/source-prerequisites.sh"
python3 - "$base/pa194-scheduler-code/check.sh" "$root/scheduler-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-scheduler-code.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected scheduler prerequisite wrapper')
s=s.replace(old,'root=$PA194_TARGET_SOURCE_SCHEDULER',1).replace(trap,'',1)
s += '''
export LEAN_PATH="$PA194_TARGET_SOURCE_SRC:$LEAN_PATH"
for module in PA194SourceGateReduction PA194SourceGateTargetLink; do
  lean -M6000 -j1 -o "$root/final/$module.olean" "$base/pa195-calibration/$module.lean" | tee "$root/final/$module.axioms.log"
  if rg -q 'sorryAx' "$root/final/$module.axioms.log"; then exit 1; fi
done
lean -M6000 -j1 -o "$root/final/PA194SchedulerHalt.olean" "$base/pa194-scheduler-halt/PA194SchedulerHalt.lean" | tee "$root/final/halt-axioms.log"
lean -M6000 -j1 -o "$root/final/PA194TargetSource.olean" "$base/pa194-target-source/PA194TargetSource.lean" | tee "$root/final/source-axioms.log"
if rg -q 'sorryAx' "$root/final/halt-axioms.log" "$root/final/source-axioms.log"; then exit 1; fi
'''
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/scheduler-prerequisites.sh"
bash "$root/scheduler-prerequisites.sh"
