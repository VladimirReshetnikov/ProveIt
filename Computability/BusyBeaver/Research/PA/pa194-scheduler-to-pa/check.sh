#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-scheduler-to-pa.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/bridge"
export PA194_SCHEDULER_PA_BRIDGE_ROOT="$root/bridge"
python3 - "$base/pa194-target-source/check.sh" "$root/bridge-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-target-source.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected target-to-PA bridge prerequisite wrapper')
s=s.replace(old,'root=$PA194_SCHEDULER_PA_BRIDGE_ROOT',1).replace(trap,'',1)
line='lean -M6000 -j1 -o "$root/final/PA194TargetSource.olean" "$base/pa194-target-source/PA194TargetSource.lean" | tee "$root/final/source-axioms.log"\n'
extra='''lean -M6000 -j1 -o "$root/final/PA194SchedulerIteration.olean" "$base/pa194-scheduler-iteration/PA194SchedulerIteration.lean" | tee "$root/final/iteration-axioms.log"
lean -M6000 -j1 -o "$root/final/PA194SchedulerToPA.olean" "$base/pa194-scheduler-to-pa/PA194SchedulerToPA.lean" | tee "$root/final/endpoint-axioms.log"
if rg -q 'sorryAx' "$root/final/iteration-axioms.log" "$root/final/endpoint-axioms.log"; then exit 1; fi
'''
if s.count(line) != 1:
    raise SystemExit('unexpected target-to-PA bridge Lean command')
s=s.replace(line,line+extra,1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/bridge-prerequisites.sh"
bash "$root/bridge-prerequisites.sh"
