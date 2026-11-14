#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
repo=$(git rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-distinct-gate-endpoint.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/source" "$root/scheduler"
export PA194_DISTINCT_GATE_SRC="$root/source" PA194_DISTINCT_GATE_REPO="$repo"
python3 - "$base/pa195-calibration/check-equal-gate-numeric.sh" "$root/source-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-head6.XXXXXXXX")'
trap='trap \'rm -rf "$task_dir"\' EXIT'
repo='repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
if s.count(old) != 1 or s.count(trap) != 1 or s.count(repo) != 1:
    raise SystemExit('unexpected equal-gate prerequisite wrapper')
s=s.replace(repo,'repo=$PA194_DISTINCT_GATE_REPO',1).replace(old,'task_dir=$PA194_DISTINCT_GATE_SRC',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/source-prerequisites.sh"
bash "$root/source-prerequisites.sh"
python3 - "$base/pa194-scheduler-halt-code/check.sh" "$root/halt-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
line='lean -M6000 -j1 -o "$root/final/PA194SchedulerHaltCode.olean" "$base/pa194-scheduler-halt-code/PA194SchedulerHaltCode.lean" | tee "$root/final/halt-code-axioms.log"\n'
extra='''export LEAN_PATH="$PA194_DISTINCT_GATE_SRC:$LEAN_PATH"
lean -M6000 -j1 -o "$root/final/PA194DistinctGateEndpoint.olean" "$base/pa194-distinct-gate-endpoint/PA194DistinctGateEndpoint.lean" | tee "$root/final/distinct-gate-axioms.log"
if rg -q 'sorryAx' "$root/final/distinct-gate-axioms.log"; then exit 1; fi
'''
if s.count(line) != 1:
    raise SystemExit('unexpected halt-code prerequisite wrapper')
Path(sys.argv[2]).write_text(s.replace(line,line+extra,1))
PY
bash -n "$root/halt-prerequisites.sh"
bash "$root/halt-prerequisites.sh"
