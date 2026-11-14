#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
repo=$(git rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-scheduler-halt.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
export PA194_SCHEDULER_HALT_ROOT="$root"
python3 - "$base/pa194-scheduler-code/check.sh" "$root/scheduler-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-scheduler-code.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected scheduler prerequisite wrapper')
s=s.replace(old,'root=$PA194_SCHEDULER_HALT_ROOT',1).replace(trap,'',1)
s += '''\nlean -M6000 -j1 -o "$root/final/PA194SchedulerHalt.olean" "$base/pa194-scheduler-halt/PA194SchedulerHalt.lean" | tee "$root/final/halt-axioms.log"\nif rg -q 'sorryAx' "$root/final/halt-axioms.log"; then\n  echo 'Unexpected sorryAx in modeled scheduler halt endpoint' >&2\n  exit 1\nfi\n'''
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/scheduler-prerequisites.sh"
bash "$root/scheduler-prerequisites.sh"
