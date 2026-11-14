#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-scheduler-halt-code.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
python3 - "$base/pa194-scheduler-to-pa/check.sh" "$root/halt-code-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
line = 'lean -M6000 -j1 -o "$root/final/PA194SchedulerToPA.olean" "$base/pa194-scheduler-to-pa/PA194SchedulerToPA.lean" | tee "$root/final/endpoint-axioms.log"\n'
extra = '''lean -M6000 -j1 -o "$root/final/PA194SchedulerHaltCode.olean" "$base/pa194-scheduler-halt-code/PA194SchedulerHaltCode.lean" | tee "$root/final/halt-code-axioms.log"
if rg -q 'sorryAx' "$root/final/halt-code-axioms.log"; then exit 1; fi
'''
if s.count(line) != 1:
    raise SystemExit('unexpected scheduler endpoint Lean command')
Path(sys.argv[2]).write_text(s.replace(line, line + extra, 1))
PY
bash -n "$root/halt-code-prerequisites.sh"
bash "$root/halt-code-prerequisites.sh"
