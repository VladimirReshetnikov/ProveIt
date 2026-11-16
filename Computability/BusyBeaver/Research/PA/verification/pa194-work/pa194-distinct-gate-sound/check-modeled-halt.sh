#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
: "${PA194_MODELED_GATE_PREREQ_PATH:?Set PA194_MODELED_GATE_PREREQ_PATH to ordered general-witness prerequisite object directories}"
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA/verification
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-modeled-halt-pa.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/pa194-work/pa194-distinct-gate-endpoint/check.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
line = 'lean -M6000 -j1 -o "$root/final/PA194DistinctGateEndpoint.olean" "$base/pa194-work/pa194-distinct-gate-endpoint/PA194DistinctGateEndpoint.lean" | tee "$root/final/distinct-gate-axioms.log"\n'
extra = '''export LEAN_PATH="$root/final:$PA194_DISTINCT_GATE_SRC:$PA194_MODELED_GATE_PREREQ_PATH:$LEAN_PATH"
lean -M6000 -j1 -o "$root/final/PA194DistinctGateNumeric.olean" "$base/pa194-work/pa194-distinct-gate-sound/PA194DistinctGateNumeric.lean" | tee "$root/final/distinct-numeric-axioms.log"
lean -M6000 -j1 -o "$root/final/PA194ModeledHaltRefutesPA.olean" "$base/pa194-work/pa194-distinct-gate-sound/PA194ModeledHaltRefutesPA.lean" | tee "$root/final/modeled-halt-axioms.log"
if rg -q 'sorryAx' "$root/final/distinct-numeric-axioms.log" "$root/final/modeled-halt-axioms.log"; then exit 1; fi
'''
if s.count(line) != 1:
    raise SystemExit('unexpected distinct gate endpoint Lean command')
Path(sys.argv[2]).write_text(s.replace(line, line + extra, 1))
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
