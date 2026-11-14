#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
wrapper=$(mktemp "${TMPDIR:-/dev/shm}/pa194-one-way-check.XXXXXXXX")
trap 'rm -f "$wrapper"' EXIT
python3 - Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-generic-bridge.sh "$wrapper" <<'PY'
from pathlib import Path
import sys
source = Path(sys.argv[1]).read_text()
marker = "if rg -q 'sorryAx' \"$task_dir/axioms.log\"; then"
if source.count(marker) != 1:
    raise SystemExit('unexpected generic-bridge axiom-check marker')
addition = '''lean -M6000 -j1 -o "$task_dir/ConPAISigma1Directions.olean" \\
  Computability/BusyBeaver/Research/PA/isigma1-machine/ConPAISigma1Directions.lean | tee -a "$task_dir/axioms.log"
lean -M6000 -j1 "$base/PA194OneWayEndpoint.lean" | tee -a "$task_dir/axioms.log"
'''
Path(sys.argv[2]).write_text(source.replace(marker, addition + marker))
PY
bash -n "$wrapper"
bash "$wrapper"
