#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-standard-stepper-wrapper.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-stepper-zip.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old_repo = 'repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
new_repo = 'repo=$(git rev-parse --show-toplevel)'
old_check = 'if rg -q "sorryAx" "$BINARY_TAPE_TASK_DIR/axioms.log"; then'
new_check = '''lean -M6000 -j1 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194StandardCodeBridge.lean \\
  -o "$BINARY_TAPE_TASK_DIR/PA194StandardCodeBridge.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194StandardStepperBridge.lean \\
  -o "$BINARY_TAPE_TASK_DIR/PA194StandardStepperBridge.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
lean -M6000 -j1 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194PackedNumeralBridge.lean \\
  -o "$BINARY_TAPE_TASK_DIR/PA194PackedNumeralBridge.olean" | tee -a "$BINARY_TAPE_TASK_DIR/axioms.log"
''' + old_check
if s.count(old_repo) != 1 or s.count(old_check) != 1:
    raise SystemExit('unexpected stepper-zip checker structure')
s = s.replace(old_repo, new_repo, 1).replace(old_check, new_check, 1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
