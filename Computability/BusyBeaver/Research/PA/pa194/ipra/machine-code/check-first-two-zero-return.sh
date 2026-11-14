#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-first-two-zero-return-wrapper.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-first-three-blank-tail-to24.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old = 'PA194FirstThreeBlankTailTo24; do'
new = ('PA194FirstThreeBlankTailTo24 PA194FirstTwoBoundary PA194FirstTwoFirstTo86 '
       'PA194FirstTwoFirstTo73 PA194FirstTwoPositiveTo85 PA194FirstTwoPositiveTo106 '
       'PA194FirstTwoPositiveTo71 PA194FirstTwoZeroTo1 PA194FirstTwoZeroTo3 '
       'PA194FirstTwoZeroTo7 PA194FirstTwoZeroReturn; do')
if s.count(old) != 1:
    raise SystemExit('unexpected first-three module list')
Path(sys.argv[2]).write_text(s.replace(old, new, 1))
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
