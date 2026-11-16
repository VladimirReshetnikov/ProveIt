#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-first-one-zero-wrapper.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-first-at-least-two-to24.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old = 'PA194FirstTwoZeroFinish PA194FirstTwoZeroTo24 PA194FirstTwoAllTo24 PA194FirstAtLeastTwoTo24; do'
new = ('PA194FirstTwoZeroFinish PA194FirstTwoZeroTo24 PA194FirstTwoAllTo24 PA194FirstAtLeastTwoTo24 '
       'PA194FirstOneBoundary PA194FirstOneFirstTo36 PA194FirstOneFirstTo48 '
       'PA194FirstOneZeroTo1 PA194FirstOneZeroTo3 PA194FirstOneZeroTo7 PA194FirstOneZeroReturn '
       'PA194FirstOneZeroFinish PA194FirstOneZeroTo24; do')
if s.count(old) != 1:
    raise SystemExit('unexpected first-at-least-two module list')
Path(sys.argv[2]).write_text(s.replace(old, new, 1))
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
