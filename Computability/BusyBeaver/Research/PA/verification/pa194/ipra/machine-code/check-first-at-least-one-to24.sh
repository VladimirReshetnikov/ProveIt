#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-first-at-least-one-wrapper.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-first-one-zero-to24.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old = 'PA194FirstOneZeroFinish PA194FirstOneZeroTo24; do'
new = ('PA194FirstOneZeroFinish PA194FirstOneZeroTo24 PA194FirstOnePositiveTo68 '
       'PA194FirstOnePositiveTo93 PA194HalfFileTwo PA194NinetyThreeReturnTwo '
       'PA194FirstOneHeaderTo24 PA194FirstOnePositiveTo24 PA194FirstOneAllTo24 '
       'PA194FirstAtLeastOneTo24; do')
if s.count(old) != 1:
    raise SystemExit('unexpected first-one zero-selected module list')
Path(sys.argv[2]).write_text(s.replace(old, new, 1))
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
