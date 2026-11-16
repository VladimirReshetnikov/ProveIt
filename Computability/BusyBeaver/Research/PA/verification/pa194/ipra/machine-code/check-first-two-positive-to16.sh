#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-first-two-positive16-wrapper.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-first-three-first-split.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old = 'PA194FirstThreeFirstSplit; do'
new = ('PA194FirstThreeFirstSplit PA194FirstTwoBoundary PA194FirstTwoFirstTo86 '
       'PA194FirstTwoFirstTo73 PA194FirstTwoPositiveTo85 PA194FirstTwoPositiveTo106 '
       'PA194FirstTwoPositiveTo71 PA194HalfFileScan PA194HalfFileSix PA194FirstTwoPositiveTo14 '
       'PA194LeftOneRows PA194HalfFileSixShape PA194FirstTwoPositiveTo14Shape '
       'PA194FourteenOddTo16 PA194FirstTwoPositiveTo16; do')
if s.count(old) != 1:
    raise SystemExit('unexpected first-three split module list')
Path(sys.argv[2]).write_text(s.replace(old, new, 1))
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
