#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
# Nested wrappers are generated under TMPDIR; keep Git bound to this worktree.
export GIT_DIR="$(git rev-parse --absolute-git-dir)"
export GIT_WORK_TREE="$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-first-all-wrapper.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-first-at-least-one-to24.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old = 'PA194FirstAtLeastOneTo24; do'
new = ('PA194FirstAtLeastOneTo24 PA194FirstZeroBoundary '
       'PA194FirstZeroFirstTo46 PA194FirstZeroFirstTo110 PA194FirstZeroZeroTo1 '
       'PA194FirstZeroZeroTo3 PA194FirstZeroZeroTo7 PA194FirstZeroZeroReturn '
       'PA194FirstZeroZeroFinish PA194FirstZeroZeroTo24 '
       'PA194FirstZeroPositiveTo95 PA194FirstZeroPositiveTo114 PA194HalfFileFour '
       'PA194FirstZeroPositiveTo16 PA194SixteenFourRuns PA194OneFourteenReturnFour '
       'PA194FirstZeroHeaderTo24 PA194FirstZeroPositiveTo24 PA194FirstZeroAllTo24 '
       'PA194FirstAllTo24; do')
if s.count(old) != 1:
    raise SystemExit('unexpected first-at-least-one module list')
Path(sys.argv[2]).write_text(s.replace(old, new, 1))
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
