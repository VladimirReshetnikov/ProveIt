#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-first-all-wrapper.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import re
import subprocess
import sys

base = Path(sys.argv[1])
out = Path(sys.argv[2])
s = (base / 'check-first-at-least-one-to24.sh').read_text()
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
s = s.replace(old, new, 1)
# The next three wrappers only prepare another shell script. Run those pure
# preparation snippets here so none discovers Git from its temporary location.
pat = re.compile(r'''python3 - "\$base/([^" ]+)" "\$task_dir/([^" ]+)" <<'PY'\n(.*?)\nPY''', re.S)
for n in range(3):
    m = pat.search(s)
    if m is None:
        raise SystemExit(f'unexpected nested wrapper at preparation layer {n}')
    tmp = out.with_name(f'prepared-{n}.sh')
    subprocess.run([sys.executable, '-', str(base / m.group(1)), str(tmp)],
                   input=m.group(3), text=True, check=True)
    s = tmp.read_text()
if 'repo=$(git rev-parse --show-toplevel)' not in s:
    raise SystemExit('unexpected combined prerequisite repository discovery')
if re.search(r'^repo=\$\(git -C ', s, re.M):
    raise SystemExit('combined prerequisite still discovers Git from its temporary directory')
out.write_text(s)
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
