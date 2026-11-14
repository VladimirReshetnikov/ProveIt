#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-shift-source
upstream=$base/jamesyc-upstream/pa196/M6/Source
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-shift-source.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Reuse the pinned source/macro prerequisite builder without the AX batches.
python3 - "$base/pa194-ax-core/check.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_SHIFT_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
s=s.replace(old,'',1)
marker='lean -M6000 -j1 -o "$task_dir/PA194AXSymbolic.olean"'
if s.count(marker)!=1: raise SystemExit('unexpected prerequisite boundary')
Path(sys.argv[2]).write_text(s[:s.index(marker)])
PY
export PA194_SHIFT_TASK_DIR="$task_dir"
bash "$task_dir/prerequisites.sh"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for mod in S36Drain CyclicDriver NonexitCycle; do
  lean -M6000 -j1 -o "$task_dir/M6/Source/$mod.olean" "$upstream/$mod.lean"
done
for mod in PA194StackDecode PA194NIPBinding PA194S36Binding PA194S36Lift PA194NIPGuard; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean"
done
lean -M6000 -j1 "$package/PA194ShiftCommand.lean" | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in Shift source theorem' >&2
  exit 1
fi
