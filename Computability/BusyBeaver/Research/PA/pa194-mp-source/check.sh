#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-mp-source
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-mp-source.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Reuse the pinned source and macro prerequisite builder without AX batches.
python3 - "$base/pa194-ax-core/check.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_MP_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
s=s.replace(old,'',1)
marker='lean -M6000 -j1 -o "$task_dir/PA194AXSymbolic.olean"'
if s.count(marker)!=1: raise SystemExit('unexpected prerequisite boundary')
Path(sys.argv[2]).write_text(s[:s.index(marker)])
PY
export PA194_MP_TASK_DIR="$task_dir"
bash "$task_dir/prerequisites.sh"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for mod in PA194MPField PA194MPPush PA194MPCopy PA194MPCons PA194MPGuardSteps PA194MPGuard PA194MPStore PA194MPPrelude PA194MPSuccessPush; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean"
done
lean -M6000 -j1 "$package/PA194MPCommand.lean" | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in MP source theorem' >&2
  exit 1
fi
