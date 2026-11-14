#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-diagonal-selector
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-diagonal-selector.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Retain the full checked source/command prerequisites until this run ends.
python3 - "$base/pa194-command-source/check.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_DIAGONAL_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_DIAGONAL_TASK_DIR="$task_dir"
bash "$task_dir/prerequisites.sh"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for mod in PA194Words PA194Pops PA194ShiftTwo PA194AXOnce PA194HeadShape; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean"
done
lean -M6000 -j1 "$package/PA194Diagonal.lean" | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in diagonal selector' >&2
  exit 1
fi
