#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-compound-shift-step
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-compound-shift-step.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/prereq" "$task_dir/final"
export PA194_COMPOUND_SHIFT_PREREQ_DIR="$task_dir/prereq"
python3 - "$base/pa194-source-atom-shift-code-model/check.sh" "$task_dir/compound-shift-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_COMPOUND_SHIFT_PREREQ_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected atom shift code task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected atom shift code cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
bash -n "$task_dir/compound-shift-prerequisites.sh"
bash "$task_dir/compound-shift-prerequisites.sh"
export LEAN_PATH="$task_dir/final:$task_dir/prereq/final:$task_dir/prereq/prereq/final:$task_dir/prereq/prereq/model:$task_dir/prereq/prereq/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/final/PA194CompoundShiftStep.olean" "$package/PA194CompoundShiftStep.lean" | tee "$task_dir/final/axioms.log"
if rg -q 'sorryAx' "$task_dir/final/axioms.log"; then
  echo 'Unexpected sorryAx in compound shift dependencies' >&2
  exit 1
fi
