#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-lk-budget-primrec
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-lk-budget-primrec.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/pa194-source-depth-primrec/check.sh" "$task_dir/lk-budget-primrec-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_LK_BUDGET_PRIMREC_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected source depth task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected source depth cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_LK_BUDGET_PRIMREC_TASK_DIR="$task_dir"
bash -n "$task_dir/lk-budget-primrec-prerequisites.sh"
bash "$task_dir/lk-budget-primrec-prerequisites.sh"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194BudgetSkeleton.olean" "$package/PA194BudgetSkeleton.lean" | tee "$task_dir/lk-budget-primrec-axioms.log"
if rg -q 'sorryAx' "$task_dir/lk-budget-primrec-axioms.log"; then
  echo 'Unexpected sorryAx in LK budget dependencies' >&2
  exit 1
fi
