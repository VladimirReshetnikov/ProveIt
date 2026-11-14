#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-paeq-term-subst-growth.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
sha256sum -c "$base/pa194-paeq-term-blueprint/upstream.sha256"
sha256sum -c "$base/pa194-paeq-formula/upstream.sha256"
sha256sum -c "$base/pa194-paeq-bshift-growth/upstream.sha256"
sha256sum -c "$base/pa194-paeq-term-subst-growth/upstream.sha256"
export PA194_PAEQ_TERM_SUBST_REPO="$PWD"
python3 - "$base/pa196-vs-u208/ipra/check.sh" "$root/paeq-term-subst-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old = 'repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
marker = 'lean -M6000 -j1 "$bridge/PA196PAQVecTowerAlgebra.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAQVecTowerAlgebra.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"\n'
if s.count(old) != 1 or s.count(marker) != 1:
    raise SystemExit('unexpected qVec prerequisite wrapper')
s = s.replace(old, 'repo=$PA194_PAEQ_TERM_SUBST_REPO', 1)
s = s[:s.index(marker) + len(marker)] + '''lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-qvec-ceiling/PA194QVecCeiling.lean -o "$PA196_TASK_CHECK_DIR/PA194QVecCeiling.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
for task_mod in PA194PAeqTermBlueprint PA194PAeqTermCode; do
  lean -M6000 -j1 "Computability/BusyBeaver/Research/PA/pa194-paeq-term-blueprint/$task_mod.lean" -o "$PA196_TASK_CHECK_DIR/$task_mod.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
done
for task_mod in PA194PAeqSyntax PA194PAeqLanguage; do
  lean -M6000 -j1 "Computability/BusyBeaver/Research/PA/pa194-paeq-formula/$task_mod.lean" -o "$PA196_TASK_CHECK_DIR/$task_mod.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
done
for task_mod in PA194PAeqBShiftGrowth; do
  lean -M6000 -j1 "Computability/BusyBeaver/Research/PA/pa194-paeq-bshift-growth/$task_mod.lean" -o "$PA196_TASK_CHECK_DIR/$task_mod.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
done
for task_mod in PA194PAeqTermSubstGrowth PA194PAeqTermSubstVecGrowth; do
  lean -M6000 -j1 "Computability/BusyBeaver/Research/PA/pa194-paeq-term-subst-growth/$task_mod.lean" -o "$PA196_TASK_CHECK_DIR/$task_mod.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
done
if rg -q "sorryAx" "$PA196_TASK_CHECK_DIR/axioms.log"; then exit 1; fi
'\n'''
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/paeq-term-subst-prerequisites.sh"
bash "$root/paeq-term-subst-prerequisites.sh"
