#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-qvec-ceiling.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
export PA194_QVEC_REPO="$PWD"
python3 - "$base/pa196-vs-u208/ipra/check.sh" "$root/qvec-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old = 'repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
marker = 'lean -M6000 -j1 "$bridge/PA196PAQVecTowerAlgebra.lean" -o "$PA196_TASK_CHECK_DIR/PA196PAQVecTowerAlgebra.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"\n'
if s.count(old) != 1 or s.count(marker) != 1:
    raise SystemExit('unexpected qVec prerequisite wrapper')
s = s.replace(old, 'repo=$PA194_QVEC_REPO', 1)
s = s[:s.index(marker) + len(marker)] + '''lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-qvec-ceiling/PA194QVecCeiling.lean -o "$PA196_TASK_CHECK_DIR/PA194QVecCeiling.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
if rg -q "sorryAx" "$PA196_TASK_CHECK_DIR/axioms.log"; then exit 1; fi
'\n'''
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/qvec-prerequisites.sh"
bash "$root/qvec-prerequisites.sh"
