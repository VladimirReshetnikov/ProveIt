#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-source-pra-codes
source=Computability/DiophantineConsistency/Lean/DiophantineConsistency
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-pra-codes.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/pa194-lk-budget-primrec/check.sh" "$task_dir/source-pra-codes-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_SOURCE_PRA_CODES_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected LK budget task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected LK budget cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_SOURCE_PRA_CODES_TASK_DIR="$task_dir"
bash -n "$task_dir/source-pra-codes-prerequisites.sh"
bash "$task_dir/source-pra-codes-prerequisites.sh"
sha256sum -c "$package/upstream.sha256"
mkdir -p "$task_dir/DiophantineConsistency"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for mod in PRAFunctionCodes PRAFiniteFunctionCodes; do
  lean -M6000 -j1 -o "$task_dir/DiophantineConsistency/$mod.olean" "$source/$mod.lean"
done
lean -M6000 -j1 -o "$task_dir/PA194SourcePRACodes.olean" "$package/PA194SourcePRACodes.lean" | tee "$task_dir/source-pra-codes-axioms.log"
if rg -q 'sorryAx' "$task_dir/source-pra-codes-axioms.log"; then
  echo 'Unexpected sorryAx in PRA code bridge dependencies' >&2
  exit 1
fi
