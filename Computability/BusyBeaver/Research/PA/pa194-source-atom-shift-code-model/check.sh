#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-source-atom-shift-code-model
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-atom-shift-code-model.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/prereq" "$task_dir/final"
export PA194_ATOM_SHIFT_CODE_PREREQ_ROOT="$task_dir/prereq"
python3 - "$base/pa194-source-term-shift-code-model/check.sh" "$task_dir/atom-shift-code-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^root=\$\(mktemp[^\n]*\)\s*$', 'root=$PA194_ATOM_SHIFT_CODE_PREREQ_ROOT', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected term shift code root declaration')
old="trap 'rm -rf \"$root\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected term shift code cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
bash -n "$task_dir/atom-shift-code-prerequisites.sh"
bash "$task_dir/atom-shift-code-prerequisites.sh"
export LEAN_PATH="$task_dir/final:$task_dir/prereq/final:$task_dir/prereq/model:$task_dir/prereq/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for name in PA194VectorShiftCodeModel PA194AtomShiftCodeModel; do
  lean -M6000 -j1 -o "$task_dir/final/$name.olean" "$package/$name.lean" | tee -a "$task_dir/final/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/final/axioms.log"; then
  echo 'Unexpected sorryAx in source atom shift code dependencies' >&2
  exit 1
fi
