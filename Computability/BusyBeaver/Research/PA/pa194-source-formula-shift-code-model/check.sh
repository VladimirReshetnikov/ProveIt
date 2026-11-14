#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-source-formula-shift-code-model
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-formula-shift-code-model.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/source" "$root/update" "$root/final"
export PA194_SOURCE_SHIFT_SOURCE_DIR="$root/source" PA194_SOURCE_SHIFT_UPDATE_DIR="$root/update"
export PA194_SOURCE_SHIFT_REPO="$PWD"
python3 - "$base/pa194-source-atom-shift-code-model/check.sh" "$root/source-prerequisites.sh" "$base/pa195-calibration/check-formula-update.sh" "$root/update-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
src,srcout,update,updateout=sys.argv[1:]
def patch_task(text, var):
    text,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', f'task_dir=${var}', text, count=1, flags=re.M)
    if n != 1: raise SystemExit('unexpected prerequisite task directory declaration')
    old="trap 'rm -rf \"$task_dir\"' EXIT"
    if text.count(old) != 1: raise SystemExit('unexpected prerequisite cleanup declaration')
    return text.replace(old,'',1)
Path(srcout).write_text(patch_task(Path(src).read_text(),'PA194_SOURCE_SHIFT_SOURCE_DIR'))
s=patch_task(Path(update).read_text(),'PA194_SOURCE_SHIFT_UPDATE_DIR')
old='repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
if s.count(old) != 1: raise SystemExit('unexpected update repository declaration')
s=s.replace(old,'repo=$PA194_SOURCE_SHIFT_REPO',1)
old='lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa195-calibration/PA194FormulaUpdate.lean'
if s.count(old) != 1: raise SystemExit('unexpected formula update Lean invocation')
s=s.replace(old,'lean -M6000 -j1 -o "$task_dir/PA194FormulaUpdate.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194FormulaUpdate.lean',1)
Path(updateout).write_text(s)
PY
bash -n "$root/source-prerequisites.sh"
bash -n "$root/update-prerequisites.sh"
bash "$root/source-prerequisites.sh"
bash "$root/update-prerequisites.sh"
export LEAN_PATH="$root/final:$root/update:$root/source/final:$root/source/prereq/final:$root/source/prereq/model:$root/source/prereq/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for item in \
  'pa194-source-term-shift-code-model PA194TermShiftCodeModel' \
  'pa194-source-atom-shift-code-model PA194VectorShiftCodeModel' \
  'pa194-source-atom-shift-code-model PA194AtomShiftCodeModel'; do
  read -r dir name <<< "$item"
  lean -M6000 -j1 -o "$root/final/$name.olean" "$base/$dir/$name.lean" | tee -a "$root/final/axioms.log"
done
lean -M6000 -j1 -o "$root/final/PA194SourceShiftHistory.olean" "$package/PA194SourceShiftHistory.lean" | tee -a "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in source formula shift dependencies' >&2
  exit 1
fi
