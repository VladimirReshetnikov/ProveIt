#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-source-term-shift-code-model
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-term-shift-code-model.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/source" "$root/model" "$root/final"
export PA194_TERM_CODE_SOURCE_DIR="$root/source" PA194_TERM_CODE_MODEL_DIR="$root/model"
export PA194_TERM_CODE_REPO="$PWD"
python3 - "$base/pa194-source-term-shift-model/check.sh" "$root/source-prerequisites.sh" "$base/pa195-calibration/check-term-well-formed-unconditional.sh" "$root/model-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
src,srcout,model,modelout=sys.argv[1:]
def patch_task(text, var):
    text,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', f'task_dir=${var}', text, count=1, flags=re.M)
    if n != 1: raise SystemExit('unexpected prerequisite task directory declaration')
    old="trap 'rm -rf \"$task_dir\"' EXIT"
    if text.count(old) != 1: raise SystemExit('unexpected prerequisite cleanup declaration')
    return text.replace(old,'',1)
Path(srcout).write_text(patch_task(Path(src).read_text(),'PA194_TERM_CODE_SOURCE_DIR'))
s=patch_task(Path(model).read_text(),'PA194_TERM_CODE_MODEL_DIR')
old='repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
if s.count(old) != 1: raise SystemExit('unexpected model repository declaration')
s=s.replace(old,'repo=$PA194_TERM_CODE_REPO',1)
marker='lean -M6000 -j1 -o "$task_dir/PA194FVarCode.olean"'
if s.count(marker) != 1: raise SystemExit('unexpected model dependency boundary')
s=s[:s.index(marker)] + '''if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in model prerequisites' >&2
  exit 1
fi
'''
Path(modelout).write_text(s)
PY
bash -n "$root/source-prerequisites.sh"
bash -n "$root/model-prerequisites.sh"
bash "$root/source-prerequisites.sh"
bash "$root/model-prerequisites.sh"
export LEAN_PATH="$root/final:$root/model:$root/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194TermShiftCodeModel.olean" "$package/PA194TermShiftCodeModel.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in source term shift code dependencies' >&2
  exit 1
fi
