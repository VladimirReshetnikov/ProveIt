#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the pinned iPRA build}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the pinned Foundation build}"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
export IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
repo=$(git rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-dispatch-increment.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-header-controller.sh" "$task_dir/header-prerequisites.sh" \
  "$base/check-increment-source.sh" "$task_dir/increment-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
for src,dst in ((sys.argv[1],sys.argv[2]),(sys.argv[3],sys.argv[4])):
    s=Path(src).read_text()
    old='repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
    line='\n'+old+'\n'
    if line in s:
        if s.count(line) != 1:
            raise SystemExit('unexpected prerequisite repository discovery')
        s=s.replace(line,'\nrepo=$PA194_DISPATCH_REPO\n',1)
    s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)[ \t]*$', 'task_dir=$PA194_DISPATCH_TASK_DIR', s, count=1, flags=re.M)
    if n != 1:
        raise SystemExit('unexpected prerequisite task directory')
    old="trap 'rm -rf \"$task_dir\"' EXIT"
    if s.count(old) != 1:
        raise SystemExit('unexpected prerequisite cleanup')
    s=s.replace(old,'',1)
    Path(dst).write_text(s)
PY
export PA194_DISPATCH_TASK_DIR="$task_dir" PA194_DISPATCH_REPO="$repo"
bash -n "$task_dir/header-prerequisites.sh"
bash -n "$task_dir/increment-prerequisites.sh"
bash "$task_dir/header-prerequisites.sh"
bash "$task_dir/increment-prerequisites.sh"
export LEAN_PATH="$task_dir:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for mod in PA194RightRows PA194IncrementDispatch PA194DispatchIncrementSource; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$base/$mod.lean" | tee -a "$task_dir/axioms.log"
done
if rg -q 'sorryAx' "$task_dir/axioms.log"; then
  echo 'Unexpected sorryAx in dispatch-increment theorem dependencies' >&2
  exit 1
fi
