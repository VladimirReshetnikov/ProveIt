#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-neighborhood
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-neighborhood.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Retain the freshly rebuilt reverse-rewrite prerequisites.
python3 - "$base/pa194-reverse-rewrite/check.sh" "$task_dir/neighborhood-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_NEIGHBORHOOD_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
s=s.replace(old,'',1)
old='lean -M6000 -j1 "$package/PA194ReverseDistinct.lean"'
new='lean -M6000 -j1 -o "$task_dir/PA194ReverseDistinct.olean" "$package/PA194ReverseDistinct.lean"'
if s.count(old)!=1: raise SystemExit('unexpected reverse theorem command')
Path(sys.argv[2]).write_text(s.replace(old,new,1))
PY
export PA194_NEIGHBORHOOD_TASK_DIR="$task_dir"
bash "$task_dir/neighborhood-prerequisites.sh"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194Neighborhood.olean" "$package/PA194Neighborhood.lean"
lean -M6000 -j1 "$package/PA194NeighborhoodTransport.lean" | tee "$task_dir/neighborhood-axioms.log"
if rg -q 'sorryAx' "$task_dir/neighborhood-axioms.log"; then
 echo 'Unexpected sorryAx in neighborhood interfaces' >&2
 exit 1
fi
