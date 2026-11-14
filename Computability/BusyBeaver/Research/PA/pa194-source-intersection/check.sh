#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-source-intersection
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-intersection.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/pa194-source-context/check.sh" "$task_dir/source-intersection-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_INTERSECTION_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected source context task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected source context cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_INTERSECTION_TASK_DIR="$task_dir"
bash -n "$task_dir/source-intersection-prerequisites.sh"
bash "$task_dir/source-intersection-prerequisites.sh"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194SourceIntersection.olean" "$package/PA194SourceIntersection.lean" | tee "$task_dir/source-intersection-axioms.log"
if rg -q 'sorryAx' "$task_dir/source-intersection-axioms.log"; then
  echo 'Unexpected sorryAx in intersection theorem dependencies' >&2
  exit 1
fi
