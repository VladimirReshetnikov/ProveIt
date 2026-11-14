#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-foundation-closed-separation
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-foundation-closed-separation.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/pa194-source-separation/check.sh" "$task_dir/foundation-closed-separation-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_FOUNDATION_CLOSED_SEPARATION_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected source separation task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected source separation cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_FOUNDATION_CLOSED_SEPARATION_TASK_DIR="$task_dir"
bash -n "$task_dir/foundation-closed-separation-prerequisites.sh"
bash "$task_dir/foundation-closed-separation-prerequisites.sh"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194FoundationClosedSeparation.olean" "$package/PA194FoundationClosedSeparation.lean" | tee "$task_dir/closed-separation-axioms.log"
if rg -q 'sorryAx' "$task_dir/closed-separation-axioms.log"; then
  echo 'Unexpected sorryAx in closed separation theorem dependencies' >&2
  exit 1
fi
