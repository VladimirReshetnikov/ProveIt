#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-calculus-soundness
upstream=$base/jamesyc-upstream/pa196/M6/Logic
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-calculus-soundness.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Retain fresh scheduler fairness and derivation-compiler prerequisites.
python3 - "$base/pa194-scheduler-fairness/check.sh" "$task_dir/sound-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_SOUND_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
s=s.replace(old,'',1)
old='lean -M6000 -j1 "$package/PA194Fairness.lean"'
new='lean -M6000 -j1 -o "$task_dir/PA194Fairness.olean" "$package/PA194Fairness.lean"'
if s.count(old)!=1: raise SystemExit('unexpected fairness theorem command')
Path(sys.argv[2]).write_text(s.replace(old,new,1))
PY
export PA194_SOUND_TASK_DIR="$task_dir"
bash "$task_dir/sound-prerequisites.sh"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
mkdir -p "$task_dir/M6/Logic"
lean -M6000 -j1 -o "$task_dir/M6/Logic/RestrictedImplication.olean" "$upstream/RestrictedImplication.lean"
lean -M6000 -j1 -o "$task_dir/PA194CalculusTruth.olean" "$package/PA194CalculusTruth.lean"
lean -M6000 -j1 "$package/PA194CalculusSoundness.lean" | tee "$task_dir/sound-axioms.log"
if rg -q 'sorryAx' "$task_dir/sound-axioms.log"; then
 echo 'Unexpected sorryAx in calculus/scheduler theorem' >&2
 exit 1
fi
