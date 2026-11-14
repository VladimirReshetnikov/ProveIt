#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-ax-guard
upstream=$base/jamesyc-upstream/pa196/M6/Source
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-ax-guard.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Reuse the core builder, retaining its private artifacts until this run ends.
python3 - "$base/pa194-ax-core/check.sh" "$task_dir/core.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_AX_GUARD_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected core task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected core cleanup declaration')
s=s.replace(old,'',1)
old='lean -M6000 -j1 --root="$task_dir" "$task_dir/PA194AXPlan.lean"'
new='lean -M6000 -j1 --root="$task_dir" -o "$task_dir/PA194AXPlan.olean" "$task_dir/PA194AXPlan.lean"'
if s.count(old)!=1: raise SystemExit('unexpected core aggregate command')
s=s.replace(old,new,1)
Path(sys.argv[2]).write_text(s)
PY
export PA194_AX_GUARD_TASK_DIR="$task_dir"
bash "$task_dir/core.sh"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for mod in AXGateCompareSteps AXGateCompare; do
  lean -M6000 -j1 -o "$task_dir/M6/Source/$mod.olean" "$upstream/$mod.lean"
done
for mod in PA194AXGateBinding PA194AXGateSteps PA194AXGate; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean"
done
lean -M6000 -j1 -o "$task_dir/PA194AXComplete.olean" "$package/PA194AXComplete.lean" | tee "$task_dir/guard-axioms.log"
lean -M6000 -j1 "$package/PA194AXReadable.lean" | tee -a "$task_dir/guard-axioms.log"
if rg -q 'sorryAx' "$task_dir/guard-axioms.log"; then
  echo 'Unexpected sorryAx in full AX source theorem' >&2
  exit 1
fi
