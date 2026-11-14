#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-relational-interface
upstream=$base/jamesyc-upstream/pa196/M6/Logic
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-relational-interface.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Retain the freshly rebuilt neighborhood prerequisites.
python3 - "$base/pa194-neighborhood/check.sh" "$task_dir/relational-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_RELATIONAL_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
s=s.replace(old,'',1)
old='lean -M6000 -j1 "$package/PA194NeighborhoodTransport.lean"'
new='lean -M6000 -j1 -o "$task_dir/PA194NeighborhoodTransport.olean" "$package/PA194NeighborhoodTransport.lean"'
if s.count(old)!=1: raise SystemExit('unexpected neighborhood theorem command')
Path(sys.argv[2]).write_text(s.replace(old,new,1))
PY
export PA194_RELATIONAL_TASK_DIR="$task_dir"
bash "$task_dir/relational-prerequisites.sh"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
mkdir -p "$task_dir/M6/Logic"
for mod in NativeCalculus NativeNamed NativeDecode NativeNames NativeRenaming; do
 lean -M6000 -j1 -o "$task_dir/M6/Logic/$mod.olean" "$upstream/$mod.lean"
done
lean -M6000 -j1 -o "$task_dir/PA194RelationalInterface.olean" "$package/PA194RelationalInterface.lean"
lean -M6000 -j1 -o "$task_dir/PA194RelationalEncoding.olean" "$package/PA194RelationalEncoding.lean" | tee "$task_dir/relational-axioms.log"
for mod in PA194RelationalAtoms PA194RelationalSubstitution PA194RelationalAlpha; do
 lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean" | tee -a "$task_dir/relational-axioms.log"
done
lean -M6000 -j1 "$package/PA194RelationalFreshening.lean" | tee -a "$task_dir/relational-axioms.log"
if rg -q 'sorryAx' "$task_dir/relational-axioms.log"; then
 echo 'Unexpected sorryAx in relational interface' >&2
 exit 1
fi
