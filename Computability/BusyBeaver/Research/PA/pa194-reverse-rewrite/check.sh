#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-reverse-rewrite
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-reverse-rewrite.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Retain the freshly rebuilt separate/bundled derivation prerequisites.
python3 - "$base/pa194-bundled-diagonal/check.sh" "$task_dir/reverse-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_REVERSE_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
s=s.replace(old,'',1)
old='lean -M6000 -j1 "$package/PA194BundledDiagonal.lean"'
new='lean -M6000 -j1 -o "$task_dir/PA194BundledDiagonal.olean" "$package/PA194BundledDiagonal.lean"'
if s.count(old)!=1: raise SystemExit('unexpected bundled theorem command')
Path(sys.argv[2]).write_text(s.replace(old,new,1))
PY
export PA194_REVERSE_TASK_DIR="$task_dir"
bash "$task_dir/reverse-prerequisites.sh"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for mod in PA194ReverseSeeds PA194LogicBasic PA194LogicImplicationBasis PA194LogicDeduction PA194LogicConnectives PA194LogicVacuity PA194NegativeSpecialization; do
 lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean"
done
lean -M6000 -j1 "$package/PA194ReverseDistinct.lean" | tee "$task_dir/reverse-axioms.log"
if rg -q 'sorryAx' "$task_dir/reverse-axioms.log"; then
 echo 'Unexpected sorryAx in reverse membership rewrite' >&2
 exit 1
fi
