#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-derivation-compiler
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-derivation-compiler.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Retain the fresh source, scheduler, and diagonal-selector dependencies.
python3 - "$base/pa194-diagonal-selector/check.sh" "$task_dir/compiler-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_COMPILER_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
s=s.replace(old,'',1)
old='lean -M6000 -j1 "$package/PA194Diagonal.lean"'
new='lean -M6000 -j1 -o "$task_dir/PA194Diagonal.olean" "$package/PA194Diagonal.lean"'
if s.count(old)!=1: raise SystemExit('unexpected diagonal theorem command')
Path(sys.argv[2]).write_text(s.replace(old,new,1))
PY
export PA194_COMPILER_TASK_DIR="$task_dir"
bash "$task_dir/compiler-prerequisites.sh"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for mod in PA194HeadSelectors PA194RhoSelector PA194GateSelector; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean"
done
lean -M6000 -j1 "$package/PA194DerivationCompiler.lean" | tee "$task_dir/compiler-axioms.log"
if rg -q 'sorryAx' "$task_dir/compiler-axioms.log"; then
  echo 'Unexpected sorryAx in derivation compiler' >&2
  exit 1
fi
