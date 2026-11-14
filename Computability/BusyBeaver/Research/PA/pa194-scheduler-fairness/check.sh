#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-scheduler-fairness
upstream=$base/jamesyc-upstream/pa196/M6/Source
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-scheduler-fairness.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Retain the freshly rebuilt derivation compiler and its prerequisites.
python3 - "$base/pa194-derivation-compiler/check.sh" "$task_dir/fair-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_FAIR_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
s=s.replace(old,'',1)
old='lean -M6000 -j1 "$package/PA194DerivationCompiler.lean"'
new='lean -M6000 -j1 -o "$task_dir/PA194DerivationCompiler.olean" "$package/PA194DerivationCompiler.lean"'
if s.count(old)!=1: raise SystemExit('unexpected derivation compiler command')
Path(sys.argv[2]).write_text(s.replace(old,new,1))
PY
export PA194_FAIR_TASK_DIR="$task_dir"
bash "$task_dir/fair-prerequisites.sh"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194CommandEquiv.olean" "$base/pa194-command-source/PA194CommandEquiv.lean"
lean -M6000 -j1 -o "$task_dir/M6/Source/Enumeration.olean" "$upstream/Enumeration.lean"
lean -M6000 -j1 -o "$task_dir/PA194EncodedWord.olean" "$package/PA194EncodedWord.lean"
lean -M6000 -j1 "$package/PA194Fairness.lean" | tee "$task_dir/fair-axioms.log"
if rg -q 'sorryAx' "$task_dir/fair-axioms.log"; then
 echo 'Unexpected sorryAx in scheduler fairness theorem' >&2
 exit 1
fi
