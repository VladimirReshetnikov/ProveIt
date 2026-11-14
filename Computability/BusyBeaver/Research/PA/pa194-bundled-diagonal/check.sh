#!/usr/bin/env bash
set -euo pipefail
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-bundled-diagonal
upstream=$base/jamesyc-upstream/pa196/M6/Logic
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-bundled-diagonal.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Retain the freshly rebuilt source-calculus compiler and prerequisites.
python3 - "$base/pa194-derivation-compiler/check.sh" "$task_dir/bundle-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_BUNDLE_TASK_DIR', s, count=1, flags=re.M)
if n!=1: raise SystemExit('unexpected prerequisite task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old)!=1: raise SystemExit('unexpected prerequisite cleanup declaration')
s=s.replace(old,'',1)
old='lean -M6000 -j1 "$package/PA194DerivationCompiler.lean"'
new='lean -M6000 -j1 -o "$task_dir/PA194DerivationCompiler.olean" "$package/PA194DerivationCompiler.lean"'
if s.count(old)!=1: raise SystemExit('unexpected compiler theorem command')
Path(sys.argv[2]).write_text(s.replace(old,new,1))
PY
export PA194_BUNDLE_TASK_DIR="$task_dir"
bash "$task_dir/bundle-prerequisites.sh"
sha256sum -c "$base/pa194-calculus-soundness/upstream.sha256"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
mkdir -p "$task_dir/M6/Logic"
lean -M6000 -j1 -o "$task_dir/M6/Logic/RestrictedImplication.olean" "$upstream/RestrictedImplication.lean"
lean -M6000 -j1 -o "$task_dir/PA194CalculusTruth.olean" "$base/pa194-calculus-soundness/PA194CalculusTruth.lean"
lean -M6000 -j1 -o "$task_dir/PA194CalculusConnectives.olean" "$package/PA194CalculusConnectives.lean"
lean -M6000 -j1 "$package/PA194BundledDiagonal.lean" | tee "$task_dir/bundle-axioms.log"
if rg -q 'sorryAx' "$task_dir/bundle-axioms.log"; then
 echo 'Unexpected sorryAx in bundled diagonal transformations' >&2
 exit 1
fi
