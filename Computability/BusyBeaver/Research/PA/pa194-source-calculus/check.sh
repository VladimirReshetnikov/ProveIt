#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-source-calculus
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-calculus.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
# Keep every freshly rebuilt relational prerequisite in the same overlay.
python3 - "$base/pa194-relational-interface/check.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_SOURCE_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected relational task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected relational cleanup declaration')
s=s.replace(old,'',1)
old='lean -M6000 -j1 "$package/PA194RelationalFreshening.lean"'
new='lean -M6000 -j1 -o "$task_dir/PA194RelationalFreshening.olean" "$package/PA194RelationalFreshening.lean"'
if s.count(old) != 1: raise SystemExit('unexpected relational freshening command')
Path(sys.argv[2]).write_text(s.replace(old,new,1))
PY
export PA194_SOURCE_TASK_DIR="$task_dir"
bash "$task_dir/prerequisites.sh"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for mod in PA194SourceSyntax PA194SourceRewriting PA194RelationalSourceCode PA194RelationalSourceAllocation PA194RelationalSourceInstantiation PA194RelationalSourceGeneralization PA194RelationalPointed PA194RelationalSourceNegation PA194RelationalSourceExistential; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean" | tee -a "$task_dir/source-axioms.log"
done
if rg -q 'sorryAx' "$task_dir/source-axioms.log"; then
  echo 'Unexpected sorryAx in source calculus theorem dependencies' >&2
  exit 1
fi
