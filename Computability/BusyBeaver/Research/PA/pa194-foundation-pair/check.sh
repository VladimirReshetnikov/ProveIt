#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-foundation-pair
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-foundation-pair.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/pa194-foundation-raw-successor/check.sh" "$task_dir/foundation-pair-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_FOUNDATION_PAIR_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected raw successor task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected raw successor cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_FOUNDATION_PAIR_TASK_DIR="$task_dir"
bash -n "$task_dir/foundation-pair-prerequisites.sh"
bash "$task_dir/foundation-pair-prerequisites.sh"
sha256sum -c "$base/pa194-foundation-graph-context/upstream.sha256"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$task_dir/PA194FoundationGraphContext.olean" "$base/pa194-foundation-graph-context/PA194FoundationGraphContext.lean" | tee "$task_dir/foundation-pair-axioms.log"
for mod in PA194FoundationPairGraph PA194FoundationPairExistence PA194FoundationKuratowskiExistence PA194FoundationPairSupplier PA194FoundationPairNumeric; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean" | tee -a "$task_dir/foundation-pair-axioms.log"
done
if rg -q 'sorryAx' "$task_dir/foundation-pair-axioms.log"; then
  echo 'Unexpected sorryAx in pair theorem dependencies' >&2
  exit 1
fi
