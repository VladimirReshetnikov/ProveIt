#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-foundation-graph-exact
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-foundation-graph-exact.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/pa194-foundation-graph-extension/check.sh" "$task_dir/foundation-graph-exact-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_FOUNDATION_GRAPH_EXACT_TASK_DIR', s, count=1, flags=re.M)
if n != 1: raise SystemExit('unexpected graph extension task directory declaration')
old="trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1: raise SystemExit('unexpected graph extension cleanup declaration')
Path(sys.argv[2]).write_text(s.replace(old,'',1))
PY
export PA194_FOUNDATION_GRAPH_EXACT_TASK_DIR="$task_dir"
bash -n "$task_dir/foundation-graph-exact-prerequisites.sh"
bash "$task_dir/foundation-graph-exact-prerequisites.sh"
sha256sum -c "$base/pa194-foundation-successor/upstream.sha256"
sha256sum -c "$package/upstream.sha256"
export LEAN_PATH="$task_dir:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
# The classification needs equality and linearity lemmas from this ordered
# prefix of the successor package, built into the same fresh overlay.
for suf in ClosureLogic ClosureEquality ClosureStructural ClosureLinear; do
  mod="PA194FoundationOrdinalSuccessor$suf"
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$base/pa194-foundation-successor/$mod.lean" | tee -a "$task_dir/graph-exact-axioms.log"
done
for mod in PA194FoundationPairTransport PA194FoundationPairDecoding PA194FoundationKuratowskiComponents PA194FoundationKuratowskiElimination PA194FoundationKuratowskiDecoder PA194FoundationKuratowskiTransport PA194FoundationGraphClassification PA194FoundationGraphExactExistence PA194FoundationGraphExactNumeric; do
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$package/$mod.lean" | tee -a "$task_dir/graph-exact-axioms.log"
done
if rg -q 'sorryAx' "$task_dir/graph-exact-axioms.log"; then
  echo 'Unexpected sorryAx in exact graph theorem dependencies' >&2
  exit 1
fi
