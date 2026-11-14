#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
package=$base/pa194-source-code-graphs
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-code-graphs.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/source" "$root/graph" "$root/final"
export PA194_COMBINED_SOURCE_DIR="$root/source" PA194_COMBINED_GRAPH_DIR="$root/graph"
export PA194_COMBINED_REPO="$PWD"
python3 - "$base/pa194-search-pra-code/check.sh" "$root/source-prerequisites.sh" "$base/pa195-calibration/check-code-graph.sh" "$root/graph-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
src,srcout,graph,graphout=sys.argv[1:]
def patch_task(text, var):
    text,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', f'task_dir=${var}', text, count=1, flags=re.M)
    if n != 1: raise SystemExit('unexpected prerequisite task directory declaration')
    old="trap 'rm -rf \"$task_dir\"' EXIT"
    if text.count(old) != 1: raise SystemExit('unexpected prerequisite cleanup declaration')
    return text.replace(old,'',1)
Path(srcout).write_text(patch_task(Path(src).read_text(),'PA194_COMBINED_SOURCE_DIR'))
s=patch_task(Path(graph).read_text(),'PA194_COMBINED_GRAPH_DIR')
old='repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
if s.count(old) != 1: raise SystemExit('unexpected graph repository declaration')
s=s.replace(old,'repo=$PA194_COMBINED_REPO',1)
old='lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CodeGraph.lean'
if s.count(old) != 1: raise SystemExit('unexpected graph Lean invocation')
s=s.replace(old,'lean -M6000 -j1 -o "$task_dir/PA194CodeGraph.olean" Computability/BusyBeaver/Research/PA/pa195-calibration/PA194CodeGraph.lean',1)
Path(graphout).write_text(s)
PY
bash -n "$root/source-prerequisites.sh"
bash -n "$root/graph-prerequisites.sh"
bash "$root/source-prerequisites.sh"
bash "$root/graph-prerequisites.sh"
export LEAN_PATH="$root/final:$root/graph:$root/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for item in \
  'pa194-source-pra-codes PA194SourcePRACodes' \
  'pa194-search-pra-code PA194SearchPRACode' \
  'pa194-sequent-depth-pra-code PA194SeqDepthPRACode'; do
  read -r dir name <<< "$item"
  lean -M6000 -j1 -o "$root/final/$name.olean" "$base/$dir/$name.lean" | tee -a "$root/final/axioms.log"
done
lean -M6000 -j1 -o "$root/final/PA194SourceCodeGraphs.olean" "$package/PA194SourceCodeGraphs.lean" | tee -a "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in source-code graph dependencies' >&2
  exit 1
fi
