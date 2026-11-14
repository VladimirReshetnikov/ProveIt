#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-target-history.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/gen" "$root/vector" "$root/final"
export PA194_HISTORY_GEN_ROOT="$root/gen" PA194_HISTORY_VECTOR_ROOT="$root/vector"
python3 - "$base/pa194-target-gen/check.sh" "$root/gen-prerequisites.sh" "$base/pa194-source-search-vector/check.sh" "$root/vector-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
for src,out,name,var in [(sys.argv[1],sys.argv[2],'pa194-target-gen','PA194_HISTORY_GEN_ROOT'),
                          (sys.argv[3],sys.argv[4],'pa194-source-search-vector','PA194_HISTORY_VECTOR_ROOT')]:
    s=Path(src).read_text()
    old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/'+name+'.XXXXXXXX")'
    trap='trap \'rm -rf "$root"\' EXIT'
    if s.count(old) != 1 or s.count(trap) != 1:
        raise SystemExit('unexpected prerequisite wrapper '+src)
    s=s.replace(old,'root=$'+var,1).replace(trap,'',1)
    Path(out).write_text(s)
PY
bash -n "$root/gen-prerequisites.sh"
bash -n "$root/vector-prerequisites.sh"
bash "$root/gen-prerequisites.sh"
bash "$root/vector-prerequisites.sh"
gen="$root/gen"
mp="$gen/mp"
h1graph="$mp/h1graph"
checker="$h1graph/checker"
standard="$checker/standard"
parent="$standard/parent"
inversion="$parent/inversion"
graph="$inversion/graph"
fields="$graph/fields"
choice="$fields/choice"
preimage="$choice/parent"
setroot="$preimage/parent"
search="$setroot/search"
source="$search/dependency"
vector="$root/vector"
vsearch="$vector/search"
vsource="$vsearch/dependency"
export LEAN_PATH="$root/final:$gen/final:$mp/final:$h1graph/final:$checker/final:$standard/final:$parent/final:$inversion/final:$graph/final:$fields/final:$choice/final:$preimage/final:$setroot/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$vector/final:$vsearch/final:$vsource/final:$vsource/update:$vsource/source/final:$vsource/source/prereq/final:$vsource/source/prereq/model:$vsource/source/prereq/source:$parent/compiler:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194TargetStep.olean" "$base/pa194-target-history/PA194TargetStep.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in target proof-history interpreter' >&2
  exit 1
fi
