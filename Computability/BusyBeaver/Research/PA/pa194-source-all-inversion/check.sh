#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-all-inversion.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/graph" "$root/final"
export PA194_INVERSION_GRAPH_ROOT="$root/graph"
python3 - "$base/pa194-source-all-choice-graph/check.sh" "$root/all-choice-graph-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-all-choice-graph.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected universal-choice graph prerequisite wrapper')
s=s.replace(old,'root=$PA194_INVERSION_GRAPH_ROOT',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/all-choice-graph-prerequisites.sh"
bash "$root/all-choice-graph-prerequisites.sh"
graph="$root/graph"
fields="$graph/fields"
choice="$fields/choice"
parent="$choice/parent"
setroot="$parent/parent"
search="$setroot/search"
source="$search/dependency"
export LEAN_PATH="$root/final:$graph/final:$fields/final:$choice/final:$parent/final:$setroot/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194AllInversion.olean" "$base/pa194-source-all-inversion/PA194AllInversion.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in universal-rule inversion' >&2
  exit 1
fi
