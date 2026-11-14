#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-target-history-extended.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/sound" "$root/final"
export PA194_EXTENDED_SOUND_ROOT="$root/sound"
python3 - "$base/pa194-target-history-sound/check.sh" "$root/sound-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-target-history-sound.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected target history sound prerequisite wrapper')
s=s.replace(old,'root=$PA194_EXTENDED_SOUND_ROOT',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/sound-prerequisites.sh"
bash "$root/sound-prerequisites.sh"
sound="$root/sound"
history="$sound/history"
gen="$history/gen"
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
vector="$history/vector"
vsearch="$vector/search"
vsource="$vsearch/dependency"
export LEAN_PATH="$root/final:$sound/final:$history/final:$gen/final:$mp/final:$h1graph/final:$checker/final:$standard/final:$parent/final:$inversion/final:$graph/final:$fields/final:$choice/final:$preimage/final:$setroot/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$vector/final:$vsearch/final:$vsource/final:$vsource/update:$vsource/source/final:$vsource/source/prereq/final:$vsource/source/prereq/model:$vsource/source/prereq/source:$parent/compiler:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for spec in \
  'pa194-target-leaves PA194TargetLeaves' \
  'pa194-target-leaves-standard PA194TargetLeavesStandard' \
  'pa194-target-gate PA194TargetGate' \
  'pa194-target-rho8 PA194TargetRho8' \
  'pa194-target-history-extended PA194TargetExtendedStep'; do
  read -r package module <<< "$spec"
  lean -M6000 -j1 -o "$root/final/$module.olean" "$base/$package/$module.lean" | tee "$root/final/$module.axioms.log"
  if rg -q 'sorryAx' "$root/final/$module.axioms.log"; then
    echo "Unexpected sorryAx in $module" >&2
    exit 1
  fi
done
