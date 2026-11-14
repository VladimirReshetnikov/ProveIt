#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-scheduler-standard.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/shiftstandard" "$root/final"
export PA194_SCHEDULER_STANDARD_SHIFT_ROOT="$root/shiftstandard"
python3 - "$base/pa194-machine-shift-mp-standard/check.sh" "$root/shiftstandard-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-machine-shift-mp-standard.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected SHIFT/MP standard prerequisite wrapper')
s=s.replace(old,'root=$PA194_SCHEDULER_STANDARD_SHIFT_ROOT',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/shiftstandard-prerequisites.sh"
bash "$root/shiftstandard-prerequisites.sh"
shiftstandard="$root/shiftstandard"
effects="$shiftstandard/effects"
ax="$effects/ax"
store="$ax/store"
line="$store/line"
mpclosure="$line/mpclosure"
replay="$mpclosure/replay"
generalize="$replay/generalize"
leaves="$generalize/leaves"
length="$leaves/length"
guarded="$length/guarded"
extended="$guarded/extended"
sound="$extended/sound"
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
export LEAN_PATH="$root/final:$shiftstandard/final:$effects/final:$ax/final:$store/final:$line/final:$mpclosure/final:$replay/final:$generalize/final:$leaves/final:$length/final:$guarded/final:$extended/final:$sound/final:$history/final:$gen/final:$mp/final:$h1graph/final:$checker/final:$standard/final:$parent/final:$inversion/final:$graph/final:$fields/final:$choice/final:$preimage/final:$setroot/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$vector/final:$vsearch/final:$vsource/final:$vsource/update:$vsource/source/final:$vsource/source/prereq/final:$vsource/source/prereq/model:$vsource/source/prereq/source:$parent/compiler:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for spec in \
  'pa194-machine-ax-standard PA194MachineAXStandard' \
  'pa194-scheduler-code PA194SchedulerCode' \
  'pa194-scheduler-standard PA194SchedulerStandard'; do
  read -r package module <<< "$spec"
  lean -M6000 -j1 -o "$root/final/$module.olean" "$base/$package/$module.lean" | tee "$root/final/$module.axioms.log"
  if rg -q 'sorryAx' "$root/final/$module.axioms.log"; then
    echo "Unexpected sorryAx in $module" >&2
    exit 1
  fi
done
