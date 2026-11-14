#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-machine-shift-mp-standard.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/effects" "$root/final"
export PA194_SHIFT_STANDARD_EFFECTS_ROOT="$root/effects"
python3 - "$base/pa194-machine-shift-mp-code/check.sh" "$root/effects-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-machine-shift-mp-code.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected machine SHIFT/MP effect prerequisite wrapper')
s=s.replace(old,'root=$PA194_SHIFT_STANDARD_EFFECTS_ROOT',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/effects-prerequisites.sh"
bash "$root/effects-prerequisites.sh"
effects="$root/effects"
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
export LEAN_PATH="$root/final:$effects/final:$ax/final:$store/final:$line/final:$mpclosure/final:$replay/final:$generalize/final:$leaves/final:$length/final:$guarded/final:$extended/final:$sound/final:$history/final:$gen/final:$mp/final:$h1graph/final:$checker/final:$standard/final:$parent/final:$inversion/final:$graph/final:$fields/final:$choice/final:$preimage/final:$setroot/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$vector/final:$vsearch/final:$vsource/final:$vsource/update:$vsource/source/final:$vsource/source/prereq/final:$vsource/source/prereq/model:$vsource/source/prereq/source:$parent/compiler:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194MachineShiftMPStandard.olean" "$base/pa194-machine-shift-mp-standard/PA194MachineShiftMPStandard.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in standard SHIFT/MP binding' >&2
  exit 1
fi
