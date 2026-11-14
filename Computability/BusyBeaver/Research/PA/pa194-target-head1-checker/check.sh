#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-target-head1-checker.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/standard" "$root/final"
export PA194_CHECKER_STANDARD_ROOT="$root/standard"
python3 - "$base/pa194-target-head1-standard/check.sh" "$root/head1-standard-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-target-head1-standard.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected target h1 standard prerequisite wrapper')
s=s.replace(old,'root=$PA194_CHECKER_STANDARD_ROOT',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/head1-standard-prerequisites.sh"
bash "$root/head1-standard-prerequisites.sh"
standard="$root/standard"
parent="$standard/parent"
inversion="$parent/inversion"
graph="$inversion/graph"
fields="$graph/fields"
choice="$fields/choice"
preimage="$choice/parent"
setroot="$preimage/parent"
search="$setroot/search"
source="$search/dependency"
export LEAN_PATH="$root/final:$standard/final:$parent/final:$inversion/final:$graph/final:$fields/final:$choice/final:$preimage/final:$setroot/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$parent/compiler:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194Head1Checker.olean" "$base/pa194-target-head1-checker/PA194Head1Checker.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in target h1 checker' >&2
  exit 1
fi
