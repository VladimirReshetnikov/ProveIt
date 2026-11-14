#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-all-choice.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/parent" "$root/final"
export PA194_CHOICE_PARENT_ROOT="$root/parent"
python3 - "$base/pa194-source-all-preimage/check.sh" "$root/all-preimage-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-all-preimage.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected universal preimage prerequisite wrapper')
s=s.replace(old,'root=$PA194_CHOICE_PARENT_ROOT',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/all-preimage-prerequisites.sh"
bash "$root/all-preimage-prerequisites.sh"
parent="$root/parent"
setroot="$parent/parent"
search="$setroot/search"
source="$search/dependency"
export LEAN_PATH="$root/final:$parent/final:$setroot/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194AllChoice.olean" "$base/pa194-source-all-choice/PA194AllChoice.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in universal-rule choice' >&2
  exit 1
fi
