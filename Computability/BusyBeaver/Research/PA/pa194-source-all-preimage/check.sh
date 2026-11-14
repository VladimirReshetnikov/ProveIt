#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-all-preimage.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/parent" "$root/final"
export PA194_ALL_PARENT_ROOT="$root/parent"
python3 - "$base/pa194-source-set-search-root/check.sh" "$root/set-root-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-set-search-root.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected set-search root prerequisite wrapper')
s=s.replace(old,'root=$PA194_ALL_PARENT_ROOT',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/set-root-prerequisites.sh"
bash "$root/set-root-prerequisites.sh"
parent="$root/parent"
search="$parent/search"
source="$search/dependency"
export LEAN_PATH="$root/final:$parent/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194AllPreimage.olean" "$base/pa194-source-all-preimage/PA194AllPreimage.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in universal-rule preimage' >&2
  exit 1
fi
