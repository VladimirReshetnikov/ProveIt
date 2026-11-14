#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-set-search-root.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/search" "$root/final"
export PA194_SET_ROOT_SEARCH="$root/search"
python3 - "$base/pa194-source-set-search/check.sh" "$root/set-search-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-set-search.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected set-search prerequisite wrapper')
s=s.replace(old,'root=$PA194_SET_ROOT_SEARCH',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/set-search-prerequisites.sh"
bash "$root/set-search-prerequisites.sh"
search="$root/search"
source="$search/dependency"
export LEAN_PATH="$root/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194SetSearchRoot.olean" "$base/pa194-source-set-search-root/PA194SetSearchRoot.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in source set-search root' >&2
  exit 1
fi
