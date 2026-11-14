#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-set-search.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/dependency" "$root/final"
export PA194_SET_SEARCH_PARENT="$root/dependency"
python3 - "$base/pa194-source-formula-shift-code-model/check.sh" "$root/source-shift-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-formula-shift-code-model.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected source-shift prerequisite wrapper')
s=s.replace(old,'root=$PA194_SET_SEARCH_PARENT',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/source-shift-prerequisites.sh"
bash "$root/source-shift-prerequisites.sh"
source="$root/dependency"
export LEAN_PATH="$root/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194SetSearch.olean" "$base/pa194-source-set-search/PA194SetSearch.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in source set search' >&2
  exit 1
fi
