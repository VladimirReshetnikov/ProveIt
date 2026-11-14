#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
repo=$(git rev-parse --show-toplevel)
cd "$repo"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-machine-ax-standard.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
export PA194_AX_STANDARD_ROOT="$root"
python3 - "$base/pa194-machine-ax-code/check.sh" "$root/ax-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-machine-ax-code.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected machine AX prerequisite wrapper')
s=s.replace(old,'root=$PA194_AX_STANDARD_ROOT',1).replace(trap,'',1)
s += '''\nlean -M6000 -j1 -o "$root/final/PA194MachineAXStandard.olean" "$base/pa194-machine-ax-standard/PA194MachineAXStandard.lean" | tee "$root/final/standard-axioms.log"\nif rg -q 'sorryAx' "$root/final/standard-axioms.log"; then\n  echo 'Unexpected sorryAx in standard AX binding' >&2\n  exit 1\nfi\n'''
Path(sys.argv[2]).write_text(s)
PY
bash -n "$root/ax-prerequisites.sh"
bash "$root/ax-prerequisites.sh"
