#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-target-truth.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
python3 - "$base/pa194-target-proof-leaves/check.sh" "$root/truth-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
line = 'lean -M6000 -j1 -o "$root/final/PA194TargetProofLeaf.olean" "$base/pa194-target-proof-leaves/PA194TargetProofLeaf.lean" | tee "$root/final/axioms.log"\n'
extra = '''lean -M6000 -j1 -o "$root/final/PA194VerumNode.olean" "$base/pa194-forward-audit/PA194VerumNode.lean" | tee "$root/final/verum-axioms.log"
lean -M6000 -j1 -o "$root/final/PA194TargetTruth.olean" "$base/pa194-target-truth/PA194TargetTruth.lean" | tee "$root/final/truth-axioms.log"
if rg -q 'sorryAx' "$root/final/verum-axioms.log" "$root/final/truth-axioms.log"; then exit 1; fi
'''
if s.count(line) != 1:
    raise SystemExit('unexpected target proof-leaf Lean command')
Path(sys.argv[2]).write_text(s.replace(line, line + extra, 1))
PY
bash -n "$root/truth-prerequisites.sh"
bash "$root/truth-prerequisites.sh"
