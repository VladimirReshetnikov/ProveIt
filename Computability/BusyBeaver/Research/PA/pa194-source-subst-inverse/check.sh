#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-subst-inverse.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
python3 - "$base/pa194-source-all-inversion/check.sh" "$root/subst-inversion-prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
line = 'lean -M6000 -j1 -o "$root/final/PA194AllInversion.olean" "$base/pa194-source-all-inversion/PA194AllInversion.lean" | tee "$root/final/axioms.log"\n'
extra = '''lean -M6000 -j1 -o "$root/final/PA194SubstInverse.olean" "$base/pa194-source-subst-inverse/PA194SubstInverse.lean" | tee "$root/final/subst-inverse-axioms.log"
if rg -q 'sorryAx' "$root/final/subst-inverse-axioms.log"; then exit 1; fi
'''
if s.count(line) != 1:
    raise SystemExit('unexpected universal-rule inversion Lean command')
Path(sys.argv[2]).write_text(s.replace(line, line + extra, 1))
PY
bash -n "$root/subst-inversion-prerequisites.sh"
bash "$root/subst-inversion-prerequisites.sh"
