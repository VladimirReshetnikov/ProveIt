#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mode="${1:-core}"
case "$mode" in core|full|all) ;; *) echo 'Usage: bash replay.sh [core|full|all]' >&2; exit 2;; esac
python3 scripts/check_manifest.py
mkdir -p build/replay
cp scripts/check_exact_identities.py scripts/check_enumeration.py build/replay/
python3 build/replay/check_exact_identities.py | tee build/replay/exact.log
python3 build/replay/check_enumeration.py | tee build/replay/enumeration.log
python3 - <<'PY'
import json
from pathlib import Path
for name in ['exact-identity-check.json','enumeration-check.json']:
    assert json.loads((Path('build/replay')/name).read_text())==json.loads((Path('results')/name).read_text()), name
print('PASS exact results match frozen JSON')
PY
if [[ "$mode" == full || "$mode" == all ]]; then
 python3 -c 'import numpy' || { echo 'NumPy is required for the full residual check' >&2; exit 1; }
 cp scripts/check_corrector.py build/replay/
 python3 build/replay/check_corrector.py | tee build/replay/corrector.log
 python3 - <<'PY'
import json, math
from pathlib import Path
old=json.loads(Path('results/corrector-check.json').read_text())
new=json.loads(Path('build/replay/corrector-check.json').read_text())
assert len(old)==len(new)==40
for a,b in zip(old,new):
    assert a[:4]==b[:4]
    assert all(math.isclose(x,y,abs_tol=2e-6,rel_tol=2e-6) for x,y in zip(a[4:],b[4:]))
print('PASS floating results match within 2e-6 cross-platform replay tolerance')
PY
fi
if [[ "$mode" == all ]]; then bash build.sh; fi
printf 'PASS replay mode %s\n' "$mode"
