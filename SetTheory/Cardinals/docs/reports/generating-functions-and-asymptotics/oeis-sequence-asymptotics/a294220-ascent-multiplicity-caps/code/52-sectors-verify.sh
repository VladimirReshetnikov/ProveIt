#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python3}"
mkdir -p checks/replay
"$PYTHON" sources/fixed-sector-verify.py --order 3 --numerics > checks/replay/fixed-sector-validation.json
cmp sources/fixed-sector-validation.json checks/replay/fixed-sector-validation.json
"$PYTHON" sources/fixed-sector-independent-audit.py > checks/replay/fixed-sector-independent-validation.json
cmp sources/fixed-sector-independent-validation.json checks/replay/fixed-sector-independent-validation.json
"$PYTHON" - <<'PY'
import json
from pathlib import Path
r = json.loads(Path('checks/replay/fixed-sector-independent-validation.json').read_text())
assert r['all_checks_pass'] is True, 'Independent checks failed'
PY
"$PYTHON" sources/root-sector-gamma-check.py > checks/replay/root-sector-gamma-validation.txt
cmp checks/root-sector-gamma-validation.txt checks/replay/root-sector-gamma-validation.txt
"$PYTHON" checks/check-reciprocal.py > checks/replay/reciprocal-validation.json
cmp checks/reciprocal-validation.json checks/replay/reciprocal-validation.json
printf 'PASS: author replay, independent checks, Gamma moments, reciprocal algebra\n'
