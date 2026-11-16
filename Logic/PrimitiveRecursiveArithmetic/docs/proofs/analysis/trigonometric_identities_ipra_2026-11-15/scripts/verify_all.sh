#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/verify_identities.py
python3 - <<'PY'
import json
from pathlib import Path
p=Path('artifacts/identity_certificates.json')
d=json.loads(p.read_text())
assert d['summary']['failures'] == 0
assert d['summary']['checks'] == 227
print('certificate ledger OK:', d['summary'])
PY
