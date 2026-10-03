#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p checks/replay
python3 checks/compaction-verify.py > checks/replay/compaction-validation.json
python3 checks/compaction-bijection-check.py > checks/replay/compaction-bijection-validation.json
python3 checks/barrier-verify.py > checks/replay/barrier-validation.json
python3 checks/evaluate-constants.py > checks/replay/constants.json
python3 checks/verify-large-cap.py > checks/replay/large-cap-validation.json
python3 - <<'PY'
import json
from pathlib import Path
for name in ['compaction-validation.json','compaction-bijection-validation.json','barrier-validation.json','constants.json','large-cap-validation.json']:
    p=Path('checks')/name
    if p.exists():
        assert json.loads(p.read_text())==json.loads((Path('checks/replay')/name).read_text()),name
    print(name+': passed')
PY
