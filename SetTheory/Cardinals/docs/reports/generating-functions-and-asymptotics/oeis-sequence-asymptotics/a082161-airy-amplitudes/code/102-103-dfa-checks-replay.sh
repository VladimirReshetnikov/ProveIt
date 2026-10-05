#!/usr/bin/env bash
# No dependency installation, network access, input generation, or input rewriting.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
PYTHON="${PYTHON:-python3}"
mkdir -p logs
rm -f logs/run_records.json
export PYTHONDONTWRITEBYTECODE=1
"$PYTHON" verify.py 2>&1 | tee logs/exact_normal.log
"$PYTHON" -O verify.py 2>&1 | tee logs/exact_optimized.log
"$PYTHON" negative_tests.py 2>&1 | tee logs/negative_normal.log
"$PYTHON" -O negative_tests.py 2>&1 | tee logs/negative_optimized.log
"$PYTHON" - <<'PY' > logs/run_records.json
from datetime import datetime, timezone
from pathlib import Path
import hashlib, json, platform, sys
import sympy
names=('exact_normal.log','exact_optimized.log','negative_normal.log','negative_optimized.log')
record={'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
        'python':platform.python_version(),'sympy':sympy.__version__,
        'commands':[[sys.executable,'verify.py'],[sys.executable,'-O','verify.py'],
                    [sys.executable,'negative_tests.py'],[sys.executable,'-O','negative_tests.py']],
        'exit_statuses':[0,0,0,0],
        'scope':'Finite exact algebra and integrity replay, not an analytic proof.',
        'logs':{name:hashlib.sha256((Path('logs')/name).read_bytes()).hexdigest() for name in names},
        'source_manifest_sha256':hashlib.sha256(Path('manifest.json').read_bytes()).hexdigest()}
print(json.dumps(record,indent=2))
PY
printf '%s\n' 'REPLAY PASS: normal and optimized exact checks and corruption rejection; logs/run_records.json recorded'
