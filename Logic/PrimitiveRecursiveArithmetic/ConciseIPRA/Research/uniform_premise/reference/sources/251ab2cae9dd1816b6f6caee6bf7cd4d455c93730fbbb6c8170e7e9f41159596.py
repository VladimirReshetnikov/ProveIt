"""Run the affine fixtures against the standalone explanatory implementation."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
cases = json.loads((ROOT / 'tests/cases.json').read_text())['code/checker.py']
rows = []
for case in cases:
    for optimized in (False, True):
        p = subprocess.run([sys.executable] + (['-O'] if optimized else []) +
                           [str(ROOT / 'code/readable_checker.py')],
                           input=json.dumps(case['packet']), text=True,
                           capture_output=True, timeout=12)
        accepted = p.returncode == 0 and p.stdout.strip() == 'ACCEPT'
        passed = accepted == case['accept'] and (accepted or p.returncode != 0)
        rows.append(dict(name=case['name'], optimized=optimized,
                         expected=case['accept'], accepted=accepted, passed=passed))
result = dict(runs=len(rows), passed=sum(r['passed'] for r in rows), rows=rows)
print(json.dumps({k:v for k,v in result.items() if k != 'rows'}))
if result['runs'] != result['passed']:
    print(json.dumps([r for r in rows if not r['passed']], indent=2))
    raise SystemExit(1)
