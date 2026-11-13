"""Reproduce the package's finite executable checks; this is not a proof."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
commands = [
    ['tools/measure.py', '--check'],
    ['verify_duplicate_index.py'],
    ['verify_families.py'],
    ['tools/verify_three_field.py'],
]
for command in commands:
    result = subprocess.run([sys.executable, *command], cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        print(result.stdout)
        print(result.stderr)
        raise SystemExit(result.returncode)
    print('PASS', command[0])
family = json.loads((ROOT / 'evidence/family_validation.json').read_text())
three = json.loads((ROOT / 'evidence/three_field_verification.json').read_text())
receipt = {'status': 'PASS', 'python': sys.version,
           'checks': [c[0] for c in commands],
           'three_field_cases': three['cases'], 'three_field_executions': three['executions'],
           'family_executions': family['process_executions'],
           'total_executions': family['process_executions'] + three['executions'],
           'family_receipt': 'evidence/family_validation.json',
           'three_field_receipt': 'evidence/three_field_verification.json',
           'limitation': 'Finite regression and static checks; soundness/completeness are written arguments, not machine-verified here.'}
(ROOT / 'evidence/reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
