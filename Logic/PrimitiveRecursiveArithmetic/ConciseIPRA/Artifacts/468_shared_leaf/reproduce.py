"""Reproduce the local checker measurements and regression evidence."""
from pathlib import Path
import json
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parent
subprocess.run([sys.executable, str(root / 'code' / 'verify.py')], check=True)
shutil.copyfile(root / 'code' / 'verification.json',
                root / 'evidence' / 'verification.json')
result = json.loads((root / 'evidence' / 'verification.json').read_text())
print(f"Completed {result['checks']} process checks; failures: {len(result['failed'])}.")
print('The report contains the semantic proof and its inherited dependencies.')
subprocess.run([sys.executable, str(root / 'boundary_review' / 'boundary_audit.py'),
                str(root / 'code' / 'checker468.py'),
                str(root / 'boundary_review')], check=True)
