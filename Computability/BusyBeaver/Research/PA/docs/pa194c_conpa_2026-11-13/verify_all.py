#!/usr/bin/env python3
"""Run the deterministic release checks; no stochastic search is needed."""
from pathlib import Path
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise SystemExit('Do not disable assertions when checking certificates.')
for name in ['construction/build.py', 'verification/check_commands.py',
             'verification/check_physical.py', 'verification/check_novelty.py']:
    print('\nChecking', name, flush=True)
    subprocess.run([sys.executable, '-B', str(ROOT / name)], cwd=ROOT, check=True)
print('All PA194C release checks passed.')
