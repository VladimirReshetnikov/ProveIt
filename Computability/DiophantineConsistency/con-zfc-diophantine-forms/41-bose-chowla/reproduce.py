#!/usr/bin/env python3
"""Run all primary checks offline, using Python 3.10+ standard library."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
for script in ('check_equation.py', 'check_coefficients.py', 'check_circuit_independent.py'):
    subprocess.run([sys.executable, str(ROOT / 'code' / script)], check=True, cwd=ROOT)
print('All primary checks passed. These checks do not search for a ZFC refutation.')
