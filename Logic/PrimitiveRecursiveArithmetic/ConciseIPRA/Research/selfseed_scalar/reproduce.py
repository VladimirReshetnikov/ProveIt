"""Offline checks. No network, third-party Python package, or unsafe import."""
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
for script in ['measure.py', 'tests/check_kernels.py', 'tests/check_selfseed_model.py']:
    subprocess.run([sys.executable, str(ROOT/script)], cwd=ROOT, check=True)
print('All packaged measurements and finite tests passed.')
