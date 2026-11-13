"""Reproduce the measured kernels and complete-process controls offline."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
for script in ('measure.py', 'tests/verify.py', 'successor_variant/tests/verify.py'):
    subprocess.run([sys.executable, str(root / script)], cwd=root, check=True)
if '--pdf' in sys.argv:
    subprocess.run([sys.executable, str(root / 'build.py')], cwd=root, check=True)
