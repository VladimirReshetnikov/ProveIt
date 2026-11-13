"""Reproduce the finite acceptance, rejection, and mutation checks."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
subprocess.run([sys.executable, str(root / 'tests' / 'test_profiles.py')],
               cwd=root, check=True)
