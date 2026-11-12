"""Rebuild the certificate evidence and the source-size comparison."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
subprocess.run([sys.executable, str(root / 'code' / 'reproduce.py')], check=True)
