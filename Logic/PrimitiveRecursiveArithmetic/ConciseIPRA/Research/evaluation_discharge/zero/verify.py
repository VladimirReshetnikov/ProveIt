"""Reproduce this companion from any working directory."""
from pathlib import Path
import runpy
import sys
base = Path(__file__).resolve().parent
sys.path.insert(0, str(base / 'validation'))
runpy.run_path(str(base / 'validation/verify.py'), run_name='__main__')
