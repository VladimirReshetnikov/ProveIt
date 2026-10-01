"""Recompute the rational matrix identities; requires SymPy."""
from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
subprocess.run([sys.executable,str(ROOT/'code/check_schur.py')]+list(map(str,range(2,15))),check=True)
subprocess.run([sys.executable,str(ROOT/'code/check_fixed_offset.py')],check=True)
subprocess.run([sys.executable,str(ROOT/'code/run_all.py')],check=True)
print('All rational matrix computations reproduced')
