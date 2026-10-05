"""Standalone reconstruction/replay for the two nested BB profiles."""
from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parent
for profile in ('130','170'):
 subprocess.run([sys.executable,'-O',str(ROOT/f'check_{profile}_schur.py')],check=True,cwd=ROOT)
 subprocess.run([sys.executable,'-O',str(ROOT/'replay_reduced_certificates.py'),profile],check=True,cwd=ROOT)
print('All nested BB matrix identities, support polynomials, SOS and rational repairs pass.')
