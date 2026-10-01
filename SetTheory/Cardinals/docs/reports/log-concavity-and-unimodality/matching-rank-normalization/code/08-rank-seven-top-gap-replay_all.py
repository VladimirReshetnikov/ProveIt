#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent
for name in ['verify_barrier.py','verify_rayleigh_seed.py']:
 subprocess.run([sys.executable,'-O',str(root/name)],check=True)
print('All exact incidence, endpoint and seed checks passed.')
