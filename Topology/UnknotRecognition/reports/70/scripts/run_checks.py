#!/usr/bin/env python3
"""Run reproducible correctness checks; benchmark reruns are deliberately separate."""
from pathlib import Path
import os
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[1]
env = dict(os.environ, PYTHONPATH=str(ROOT/'src'), PYTHONDONTWRITEBYTECODE='1')
commands = [
    [sys.executable,'-m','unittest','discover','-s','tests','-v'],
    [sys.executable,'scripts/audit.py'],
    [sys.executable,'-m','affine_orbits','examples/sharp-nine-profiles.json',
     '--verify','examples/sharp-nine-profiles.certificate.json'],
]
for command in commands:
    subprocess.run(command,cwd=ROOT,env=env,check=True)
print('All requested correctness checks passed; native comparisons not run.')
