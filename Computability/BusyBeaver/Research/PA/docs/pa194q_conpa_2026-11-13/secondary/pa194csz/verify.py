#!/usr/bin/env python3
"""Rebuild PA194CSZ and replay its independent literal verification."""
from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parent
if not __debug__:raise RuntimeError('Run with assertions enabled, not python -O')
for script in ['build_csz.py','check_invariant.py','verification/check_csz.py']:
    subprocess.run([sys.executable,'-B',str(ROOT/script)],cwd=ROOT,check=True)
print('PA194CSZ construction, inductive invariant and independent physical replay PASS')
