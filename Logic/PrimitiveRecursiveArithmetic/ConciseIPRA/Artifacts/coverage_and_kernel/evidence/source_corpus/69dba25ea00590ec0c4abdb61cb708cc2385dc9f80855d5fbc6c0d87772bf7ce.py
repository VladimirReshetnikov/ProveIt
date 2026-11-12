"""Recompute source metrics and finite checks using only this archive."""
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parent
for relative in ['measure.py','tests/produce.py','tests/verify.py','tests/audit_supply.py','tests/independent_supply_audit.py']:
    print('Running '+relative,flush=True)
    subprocess.run([sys.executable,str(ROOT/relative)],cwd=ROOT,check=True)
print('All source measurements and finite checks passed.')
