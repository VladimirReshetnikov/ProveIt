#!/usr/bin/env python3
"""Rebuild complete quantified primitive proofs; output directory must be new."""
from pathlib import Path
import argparse, subprocess, sys
ROOT = Path(__file__).resolve().parent
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('output', type=Path)
p.add_argument('--table', choices=('both', 'cb1', 'normalized'), default='both')
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
validator = ROOT / 'baseline/k215/code/runtime-inputs/validate_native.py'
for name, table in [('cb1', 'q13_cb215.native.tm'), ('normalized', 'q13_normal215.native.tm')]:
    if a.table not in ('both', name):
        continue
    cmd = [sys.executable, str(validator), str(ROOT / 'verified-machines' / table),
           str(ROOT / 'verified-machines/q13_cb.sites.json'), str(a.output / name), '--all-failures']
    subprocess.run(cmd, check=True)
print('Fresh symbolic runtime records written to', a.output)
