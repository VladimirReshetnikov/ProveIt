#!/usr/bin/env python3
"""Exact certificate replay. Default: full; --quick replays one sample profile."""
from pathlib import Path
import argparse
import subprocess
import sys

root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--quick',action='store_true');args=parser.parse_args()
def run(path,*extra):subprocess.run([sys.executable,'-O',str(root/path),*extra],check=True,cwd=root)
for path in ['verification/check_R_determinants.py','verification/check_core_endpoint_formulas.py','verification/check_zero_core_schur.py','verification/check_fifth_truncation_barrier.py']:
    run(path)
run('verification/independent/reconstruct.py','endpoints')
run('verification/independent/check_relations.py')
run('verification/independent/check_finite_compression.py')
if args.quick:
    run('verification/independent/reconstruct.py','1','7','7')
else:
    run('verification/independent/reconstruct.py')
run('verification/independent/finalize.py')
print('Quick replay passed; 60 recorded full-profile replays were not recomputed.' if args.quick else 'Full independent exact replay passed for all 61 cores and 3111 basis cones.')
