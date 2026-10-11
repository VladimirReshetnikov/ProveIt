#!/usr/bin/env python3
"""Replay supplied exact checks and, optionally, numerical diagnostics."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exact-only', action='store_true')
    args = ap.parse_args()
    jobs = [
        ['verification/verify_ordered_exact.py'],
        ['verification/verify_harmonic_symbolic.py'],
        ['verification/verify_reflected_collision.py', '--exact-only',
         '--output', 'results/reflected_exact.json'],
        ['certificates/cayley/code/verify_complete_cayley.py'],
    ]
    if not args.exact_only:
        jobs += [
            ['verification/verify_ordered_numeric.py'],
            ['verification/verify_harmonic.py'],
            ['verification/verify_reflected_collision.py', '--higher-stieltjes',
             '--output', 'results/reflected_collision.json'],
        ]
    (ROOT/'results').mkdir(exist_ok=True)
    receipts = []
    for arguments in jobs:
        print('Running: '+ ' '.join(arguments), flush=True)
        start = time.monotonic()
        result = subprocess.run([sys.executable]+arguments, cwd=ROOT)
        receipts.append({'arguments':arguments,'returncode':result.returncode,
                         'elapsed_seconds':round(time.monotonic()-start,3)})
        if result.returncode:
            raise SystemExit(result.returncode)
    mode = 'exact' if args.exact_only else 'all'
    path = ROOT/'results'/('runner_'+mode+'.json')
    path.write_text(json.dumps({'status':'PASS','mode':mode,'jobs':receipts},indent=2)+'\n')
    print('All requested checks passed.', flush=True)


if __name__ == '__main__':
    main()
