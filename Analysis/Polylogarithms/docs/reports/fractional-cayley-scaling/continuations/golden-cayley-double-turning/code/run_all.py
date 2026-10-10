#!/usr/bin/env python3
"""Replay all finite certificates; optionally regenerate diagnostic figures."""
from pathlib import Path
import argparse
import importlib.metadata
import json
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--figures', action='store_true',
                        help='also regenerate the two illustrative figures')
    args = parser.parse_args()
    scripts = [
        'certify_euler_bound.py',
        'review_euler_certificate.py',
        'certify_double_turning.py',
        'certify_golden_ladders.py',
        'verify_cayley_projection.py',
    ]
    if args.figures:
        scripts.append('make_figures.py')
    receipt = {
        'python': platform.python_version(),
        'platform': platform.platform(),
        'dependencies': {name: importlib.metadata.version(name)
                         for name in ['sympy', 'mpmath']},
        'figures_regenerated': args.figures,
        'runs': [],
    }
    for script in scripts:
        print('Running', script, flush=True)
        started = time.monotonic()
        result = subprocess.run([sys.executable, str(ROOT/'code'/script)],
                                cwd=ROOT, capture_output=True, text=True)
        receipt['runs'].append({
            'script': 'code/'+script,
            'exit_code': result.returncode,
            'elapsed_seconds': round(time.monotonic()-started,3),
        })
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            receipt['status'] = 'FAIL'
            break
        print('PASS', script, flush=True)
    else:
        receipt['status'] = 'PASS'
    out = ROOT/'verification'/'replay_summary.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(receipt,indent=2)+'\n')
    print('Overall:', receipt['status'])
    return 0 if receipt['status'] == 'PASS' else 1

if __name__ == '__main__':
    raise SystemExit(main())
