#!/usr/bin/env python3
"""Rerun the original finite checks. No network access or Lean build is used."""
import argparse
import importlib.metadata
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--pdf', action='store_true', help='also compile report.tex')
    args = ap.parse_args()
    base = Path(__file__).resolve().parent
    (base/'checks').mkdir(exist_ok=True)
    (base/'figures').mkdir(exist_ok=True)
    jobs = [
        ('prefilter_run.log', [sys.executable, 'code/verify_ktheory_prefilter.py',
          '--ranks', '--output', 'checks/prefilter_results.json']),
        ('small_reconstruction_run.log', [sys.executable,
          'code/verify_ktheory_small.py', '--output',
          'checks/small_reconstruction_results.json']),
        ('mean_transfer_run.log', [sys.executable, 'code/check_mean_transfer.py']),
        ('mean_models_run.log', [sys.executable, 'code/mean_models.py']),
    ]
    if args.pdf:
        jobs.append(('latex_build.log', [sys.executable, 'code/build_pdf.py']))
    record = {'python': platform.python_version(), 'platform': platform.platform(),
              'packages': {}, 'runs': []}
    for package in ('sympy', 'numpy', 'matplotlib'):
        record['packages'][package] = importlib.metadata.version(package)
    for log, command in jobs:
        print('Running:', ' '.join(command), flush=True)
        start = time.monotonic()
        run = subprocess.run(command, cwd=base, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True)
        (base/'checks'/log).write_text(run.stdout)
        record['runs'].append({'command': command, 'exit_code': run.returncode,
                               'seconds': round(time.monotonic()-start, 3),
                               'log': 'checks/'+log})
        (base/'checks'/'reproduction_runs.json').write_text(
            json.dumps(record, indent=2)+'\n')
        if run.returncode:
            print(run.stdout)
            raise SystemExit(run.returncode)
        print('PASS:', log, flush=True)
    print('All requested computations passed. See report.pdf for interpretation.')


if __name__ == '__main__':
    main()
