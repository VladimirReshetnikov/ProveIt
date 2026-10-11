#!/usr/bin/env python3
"""Run the supplied exact checks and independent numerical diagnostics.

No exploratory S6 search is run. The analytic theorems are proved in the
article; finite and floating-point diagnostics do not replace those proofs.
"""
from pathlib import Path
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    results = ROOT / 'results'
    results.mkdir(exist_ok=True)
    scripts = ['verify_mixed.py', 'verify_harmonic_transport.py',
               'check_cubic_rays.py', 'check_specializations.py']
    records = []
    for name in scripts:
        path = ROOT / 'code' / name
        if not path.is_file():
            raise SystemExit(f'Missing verification script: {name}')
        start = time.monotonic()
        run = subprocess.run([sys.executable, str(path)], cwd=ROOT,
                             capture_output=True, text=True)
        log = results / (path.stem + '_run.txt')
        log.write_text(run.stdout + run.stderr)
        record = {'script': name, 'exit_code': run.returncode,
                  'elapsed_seconds': round(time.monotonic()-start, 3),
                  'log': str(log.relative_to(ROOT))}
        records.append(record)
        print(json.dumps(record), flush=True)
        if run.returncode:
            print((run.stdout + run.stderr)[-5000:])
            raise SystemExit(run.returncode)
    output = {'schema': 'proveit.research.verification-run.v1',
              'all_scripts_passed': True, 'records': records,
              'qualification': 'Exact finite checks and floating-point diagnostics; analytic proofs are in the article.'}
    (results / 'verification_run.json').write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
