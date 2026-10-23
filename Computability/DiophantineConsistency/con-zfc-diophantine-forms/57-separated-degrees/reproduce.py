#!/usr/bin/env python3
"""Rebuild and audit all new release polynomials without external packages."""
from pathlib import Path
from hashlib import sha256
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    if not __debug__:
        raise SystemExit('Run without -O/-OO: some independent checks use assertions.')
    pin = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    checked = 0
    for r in pin['files']:
        path = ROOT/r['local_path']
        if sha256(path.read_bytes()).hexdigest() != r['sha256']:
            raise ValueError('Pinned file changed: '+r['local_path'])
        checked += 1
    scripts = [
        'build.py', 'materialize.py',
        'low_degree/build_twelve_balanced.py',
        'low_degree/build_twelve_reduced.py',
        'low_degree/build_twelve.py',
        'low_degree/build_thirteen.py',
        'verify.py', 'data/verify_channels.py', 'data/check_toy_channels.py',
        'coefficients/audit_coefficients.py', 'low_degree/verify.py',
        'quartic/build_verify.py',
        'quartic/upstream/34-integer14/coefficients/verify_independent.py',
    ]
    receipts = []
    env = dict(os.environ)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env.pop('PYTHONOPTIMIZE', None)
    for script in scripts:
        run = subprocess.run([sys.executable, str(ROOT/script)], cwd=ROOT,
                             env=env, text=True, capture_output=True)
        if run.returncode:
            print(run.stdout)
            print(run.stderr, file=sys.stderr)
            raise SystemExit('Failed: '+script)
        receipts.append(dict(script=script,status='PASS',
                             stdout_sha256=sha256(run.stdout.encode()).hexdigest()))
        print('PASS '+script, flush=True)
    result = dict(status='PASS',pinned_input_files_checked=checked,steps=receipts,
                  scope='All new circuit builds and finite audits; no proof-assistant kernel or consistency search.')
    (ROOT/'certificates/REPRODUCTION.json').write_text(json.dumps(result,indent=2)+'\n')
    print('All '+str(len(scripts))+' reproduction steps passed.')


if __name__=='__main__':
    main()
