#!/usr/bin/env python3
"""Authenticate the release and replay exact finite checks in a temporary copy.

The unbounded mathematical theorem is in the article and identified source
proofs. This program is a finite algebra/data audit, not a formal ZFC prover.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def authenticate():
    manifest = json.loads((ROOT/'MANIFEST.json').read_text())
    for record in manifest['files']:
        path = ROOT/record['path']
        require(path.is_file(), 'Missing delivered file: '+record['path'])
        data = path.read_bytes()
        require(len(data) == record['bytes'], 'Changed length: '+record['path'])
        require(hashlib.sha256(data).hexdigest() == record['sha256'],
                'Changed SHA256: '+record['path'])
    return len(manifest['files'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-only', action='store_true')
    args = parser.parse_args()
    count = authenticate()
    print('Authenticated', count, 'delivered files.', flush=True)
    if args.manifest_only:
        return
    outputs = ROOT/'verification'
    outputs.mkdir(exist_ok=True)
    mode = 'optimized' if sys.flags.optimize else 'normal'
    logfile_dir = outputs/('logs_'+mode)
    logfile_dir.mkdir(exist_ok=True)
    flags = ['-'+'O'*sys.flags.optimize] if sys.flags.optimize else []
    stages = [
        ('quartic_coefficients_and_dependencies', 'quartic42', 'verify_dependencies.py'),
        ('quartic_builder', 'quartic42', 'build_verify.py'),
        ('quartic_independent_algebra', 'quartic42', 'independent_algebra.py'),
        ('sextic_and_octic_restoration', 'quartic42/companions', 'build_companions.py'),
        ('positive13_builder', 'positive13', 'build.py'),
        ('positive13_formula_checker', 'positive13', 'check.py'),
        ('positive13_independent_degree', 'positive13', 'p13_independent_check.py'),
        ('nine_complete_reconstruction', 'nine', 'reproduce.py'),
    ]
    optional = ROOT/'quartic42/companions/check_low_degree_companions.py'
    if optional.is_file():
        stages.insert(4, ('companions_independent_algebra',
                          'quartic42/companions', 'check_low_degree_companions.py'))
    receipts = []
    with tempfile.TemporaryDirectory(prefix='con-zfc-replay-') as work:
        work = Path(work)
        for component in ('quartic42', 'positive13', 'nine'):
            shutil.copytree(ROOT/component, work/component,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        for name, directory, script in stages:
            start = time.monotonic()
            result = subprocess.run([sys.executable, *flags, script],
                cwd=work/directory, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True)
            (logfile_dir/(name+'.log')).write_text(result.stdout)
            receipt = {'stage':name, 'returncode':result.returncode,
                       'elapsed_seconds':round(time.monotonic()-start,3)}
            receipts.append(receipt)
            print(name+': '+('PASS' if result.returncode == 0 else 'FAIL'), flush=True)
            if result.returncode:
                print(result.stdout[-12000:])
                break
    passed = len(receipts) == len(stages) and all(r['returncode'] == 0 for r in receipts)
    report = {
        'status':'PASS' if passed else 'FAIL', 'python':sys.version.split()[0],
        'optimization_level':sys.flags.optimize,
        'authenticated_files':count, 'stages':receipts,
        'scope':'Finite exact algebra/data and coefficient reconstruction; '
                'unbounded semantics use the supplied mathematical proofs. '
                'This is not a new proof-assistant or object-language ZFC certificate.'}
    destination = outputs/('REPLAY_OPTIMIZED.json' if sys.flags.optimize else 'REPLAY.json')
    destination.write_text(json.dumps(report,indent=2)+'\n')
    require(passed, 'Replay failed; see '+str(destination))
    print('All finite checks passed. Receipt:', destination, flush=True)


if __name__ == '__main__':
    main()
