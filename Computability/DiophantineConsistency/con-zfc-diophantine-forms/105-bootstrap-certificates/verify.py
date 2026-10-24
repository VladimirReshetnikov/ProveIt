#!/usr/bin/env python3
"""Authenticate and replay the complete research release using only local files.

All potentially writing component tools run in an isolated temporary copy.
This driver does not import any mathematical builder. Component checkers supply
the exact algebra checks; unrestricted correctness is proved in the report.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
FLAGS = ['-O'] if sys.flags.optimize else []


def need(ok, message):
    if not ok:
        raise ValueError(message)


def authenticate():
    path = ROOT / 'MANIFEST.json'
    if not path.exists():
        return {'status': 'not yet emitted during release preparation'}
    manifest = json.loads(path.read_text())
    for rec in manifest['files']:
        target = ROOT / rec['path']
        need(target.is_file(), 'missing file: ' + rec['path'])
        need(target.stat().st_size == rec['bytes'], 'size differs: ' + rec['path'])
        need(sha256(target.read_bytes()).hexdigest() == rec['sha256'], 'hash differs: ' + rec['path'])
    return {'status': 'PASS', 'files': len(manifest['files'])}


def command(root, script, args=(), parse=True):
    completed = subprocess.run([sys.executable, *FLAGS, str(root / script), *map(str, args)],
                               cwd=root, capture_output=True, text=True,
                               env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
    need(completed.returncode == 0,
         script + ' failed:\n' + completed.stdout + completed.stderr)
    return json.loads(completed.stdout) if parse else completed.stdout


def direct(root):
    output = root / 'direct-receipt.json'
    command(root, 'direct/verify.py', ['--output', output])
    return json.loads(output.read_text())


def integer(root, label):
    parent = root / 'direct/equations/parent781/equation.json'
    equation = root / 'integer/equations' / label
    return command(root, 'integer/verify_integer.py', ['--parent', parent, '--equations', equation])


def integer_rebuild(root):
    parent = root / 'direct/equations/parent781/equation.json'
    results = {}
    for label, cap in [('integer956', 16), ('integer989', 4)]:
        output = root / ('rebuilt-' + label)
        command(root, 'integer/build_integer.py', [parent, output, '--cap', cap], parse=False)
        files = ['guarded.json', 'sign_certificate.json', 'equation.json',
                 'projection.json', 'polynomial.json', 'metrics.json']
        for filename in files:
            need((output / filename).read_bytes() == (root / 'integer/equations' / label / filename).read_bytes(),
                 label + ' byte reconstruction: ' + filename)
        results[label] = {'status': 'PASS', 'byte_identical_files': files}
    return results


def norms(root):
    result = command(root, 'norms/build_and_check.py')
    # The builder writes its five outputs; compare them with the delivered files.
    names = [r['name'] for r in result['equations']]
    for name in names:
        path = Path('norms/equations') / (name + '.json')
        need((root / path).read_bytes() == (ROOT / path).read_bytes(), 'norm endpoint rebuild: ' + name)
    return result


def run():
    authentication = authenticate()
    results = {}
    with tempfile.TemporaryDirectory(prefix='con-zfc-release-') as temporary:
        work = Path(temporary) / 'package'
        shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns('__pycache__', '*.pyc', '*.log', '*.aux', '*.out', '*.toc'))
        jobs = {
            'direct': lambda: direct(work),
            'integer956': lambda: integer(work, 'integer956'),
            'integer989': lambda: integer(work, 'integer989'),
            'integer_reconstruction': lambda: integer_rebuild(work),
            'nine_positive': lambda: command(work, 'nine/verify.py'),
            'norms': lambda: norms(work),
            'factorial_regression': lambda: command(work, 'norms/proofs/check_factorial_radius.py'),
            'baselines': lambda: command(work, 'checks/verify_baselines.py'),
        }
        failures = {}
        with ThreadPoolExecutor(max_workers=4) as pool:
            futures = {pool.submit(job): name for name, job in jobs.items()}
            for future in as_completed(futures):
                name = futures[future]
                try:
                    results[name] = future.result()
                    print(name + ': PASS', file=sys.stderr, flush=True)
                except Exception as exc:
                    failures[name] = str(exc)
                    print(name + ': FAIL', file=sys.stderr, flush=True)
        need(not failures, json.dumps(failures, indent=2))
    return {'status': 'PASS', 'python_optimization': sys.flags.optimize,
            'manifest': authentication, 'components': results,
            'scope': 'Exact finite artifact checks and reconstruction; universal proofs are in the report.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--manifest-only', action='store_true')
    args = parser.parse_args()
    receipt = authenticate() if args.manifest_only else run()
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'],
                      'python_optimization': sys.flags.optimize,
                      'components': sorted(receipt.get('components', {})),
                      'manifest': receipt.get('manifest', receipt if args.manifest_only else None)}, indent=2))
