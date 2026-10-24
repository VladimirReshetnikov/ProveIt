#!/usr/bin/env python3
"""Replay this package in isolation; no network or proof search is performed."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def authenticate():
    count = 0
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        digest, name = line.split('  ', 1)
        relative = PurePosixPath(name)
        need(not relative.is_absolute() and '..' not in relative.parts,
             'invalid manifest path')
        data = (ROOT / name).read_bytes()
        need(hashlib.sha256(data).hexdigest() == digest,
             'manifest mismatch: ' + name)
        count += 1
    need(count > 30, 'incomplete delivery manifest')
    ledger = json.loads((ROOT / 'provenance/SOURCES.json').read_text())
    for entry in ledger['files']:
        data = (ROOT / entry['local_path']).read_bytes()
        need(hashlib.sha256(data).hexdigest() == entry['sha256'],
             'source SHA256: ' + entry['local_path'])
        blob = b'blob ' + str(len(data)).encode() + b'\0' + data
        need(hashlib.sha1(blob).hexdigest() == entry['git_blob_sha1'],
             'source Git blob: ' + entry['local_path'])
    return count


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt', type=Path,
                    help='optional output outside the frozen delivery')
    args = ap.parse_args()
    authenticated = authenticate()
    prefix = [sys.executable, '-B'] + ([] if __debug__ else ['-O'])
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    with tempfile.TemporaryDirectory(prefix='conzfc-dyadic-pell-') as name:
        local = Path(name) / 'package'
        shutil.copytree(ROOT, local,
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))

        def run(relative, *extra):
            result = subprocess.run(prefix + [str(local / relative), *extra],
                                    cwd=local, env=env, text=True,
                                    capture_output=True, check=True)
            return result.stdout

        build_message = run('dyadic10/build.py', '--check').strip()
        dyadic = json.loads(run('dyadic10/audit.py'))
        direct = json.loads(run('direct780/verify.py'))
        need(dyadic['operations'] == 133, 'dyadic gate count')
        need(all(x['degree'] == 706 and x['leading_form_matches']
                 for x in dyadic['degree_checks']), 'dyadic degree checks')
        numeric = direct['independent_check']['polynomial']
        expected = {'variables': 780, 'residuals': 434, 'degree': 4,
                    'monomials': 9628,
                    'coefficient_height': 2445790974704,
                    'eliminations': 303}
        need(all(numeric[k] == v for k, v in expected.items()),
             'direct polynomial metrics')
        need(len(direct['rejected_corruptions']) == 6,
             'direct rejection controls')
        receipt = {
            'status': 'PASS',
            'optimized_python': not __debug__,
            'authenticated_delivery_files': authenticated,
            'dyadic_builder': build_message,
            'dyadic_checks': dyadic,
            'direct_checks': direct,
            'scope': ('Exact fixed-artifact replay and mathematical proof premises. '
                      'Inherited source calibrations are stated in the article; '
                      'this is not a consistency decision or a proof-assistant endpoint.')
        }
    text = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.receipt:
        destination = args.receipt.resolve()
        need(ROOT not in destination.parents,
             'write the receipt outside the frozen delivery')
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
