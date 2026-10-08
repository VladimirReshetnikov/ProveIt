#!/usr/bin/env python3
"""Verify delivered hashes and replay the research package's correctness gates."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent
FAST = ROOT / 'fast'


def verify_hashes():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    failures = []
    for name, expected in manifest['files'].items():
        path = ROOT / name
        if not path.is_file():
            failures.append(f'missing: {name}')
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            failures.append(f'changed: {name}')
    if failures:
        raise SystemExit('\n'.join(failures))
    print(f"Verified {len(manifest['files'])} delivered file hashes.", flush=True)


def run(command, *, cwd=FAST):
    environment = os.environ.copy()
    environment['PYTHONPATH'] = os.pathsep.join([
        str(FAST), str(FAST / 'tests'), environment.get('PYTHONPATH', ''),
    ])
    print('Running:', ' '.join(map(str, command)), flush=True)
    subprocess.run(command, cwd=cwd, env=environment, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument('--hashes', action='store_true', help='Check delivered bytes only')
    scope.add_argument('--full', action='store_true', help='Replay all maintained tests and both finite cover audits')
    args = parser.parse_args()
    verify_hashes()
    if args.hashes:
        return
    if args.full:
        run([sys.executable, '-B', '-m', 'unittest', 'discover', '-s', 'tests', '-v'])
    else:
        run([sys.executable, '-B', '-m', 'unittest', '-v',
             'test_spin_jones', 'test_spin_order', 'test_spin_jones_integration',
             'test_compressed_lcs', 'test_lcs_bounds', 'test_lcs_transitions',
             'test_boundary_transport', 'test_normal_surface'])
    with tempfile.TemporaryDirectory(prefix='unknot-audit-') as directory:
        for script, filename in [('audit.py', 'transport.json'),
                                 ('audit_canonical.py', 'canonical.json')]:
            output = Path(directory) / filename
            run([sys.executable, '-B', str(FAST / 'boundary_transport_research' / script),
                 '--output', str(output)])
    print('Requested correctness gates completed. Timings are not replayed by this command.', flush=True)


if __name__ == '__main__':
    main()
