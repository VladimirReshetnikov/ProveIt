#!/usr/bin/env python3
"""Verify the release and replay all three lanes in isolated temporary copies.

Python standard library only. No consistency search or network access.
Checks use exceptions, so python -O does not disable acceptance conditions.
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
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'receipts/replays/latest.json')
    parser.add_argument('--skip-manifest', action='store_true',
                        help='For a source rebuild before sealing MANIFEST.json only.')
    args = parser.parse_args()
    record = {'status': 'RUNNING', 'optimized_python': bool(sys.flags.optimize),
              'snapshot': 'ec80841c07e91be8956ce6ed4af9a9c0b782d3d9',
              'manifest_files': 0, 'lanes': {}}
    if not args.skip_manifest:
        manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
        for item in manifest['files']:
            path = ROOT / item['path']
            require(path.is_file(), 'missing release file: ' + item['path'])
            data = path.read_bytes()
            require(len(data) == item['bytes'], 'size mismatch: ' + item['path'])
            require(hashlib.sha256(data).hexdigest() == item['sha256'],
                    'digest mismatch: ' + item['path'])
        record['manifest_files'] = len(manifest['files'])
    python = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
    jobs = [
        ('integer12', ['verify.py', '--output', 'ROOT_REPLAY.json']),
        ('positive10', ['verify718.py']),
        ('direct_quartic', ['centered_verify.py', '--receipt', 'ROOT_REPLAY.json']),
    ]
    with tempfile.TemporaryDirectory(prefix='conzfc-release-') as temp:
        for name, command in jobs:
            destination = Path(temp) / name
            shutil.copytree(ROOT / name, destination,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            started = time.monotonic()
            result = subprocess.run(python + command, cwd=destination,
                                    text=True, capture_output=True)
            require(result.returncode == 0,
                    name + ' failed:\n' + result.stdout + '\n' + result.stderr)
            payload_path = destination / ('CHECKS718.json' if name == 'positive10'
                                          else 'ROOT_REPLAY.json')
            payload = json.loads(payload_path.read_text())
            record['lanes'][name] = {
                'command': ' '.join(['python3', '-B'] +
                                    (['-O'] if sys.flags.optimize else []) + command),
                'seconds': round(time.monotonic() - started, 3),
                'returncode': result.returncode,
                'receipt': payload,
            }
            print(name + ': PASS', flush=True)
    record['status'] = 'PASS'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print('Release replay: PASS; receipt ' + str(args.output))


if __name__ == '__main__':
    main()
