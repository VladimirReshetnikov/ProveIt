#!/usr/bin/env python3
"""Replay the delivered Lean files inside an existing pinned Lake project.

This script does not apply patches or edit repository sources. Its replay
logs and receipt are written below this packet's validation/replay directory.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
import time

EXPECTED_MATHLIB = '81a5d257c8e410db227a6665ed08f64fea08e997'


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=pathlib.Path, required=True,
                        help='Existing Lake project with the pinned Mathlib cache')
    parser.add_argument('--lake', default='lake', help='Lake executable')
    args = parser.parse_args()
    packet = pathlib.Path(__file__).resolve().parent
    project = args.project.resolve()
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    if mathlib['rev'] != EXPECTED_MATHLIB:
        raise SystemExit('Mathlib revision differs from the reviewed manifest.')
    version = subprocess.run([args.lake, 'env', 'lean', '--version'],
                             cwd=project, text=True, capture_output=True)
    if version.returncode or 'version 4.32.0' not in version.stdout:
        raise SystemExit('Lean 4.32.0 is required.\n' + version.stdout + version.stderr)
    plan = json.loads((packet / 'validation' / 'replay-plan.json').read_text())
    output = packet / 'validation' / 'replay'
    output.mkdir(exist_ok=True)
    records = []
    for relative in plan['checked_files']:
        source = packet / relative
        log = output / (source.stem + '.log')
        command = [args.lake, 'env', 'lean', '-j', '1', str(source)]
        started = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=project, stdout=stream,
                                    stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - started
        record = {'file': relative, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                  'exit_code': result.returncode, 'wall_seconds': elapsed,
                  'command': command, 'log': str(log.relative_to(packet))}
        records.append(record)
        print(f'{relative}: exit {result.returncode}', flush=True)
        if result.returncode:
            break
    receipt = {'lean_version': version.stdout.strip(), 'mathlib_commit': EXPECTED_MATHLIB,
               'scope': plan['scope'], 'results': records,
               'success': len(records) == len(plan['checked_files']) and
                          all(r['exit_code'] == 0 for r in records)}
    (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return 0 if receipt['success'] else 1


if __name__ == '__main__':
    sys.exit(main())
