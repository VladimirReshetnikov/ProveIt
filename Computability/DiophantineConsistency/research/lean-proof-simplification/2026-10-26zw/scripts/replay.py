#!/usr/bin/env python3
"""Check the six standalone Lean artifacts in an existing Lake project.

No installation, patch application, or production rebuild is performed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', required=True, type=Path)
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    project = args.project.resolve()
    bundle = Path(__file__).resolve().parents[1]
    result_dir = bundle / 'replay-results'
    result_dir.mkdir(exist_ok=True)
    expected = json.loads((bundle / 'evidence/source_manifest.json').read_text())
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    if mathlib['rev'] != expected['mathlib_commit']:
        raise SystemExit('mathlib revision differs from the reviewed revision')
    version = subprocess.run(['lake', 'env', 'lean', '--version'], cwd=project,
                             text=True, capture_output=True, check=True)
    if 'version 4.32.0,' not in version.stdout:
        raise SystemExit('Lean version differs from 4.32.0: ' + version.stdout)
    results = []
    for source in sorted((bundle / 'lean').glob('*.lean')):
        command = ['lake', 'env', 'lean', str(source)]
        started = time.monotonic()
        proc = subprocess.run(command, cwd=project, text=True,
                              capture_output=True, timeout=args.timeout)
        output = proc.stdout + proc.stderr
        (result_dir / (source.stem + '.log')).write_text(output)
        item = {'file': str(source.relative_to(bundle)),
                'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'exit_code': proc.returncode,
                'seconds': round(time.monotonic() - started, 3),
                'command': command}
        results.append(item)
        print(source.name, 'PASS' if proc.returncode == 0 else 'FAIL', flush=True)
    (result_dir / 'results.json').write_text(json.dumps({
        'lean_version': version.stdout.strip(), 'mathlib_commit': mathlib['rev'],
        'scope': 'Standalone kernels and conditional source-body fixtures only',
        'results': results}, indent=2) + '\n')
    raise SystemExit(0 if all(r['exit_code'] == 0 for r in results) else 1)


if __name__ == '__main__':
    main()
