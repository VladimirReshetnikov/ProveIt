#!/usr/bin/env python3
"""Replay the standalone Lean checks; optionally check patch applicability.

This is not a production ProveIt build. Every subprocess exit code is checked.
The Lean compiler must be version 4.32.0. No external Python packages are used.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default=shutil.which('lean'))
    parser.add_argument('--repo', type=Path, help='Optional ProveIt checkout at the review pin')
    parser.add_argument('--output', type=Path, default=None)
    args = parser.parse_args()
    if not args.lean:
        parser.error('Supply --lean /absolute/path/to/lean (version 4.32.0).')
    root = Path(__file__).resolve().parent.parent
    evidence = root / 'evidence'
    evidence.mkdir(exist_ok=True)
    version = subprocess.run([args.lean, '--version'], text=True, capture_output=True)
    if version.returncode or 'version 4.32.0,' not in version.stdout:
        raise SystemExit('Expected Lean 4.32.0: ' + version.stdout + version.stderr)
    result = {'scope': 'standalone mechanism prototypes; not production integration',
              'lean_version': version.stdout.strip(), 'checks': []}
    failed = False
    for source in sorted((root / 'lean').glob('*.lean')):
        proc = subprocess.run([args.lean, str(source)], text=True, capture_output=True,
                              cwd=root)
        log = proc.stdout + proc.stderr
        (evidence / (source.stem + '.log')).write_text(log, encoding='utf-8')
        item = {'file': str(source.relative_to(root)), 'exit_code': proc.returncode,
                'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'axiom_report': [s for s in log.splitlines() if 'axioms' in s]}
        result['checks'].append(item)
        print(f'{source.name}: exit {proc.returncode}')
        failed |= proc.returncode != 0
    if args.repo:
        patch = root / 'patches' / 'DecoderFusion.proposed.patch'
        proc = subprocess.run(['git', 'apply', '--check', str(patch)], cwd=args.repo,
                              text=True, capture_output=True)
        (evidence / 'patch-applicability.log').write_text(
            f'exit_code={proc.returncode}\n' + proc.stdout + proc.stderr, encoding='utf-8')
        result['patch'] = {'exit_code': proc.returncode,
                           'scope': 'applicability only; production Lean build not run'}
        failed |= proc.returncode != 0
    result['status'] = 'failed' if failed else 'passed'
    output = args.output or evidence / 'validation.json'
    output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    if failed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
