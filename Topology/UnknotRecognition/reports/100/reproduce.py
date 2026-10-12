#!/usr/bin/env python3
"""Validate the frozen research bundle; optional full native corpus audit."""

import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent


def hashes():
    count = 0
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = ROOT / relative
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise AssertionError(f'Packaged hash mismatch: {relative}')
        count += 1
    print(f'Package hashes verified: {count} files.', flush=True)


def run(arguments, *, cwd=ROOT, env=None):
    print('Running:', ' '.join(str(x) for x in arguments), flush=True)
    subprocess.run([str(x) for x in arguments], cwd=cwd, env=env, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='focused tests and saved replay (default)')
    parser.add_argument('--full-corpus', action='store_true', help='also rerun the 106-case native weighted audit')
    parser.add_argument('--output', type=Path, help='output JSON path for --full-corpus')
    args = parser.parse_args()
    hashes()
    runtime = ROOT / 'runtime/fast'
    env = dict(os.environ, PYTHONPATH=str(runtime))
    run([sys.executable, '-m', 'unittest', '-v', 'tests.test_core_dual_forest',
         'tests.test_normal_cut_dual'], cwd=runtime, env=env)
    run([sys.executable, '-m', 'unittest', '-v', 'test_quotient'],
         cwd=ROOT / 'research/quotient',
         env=dict(os.environ, PYTHONPATH=str(ROOT / 'research/quotient')))
    run([sys.executable, ROOT / 'research/experiments/replay_saved.py',
         ROOT / 'research/certificates'], env=env)
    if args.full_corpus:
        if args.output is None:
            parser.error('--full-corpus requires --output, outside the frozen bundle if desired')
        run([sys.executable, ROOT / 'research/experiments/audit_native.py',
             '--corpus', ROOT / 'research/data/native_corpus.json',
             '--output', args.output.resolve(), '--label', 'reproduced_max_weight',
             '--strategy', 'max_weight'], env=env)
    print('All requested reproduction checks passed.', flush=True)


if __name__ == '__main__':
    main()
