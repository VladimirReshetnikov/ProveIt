#!/usr/bin/env python3
"""Reproduce the bounded local fold scopes recorded beside this script."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gc222', type=Path, required=True)
    parser.add_argument('--g223', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cxx', default='g++')
    parser.add_argument('--finite-fixture', action='store_true',
                        help='also replay the explicitly finite discovery-domain scope')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    receipt = json.loads((here / 'search_receipt.json').read_text())
    inputs = [('GC222', args.gc222.resolve(), receipt['baseline_gc222_sha256'])]
    if args.g223 is not None:
        inputs.insert(0, ('G223', args.g223.resolve(), receipt['baseline_g223_sha256']))
    for name, path, expected in inputs:
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f'{name} table does not match the pinned native-label input')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name in ('neutral', 'two_helpers', 'halting_folds'):
        subprocess.run([args.cxx, '-O3', '-std=c++17', str(here / (name + '.cpp')),
                        '-o', str(out / name)], check=True)

    def run(name, argv, stem):
        print(stem, flush=True)
        with (out / (stem + '.txt')).open('w') as stdout, \
                (out / (stem + '.log')).open('w') as stderr:
            subprocess.run([str(out / name)] + list(map(str, argv)),
                           stdout=stdout, stderr=stderr, check=True)
        print((out / (stem + '.log')).read_text().splitlines()[-1], flush=True)

    for name, path, _ in inputs:
        run('neutral', [path, 5, 5, 65, 65], 'neutral_' + name)
        run('two_helpers', [path, 5, 5, 65, 65, out / ('neutral_' + name + '.txt')],
            'folds_' + name)
        if name == 'GC222':
            run('halting_folds', [path, 6, 129], 'halt_' + name)
            if args.finite_fixture:
                fixture = here / 'finite_GC222.txt'
                expected = receipt['scopes'][-1]['fixture_sha256']
                if hashlib.sha256(fixture.read_bytes()).hexdigest() != expected:
                    raise ValueError('Changed finite discovery fixture')
                run('neutral', [path, 5, 5, 65, 65, fixture], 'neutral_GC222_finite')
                run('two_helpers', [path, 5, 5, 65, 65,
                    out / 'neutral_GC222_finite.txt', fixture], 'folds_GC222_finite')
    for path in out.glob('folds_*.txt'):
        if path.stat().st_size:
            raise ValueError('Unexpected survivor: inspect ' + str(path))
    if (out / 'halt_GC222.txt').stat().st_size:
        raise ValueError('Unexpected terminal-relaxed survivor')
    print('COMPLETED_SCOPED_SEARCHES_REPRODUCED_NO_SURVIVOR', flush=True)


if __name__ == '__main__':
    main()
