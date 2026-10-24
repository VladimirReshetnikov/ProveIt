#!/usr/bin/env python3
"""Replay the packet's exact finite checks using only Python's standard library.

Unbounded source equivalences are ordinary proofs in the manuscript; this
program certifies the finite algebraic and reconstruction artifacts.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def check_manifest():
    manifest = HERE / 'MANIFEST.sha256'
    if not manifest.exists():
        return None
    count = 0
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = HERE / name
        if not path.is_file() or sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError('release hash mismatch: ' + name)
        count += 1
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild-direct', action='store_true',
                        help='also replay the slower monic optimizer byte-for-byte')
    args = parser.parse_args()
    checked_files = check_manifest()
    optimized = bool(sys.flags.optimize)
    suffix = '_OPTIMIZED' if optimized else ''
    review_suffix = '_optimized' if optimized else ''
    commands = [
        ('ten_positive/build.py', '--check'),
        ('ten_positive/build_integer.py', '--check'),
        ('ten_positive/check.py',),
        ('ten_positive/rebuild_coefficients.py',),
        ('ten_positive/review/ten_saturation_review.py', '--equation',
         'ten_positive/equation.json', '--output',
         'ten_positive/review/ten_saturation_review' + review_suffix + '.json'),
        ('direct/independent_source_check.py', '--output',
         'INDEPENDENT_SOURCE' + suffix + '.json'),
        ('direct/check.py',),
    ]
    if args.rebuild_direct:
        commands.append(('direct/build.py', '--check'))
    executable = [sys.executable, '-B'] + (['-' + 'O' * sys.flags.optimize] if optimized else [])
    receipts = []
    for command in commands:
        print('Checking ' + ' '.join(command), flush=True)
        result = subprocess.run(executable + list(command), cwd=HERE,
                                text=True, capture_output=True)
        if result.returncode:
            sys.stdout.write(result.stdout)
            sys.stderr.write(result.stderr)
            raise RuntimeError('failed check: ' + command[0])
        receipts.append({'command': list(command), 'status': 'PASS'})
    # Manifest validity is deliberately not included in a mutable receipt:
    # it is checked before execution and is stable after a reproducible run.
    receipt = {
        'status': 'PASS',
        'python_optimization': sys.flags.optimize,
        'checks': receipts,
        'scope': 'Exact finite artifacts, coefficients and integer restorations; '
                 'ordinary unbounded source proofs and inherited calibrations are separate.'
    }
    output = HERE / ('VERIFICATION' + suffix + '.json')
    # The optional optimizer has its own stable receipt and must not overwrite
    # the release receipt for the standard command.
    if args.rebuild_direct:
        output = HERE / ('REBUILD_VERIFICATION' + suffix + '.json')
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'checks': len(receipts),
                      'python_optimization': sys.flags.optimize,
                      'release_files_checked': checked_files,
                      'receipt': output.name}, indent=2))


if __name__ == '__main__':
    main()
