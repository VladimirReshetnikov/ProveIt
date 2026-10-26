#!/usr/bin/env python3
"""Finite arithmetic checks, not Lean proof or unbounded verification.

Read-only by default: JSON is emitted to stdout. Use --output explicitly to
write a receipt. Every check remains active under python -O.
"""
import argparse
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checks():
    count = 0
    for N in range(1, 17):
        modulus = N * 2011
        quotients = sorted({0, 1, max(N - 1, 0), N, N + 1, 10 * N, 10**20 + N})
        for bi in range(N):
            b = bi * 2011
            for q in quotients:
                for residue, address in ((19, 941), (20, 940)):
                    shift = 2011 * q + residue
                    theta = (b - (shift - shift % 2011)) % modulus
                    for j in range(9):
                        require((b + 960 + j - shift) % modulus ==
                                (theta + address + j) % modulus,
                                'Source-address identity failed')
                        count += 1
    # Dropping the high-color guard admits this literal Allowed.pass 0 0 tile.
    pass_zero = (0, 0, 0, 0)
    require(pass_zero[1] == 0 and pass_zero[3] == 0, 'Zero tile edge mismatch')
    require(not (0 >= 434), 'Zero color unexpectedly meets high-color guard')
    require(0 not in (434, 435, 436, 437, 438), 'Zero unexpectedly has a high-color fiber')
    return {
        'status': 'FINITE PYTHON ARITHMETIC CHECKS; NOT LEAN ELABORATION, NOT A PROOF',
        'source_translation': {
            'checks': count,
            'coverage': 'All aligned bases for N=1..16; offsets 19 and 20; all nine copied positions; quotient shifts 0,1,N-1,N,N+1,10N,10^20+N (deduplicated).',
            'purpose': 'Checks actual modulo-N*2011 source addresses across wraparound and arbitrarily-large representative examples, supplementing bit-prefix regressions.',
        },
        'guard_counterexample': {
            'tile': list(pass_zero), 'allowed_constructor': 'Allowed.pass (0 : Fin 2) (0 : Fin 2)',
            'color': 0,
            'result': 'Both equalities to color 0 hold, but both proposed high-color fiber right sides are false. The c >= 434 premise is essential.',
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Explicit receipt path; default is stdout only')
    args = parser.parse_args()
    try:
        encoded = json.dumps(checks(), indent=2) + '\n'
        if args.output is not None:
            args.output.write_text(encoded)
        else:
            print(encoded, end='')
    except (OSError, ValueError) as error:
        parser.exit(1, 'Arithmetic checks failed: ' + str(error) + '\n')


if __name__ == '__main__':
    main()
