#!/usr/bin/env python3
"""Finite arithmetic regression for the kernel-proved selector.
The Coq theorems, not this finite test, establish the all-natural result.
"""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path


def pair(a, b):
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(n):
    s = (math.isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def pack(heads, tail):
    for x in reversed(heads):
        tail = pair(x, tail)
    return tail


def execute(word, q, explicit_depth):
    pops = 0
    for c in word:
        t, w, d, h = q
        if c == 'N':
            if h == 1:
                return None, pops
            assert explicit_depth > 0, 'read below protected prefix'
            x, v = unpair(w)
            q = (t, v, d, x)
            explicit_depth -= 1
            pops += 1
        else:
            q = (h, pair(t, w), d, h)
            explicit_depth += 1
    assert explicit_depth == 0
    return q, pops


def check():
    count = early = normal = 0
    for length in range(1, 5):
        for rows in itertools.product(range(3), repeat=length):
            for j in range(length):
                word = 'N' * (j + 1) + 'D' + 'N' * (length + 1 - j)
                for g, h, tail in itertools.product(range(3), repeat=3):
                    d = 7
                    q, pops = execute(word, (g, pack(rows + (0,), tail), d, h), length + 1)
                    assert q is None or q == (rows[j], tail, d, 0)
                    assert q is None or pops == length + 2
                    count += 1
                    early += q is None
                    normal += q is not None
    # A zero numeric stack can carry arbitrarily many explicit zero heads.
    assert all(pack([0] * n, 0) == 0 for n in range(20))
    # A nonzero bottom sentinel leaves a nonzero cache: it cannot be dropped
    # from the theorem's precondition while keeping its conclusion.
    bad, _ = execute('NDNN', (0, pack([2, 3], 5), 7, 0), 2)
    assert bad == (2, 5, 7, 3)
    return {
        'status': 'PASS_FINITE_CORROBORATION',
        'cases': count,
        'early_halts': early,
        'normal_returns': normal,
        'tested_row_lengths': [1, 2, 3, 4],
        'tested_row_values': [0, 1, 2],
        'counter_preserved': 7,
        'opaque_tail_reads': 0,
        'nonzero_sentinel_counterexample': {'actual': list(bad), 'claimed_zero_cache': False},
        'scope': 'Finite regression only; unrestricted theorem is in NativeSelection.v.'
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    receipt = check()
    receipt['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    data = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        args.output.write_text(data)
    print(data, end='')


if __name__ == '__main__':
    main()
