#!/usr/bin/env python3
"""Exhaust balanced words modulo alphabet permutations, independently of C++.

Run: python src/exhaust_python.py 6 > data/python_through18.json
For k>0 the alphabet-permutation action is free, so each representative has
weight six. This implementation does NOT quotient enumeration by reversal.
"""
from __future__ import annotations
import argparse
from itertools import combinations
import json
from math import factorial
import time
from mix_parser import Parser


def representatives(k: int):
    if k == 0:
        yield ''
        return
    n = 3*k
    for aa_tail in combinations(range(1, n), k-1):
        aa = {0, *aa_tail}
        rest = [j for j in range(n) if j not in aa]
        for bb_tail in combinations(rest[1:], k-1):
            bb = {rest[0], *bb_tail}
            yield ''.join('a' if j in aa else 'b' if j in bb else 'c'
                          for j in range(n))


def run(max_k: int):
    p2, p3 = Parser(2, 500_000), Parser(3, 500_000)
    rows = []
    for k in range(max_k + 1):
        start = time.perf_counter()
        count = bad2 = bad3 = 0
        rejected2 = []
        for word in representatives(k):
            count += 1
            if not p2.accepts_word(word):
                bad2 += 1
                if k <= 5:
                    rejected2.append(word)
                if not p3.accepts_word(word):
                    bad3 += 1
        weight = 1 if k == 0 else 6
        total = factorial(3*k) // factorial(k)**3
        assert count * weight == total
        rows.append({'length': 3*k, 'renaming_orbits': count,
                     'total_words': total, 'rejected_r2': bad2 * weight,
                     'rejected_r3': bad3 * weight,
                     'rejected_r2_representatives_if_length_at_most_15': rejected2,
                     'seconds': time.perf_counter() - start})
    return {'complete': True, 'max_length': 3*max_k, 'results': rows}

if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('max_k', type=int, nargs='?', default=5)
    args = cli.parse_args()
    if args.max_k < 0:
        cli.error('max_k must be nonnegative')
    print(json.dumps(run(args.max_k), indent=2))
