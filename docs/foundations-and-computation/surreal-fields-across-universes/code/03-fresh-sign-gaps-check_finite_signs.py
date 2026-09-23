#!/usr/bin/env python3
"""Finite regression checks for Surreal Fields Across Set-Theoretic Universes.

These checks verify sign conventions and finite block indices, NOT the
transfinite freshness, forcing, saturation, or class-isomorphism theorems.
Python 3.9+; standard library only.
"""
from __future__ import annotations

import argparse
import itertools
import json
from functools import cmp_to_key
from pathlib import Path
from typing import Dict, List, Sequence, Tuple


def compare(a: str, b: str) -> int:
    """First-disagreement sign order: '-' < end-of-sequence < '+'."""
    if set(a + b) - {'-', '+'}:
        raise ValueError("A sign string may contain only '+' and '-'.")
    rank = {'-': -1, '+': 1}
    for index in range(max(len(a), len(b))):
        av = rank[a[index]] if index < len(a) else 0
        bv = rank[b[index]] if index < len(b) else 0
        if av != bv:
            return 1 if av > bv else -1
    return 0


def encode(values: Sequence[int]) -> Tuple[str, List[str], List[str]]:
    """Build the finite counterpart of +(f(xi)+1), minus, per block."""
    if any(not isinstance(v, int) or isinstance(v, bool) or v < 0 for v in values):
        raise ValueError('Values must be nonnegative integers.')
    sign = ''.join('+' * (v + 1) + '-' for v in values)
    left: List[str] = []
    right: List[str] = []
    boundary = 0
    for value in values:
        left.append(sign[:boundary + value])
        right.append(sign[:boundary + value + 1])
        boundary += value + 2
    return sign, left, right


def decode(sign: str) -> List[int]:
    """Decode completed nonempty-plus blocks ending in minus signs."""
    if not sign:
        return []
    if set(sign) - {'-', '+'} or not sign.endswith('-'):
        raise ValueError('Not a completed block code.')
    runs = sign[:-1].split('-')
    if any(not run or set(run) != {'+'} for run in runs):
        raise ValueError('Every block must have a nonempty plus run.')
    return [len(run) - 1 for run in runs]


def require(condition: bool, description: str) -> None:
    # Unlike an assert statement, this remains enabled under python -O.
    if not condition:
        raise RuntimeError(description)


def run_checks() -> Dict[str, object]:
    universe = [''.join(s) for n in range(7)
                for s in itertools.product('-+', repeat=n)]
    ordered = sorted(universe, key=cmp_to_key(compare))
    cone_checks = 0
    for prefix in universe:
        indices = [i for i, sign in enumerate(ordered)
                   if sign.startswith(prefix)]
        require(indices == list(range(indices[0], indices[-1] + 1)),
                'Nonconvex finite prefix cone: ' + prefix)
        cone_checks += 1

    comparison_checks = 0
    for a in universe:
        for b in universe:
            require(compare(a, b) == -compare(b, a), 'Antisymmetry failed.')
            require((compare(a, b) == 0) == (a == b), 'Equality failed.')
            comparison_checks += 1

    block_cases = 0
    nested_checks = 0
    for length in range(1, 5):
        for values in itertools.product(range(4), repeat=length):
            sign, left, right = encode(values)
            require(decode(sign) == list(values), 'Block round-trip failed.')
            for index, (a, b) in enumerate(zip(left, right)):
                require(compare(a, sign) < 0 < compare(b, sign),
                        'Endpoint has wrong side.')
                require(sign[len(a)] == '+' and sign[len(b)] == '-',
                        'Terminal-plus/minus index is wrong.')
                for later in range(index + 1, length):
                    require(compare(a, left[later]) < 0, 'Left nesting failed.')
                    require(compare(right[later], b) < 0, 'Right nesting failed.')
                    nested_checks += 1
            block_cases += 1

    return {
        'status': 'passed',
        'finite_sign_strings': len(universe),
        'maximum_sign_length_for_cone_tests': 6,
        'ordered_pair_comparison_checks': comparison_checks,
        'prefix_cone_convexity_checks': cone_checks,
        'block_code_cases': block_cases,
        'nested_endpoint_pairs': nested_checks,
        'scope': ('Finite regression checks only. No test or formal verification '
                  'of freshness, forcing, saturation, or proper-class theorems.'),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='Optional destination for a JSON report.')
    args = parser.parse_args()
    report = run_checks()
    serialized = json.dumps(report, indent=2) + '\n'
    print(serialized, end='')
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized, encoding='utf-8')


if __name__ == '__main__':
    main()
