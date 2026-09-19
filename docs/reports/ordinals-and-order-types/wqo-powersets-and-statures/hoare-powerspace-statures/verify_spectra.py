#!/usr/bin/env python3
"""Exhaust finite poset data for the proposed Hoare-stature spectrum theorem.

Python 3.9+, standard library only. No transfinite proof is performed here.
Every relation considered has i <_Q j only if i < j as integers. Every
finite poset has a linear extension, so this covers every isomorphism type,
usually with repetitions. Outputs contain one concrete witness per pair.
"""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Iterator, List, Sequence, Tuple


def posets(n: int) -> Iterator[Tuple[int, ...]]:
    """Yield strict predecessor masks of naturally labelled n-point posets."""
    edges = [(i, j) for j in range(n) for i in range(j)]
    for mask in range(1 << len(edges)):
        pred = [0] * n
        for k, (i, j) in enumerate(edges):
            if (mask >> k) & 1:
                pred[j] |= 1 << i
        transitive = True
        for j, pj in enumerate(pred):
            for i in range(j):
                if (pj >> i) & 1 and pred[i] & ~pj:
                    transitive = False
                    break
            if not transitive:
                break
        if transitive:
            yield tuple(pred)


def downsets(pred: Sequence[int]) -> List[int]:
    """Return every downset as a point-membership bit mask."""
    n = len(pred)
    return [d for d in range(1 << n)
            if all(not ((d >> j) & 1) or not (pred[j] & ~d)
                   for j in range(n))]


def finite_model(pred: Sequence[int], u: int, core_size: int) -> Tuple[int, ...]:
    """Replace the infinite core by a finite antichain.

    Core points precede every q outside U, and have no other comparabilities.
    Q retains its original order. U must be a downset of Q.
    """
    if core_size < 1:
        raise ValueError('core_size must be positive')
    if u not in downsets(pred):
        raise ValueError('U is not a downset')
    core_mask = (1 << core_size) - 1
    return tuple([0] * core_size + [
        (pj << core_size) | (0 if (u >> j) & 1 else core_mask)
        for j, pj in enumerate(pred)
    ])


def members(mask: int, n: int) -> List[int]:
    return [i for i in range(n) if (mask >> i) & 1]


def verify(max_n: int, check_n: int, out: Path) -> None:
    if not 0 <= check_n <= max_n <= 7:
        raise ValueError('require 0 <= check_n <= max_n <= 7')
    out.mkdir(parents=True, exist_ok=True)
    summary = []
    witnesses = {}
    rows = []
    finite_checks = 0
    pair_instances = 0
    for n in range(max_n + 1):
        count = 0
        pairs = {}
        for pred in posets(n):
            count += 1
            ideals = downsets(pred)
            jq = len(ideals)
            for u in ideals:
                pair_instances += 1
                ju = sum(1 for d in ideals if not (d & ~u))
                a, b = ju, jq - ju
                assert a >= 1 and b >= 0 and n + 1 <= a + b <= 2 ** n
                if (a, b) not in pairs:
                    pairs[(a, b)] = {
                        'n': n, 'omega_coefficient': a, 'finite_tail': b,
                        'j_Q': jq, 'j_U': ju,
                        'strict_order_pairs': [[i, j] for j in range(n)
                                               for i in range(j)
                                               if (pred[j] >> i) & 1],
                        'U': members(u, n),
                    }
                if n <= check_n:
                    for core_size in range(1, 4):
                        actual = len(downsets(finite_model(pred, u, core_size)))
                        expected = (2 ** core_size) * a + b
                        assert actual == expected, (n, pred, u, core_size,
                                                    actual, expected)
                        finite_checks += 1
        keys = sorted(pairs)
        assert keys[0] == (1, n)
        assert keys[-1] == (2 ** n, 0)
        summary.append({'n': n, 'naturally_labelled_posets': count,
                        'distinct_spectrum_values': len(keys),
                        'min_pair': list(keys[0]), 'max_pair': list(keys[-1])})
        witnesses[str(n)] = [pairs[key] for key in keys]
        for a, b in keys:
            rows.append({'n': n, 'omega_coefficient': a, 'finite_tail': b,
                         'j_Q': a + b})
        print(f'n={n}: {count} relations; {len(keys)} spectrum values', flush=True)
    assert [(r['omega_coefficient'], r['finite_tail']) for r in witnesses['0']] == [(1, 0)]
    if max_n >= 1:
        assert [(r['omega_coefficient'], r['finite_tail']) for r in witnesses['1']] == [(1, 1), (2, 0)]
    if max_n >= 2:
        assert [(r['omega_coefficient'], r['finite_tail']) for r in witnesses['2']] == [
            (1, 2), (1, 3), (2, 1), (2, 2), (3, 0), (4, 0)]
    report = {
        'description': 'Finite data supporting, but not proving, the transfinite theorem.',
        'enumeration': 'all transitive subrelations of the natural strict linear order',
        'max_n': max_n, 'finite_model_check_max_n': check_n,
        'finite_core_sizes_checked': [1, 2, 3],
        'poset_downset_pair_instances': pair_instances,
        'finite_model_checks_passed': finite_checks,
        'summary': summary,
    }
    (out / 'verification_results.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    (out / 'witnesses.json').write_text(json.dumps(witnesses, indent=2) + '\n', encoding='utf-8')
    with (out / 'spectra.csv').open('w', encoding='utf-8', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=['n', 'omega_coefficient', 'finite_tail', 'j_Q'])
        writer.writeheader()
        writer.writerows(rows)
    print(f'{finite_checks} independent finite-model counts passed.', flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=6)
    parser.add_argument('--finite-check-n', type=int, default=4)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    verify(args.max_n, args.finite_check_n, args.output)


if __name__ == '__main__':
    main()
