#!/usr/bin/env python3
"""Rebuild the S4 certificate from exact relation schemas.

This discovery script is deliberately separate from verify_s4.py. It uses
fraction-free elimination and records a proof DAG, then expands that DAG
into a rational combination of independently regenerable relation rows.
Only the Python standard library is required. The checked-in certificate
can be replayed without running this script.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache, reduce
from itertools import product
from math import gcd
from pathlib import Path
import argparse
import json
import time
import verify_s4 as V


@lru_cache(None)
def compositions(n):
    if not n:
        return ((),)
    return tuple((a,) + tail for a in range(1, n + 1)
                 for tail in compositions(n - a))


@lru_cache(None)
def values(n):
    if not n:
        return ((),)
    return tuple(tuple(zip(indices, colors))
                 for indices in compositions(n)
                 for colors in product(range(4), repeat=len(indices))
                 if (indices[0], colors[0]) != (1, 0))


def descriptors():
    for p in (1, 2):
        lefts = values(p) + ((((1, 0),),) if p == 1 else ())
        for left in lefts:
            for right in values(5 - p):
                yield ('ds', left, right)
    for weight in range(1, 6):
        for indices in compositions(weight):
            for colors in product(range(2), repeat=len(indices)):
                if (indices[0], colors[0]) == (1, 0):
                    continue
                seed = tuple(zip(indices, colors))
                for multiplier in values(5 - weight):
                    yield ('lift', ('dist', seed), multiplier)


def primitive(row):
    row = {k: v for k, v in row.items() if v}
    if not row:
        return {}, 1
    divisor = reduce(gcd, row.values())
    if row[min(row)] < 0:
        divisor = -divisor
    return {k: v // divisor for k, v in row.items()}, divisor


def discover(output):
    start = time.monotonic()
    variables = sorted({min(z, tuple((a, (-c) % 4) for a, c in z))
                        for z in values(5)
                        if any(c % 2 for _, c in z)},
                       key=lambda z: (len(z), z), reverse=True)
    index = {z: j for j, z in enumerate(variables)}
    pivots, operations, initial_divisors, sources = {}, {}, {}, {}
    selected, seen = [], set()

    def eliminate(row):
        row, initial_divisor = primitive(row.copy())
        steps = []
        while row:
            key = min(row)
            if key not in pivots:
                break
            pivot = pivots[key]
            a, b = row[key], pivot[key]
            common = gcd(a, b)
            a, b = a // common, b // common
            row = {j: b * v for j, v in row.items()}
            V.add(row, pivot, -a)
            row, divisor = primitive(row)
            steps.append((key, a, b, divisor))
        return row, initial_divisor, steps

    total = 0
    for descriptor in descriptors():
        raw = V.standard_relation(descriptor)
        integer_row = {index[z]: c for z, c in raw.items()}
        canonical, _ = primitive(integer_row)
        if not canonical:
            continue
        signature = tuple(sorted(canonical.items()))
        if signature in seen:
            continue
        seen.add(signature)
        total += 1
        row, initial, steps = eliminate(integer_row)
        if row:
            key = min(row)
            pivots[key] = row
            operations[key] = steps
            initial_divisors[key] = initial
            sources[key] = len(selected)
            selected.append((descriptor, integer_row))
        if total % 300 == 0:
            print(f'{total} rows, rank {len(pivots)}, '
                  f'{time.monotonic() - start:.1f}s', flush=True)

    seed = ((1, 1), (4, 0))
    target = V.target_relation()
    combined = target.copy()
    V.add(combined, V.duality_relation(seed), 1120)
    residue, initial, steps = eliminate({index[z]: c
                                         for z, c in combined.items()})
    assert not residue, 'The chosen relation family did not prove the target.'
    pending, source_coefficients = {}, {}

    def unwind(coefficient, steps):
        for key, a, b, divisor in reversed(steps):
            pending[key] = (pending.get(key, Fraction(0))
                            - coefficient * Fraction(a, divisor))
            coefficient *= Fraction(b, divisor)
        return coefficient

    target_coefficient = unwind(Fraction(1), steps) / initial
    for key in sorted(pivots, reverse=True):
        coefficient = pending.get(key, Fraction(0))
        if coefficient:
            coefficient = (unwind(coefficient, operations[key])
                           / initial_divisors[key])
            source = sources[key]
            source_coefficients[source] = (
                source_coefficients.get(source, Fraction(0)) + coefficient)

    entries = []
    for source, coefficient in sorted(source_coefficients.items()):
        if coefficient:
            descriptor, _ = selected[source]
            entries.append({'coefficient': str(-coefficient / target_coefficient),
                            'relation': descriptor})
    data = {
        'format': 'Gaussian S4 exact rational relation certificate v1',
        'target': ('1120*S4 - 640*g41 + 480*g32 + 1440*g23 - 5*pi^5 '
                   '+ 135*G*zeta(3) + 2240*beta(4)*log(2)'),
        'target_as_words': list(target.items()),
        'duality': {'indices_colors': seed, 'coefficient': '-1120'},
        'standard_relations': entries,
    }
    output.write_text(json.dumps(data, indent=2) + '\n')
    report = V.verify(output)
    report.update(discovery_rows=total, discovery_rank=len(pivots),
                  elapsed_seconds=time.monotonic() - start)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', nargs='?', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'results' / 'S4_certificate_rebuilt.json')
    args = parser.parse_args()
    discover(args.output)
