#!/usr/bin/env python3
"""Exact cutoff-cylinder probabilities and their first phase-resolved correction."""
from __future__ import annotations
import argparse
import csv
import itertools
import json
from pathlib import Path
import mpmath as mp
import sympy as sp
from catalan_statistics import catalans, parts_to, saddle


def exact_counts(nmax: int) -> list[int]:
    p = [0] * (nmax + 1)
    p[0] = 1
    for c in parts_to(nmax):
        for n in range(c, nmax + 1):
            p[n] += p[n-c]
    return p


def cylinder_numerator(p: list[int], n: int, sizes: list[int], values: tuple[int, ...]) -> int:
    """Inclusion-exclusion for exactly the specified multiplicities."""
    total = 0
    for bits in itertools.product((0, 1), repeat=len(sizes)):
        shift = sum(c*(r+b) for c, r, b in zip(sizes, values, bits))
        if shift <= n:
            total += (-1)**sum(bits) * p[n-shift]
    return total


def phase_probability(theta, indices: tuple[int, ...], values: tuple[int, ...]):
    q = mp.mpf(1)
    T = mp.mpf(0)
    S2 = mp.mpf(0)
    curvature = mp.mpf(0)
    for j, r in zip(indices, values):
        d = j-theta
        v = mp.power(4, d)
        e = mp.exp(-v)
        q *= (1-e)*mp.exp(-r*v)
        first = v*e/(1-e) - r*v
        T += first
        S2 += v*v*e/(1-e)**2
        curvature += d*first
    correction = -mp.mpf('1.5')*curvature + (S2-T*T-2*T)/2
    return q, correction


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=1000000)
    parser.add_argument('--dps', type=int, default=60)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data')
    args = parser.parse_args()
    if args.max_n < 100 or args.dps < 30:
        parser.error('Use max-n >= 100 and dps >= 30.')
    args.output.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = args.dps
    p = exact_counts(args.max_n)
    # An independent exhaustive check for two specified part sizes at small n.
    sizes = [2, 5]
    for n in range(61):
        remaining = [c for c in parts_to(n) if c not in sizes]
        counts = [0]*(n+1)
        counts[0] = 1
        for c in remaining:
            for k in range(c, n+1):
                counts[k] += counts[k-c]
        for values in itertools.product(range(3), repeat=2):
            left = n-sum(c*r for c, r in zip(sizes, values))
            direct = counts[left] if left >= 0 else 0
            assert cylinder_numerator(p, n, sizes, values) == direct
    # Generic product-amplitude identity at first conditioning order.
    s, L, L1, L2, Q, DQ, D2Q = sp.symbols('s L L1 L2 Q DQ D2Q')
    a1 = -s*L1*Q + L*DQ
    a2 = (2*s*L1+s*s*L2)*Q - 2*s*L1*DQ + L*(D2Q-DQ)
    expected = -s*s*L2*Q/2 + s*L1*DQ - L*(D2Q+DQ)/2
    assert sp.expand(-(a2+2*a1)/2-expected) == 0
    rows = []
    for n in (100, 1000, 10000, 100000, 1000000):
        if n > args.max_n:
            continue
        t, m, _ = saddle(n, 4)
        M = int(mp.floor(m))
        theta = m-M
        cs = catalans(M+1)
        for values in ((0, 0), (1, 0), (0, 1), (1, 1)):
            num = cylinder_numerator(p, n, [cs[M-1], cs[M]], values)
            exact = mp.mpf(num)/p[n]
            q, correction = phase_probability(theta, (0, 1), values)
            rows.append(dict(n=n, z_M=values[0], z_Mplus1=values[1],
                             exact=str(exact), limit=str(q),
                             corrected=str(q*(1+correction/m)),
                             limit_error=str(q-exact),
                             corrected_error=str(q*(1+correction/m)-exact)))
    with (args.output/'cutoff_cylinders.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
    result = {'checks': ['549 exact cutoff-cylinder inclusion-exclusion checks',
                         'exact first-order joint differential-operator identity'],
              'max_n': args.max_n, 'dps': args.dps,
              'scope': 'Finite exact checks and non-certified numerical comparisons.'}
    (args.output/'cutoff_verification.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
