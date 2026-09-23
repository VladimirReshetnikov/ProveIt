#!/usr/bin/env python3
"""Exact finite checks accompanying the research manuscript.

These tests do not verify infinite Hahn supports, proper classes, or the
existence of a derivation on all real numbers. Python 3.10+; standard library.
Run `python verify.py --output verification.json` from any working directory.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as F
import json
from pathlib import Path
import random
from typing import Callable, TypeVar

SEED = 20260923
rng = random.Random(SEED)
counts: dict[str, int] = defaultdict(int)
K = TypeVar('K')
Series = dict[int, F]
Source = dict[tuple[int, int], F]  # (outer exponent, power of b)
Target = dict[tuple[int, int, int], F]  # (outer block, Taylor degree, power of b)


def check(condition: bool, group: str, message: str) -> None:
    counts[group] += 1
    if not condition:
        raise AssertionError(f'{group}: {message}')


def clean(p: dict[K, F]) -> dict[K, F]:
    return {k: v for k, v in p.items() if v}


def add(p: dict[K, F], q: dict[K, F]) -> dict[K, F]:
    r = p.copy()
    for k, v in q.items():
        r[k] = r.get(k, F(0)) + v
    return clean(r)


def mul(p: Series, q: Series) -> Series:
    r: dict[int, F] = defaultdict(F)
    for a, x in p.items():
        for b, y in q.items():
            r[a + b] += x * y
    return clean(r)


def ct(p: Series) -> F:
    return p.get(0, F(0))


def random_series(size: int = 10) -> Series:
    p: dict[int, F] = defaultdict(F)
    for _ in range(size):
        p[rng.randrange(-9, 10)] += F(rng.randrange(-7, 8), rng.randrange(1, 8))
    return clean(p)


def monomial_embedding(p: Series, dilation: int, weight: F) -> Series:
    return {dilation * g: x * weight ** g for g, x in p.items()}


def monomial_adjoint(p: Series, dilation: int, weight: F) -> Series:
    return {h // dilation: y / weight ** (h // dilation)
            for h, y in p.items() if h % dilation == 0}


def triangular_checks() -> None:
    for n in range(1, 25):
        for _ in range(12):
            a = [[F(rng.randrange(-5, 6), rng.randrange(1, 6)) if j <= i else F(0)
                  for j in range(n)] for i in range(n)]
            for i in range(n):
                while a[i][i] == 0:
                    a[i][i] = F(rng.randrange(-5, 6), rng.randrange(1, 6))
            c: list[F] = []
            for i in range(n):
                old = sum((a[i][j] * c[j] for j in range(i)), F(0))
                c.append(F(0) if old else F(1))
                val = sum((a[i][j] * c[j] for j in range(i + 1)), F(0))
                check(val != 0, 'triangular_detector', 'a triangular row vanished')
                check(all(a[i][j] == 0 for j in range(i + 1, n)),
                      'triangular_detector', 'nonzero entry beyond diagonal')
            for i in range(n):
                full = sum((a[i][j] * c[j] for j in range(n)), F(0))
                prefix = sum((a[i][j] * c[j] for j in range(i + 1)), F(0))
                check(full == prefix != 0, 'triangular_detector', 'prefix mismatch')


def adjoint_checks() -> None:
    j: Callable[[Series], Series] = lambda p: monomial_embedding(p, 2, F(2))
    e: Callable[[Series], Series] = lambda p: monomial_adjoint(p, 2, F(2))
    h: Callable[[Series], Series] = lambda p: monomial_embedding(p, 3, F(3))
    eh: Callable[[Series], Series] = lambda p: monomial_adjoint(p, 3, F(3))
    for _ in range(500):
        x, y, z = random_series(), random_series(), random_series()
        check(ct(mul(j(x), y)) == ct(mul(x, e(y))),
              'monomial_adjoint', 'constant-term adjoint identity')
        check(e(mul(j(x), y)) == mul(x, e(y)),
              'monomial_adjoint', 'projection formula')
        check(e(j(x)) == x, 'monomial_adjoint', 'retraction identity')
        check(ct(j(x)) == ct(x), 'monomial_adjoint', 'constant term')
        check(j(mul(x, z)) == mul(j(x), j(z)),
              'monomial_adjoint', 'embedding multiplicativity')
        check(j(add(x, z)) == add(j(x), j(z)),
              'monomial_adjoint', 'embedding additivity')
        check(j(e(j(e(y)))) == j(e(y)),
              'monomial_adjoint', 'idempotent projection')
        check(h(j(x)) == monomial_embedding(x, 6, F(18)),
              'monomial_adjoint', 'composite monomial weight')
        check(e(eh(y)) == monomial_adjoint(y, 6, F(18)),
              'monomial_adjoint', 'adjoint tower law')
    u, invu = {1: F(1)}, {-1: F(1)}
    check(e(u) == {} and e(invu) == {}, 'monomial_adjoint', 'kernel monomials')
    check(e(mul(u, invu)) == {0: F(1)},
          'monomial_adjoint', 'explicit nonmultiplicativity')


def source_mul(p: Source, q: Source) -> Source:
    r: dict[tuple[int, int], F] = defaultdict(F)
    for (g, d), x in p.items():
        for (h, e), y in q.items():
            r[g + h, d + e] += x * y
    return clean(r)


def generalized_binomial(d: int, n: int) -> F:
    result = F(1)
    for j in range(n):
        result *= F(d - j, j + 1)
    return result


def lift(p: Source, cutoff: int) -> Target:
    # b^d -> sum binomial(d,n) b^(d-n) T^n, truncated only in Taylor degree.
    r: dict[tuple[int, int, int], F] = defaultdict(F)
    for (g, d), x in p.items():
        for n in range(cutoff + 1):
            r[g, n, d - n] += x * generalized_binomial(d, n)
    return clean(r)


def target_mul(p: Target, q: Target, cutoff: int) -> Target:
    r: dict[tuple[int, int, int], F] = defaultdict(F)
    for (g, n, d), x in p.items():
        for (h, m, e), y in q.items():
            if n + m <= cutoff:
                r[g + h, n + m, d + e] += x * y
    return clean(r)


def source_ct(p: Source) -> dict[int, F]:
    return {d: x for (g, d), x in p.items() if g == 0}


def target_ct(p: Target) -> dict[int, F]:
    return {d: x for (g, n, d), x in p.items() if g == 0 and n == 0}


def source_integer_part(p: Source) -> bool:
    # Coefficients are in Q[b,b^-1], with b transcendental.
    return (all(g <= 0 for g, _ in p)
            and all(d == 0 for (g, d) in p if g == 0)
            and p.get((0, 0), F(0)).denominator == 1)


def target_integer_part(p: Target) -> bool:
    return (all((g, n) <= (0, 0) for g, n, _ in p)
            and all(d == 0 for (g, n, d) in p if (g, n) == (0, 0))
            and p.get((0, 0, 0), F(0)).denominator == 1)


def random_source(size: int = 8) -> Source:
    p: dict[tuple[int, int], F] = defaultdict(F)
    for _ in range(size):
        p[rng.randrange(-3, 4), rng.randrange(-3, 5)] += F(
            rng.randrange(-4, 5), rng.randrange(1, 5))
    return clean(p)


def taylor_checks() -> None:
    cutoff = 6
    for _ in range(180):
        x, y = random_source(), random_source()
        jx, jy = lift(x, cutoff), lift(y, cutoff)
        check(lift(source_mul(x, y), cutoff) == target_mul(jx, jy, cutoff),
              'taylor_blocks', 'multiplicativity modulo Taylor degree bound')
        check(lift(add(x, y), cutoff) == add(jx, jy),
              'taylor_blocks', 'additivity')
        check(target_ct(jx) == source_ct(x), 'taylor_blocks', 'constant coefficient')
        check(target_integer_part(jx) == source_integer_part(x),
              'taylor_blocks', 'reflection of symbolic integer-part membership')
        if x:
            vg = min(g for g, _ in x)
            vt = min((g, n) for g, n, _ in jx)
            check(vt == (vg, 0), 'taylor_blocks', 'lexicographic valuation')
        # Make an omnific-like input: negative blocks plus an integer.
        oz = {(g - 5, d): value for (g, d), value in x.items()}
        oz[(0, 0)] = F(rng.randrange(-6, 7))
        oz = clean(oz)
        check(source_integer_part(oz), 'taylor_blocks', 'constructed source membership')
        check(target_integer_part(lift(oz, cutoff)),
              'taylor_blocks', 'negative blocks remain negative')
    b: Source = {(0, 1): F(1)}
    binv: Source = {(0, -1): F(1)}
    one: Target = {(0, 0, 0): F(1)}
    check(lift(b, cutoff) == {(0, 0, 1): F(1), (0, 1, 0): F(1)},
          'taylor_blocks', 'b maps to b+T')
    check(target_mul(lift(b, cutoff), lift(binv, cutoff), cutoff) == one,
          'taylor_blocks', 'formal reciprocal prefix')
    for a in range(-5, 6):
        for bdeg in range(-5, 6):
            for n in range(10):
                lhs = sum((generalized_binomial(a, j) * generalized_binomial(bdeg, n-j)
                           for j in range(n + 1)), F(0))
                check(lhs == generalized_binomial(a + bdeg, n),
                      'taylor_blocks', 'generalized Vandermonde / Leibniz')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().with_name('verification.json'))
    args = parser.parse_args()
    triangular_checks()
    adjoint_checks()
    taylor_checks()
    report = {
        'status': 'PASS',
        'seed': SEED,
        'arithmetic': 'fractions.Fraction; exact integer and rational arithmetic',
        'assertions_by_group': dict(counts),
        'total_assertions': sum(counts.values()),
        'scope': [
            'Finite lower-triangular support detector identities',
            'Finite Laurent constant-term adjoints and transfer identities',
            'Rank-two lexicographic Taylor block identities through degree 6',
            'Generalized binomial convolution through degree 9'
        ],
        'not_verified': [
            'Arbitrary infinite Hahn support claims',
            'Existence or computation of a derivation on all real numbers',
            'Proper-class foundations or all surreal automorphisms',
            'Historical novelty or proof-assistant verification'
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
