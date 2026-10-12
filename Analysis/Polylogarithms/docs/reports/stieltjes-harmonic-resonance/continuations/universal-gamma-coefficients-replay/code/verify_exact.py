#!/usr/bin/env python3
"""Independent exact sparse-IBP versus beta-moment verification.

The written proof, not this finite test, establishes the all-weight theorem.
Python 3.10+; standard library only. All coefficients are fractions.Fraction.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import argparse, csv, json, platform, time

Monomial = tuple[int, ...]
Polynomial = dict[Monomial, Q]

def is_canonical(m: Monomial) -> bool:
    return not m or m[-1] == 0 or (len(m) >= 2 and m[-2] == m[-1])

@lru_cache(None)
def derivative_monomial(m: Monomial) -> tuple[tuple[Monomial, int], ...]:
    result: dict[Monomial, int] = defaultdict(int)
    for r, multiplicity in Counter(m).items():
        a = list(m); a.remove(r); a.append(r + 1)
        result[tuple(sorted(a))] += multiplicity
    return tuple(result.items())

def derivative(p: Polynomial) -> Polynomial:
    result: dict[Monomial, Q] = defaultdict(Q)
    for mon, c in p.items():
        for target, multiple in derivative_monomial(mon):
            result[target] += c * multiple
    return {m: c for m, c in result.items() if c}

@lru_cache(None)
def normal_monomial(m: Monomial) -> tuple[tuple[Monomial, Q], ...]:
    """Literal triangular IBP; does not use the beta formula."""
    if is_canonical(m):
        return ((m, Q(1)),)
    r = m[-1]
    rest = list(m[:-1])
    a = rest.count(r - 1)
    primitive = tuple(sorted(rest + [r - 1]))
    result: dict[Monomial, Q] = defaultdict(Q)
    for n, coefficient in derivative_monomial(primitive):
        if n == m:
            assert coefficient == a + 1
            continue
        for k, value in normal_monomial(n):
            result[k] -= Q(coefficient, a + 1) * value
    return tuple((n, c) for n, c in result.items() if c)

def normal(p: Polynomial) -> Polynomial:
    result: dict[Monomial, Q] = defaultdict(Q)
    for m, c in p.items():
        for n, v in normal_monomial(m):
            result[n] += c * v
    return {m: c for m, c in result.items() if c}

def next_bell(p: Polynomial) -> Polynomial:
    result: dict[Monomial, Q] = defaultdict(Q)
    for m, c in p.items(): result[(0,) + m] += c
    for m, c in derivative(p).items(): result[m] -= c
    return {m: c for m, c in result.items() if c}

def partitions(n: int, lower: int = 1):
    if n == 0:
        yield ()
    else:
        for first in range(lower, n + 1):
            for tail in partitions(n - first, first):
                yield (first,) + tail

def poly_multiply(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): result[i + j] += x * y
    while len(result) > 1 and result[-1] == 0: result.pop()
    return tuple(result)

@lru_cache(None)
def phi(j: int) -> tuple[int, ...]:
    # The coefficient of x**(j+1) cancels exactly.
    return tuple((-1) ** (j + r) * comb(j + 1, r) for r in range(j + 1))

@lru_cache(None)
def beta_integral(m: Monomial) -> Q:
    """The polynomial integral only; the monomial must have positive top index."""
    counts = Counter(m); d = max(counts)
    assert d >= 1 and counts[d] >= 2
    polynomial = (1,)
    for j, count in counts.items():
        exponent = count - (2 if j == d else 0)
        for _ in range(exponent):
            polynomial = poly_multiply(polynomial, phi(j))
    return sum((Q(c * factorial(d + ell) * factorial(d), factorial(2*d + ell + 1))
                for ell, c in enumerate(polynomial)), Q(0))

@lru_cache(None)
def beta_base(positive: Monomial) -> Q:
    counts = Counter(positive); d = positive[-1]
    denominator = 1
    for j, count in counts.items():
        denominator *= factorial(count) * factorial(j + 1) ** count
    return Q((-1)**d * (d + 1), denominator) * beta_integral(positive)

def beta_coefficient(m: Monomial) -> Q:
    if not is_canonical(m): return Q(0)
    if not m or m[-1] == 0: return Q(1)
    a = m.count(0)
    weight = sum(r + 1 for r in m)
    return Q(factorial(weight), factorial(a)) * beta_base(m[a:])

def name(m: Monomial) -> str:
    return '*'.join(f'u{j}^{n}' for j, n in sorted(Counter(m).items())) or '1'

def run(max_weight: int, output: Path) -> dict:
    if max_weight < 14:
        raise ValueError('Use --max-weight at least 14 to include the nonintegrality control.')
    output.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter(); bell: Polynomial = {(): Q(1)}
    checks = zeros = nonzero = 0; rows = []; bad = []
    first_nonintegral = None; counterexample = None
    for weight in range(max_weight + 1):
        canonical = normal(bell)
        assert all(is_canonical(mon) for mon in canonical)
        for parts in partitions(weight):
            mon = tuple(j - 1 for j in parts)
            if not is_canonical(mon): continue
            checks += 1
            expected = beta_coefficient(mon); actual = canonical.get(mon, Q(0))
            if expected != actual:
                bad.append({'weight': weight, 'monomial': name(mon),
                            'ibp': str(actual), 'beta': str(expected)})
            odd_count = sum(1 for j in mon if j % 2)
            if mon and mon[-1] > 0:
                assert (expected == 0) == (odd_count % 2 == 1)
                if expected: assert (expected > 0) == (mon[-1] % 2 == 0)
            if actual:
                nonzero += 1
                if actual.denominator > 1 and first_nonintegral is None:
                    first_nonintegral = {'weight': weight, 'monomial': name(mon), 'coefficient': str(actual)}
            else: zeros += 1
            rows.append([weight, name(mon), str(actual), str(expected), actual == expected])
        if weight == 14:
            counterexample = canonical.get((1, 3, 3, 3), Q(0))
            assert counterexample == Q(-3185, 3)
            # Mutation control: equality testing must reject a changed coefficient.
            assert counterexample + 1 != beta_coefficient((1, 3, 3, 3))
        if weight < max_weight: bell = next_bell(bell)
    with (output/'exact_coefficients.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['weight','monomial','direct_ibp','beta_formula','match'])
        writer.writerows(rows)
    report = {'status': 'PASS' if not bad else 'FAIL', 'max_weight': max_weight,
              'canonical_coefficients_compared': checks, 'nonzero_coefficients': nonzero,
              'zero_coefficients': zeros, 'mismatches': bad,
              'explicit_counterexample': {'monomial': 'u1*u3^3','weight':14,'coefficient':str(counterexample)},
              'first_nonintegral_in_traversal': first_nonintegral,
              'mutation_control': 'PASS', 'python': platform.python_version(),
              'seconds': time.perf_counter()-started,
              'method': 'Exact Fraction sparse IBP compared with independent finite beta expansion; finite verification, not an all-weight proof.'}
    (output/'exact_report.json').write_text(json.dumps(report, indent=2))
    if bad: raise AssertionError(f'{len(bad)} coefficient mismatches')
    return report

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-weight', type=int, default=28)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'results')
    args = parser.parse_args()
    print(json.dumps(run(args.max_weight, args.output), indent=2))
