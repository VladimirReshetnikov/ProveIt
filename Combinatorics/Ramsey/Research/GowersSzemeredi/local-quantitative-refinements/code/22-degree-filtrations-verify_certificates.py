#!/usr/bin/env python3
"""Exact arithmetic for the certificate filtration in the accompanying article.

Only the Python standard library is required.  Exhaustive checks are deliberately
small; the all-parameter assertions are proved in the article.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb, factorial, log10
from pathlib import Path
import json


def affine_class_count(n):
    return (3 ** n - 2 ** (n + 1) + 1) // 2


def moment(a):
    return comb(a, a // 2) if a % 2 == 0 else 0


def joint_moments(k, bound):
    """M[a,b] = CT (sum U_i)^a (sum U_i^2)^b, U_i=z_i+z_i^-1."""
    keys = [(a, b) for b in range(bound // 2 + 1)
            for a in range(0, bound - 2 * b + 1, 2)]
    values = {key: int(key == (0, 0)) for key in keys}
    transitions = {}
    for a, b in keys:
        transitions[a, b] = [
            (a - i, b - j, comb(a, i) * comb(b, j) * moment(i + 2 * j))
            for i in range(0, a + 1, 2) for j in range(b + 1)]
    for _ in range(k):
        values = {key: sum(c * values[i, j] for i, j, c in transitions[key])
                  for key in keys}
    return values


def constant_terms(k, q):
    """Compute CT F_k^q and CT B_k^q by exact joint moments."""
    moments = joint_moments(k, 2 * q)
    polynomial = {(0, 0): 1}
    factor = {(0, 0): 6 - 4 * k, (1, 0): 4, (2, 0): 1, (0, 1): 1}
    for _ in range(q):
        nxt = Counter()
        for (a, b), c in polynomial.items():
            for (i, j), d in factor.items():
                nxt[a + i, b + j] += c * d
        polynomial = nxt
    numerator = sum(c * moments.get((a, b), 0)
                    for (a, b), c in polynomial.items())
    assert numerator % (2 ** q) == 0
    f = numerator // (2 ** q)
    binary = sum(comb(q, a) * 2 ** (q - a) * moments.get((a, 0), 0)
                 for a in range(q + 1))
    return f, binary


def balanced_degree_one(k, q):
    f, b = constant_terms(k, q)
    numerator = f - 2 * b - 3 ** q + 2 ** (q + 1)
    assert numerator % 2 == 0
    return numerator // 2


def profiles(k, q):
    result = [affine_class_count(q)]
    result.append(((2 * k * k + 4 * k + 3) ** q
                   - 2 * (2 * k + 2) ** q + 1) // 2)
    for t in range(2, k + 1):
        result.append(affine_class_count(q * sum(comb(k, j) for j in range(t + 1))))
    return result


def leading_coefficient(q):
    # 2^(q-1) q! [z^q] exp(-z/2) / sqrt(1-z).
    a = sum(Fraction((-1) ** j * comb(2 * (q - j), q - j),
                     2 ** j * factorial(j) * 4 ** (q - j))
            for j in range(q + 1))
    return 2 ** (q - 1) * factorial(q) * a


def enumerate_affine(k):
    verts = list(product((0, 1), repeat=k))
    out = []
    for c in (-1, 0, 1):
        for slopes in product(range(-2, 3), repeat=k):
            values = tuple(c + sum(a * x for a, x in zip(slopes, v)) for v in verts)
            if all(v in (-1, 0, 1) for v in values):
                out.append((slopes, values))
    assert len(out) == 2 * k * k + 4 * k + 3
    binary = [item for item in out if set(item[1]) <= {0, 1}]
    assert len(binary) == 2 * k + 2
    return out, binary


def enumerate_constant_term(patterns, k, q):
    # Multiplicities in a sparse Laurent polynomial; no floating-point arithmetic.
    one = Counter(slopes for slopes, _ in patterns)
    current = {tuple([0] * k): 1}
    for _ in range(q):
        nxt = Counter()
        for a, c in current.items():
            for b, d in one.items():
                nxt[tuple(x + y for x, y in zip(a, b))] += c * d
        current = nxt
    return current[tuple([0] * k)]


def mobius_coefficients(values, k, modulus=None):
    arr = list(values)
    for i in range(k):
        for mask in range(1 << k):
            if mask & (1 << i):
                arr[mask] -= arr[mask ^ (1 << i)]
                if modulus:
                    arr[mask] %= modulus
    return arr


def check_degree_duality(k, p):
    checked = 0
    for eta in product((-1, 0, 1), repeat=1 << k):
        normalized = [((-1) ** m.bit_count()) * eta[m] for m in range(1 << k)]
        coeff = mobius_coefficients(normalized, k, p)
        degree = max((i.bit_count() for i, c in enumerate(coeff) if c % p), default=-1)
        moments = [sum(eta[m] for m in range(1 << k) if m & s == s) % p
                   for s in range(1 << k)]
        minimum = min((s.bit_count() for s, c in enumerate(moments) if c), default=k + 1)
        assert minimum == k - degree
        checked += 1
    return checked


def main():
    checks = []
    for k in range(1, 4):
        ternary, binary = enumerate_affine(k)
        for q in (4, 6):
            actual = (enumerate_constant_term(ternary, k, q),
                      enumerate_constant_term(binary, k, q))
            predicted = constant_terms(k, q)
            assert actual == predicted
            checks.append({'k': k, 'q': q, 'F_CT': actual[0], 'B_CT': actual[1]})
    duality = [{'k': k, 'p': p, 'patterns': check_degree_duality(k, p)}
               for k in (1, 2, 3) for p in (5, 7)]
    tables = []
    for k in (1, 2, 3, 4, 8, 16):
        for q in (4, 16):
            u = profiles(k, q)
            all_count = u[-1] - u[0]
            all_exact = (str(all_count) if all_count.bit_length() < 1000
                         else f'A({q * 2 ** k}) - A({q})')
            tables.append({'k': k, 'd': q // 2, 'balanced_degree_one': balanced_degree_one(k, q),
                           'all_degree_one': u[1] - u[0],
                           'all_nonparity_exact': all_exact,
                           'all_nonparity_log10': round(log10(all_count), 9)})
    # Newton coefficients give an independently checked exact polynomial in k.
    polys = {}
    for q in (4, 6):
        row = [balanced_degree_one(k, q) for k in range(q + 2)]
        coefficients = []
        for _ in range(q + 2):
            coefficients.append(row[0])
            row = [b - a for a, b in zip(row, row[1:])]
        assert coefficients[-1] == 0
        assert Fraction(coefficients[q], factorial(q)) == leading_coefficient(q)
        polys[str(q)] = coefficients[:-1]
    report = {'status': 'all exact checks passed', 'constant_term_checks': checks,
              'degree_duality_checks': duality, 'tables': tables,
              'balanced_polynomial_binomial_coefficients': polys,
              'leading_coefficients': {str(q): str(leading_coefficient(q)) for q in (4, 6, 8, 16)}}
    dest = Path(__file__).resolve().parents[1] / 'data' / 'certificate_verification.json'
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'report': str(dest),
                      'small_polynomials': polys, 'table_rows': len(tables)}, indent=2))


if __name__ == '__main__':
    main()
