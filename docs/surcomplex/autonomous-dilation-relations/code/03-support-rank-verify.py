#!/usr/bin/env python3
"""Exact finite checks for Support Rank and Algebraic Independence of Dilation Orbits.

Python 3.9+ standard library only. Tests are finite consistency checks, not
formal verification of the Hahn-series or proper-class theorems.

Usage: python code/verify.py [--output data/verification_results.json]
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
import random
from fractions import Fraction as F
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

Vec = Tuple[int, ...]
Poly = Dict[Vec, F]


def rank(rows: Sequence[Sequence[F]], p: int = 0) -> int:
    if not rows:
        return 0
    a = [[int(x) % p if p else F(x) for x in row] for row in rows]
    n = len(a[0])
    pivot = 0
    for j in range(n):
        hit = next((i for i in range(pivot, len(a)) if a[i][j]), None)
        if hit is None:
            continue
        a[pivot], a[hit] = a[hit], a[pivot]
        inv = pow(a[pivot][j], -1, p) if p else 1 / a[pivot][j]
        a[pivot] = [(x * inv) % p if p else x * inv for x in a[pivot]]
        for i in range(pivot + 1, len(a)):
            mul = a[i][j]
            a[i] = [(x - mul * y) % p if p else x - mul * y
                    for x, y in zip(a[i], a[pivot])]
        pivot += 1
        if pivot == len(a):
            break
    return pivot


def determinant(rows: Sequence[Sequence[F]], p: int = 0):
    n = len(rows)
    if n == 0:
        return 1
    a = [[int(x) % p if p else F(x) for x in row] for row in rows]
    out = 1 if p else F(1)
    for j in range(n):
        hit = next((i for i in range(j, n) if a[i][j]), None)
        if hit is None:
            return 0 if p else F(0)
        if hit != j:
            a[j], a[hit] = a[hit], a[j]
            out = -out
        v = a[j][j]
        out = out * v % p if p else out * v
        inv = pow(v, -1, p) if p else 1 / v
        for i in range(j + 1, n):
            mul = a[i][j] * inv
            a[i] = [(x - mul * y) % p if p else x - mul * y
                    for x, y in zip(a[i], a[j])]
    return out % p if p else out


def inverse(rows: Sequence[Sequence[F]]) -> List[List[F]]:
    n = len(rows)
    a = [[F(x) for x in row] + [F(i == j) for j in range(n)]
         for i, row in enumerate(rows)]
    for j in range(n):
        hit = next((i for i in range(j, n) if a[i][j]), None)
        if hit is None:
            raise ValueError('Singular matrix')
        a[j], a[hit] = a[hit], a[j]
        v = a[j][j]
        a[j] = [x / v for x in a[j]]
        for i in range(n):
            if i != j:
                mul = a[i][j]
                a[i] = [x - mul * y for x, y in zip(a[i], a[j])]
    return [row[n:] for row in a]


def weight_for(support: Sequence[Vec]) -> Vec:
    r = len(support[0])
    bound = max(abs(x) for a in support for x in a)
    base = 2 * bound + 2
    return tuple(base ** j for j in range(r))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def greedy(support: Sequence[Vec], w: Vec, p: int = 0) -> List[Vec]:
    selected: List[Vec] = []
    for a in sorted(support, key=lambda b: dot(w, b), reverse=True):
        if rank(selected + [a], p) > len(selected):
            selected.append(a)
    return selected


def perm_sign(perm: Sequence[int]) -> int:
    return -1 if sum(perm[i] > perm[j] for i in range(len(perm))
                     for j in range(i + 1, len(perm))) % 2 else 1


def expanded_jacobian(poly: Poly, qs: Sequence[F], values: dict, p: int = 0):
    """Cauchy--Binet expansion with exact coefficients, not sampling."""
    m = len(qs)
    supp = list(poly)
    total = {}
    qprod = math.prod(qs)
    for comb in itertools.combinations(supp, m):
        det = determinant([values[a] for a in comb], p)
        if not det:
            continue
        coeff = qprod * math.prod(poly[a] for a in comb) * det
        for perm in itertools.permutations(range(m)):
            exponent = tuple(sum(qs[j] * comb[perm[j]][i] for j in range(m))
                             for i in range(len(supp[0])))
            value = coeff * perm_sign(perm)
            if p:
                value = int(value) % p
            total[exponent] = total.get(exponent, 0) + value
            if p:
                total[exponent] %= p
    return {a: c for a, c in total.items() if c}


def check_zero_char(poly: Poly, qs: Sequence[F], use_dual: bool = False):
    supp = list(poly)
    r = len(supp[0])
    qs = sorted([F(q) for q in qs], reverse=True)
    if len(set(qs)) != len(qs) or any(q <= 0 for q in qs):
        raise ValueError('Dilations must be distinct and positive')
    w = weight_for(supp)
    assert len({dot(w, a) for a in supp}) == len(supp)
    basis = greedy(supp, w)
    assert len(basis) == r
    m = len(qs)
    if use_dual:
        inv = inverse(basis)
        values = {a: [sum(F(a[j]) * inv[j][i] for j in range(r))
                      for i in range(m)] for a in supp}
        leading_det = F(1)
    else:
        assert m == r
        values = {a: a for a in supp}
        leading_det = determinant(basis)
    b = basis[:m]
    expected_exp = tuple(sum(qs[j] * b[j][i] for j in range(m)) for i in range(r))
    expected_coeff = math.prod(qs) * math.prod(poly[a] for a in b) * leading_det
    expanded = expanded_jacobian(poly, qs, values)
    top_weight = max(dot(w, a) for a in expanded)
    tops = [a for a in expanded if dot(w, a) == top_weight]
    assert tops == [expected_exp], (tops, expected_exp)
    assert expanded[expected_exp] == expected_coeff != 0
    return {
        'dimension': r, 'observations': m, 'support_size': len(supp),
        'weight': list(w), 'greedy_basis': [list(a) for a in b],
        'dilations_descending': [str(q) for q in qs],
        'leading_exponent': [str(x) for x in expected_exp],
        'leading_coefficient': str(expected_coeff),
        'expanded_nonzero_terms': len(expanded), 'dual_derivations': use_dual,
    }


def check_prime(poly: Poly, ns: Sequence[int], p: int):
    supp = list(poly)
    r = len(supp[0])
    ns = sorted(ns, reverse=True)
    assert len(ns) == r and len(set(ns)) == r and all(n % p for n in ns)
    w = weight_for(supp)
    b = greedy(supp, w, p)
    assert len(b) == r
    exp = tuple(sum(ns[j] * b[j][i] for j in range(r)) for i in range(r))
    coef = int(math.prod(ns) * math.prod(poly[a] for a in b)
               * determinant(b, p)) % p
    out = expanded_jacobian(poly, ns, {a: a for a in supp}, p)
    topw = max(dot(w, a) for a in out)
    assert [a for a in out if dot(w, a) == topw] == [exp]
    assert out[exp] == coef != 0
    return len(out)


def poly_mul(a, b, p=0):
    out = {}
    for x, cx in a.items():
        for y, cy in b.items():
            z = tuple(i + j for i, j in zip(x, y))
            out[z] = out.get(z, 0) + cx * cy
            if p:
                out[z] %= p
    return {a: c for a, c in out.items() if c}


def poly_power(a, n, p=0):
    r = len(next(iter(a)))
    out = {(0,) * r: 1}
    while n:
        if n & 1:
            out = poly_mul(out, a, p)
        a = poly_mul(a, a, p)
        n //= 2
    return out


def poly_add(a, b, factor=1):
    out = dict(a)
    for monomial, coefficient in b.items():
        out[monomial] = out.get(monomial, 0) + factor * coefficient
    return {a: c for a, c in out.items() if c}


def rational_jacobian_numerator(numerator, denominator, ns):
    """Clear the common squared denominator in each derivative row."""
    r = len(ns)
    rows = []
    for n in ns:
        p = {tuple(n*x for x in a): c for a, c in numerator.items()}
        q = {tuple(n*x for x in a): c for a, c in denominator.items()}
        row = []
        for i in range(r):
            dp = {a: c*a[i] for a, c in p.items() if a[i]}
            dq = {a: c*a[i] for a, c in q.items() if a[i]}
            row.append(poly_add(poly_mul(q, dp), poly_mul(p, dq), -1))
        rows.append(row)
    out = {}
    for perm in itertools.permutations(range(r)):
        term = {(0,)*r: perm_sign(perm)}
        for i, j in enumerate(perm):
            term = poly_mul(term, rows[i][j])
        out = poly_add(out, term)
    return out


def rational_checks():
    cases = [
        ({(1,0):1, (0,1):1}, {(0,0):1, (1,1):1}, [1,2], 2),
        ({(1,0,0):1, (0,1,0):1, (0,0,1):1},
         {(0,0,0):1, (1,1,1):1}, [1,2,3], 3),
        ({(0,0):1, (1,0):1, (0,1):2, (1,1):3},
         {(0,0):1, (1,0):-1, (0,1):1}, [2,5], 2),
        ({(1,0):1}, {(0,1):1}, [1,2], 1),
    ]
    result = []
    for p, q, ns, expected_rank in cases:
        union = sorted(set(p) | set(q))
        differences = [tuple(x-y for x,y in zip(a,union[0])) for a in union]
        assert rank(differences) == expected_rank
        jac = rational_jacobian_numerator(p, q, ns)
        assert bool(jac) == (expected_rank == len(ns))
        result.append({'ambient_rank': len(ns), 'difference_rank': expected_rank,
                       'dilations': ns, 'cleared_jacobian_terms': len(jac),
                       'expected_nonzero': expected_rank == len(ns)})
    return result


def run():
    rng = random.Random(20260923)
    reports = []
    tests = {'characteristic_zero_full': 0, 'characteristic_zero_partial': 0,
             'positive_characteristic_jacobians': 0, 'frobenius_identities': 0,
             'negative_dilation_counterexamples': 0, 'rank_and_inverse_checks': 0,
             'power_sum_reconstruction': 0, 'rational_function_jacobians': 0}
    for r in range(1, 5):
        count = 24 if r < 4 else 12
        for case in range(count):
            support = {tuple(int(i == j) for i in range(r)) for j in range(r)}
            target = r + rng.randrange(1, 4)
            while len(support) < target:
                support.add(tuple(rng.randrange(-2, 4) for _ in range(r)))
            poly = {a: F(rng.choice([-5, -3, -2, -1, 1, 2, 3, 7]), rng.randrange(1, 4))
                    for a in sorted(support)}
            candidates = [F(n, rng.randrange(1, 4)) for n in range(1, 20)]
            qs = rng.sample(sorted(set(candidates)), r)
            reports.append(check_zero_char(poly, qs))
            tests['characteristic_zero_full'] += 1
            if r > 1:
                m = 1 + case % (r - 1)
                check_zero_char(poly, qs[:m], True)
                tests['characteristic_zero_partial'] += 1
            b = greedy(list(poly), weight_for(list(poly)))
            inv = inverse(b)
            for i in range(r):
                for j in range(r):
                    assert sum(F(b[i][l]) * inv[l][j] for l in range(r)) == (i == j)
                    tests['rank_and_inverse_checks'] += 1
    example = {(1, 0, 0): F(1), (0, 1, 0): F(1), (0, 0, 1): F(1),
               (1, 1, 0): F(1), (0, 1, 1): F(-2), (2, 0, 1): F(3)}
    worked = check_zero_char(example, [F(1), F(2), F(4)])
    tests['characteristic_zero_full'] += 1
    for p in (2, 3, 5, 7):
        for r in (1, 2, 3):
            for case in range(6):
                support = {tuple(int(i == j) for i in range(r)) for j in range(r)}
                while len(support) < r + 2:
                    support.add(tuple(rng.randrange(-2, 4) for _ in range(r)))
                poly = {a: rng.randrange(1, p) for a in sorted(support)}
                candidates = [n for n in range(1, 24) if n % p]
                ns = rng.sample(candidates, r)
                check_prime(poly, ns, p)
                tests['positive_characteristic_jacobians'] += 1
                assert poly_power(poly, p, p) == {
                    tuple(p * x for x in a): c for a, c in poly.items()}
                tests['frobenius_identities'] += 1
    symmetric = {(1, 0): 1, (-1, 0): 1, (0, 1): 1, (0, -1): 1}
    assert {tuple(-x for x in a): c for a, c in symmetric.items()} == symmetric
    assert rank(list(symmetric)) == 2
    tests['negative_dilation_counterexamples'] += 1
    for x, y, z in itertools.product(range(-4, 5), repeat=3):
        p1 = x + y + z
        if not p1:
            continue
        p2 = x*x + y*y + z*z
        p4 = x**4 + y**4 + z**4
        e2 = F(p1*p1 - p2, 2)
        e3 = F(p4 - p1**4 + 4*p1*p1*e2 - 2*e2*e2, 4*p1)
        assert e2 == x*y + x*z + y*z and e3 == x*y*z
        tests['power_sum_reconstruction'] += 1
    rational_report = rational_checks()
    tests['rational_function_jacobians'] = len(rational_report)
    return {
        'title': 'Exact finite verification of dilation-rank certificates',
        'seed': 20260923, 'python_requirement': '3.9 or later; standard library only',
        'status': 'PASS', 'test_groups': tests, 'total_checks': sum(tests.values()),
        'worked_rank_three_certificate': worked,
        'rational_function_cases': rational_report,
        'random_full_certificates': reports,
        'scope': 'Finite determinant expansions, linear algebra, modular boundaries, and identities only. '
                 'No Lean verification; no finite test verifies infinite Hahn summation or a proper-class assertion.'
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'data' / 'verification_results.json')
    args = parser.parse_args()
    report = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: report[k] for k in ('status', 'test_groups', 'total_checks', 'worked_rank_three_certificate')}, indent=2))


if __name__ == '__main__':
    main()
