#!/usr/bin/env python3
"""Exact finite diagnostics for the accompanying research manuscript.

This program is not a proof of the infinite Hahn-field or measure results.
Run from any directory. Results are printed; existing data are not overwritten.
Requires Python >= 3.10 and SymPy >= 1.12.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, permutations, product
import json
from math import prod
import platform
import sys
from typing import Sequence

import sympy as sp

Poly = tuple[int, ...]  # Ascending powers of an indeterminate t.


def trim(a: Sequence[int]) -> Poly:
    b = list(a)
    while len(b) > 1 and b[-1] == 0:
        b.pop()
    return tuple(b) if b else (0,)


def add(a: Poly, b: Poly) -> Poly:
    out = [0] * max(len(a), len(b))
    for i, c in enumerate(a):
        out[i] += c
    for i, c in enumerate(b):
        out[i] += c
    return trim(out)


def mul(a: Poly, b: Poly) -> Poly:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def sign_permutation(p: Sequence[int]) -> int:
    inversions = sum(p[i] > p[j] for i in range(len(p))
                     for j in range(i + 1, len(p)))
    return -1 if inversions % 2 else 1


def poly_det(a: Sequence[Sequence[Poly]]) -> Poly:
    n = len(a)
    out = (0,)
    for p in permutations(range(n)):
        term = (sign_permutation(p),)
        for i in range(n):
            term = mul(term, a[i][p[i]])
        out = add(out, term)
    return out


def leading_sign(a: Poly) -> int:
    for c in a:
        if c:
            return 1 if c > 0 else -1
    return 0


def all_principal_nonnegative(a: Sequence[Sequence[Poly]]) -> bool:
    n = len(a)
    for k in range(1, n + 1):
        for subset in combinations(range(n), k):
            sub = [[a[i][j] for j in subset] for i in subset]
            if leading_sign(poly_det(sub)) < 0:
                return False
    return True


def exact_rank(a: Sequence[Sequence[int]]) -> int:
    if not a or not a[0]:
        return 0
    b = [[Fraction(x) for x in row] for row in a]
    nr, nc, pivot_row = len(b), len(b[0]), 0
    for j in range(nc):
        pivot = next((i for i in range(pivot_row, nr) if b[i][j]), None)
        if pivot is None:
            continue
        b[pivot_row], b[pivot] = b[pivot], b[pivot_row]
        scale = b[pivot_row][j]
        b[pivot_row] = [x / scale for x in b[pivot_row]]
        for i in range(pivot_row + 1, nr):
            scale = b[i][j]
            if scale:
                b[i] = [x - scale * y for x, y in zip(b[i], b[pivot_row])]
        pivot_row += 1
        if pivot_row == nr:
            break
    return pivot_row


def criterion(pdiag: Sequence[int], q: Sequence[Sequence[int]]) -> bool:
    """P PSD; C PSD; ker(C) contained in ker(Q|ker(P))."""
    null = [i for i, c in enumerate(pdiag) if c == 0]
    c = [[q[i][j] for j in null] for i in null]
    cp = [[(x,) for x in row] for row in c]
    if not all_principal_nonnegative(cp):
        return False
    q_null = [[q[i][j] for j in null] for i in range(len(pdiag))]
    # C comprises rows of Q|N, so equality of ranks is exactly kernel equality.
    return exact_rank(q_null) == exact_rank(c)


def test_two_scale() -> dict:
    by_dimension = []
    total, positive = 0, 0
    for n in range(1, 4):
        positions = [(i, j) for i in range(n) for j in range(i, n)]
        count, pos = 0, 0
        for pdiag in product((0, 1), repeat=n):
            for entries in product((-1, 0, 1), repeat=len(positions)):
                q = [[0] * n for _ in range(n)]
                for (i, j), value in zip(positions, entries):
                    q[i][j] = q[j][i] = value
                a = [[trim((pdiag[i] if i == j else 0, q[i][j]))
                      for j in range(n)] for i in range(n)]
                actual = all_principal_nonnegative(a)
                expected = criterion(pdiag, q)
                if actual != expected:
                    raise AssertionError({'dimension': n, 'P': pdiag, 'Q': q,
                                          'principal_minors': actual,
                                          'criterion': expected})
                count += 1
                pos += int(actual)
        total += count
        positive += pos
        by_dimension.append({'dimension': n, 'pairs': count, 'positive_pairs': pos})
    assert total == 5946
    return {'status': 'PASS', 'pairs': total, 'positive_pairs': positive,
            'by_dimension': by_dimension}


def test_hidden_matrices() -> dict:
    e = sp.Symbol('epsilon', real=True)
    tested = []
    for r in range(1, 5):
        hs = sp.symbols(f'h1:{r + 1}', real=True)
        h = sp.Matrix(hs)
        a = sp.ones(1, 1).row_join(h.T).col_join(
            h.row_join(h * h.T - e**2 * sp.eye(r)))
        t = sp.eye(r + 1)
        for j, hj in enumerate(hs, start=1):
            t[0, j] = hj
        d = sp.diag(1, *([-e**2] * r))
        assert (a - t.T * d * t).applyfunc(sp.expand) == sp.zeros(r + 1)
        determinant = sp.factor(a.det(method='domain-ge'))
        assert sp.expand(determinant - (-e**2)**r) == 0
        for j in range(r):
            z = sp.zeros(r + 1, 1)
            z[0] = -hs[j]
            z[j + 1] = 1
            assert sp.expand((z.T * a * z)[0] + e**2) == 0
        tested.append({'r': r, 'size': r + 1, 'determinant': str(determinant)})
    return {'status': 'PASS', 'cases': tested}


def test_prime_orbits() -> dict:
    primes = [2, 3, 5, 7, 11, 13]
    rows = []
    for n in range(1, len(primes) + 1):
        chosen = primes[:n]
        degree = prod(chosen)
        exponents = [degree * (p - 1) // p for p in chosen]
        stabilizer = [k for k in range(degree)
                      if all(k * j % degree == 0 for j in exponents)]
        assert stabilizer == [0]
        rows.append({'N': n, 'primes': chosen, 'primorial': degree,
                     'stabilizer_size': len(stabilizer),
                     'orbit_size': degree // len(stabilizer)})
    return {'status': 'PASS', 'cases': rows}


def test_prime_cosets() -> dict:
    primes = list(sp.primerange(2, 98))
    checks = 0
    for m in range(1, 61):
        for p in primes:
            if m % p == 0:
                continue
            qp = Fraction(p - 1, p)
            assert (m * qp).denominator != 1
            checks += 1
            for q in primes:
                if q == p:
                    continue
                qq = Fraction(q - 1, q)
                assert (m * (qp - qq)).denominator != 1
                checks += 1
    return {'status': 'PASS', 'm_range': [1, 60], 'largest_prime': 97,
            'exact_nonmembership_checks': checks}


def test_couplings() -> dict:
    e, c = sp.symbols('epsilon c', real=True)
    bad = sp.Matrix([[1, e], [e, 0]])
    good = sp.Matrix([[1, e], [e, e]])
    repair = sp.Matrix([[1, e], [e, c * e**2]])
    assert sp.expand(bad.det() + e**2) == 0
    assert sp.expand(good.det() - (e - e**2)) == 0
    assert sp.expand(repair.det() - (c - 1) * e**2) == 0
    return {'status': 'PASS', 'bad_determinant': str(bad.det()),
            'good_determinant': str(good.det()),
            'three_scale_determinant': str(sp.factor(repair.det()))}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', action='store_true', help='Print structured JSON only.')
    args = parser.parse_args()
    result = {
        'scope': 'Exact finite diagnostics only; not infinite-theorem verification.',
        'environment': {'python': platform.python_version(), 'sympy': sp.__version__},
        'hidden_matrix_identities': test_hidden_matrices(),
        'prime_character_orbits': test_prime_orbits(),
        'fresh_prime_cosets': test_prime_cosets(),
        'two_scale_exhaustive': test_two_scale(),
        'coupling_examples': test_couplings(),
    }
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(result['scope'])
        print(f"Python {platform.python_version()}; SymPy {sp.__version__}")
        for name, record in result.items():
            if isinstance(record, dict) and record.get('status'):
                print(f"PASS {name}")
        test = result['two_scale_exhaustive']
        print(f"Two-scale comparison: {test['pairs']} pairs, "
              f"{test['positive_pairs']} positive.")
        for row in test['by_dimension']:
            print(f"  Dimension {row['dimension']}: {row['pairs']} pairs, "
                  f"{row['positive_pairs']} positive.")
        print(f"Fresh-prime exact comparisons: "
              f"{result['fresh_prime_cosets']['exact_nonmembership_checks']}")
        print('No numerical approximation to an infinitesimal was used.')


if __name__ == '__main__':
    main()
