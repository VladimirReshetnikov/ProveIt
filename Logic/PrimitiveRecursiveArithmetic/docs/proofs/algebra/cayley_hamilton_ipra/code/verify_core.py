#!/usr/bin/env python3
"""Exact finite corroboration of the accompanying mathematical proofs.

No Cayley--Hamilton, determinant, adjugate, or charpoly library theorem is
called. Determinants are explicit signed permutation sums. SymPy is used
only as an integer multivariate polynomial normalizer in the generic tests.
These computations are NOT an iPRA proof checker and NOT a Lean proof.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import permutations
from math import factorial
from pathlib import Path
import argparse
import json
import random


def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(len(p))
                      for j in range(i + 1, len(p)))


def padd(a, b):
    return tuple((a[i] if i < len(a) else 0) +
                 (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b))))


def pscale(c, a):
    return tuple(c * v for v in a)


def pmul(a, b):
    if not a or not b:
        return ()
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return tuple(c)


def det(a):
    n = len(a)
    out = 0
    for p in permutations(range(n)):
        t = sign(p)
        for i in range(n):
            t *= a[i][p[i]]
        out += t
    return out


def pdet(a):
    n = len(a)
    out = (0,)
    for p in permutations(range(n)):
        t = (sign(p),)
        for i in range(n):
            t = pmul(t, a[i][p[i]])
        out = padd(out, t)
    return out


def minor(a, i, j):
    return [[a[r][c] for c in range(len(a)) if c != j]
            for r in range(len(a)) if r != i]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def zero(n):
    return [[0] * n for _ in range(n)]


def madd(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mscale(c, a):
    return [[c * x for x in row] for row in a]


def mmul(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n))
             for j in range(n)] for i in range(n)]


def mpow(a, k):
    out = identity(len(a))
    for _ in range(k):
        out = mmul(out, a)
    return out


def meval(c, a):
    out = zero(len(a))
    power = identity(len(a))
    for v in c:
        out = madd(out, mscale(v, power))
        power = mmul(power, a)
    return out


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def char_coeffs(a):
    n = len(a)
    pencil = [[(-a[i][j], int(i == j)) for j in range(n)]
              for i in range(n)]
    p = pdet(pencil)
    return tuple(p[i] if i < len(p) else 0 for i in range(n + 1))


def adjugate(a):
    n = len(a)
    return [[(-1) ** (i + j) * det(minor(a, j, i))
             for j in range(n)] for i in range(n)]


def adj_coeffs(a):
    n = len(a)
    pencil = [[(-a[i][j], int(i == j)) for j in range(n)]
              for i in range(n)]
    out = [zero(n) for _ in range(n)]
    for i in range(n):
        for j in range(n):
            p = pscale((-1) ** (i + j), pdet(minor(pencil, j, i)))
            for k in range(n):
                out[k][i][j] = p[k] if k < len(p) else 0
    return out


def remainder(f, p):
    """Fixed-length descending monic division; coefficient equality unneeded."""
    n = len(p) - 1
    assert n >= 1 and p[-1] == 1
    r = list(f) + [0] * max(0, n - len(f))
    for k in range(len(r) - 1, n - 1, -1):
        lead = r[k]
        for j in range(n + 1):
            r[k - n + j] -= lead * p[j]
    return tuple(r[:n])


def allzero(a, normalize=lambda x: x):
    return all(normalize(x) == 0 for row in a for x in row)


def equal(a, b, normalize=lambda x: x):
    return allzero(madd(a, mscale(-1, b)), normalize)


def verify_matrix(a, normalize=lambda x: x, extended=True):
    n = len(a)
    p = char_coeffs(a)
    assert normalize(p[-1] - 1) == 0
    assert normalize(p[0] - (-1) ** n * det(a)) == 0
    assert allzero(meval(p, a), normalize), (n, 'Cayley-Hamilton')
    adj = adjugate(a)
    expected = mscale(det(a), identity(n))
    assert equal(mmul(a, adj), expected, normalize)
    assert equal(mmul(adj, a), expected, normalize)
    if n:
        bs = adj_coeffs(a)
        assert equal(bs[-1], identity(n), normalize)
        assert equal(mscale(-1, mmul(a, bs[0])),
                     mscale(p[0], identity(n)), normalize)
        for j in range(1, n):
            assert equal(madd(bs[j - 1], mscale(-1, mmul(a, bs[j]))),
                         mscale(p[j], identity(n)), normalize)
        assert equal(adj, mscale((-1) ** (n - 1), meval(p[1:], a)), normalize)
        if extended:
            for k in range(2 * n + 4):
                f = (0,) * k + (1,)
                assert equal(mpow(a, k), meval(remainder(f, p), a), normalize)
    return p


def regular_quaternion(q):
    a, b, c, d = q
    return [[a, -b, -c, -d], [b, a, -d, c],
            [c, d, a, -b], [d, -c, b, a]]


def qmul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return (a * e - b * f - c * g - d * h,
            a * f + b * e + c * h - d * g,
            a * g - b * h + c * e + d * f,
            a * h + b * g - c * f + d * e)


def run():
    rng = random.Random(20261115)
    report = {'status': 'finite checks passed; not a universal proof',
              'seed': 20261115, 'integer_matrices': 0,
              'modular_matrix_instances': 0, 'generic_dimensions': [],
              'quaternion_homomorphism_instances': 0}
    cases = [[]]
    for n in range(1, 6):
        cases += [zero(n), identity(n)]
        cases += [[[rng.randrange(-3, 4) for _ in range(n)]
                   for _ in range(n)] for _ in range(9)]
    for a in cases:
        verify_matrix(a)
        report['integer_matrices'] += 1
        if len(a) <= 4:
            for m in (2, 4, 6, 9):
                verify_matrix(a, lambda x, m=m: x % m, extended=False)
                report['modular_matrix_instances'] += 1

    from sympy import symbols, expand
    for n in range(0, 5):
        xs = symbols(f'x0:{n*n}')
        a = [[xs[i * n + j] for j in range(n)] for i in range(n)]
        verify_matrix(a, expand, extended=False)
        report['generic_dimensions'].append(n)

    h = [[1, 2], [3, 4]]
    assert char_coeffs(h) == (-2, -5, 1)
    assert mpow(h, 4) == madd(mscale(145, h), mscale(54, identity(2)))
    hi = mscale(Fraction(1, 2), madd(h, mscale(-5, identity(2))))
    assert mmul(h, hi) == identity(2) == mmul(hi, h)
    assert meval((10, -5, 1), h) == mscale(12, identity(2))
    a, d = [[0, 1], [0, 0]], [[0, 0], [1, 0]]
    assert mmul(a, d) != mmul(d, a)
    assert (2 * 2) % 6 == (5 * 2) % 6 and (5 - 2) % 6 != 0
    for p in (2, 3, 5):
        assert all(trace(mpow(identity(p), k)) % p == 0 for k in range(1, 9))
        assert det(identity(p)) == 1 and det(zero(p)) == 0
    report['counterexamples_checked'] = [
        'permanent does not satisfy Cayley-Hamilton',
        'matrix-coefficient evaluation not multiplicative',
        'zero-divisor eigenvector need not give characteristic root',
        'trace reconstruction obstruction in characteristics 2, 3, 5']

    for _ in range(30):
        x = tuple(rng.randrange(-4, 5) for _ in range(4))
        y = tuple(rng.randrange(-4, 5) for _ in range(4))
        assert mmul(regular_quaternion(x), regular_quaternion(y)) == regular_quaternion(qmul(x, y))
        verify_matrix(regular_quaternion(x), extended=False)
        report['quaternion_homomorphism_instances'] += 1

    t = Fraction(2, 3)
    a = [[1, 2], [0, 3]]
    for k in range(12):
        assert mpow(a, k) == [[1, 3 ** k - 1], [0, 3 ** k]]
    j = [[0, 1], [-1, 0]]
    assert mmul(j, j) == mscale(-1, identity(2))
    # Exact finite exponential tail inequalities, with the manuscript's modulus.
    for u in range(1, 6):
        for s in range(0, 9):
            cut = 2 * u + 2 * u * u + s + 2
            tail = sum((Fraction(u ** k, factorial(k))
                        for k in range(cut, cut + 50)), Fraction(0))
            assert tail <= Fraction(1, 2 ** (s + 1))
    report['analytic_checks'] = 'triangular powers, rotation square, 45 rational finite-tail bounds'
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output, end='')
