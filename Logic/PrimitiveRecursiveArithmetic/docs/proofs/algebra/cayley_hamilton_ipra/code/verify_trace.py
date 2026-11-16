#!/usr/bin/env python3
"""Deterministic finite checks for the trace manuscript.

These checks are examples, not a proof of the universal identities or an
iPRA formalization. Only the Python standard library is required.
"""

from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial
from random import Random


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mul(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n))
             for j in range(n)] for i in range(n)]


def tr(a):
    return sum(a[i][i] for i in range(len(a)))


def det(a):
    n = len(a)
    ans = 0
    for p in permutations(range(n)):
        term = (-1) ** sum(p[i] > p[j] for i in range(n)
                          for j in range(i + 1, n))
        for i in range(n):
            term *= a[i][p[i]]
        ans += term
    return ans


def principal(a, k):
    return sum(det([[a[i][j] for j in s] for i in s])
               for s in combinations(range(len(a)), k))


def conv(a, b, n):
    return [sum(a[i] * b[k-i] for i in range(k+1)) for k in range(n+1)]


def check(a):
    n = len(a)
    precision = n + 3
    e = [principal(a, k) for k in range(precision + 1)]
    d = [(-1) ** k * e[k] for k in range(precision + 1)]
    s = [n]
    power = eye(n)
    for k in range(1, precision + 1):
        power = mul(power, a)
        s.append(tr(power))
    bell = [1]
    for k in range(1, precision + 1):
        assert k * e[k] == sum((-1) ** (i-1) * e[k-i] * s[i]
                               for i in range(1, k+1))
        bell.append(sum(comb(k-1, i-1) * (-1) ** (i-1)
                        * factorial(i-1) * s[i] * bell[k-i]
                        for i in range(1, k+1)))
        assert bell[k] == factorial(k) * e[k]
        h = [[s[i-j+1] if j <= i else k-i-1 if j == i+1 else 0
              for j in range(k)] for i in range(k)]
        assert det(h) == factorial(k) * e[k]
    f = eye(n)
    for k in range(1, n+1):
        af = mul(a, f)
        numer = -tr(af)
        assert numer % k == 0
        dk = numer // k
        assert dk == d[k]
        f = [[af[i][j] + dk * int(i == j) for j in range(n)]
             for i in range(n)]
    assert f == [[0] * n for _ in range(n)]
    ell = [Fraction(0)] + [-Fraction(s[j], j)
                           for j in range(1, precision+1)]
    term = [Fraction(1)] + [Fraction(0)] * precision
    exponential = term[:]
    for r in range(1, precision+1):
        term = conv(term, ell, precision)
        exponential = [exponential[k] + term[k] / factorial(r)
                       for k in range(precision+1)]
    assert exponential == d


def main():
    rng = Random(20261115)
    matrices = [[[1, 2], [3, 4]], [[1, 2], [0, 3]], [[0, 1], [-1, 0]]]
    for n in range(5):
        for _ in range(8):
            matrices.append([[rng.randrange(-3, 4) for _ in range(n)]
                             for _ in range(n)])
    for a in matrices:
        check(a)
    for p in (2, 3, 5):
        a = eye(p)
        power = a
        for _ in range(10):
            assert tr(power) % p == 0
            power = mul(power, a)
        assert det(a) % p == 1
    print(f"PASS: {len(matrices)} matrices; Newton, Bell, Hessenberg, "
          "integer Faddeev-LeVerrier, and finite exp-log checked.")
    print("PASS: characteristic 2, 3, and 5 trace obstructions checked.")
    print("These finite checks are not universal proofs or Lean verification.")


if __name__ == "__main__":
    main()
