"""Exact checks for character coefficients of the even-degree extremizer.

Run with Python 3.10+. All arithmetic uses the character product rule for SU(2)
and fractions. The proof for every degree is in the accompanying paper.
"""
from fractions import Fraction
from itertools import product


def multiply(a, b):
    """Convolve two dictionaries of coefficients in the SU(2) character basis."""
    out = {}
    for (i, ai), (j, bj) in product(a.items(), b.items()):
        for r in range(abs(i - j), i + j + 1, 2):
            out[r] = out.get(r, 0) + ai * bj
    return {i: c for i, c in out.items() if c}


def check(k):
    u = Fraction(k + 1, k)
    endpoint_q = {k: 1, k - 1: u}
    endpoint_square = multiply(endpoint_q, endpoint_q)
    r = {}
    for j in range(k):
        r[2 * j] = Fraction(k * (k + 1) - j * (j + 1), k * k)
        r[2 * j + 1] = Fraction((j + 1) ** 2, k * k)
    assert multiply({0: 2, 1: 1}, r) == endpoint_square
    for b in [Fraction(1, k + 1), Fraction(1), 2 * u, 2 * u + Fraction(1, k), 10 * u]:
        t = min(b / 2, u)
        q = {k: 1, k - 1: t}
        p = multiply(q, q)
        if b > 2 * u:
            for j, coeff in r.items():
                p[j] += (b - 2 * u) * coeff
        assert len(p) == 2 * k + 1 and min(p.values()) > 0
        assert p[2 * k] == 1 and p[2 * k - 1] == b
        assert p[0] == 1 - t * t + b * t
        if b <= 2 * u:
            assert all(p[j] == b for j in range(1, 2 * k, 2))


if __name__ == '__main__':
    for k in range(1, 101):
        check(k)
    print('Passed exact quotient and coefficient identities at k=1,...,100.')
    print('Passed 500 rational examples across both regimes and their common endpoint.')
