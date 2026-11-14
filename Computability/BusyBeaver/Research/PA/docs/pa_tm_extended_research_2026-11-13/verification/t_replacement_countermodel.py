#!/usr/bin/env python3
"""Supplementary finite checks of the all-instance T-only countervaluation.

The proof is the accompanying symbolic argument in audit.md. These tests are
not a proof that all numeric instances hold, nor a claim about PA consistency.
"""
from functools import lru_cache
from itertools import product
from math import isqrt


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    k = (isqrt(8 * n + 1) - 1) // 2
    b = n - k * (k + 1) // 2
    return k - b, b


def I(a, b): return 4 * pair(a, b)
def M(a, b): return 4 * pair(a, b) + 1
def U(a, b): return 4 * pair(b, a) + 2
def E(a, b): return 4 * pair(a, b) + 3
def N(a): return I(a, 1)
def Ex(a, b): return N(U(a, N(b)))
def And(a, b): return N(I(a, N(b)))


@lru_cache(None)
def value(n):
    if n == 0:
        return True
    a, b = unpair(n // 4)
    if n % 4 == 0:
        return not value(a) or value(b)
    if n % 4 == 2:
        return value(a)
    return a == b


def original_h1(d, h): return I(Ex(d, U(d, h)), h)
def proposed_t(d, h): return I(U(d, h), h)
def h2(d, a, h): return I(U(d, U(a, h)), U(a, U(d, h)))
def h3(h, d, a): return I(M(h, d), I(E(h, a), M(a, d)))
def h4(h, d, a): return I(E(h, d), I(M(a, h), M(a, d)))
def h5(d, h): return Ex(d, E(h, d))
def h6(d, a, h): return I(U(d, a), I(U(d, I(a, h)), U(d, h)))
def rho8(a, b, c, u): return I(I(I(c, u), a), I(I(a, c), I(b, c)))


def gate(a, b, c):
    delta = I(E(a, b), U(c, E(a, b)))
    vac = I(M(a, b), U(c, M(a, b)))
    point = I(c, M(c, b))
    sep = U(b, And(I(M(a, b), point), I(M(c, b), c)))
    q = U(c, I(sep, N(point)))
    return N(I(delta, I(vac, q)))


def main():
    assert value(0) and value(1)
    bad = M(0, 1)
    assert bad == 9 and not value(bad)
    assert value(proposed_t(0, bad))
    assert not value(original_h1(0, bad))
    assert not value(I(1, bad))
    cases = 0
    for a, b, c in product(range(12), repeat=3):
        for f in (h2(a, b, c), h3(a, b, c), h4(a, b, c),
                  h5(a, b), h6(a, b, c), proposed_t(a, b), gate(a, b, c)):
            assert value(f)
            cases += 1
        for u in range(a + 1):
            assert value(rho8(a, b, c, u))
            cases += 1
    print(f"{cases} finite schema checks pass; original h1(0,9) and 1 -> 9 fail.")


if __name__ == "__main__":
    main()
