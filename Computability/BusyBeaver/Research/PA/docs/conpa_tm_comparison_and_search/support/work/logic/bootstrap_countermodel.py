#!/usr/bin/env python3
"""A Boolean countervaluation for deleting the PA196 explosion bootstrap.

This is a countermodel of the numeric proof calculus, not a first-order
structure. Its quantifier operation is constantly True, which preserves the
calculus's generalization rule. The accompanying written proof verifies all
instances; the finite checks below are supplementary implementation checks.
"""
from functools import lru_cache
from itertools import product
from math import isqrt


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    total = (isqrt(8 * n + 1) - 1) // 2
    b = n - total * (total + 1) // 2
    return total - b, b


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
    tag = n % 4
    if tag == 0:
        return not value(a) or value(b)
    if tag == 2:
        return True
    return a == b


def h1(d, h): return I(Ex(d, U(d, h)), h)
def dual_h1(d, h): return I(h, U(d, Ex(d, h)))
def h2(d, a, h): return I(U(d, U(a, h)), U(a, U(d, h)))
def h3(h, d, a): return I(M(h, d), I(E(h, a), M(a, d)))
def h4(h, d, a): return I(E(h, d), I(M(a, h), M(a, d)))
def h5(d, h): return Ex(d, E(h, d))
def h6(d, a, h): return I(U(d, a), I(U(d, I(a, h)), U(d, h)))
def rho8(a, b, c, u): return I(I(I(c, u), a), I(I(a, c), I(b, c)))


def gate(a, b, c):
    delta = I(E(a, b), U(c, E(a, b)))
    vacuity = I(M(a, b), U(c, M(a, b)))
    point = I(c, M(c, b))
    separation = U(b, And(I(M(a, b), point), I(M(c, b), c)))
    q = U(c, I(separation, N(point)))
    return N(I(delta, I(vacuity, q)))


def main():
    assert value(0) and value(1)
    false_formula = M(0, 1)
    assert false_formula == 9 and not value(false_formula)
    assert not value(h1(0, false_formula))
    assert value(dual_h1(0, false_formula))
    for a, b, c in product(range(12), repeat=3):
        assert all(value(f) for f in (
            h2(a, b, c), h3(a, b, c), h4(a, b, c),
            h5(a, b), h6(a, b, c), gate(a, b, c), dual_h1(a, b)))
        for u in range(a + 1):
            assert value(rho8(a, b, c, u))
    print('Countervaluation verified: all tested retained schemas and dual B are true;')
    print('old h1(0,9) is false, while formula 1 is true.')
    print('The accompanying schema argument, not this finite test, proves nonderivability.')


if __name__ == '__main__':
    main()
