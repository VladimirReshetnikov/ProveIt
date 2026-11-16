#!/usr/bin/env python3
"""Finite regression checks for the explicit cubic-descent formulas.

These checks do not constitute a proof of FLT or a proof inside iPRA.
The proof and the universal identities are in cubic.tex.  This program
helps catch sign, coordinate-convention, and rounding mistakes.
"""

from itertools import product
import json


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def neg(x):
    return (-x[0], -x[1])


def mul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def conj(x):
    return (x[0] - x[1], -x[1])


def norm(x):
    a, b = x
    return a * a - a * b + b * b


def cube(x):
    return mul(mul(x, x), x)


def divrem(alpha, beta):
    a, b = alpha
    c, d = beta
    den = norm(beta)
    if den == 0:
        raise ZeroDivisionError("zero Eisenstein divisor")
    n0, n1 = a * c - a * d + b * d, b * c - a * d
    q = ((2 * n0 + den) // (2 * den), (2 * n1 + den) // (2 * den))
    r = add(alpha, neg(mul(q, beta)))
    return q, r


def divides(beta, alpha):
    a, b = alpha
    c, d = beta
    den = norm(beta)
    if den == 0:
        return alpha == (0, 0)
    return (a * c - a * d + b * d) % den == 0 and (b * c - a * d) % den == 0


def main():
    omega = (0, 1)
    lam = (1, -1)
    units = [(1, 0), (-1, 0), (0, 1), (0, -1), (-1, -1), (1, 1)]
    pairs = list(product(range(-6, 7), repeat=2))
    assert mul(lam, lam) == (0, -3)
    assert conj(lam) == mul(neg(mul(omega, omega)), lam)
    assert [x for x in pairs if norm(x) == 1] == sorted(units)
    counts = {"pair_identities": 0, "multiplicativity_and_division": 0, "unit_table": 0}
    for a, b in pairs:
        gamma = (a, b)
        M = norm(gamma)
        assert mul(gamma, conj(gamma)) == (M, 0)
        assert 2 * M == a * a + b * b + (a - b) ** 2
        assert max(abs(a), abs(b), abs(a - b)) <= 2 * M
        assert divides(lam, gamma) == ((a + b) % 3 == 0)
        assert divides(mul(lam, lam), gamma) == (a % 3 == 0 and b % 3 == 0)
        A = a ** 3 - 3 * a * b ** 2 + b ** 3
        B = 3 * a * b * (a - b)
        assert cube(gamma) == (A, B)
        delta = mul(lam, cube(gamma))
        assert delta == (A + B, 2 * B - A)
        sums = [sum(delta), sum(mul(omega, delta)), sum(mul(mul(omega, omega), delta))]
        assert sums == [3 * B, 3 * (A - B), -3 * A]
        counts["pair_identities"] += 1
        for unit in units:
            x, y = mul(unit, delta)
            if not divides(lam, gamma) and (x + y) % 9 == 0:
                assert unit in [(1, 0), (-1, 0)]
            counts["unit_table"] += 1
        for beta in pairs:
            assert norm(mul(gamma, beta)) == norm(gamma) * norm(beta)
            if beta != (0, 0):
                q, r = divrem(gamma, beta)
                assert add(mul(q, beta), r) == gamma
                assert 4 * norm(r) <= 3 * norm(beta)
                assert norm(r) < norm(beta)
            counts["multiplicativity_and_division"] += 1
    print(json.dumps({"status": "passed", "scope": "finite formula regression only", "checks": counts}, indent=2))


if __name__ == "__main__":
    main()
