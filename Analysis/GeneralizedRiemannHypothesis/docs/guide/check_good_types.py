#!/usr/bin/env python3
"""Reproduce the finite-field examples in the chapter on good local types."""

from fractions import Fraction
from itertools import product
from math import gcd


def multiply_mod_quadratic(left, right, a, b, q):
    """Multiply pairs u + vX in F_q[X]/(X^2 + aX + b)."""
    u, v = left
    s, t = right
    return ((u * s - b * v * t) % q,
            (u * t + v * s - a * v * t) % q)


def root_power(exponent, a, b, q):
    value = (1, 0)
    factor = (0, 1)
    while exponent > 0:
        if exponent % 2:
            value = multiply_mod_quadratic(value, factor, a, b, q)
        factor = multiply_mod_quadratic(factor, factor, a, b, q)
        exponent //= 2
    return value


def good_labels():
    q = 5
    group_order = (q**2 - 1) * (q**2 - q)
    weights = {"split": [], "nonprimitive": [], "primitive": []}
    for a, b in product(range(q), repeat=2):
        roots = [x for x in range(q) if (x**2 + a*x + b) % q == 0]
        if any(x in (0, 1, q-1) for x in roots) or len(roots) == 1:
            continue  # A quadratic with just one root over F_5 has a repeated root.
        if roots:
            label, degree = "split", q+1
        else:
            order = next(i for i in range(1, q**2)
                         if root_power(i, a, b, q) == (1, 0))
            label = "primitive" if order == q**2-1 else "nonprimitive"
            degree = q-1
        weights[label].append(Fraction(degree**2, group_order))

    assert [len(group) for group in weights.values()] == [1, 6, 4]
    possible = [(label, weight) for label, group in weights.items()
                for weight in group]
    good_pairs = [wa*wb for (ca, wa), (cb, wb) in product(possible, repeat=2)
                  if "primitive" in (ca, cb)]
    assert len(good_pairs) == 72
    assert sum(good_pairs) == Fraction(41, 450)
    assert root_power(6, 1, 2, q) == (2, 0)
    assert root_power(8, 1, 2, q) == (1, 3)
    print("F_5: allowed split, nonprimitive irreducible, primitive:", 1, 6, 4)
    print("Two factors: 72 good tuples, regular share 41/450.")
    print("X^2+X+2: z^6=2, z^8=1+3z.")


def frobenius_orbits():
    q, rank = 19, 3
    order = q**rank-1
    assert (q**rank-1)//(q-1) == 3*127
    primes_in_order = (2, 3, 127)
    for ell in primes_in_order:
        surviving_order = order
        while surviving_order % ell == 0:
            surviving_order //= ell
        orbit = [pow(q, i, surviving_order) for i in range(rank)]
        assert len(set(orbit)) == rank
    assert gcd(order, q) == 1
    assert len({pow(q, i, order) for i in range(rank)}) == rank
    print("F_19^3: removing any one prime part leaves three Frobenius conjugates.")


if __name__ == "__main__":
    good_labels()
    frobenius_orbits()
