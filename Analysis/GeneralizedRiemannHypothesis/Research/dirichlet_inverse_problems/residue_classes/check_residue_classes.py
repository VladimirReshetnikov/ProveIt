"""Check the trace identity and every missing-subgroup witness in four groups.

The cyclic examples of orders 4 and 6 occur for q=5 and q=7. C2 x C2
and C2 x C4 occur for q=8 and q=16. Only the Python standard library
is required. All identities are tested with exact rational arithmetic.
"""
from fractions import Fraction
from itertools import product
from math import gcd, lcm, prod


def mobius(k):
    value = 1
    p = 2
    while p * p <= k:
        if k % p == 0:
            k //= p
            if k % p == 0:
                return 0
            value = -value
        p += 1
    return -value if k > 1 else value


def phi(k):
    return sum(gcd(j, k) == 1 for j in range(1, k + 1))


def trace_value(character, element, orders):
    # The normalized trace of a primitive d-th root is mu(d)/phi(d).
    phase = sum((Fraction(i * j, d) for i, j, d in
                 zip(character, element, orders)), Fraction())
    d = phase.denominator
    return Fraction(mobius(d), phi(d))


def check(orders):
    group = list(product(*(range(d) for d in orders)))
    identity = group[0]
    generators = {}
    for a in group[1:]:
        order = lcm(*(d // gcd(d, i) for i, d in zip(a, orders)))
        orbit = frozenset(tuple(j * i % d for i, d in zip(a, orders))
                          for j in range(1, order + 1) if gcd(j, order) == 1)
        generators[orbit] = min(orbit)

    weight = {rep: len(orbit) for orbit, rep in generators.items()}
    n = prod(orders)
    assert sum(weight.values()) == n - 1
    for chi in group:
        b = sum(mass * trace_value(chi, rep, orders)
                for rep, mass in weight.items())
        assert b == (n - 1 if chi == identity else -1)

    for orbit in generators:
        multiplicities = {chi: len(orbit) -
                          sum(trace_value(chi, a, orders) for a in orbit)
                          for chi in group}
        assert multiplicities[identity] == 0
        assert all(m >= 0 and m.denominator == 1
                   for m in multiplicities.values())
        for a in group:
            # The multiplicities are invariant under Galois conjugacy, so
            # the Fourier sum is rational and equal to its normalized trace.
            actual = sum(m * trace_value(chi, a, orders)
                         for chi, m in multiplicities.items())
            expected = n * (len(orbit) * (a == identity) - (a in orbit))
            assert actual == expected
    print(f"Orders {orders}, group size {n}, minimum support {len(weight)}: OK")


if __name__ == "__main__":
    for moduli in [(4,), (6,), (2, 2), (2, 4)]:
        check(moduli)
