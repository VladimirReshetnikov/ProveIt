"""Verify the low-digit exchange and rational lower bounds in the report.

Python 3.9+, standard library only. All pass/fail decisions are exact.
"""
from fractions import Fraction
from itertools import combinations, product
from math import isqrt, prod

OLD = (0, 1, 3, 4)
CORE_DELETIONS = {1, 3, 4}
PAIR_DELETIONS = {(0, 4), (1, 4), (3, 4), (4, 4), (4, 3)}


def primes_through(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            length = (limit - p * p) // p + 1
            flags[p * p::p] = bytes(length)
    return [p for p, flag in enumerate(flags) if flag]


def free_of_midpoints(points):
    for u, v in combinations(points, 2):
        sums = tuple(a + b for a, b in zip(u, v))
        if all(s % 2 == 0 for s in sums):
            mid = tuple(s // 2 for s in sums)
            if mid in points:
                raise AssertionError((u, mid, v))


def local_exchange(spokes):
    old = set(product(OLD, repeat=spokes + 1))
    deleted = {(a,) + (1,) * spokes for a in CORE_DELETIONS}
    added = {(2,) + (1,) * spokes}
    for i in range(1, spokes + 1):
        for a, b in PAIR_DELETIONS | {(2, 2)}:
            point = [1] * (spokes + 1)
            point[0], point[i] = a, b
            (added if a == 2 else deleted).add(tuple(point))
    assert deleted <= old and old.isdisjoint(added)
    assert len(deleted) == 3 + 5 * spokes and len(added) == 1 + spokes
    return old - deleted | added, old


def weight(point, weights):
    return prod(w ** digit for w, digit in zip(weights, point))


def audit_local_proof():
    # With one new point, all unchanged coordinates in a triple are 1.
    # These are the entire possible active coordinates, including both roles.
    for spokes in (0, 1, 2, 3):
        new, old = local_exchange(spokes)
        free_of_midpoints(new)
        weights = [Fraction(1, p) for p in [2, 3, 5, 7][:spokes + 1]]
        pivot, rest = weights[0], weights[1:]
        coefficient = pivot * (1 + sum(rest)) - (1 + pivot**2 + pivot**3)
        coefficient -= sum(pivot**3 * w**2 +
                           (1/pivot + 1 + pivot**2 + pivot**3) * w**3
                           for w in rest)
        assert (sum(weight(x, weights) for x in new) -
                sum(weight(x, weights) for x in old)) == prod(weights) * coefficient
        print(f'{spokes} spokes: {len(new)} retained vectors; midpoint and weight checks passed')


def integer_example():
    primes = primes_through(50_000)
    assert len(primes) == 5_133 and primes[0] == 2
    spokes = primes[1:]
    scale = 10**15
    lower_first = sum(scale // p for p in spokes)
    upper_second = sum(-(-scale // (p*p)) for p in spokes)
    upper_third = sum(-(-scale // (p**3)) for p in spokes)
    lower = (Fraction(-7, 8) + Fraction(lower_first, 2*scale)
             - Fraction(upper_second + 27*upper_third, 8*scale))
    assert lower == Fraction(543285713107, 160000000000000)
    assert lower > Fraction(3, 1000)
    primorial = prod(primes)
    assert 10**21598 < primorial < 10**21599
    print(f'integer spoke count = {len(spokes)}')
    print(f'outward sum numerators at scale {scale}: {lower_first}, {upper_second}, {upper_third}')
    print(f'normalized gain lower bound = {lower}')
    print('10^21598 < product of the selected primes < 10^21599')
    # Outside Rankin factor > 1/2. Selected normalizations >= 1/50000.
    # The high-digit generating functions are >= 1.
    assert lower * 10**8 > 2 * 50_000
    print('absolute integer natural-density gain > 10^-21607')


def polynomial_example():
    q = 2
    irreducibles = {}
    for d in range(1, 17):
        # q^d = sum_{e|d} e I_q(e).
        rest = sum(e*n for e, n in irreducibles.items() if d % e == 0)
        n, remainder = divmod(q**d - rest, d)
        assert remainder == 0
        irreducibles[d] = n
    spokes = {d: n for d, n in irreducibles.items() if d >= 2}
    moments = [sum(Fraction(n, q**(r*d)) for d, n in spokes.items())
               for r in (1, 2, 3)]
    gain = Fraction(-7, 8) + moments[0]/2 - (moments[1] + 27*moments[2])/8
    degree_sum = 1 + sum(d*n for d, n in spokes.items())
    assert gain == Fraction(405398067839, 70368744177664)
    assert gain > Fraction(1, 200) and degree_sum == 130485
    assert 1 + sum(spokes.values()) == 8799
    print(f'F_2[x]: selected primes 8799; sum of their degrees {degree_sum}')
    print(f'F_2[x]: exact normalized gain = {gain}')


if __name__ == '__main__':
    audit_local_proof()
    integer_example()
    polynomial_example()
