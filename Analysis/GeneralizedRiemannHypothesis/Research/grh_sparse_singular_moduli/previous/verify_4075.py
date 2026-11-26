"""Exclude four-term rational relations at discriminant -4075 by interval arithmetic."""

from fractions import Fraction
from itertools import permutations
from math import prod

from cm_intervals import (
    K, ONE, S, SIGMA3, ZERO, add, ceildiv, cmul, div_pos, exp_radius, mul,
    neg, norm_squared, phase, scale,
)

UNIT = (ONE, ZERO)


def cpow(z, exponent):
    result = UNIT
    while exponent:
        if exponent % 2:
            result = cmul(result, z)
        z = cmul(z, z)
        exponent //= 2
    return result


def crecip(z):
    inverse_norm = div_pos(ONE, norm_squared(z))
    return mul(z[0], inverse_norm), mul(neg(z[1]), inverse_norm)


def small_conjugate(b):
    radius = div_pos(ONE, exp_radius(4075, 25))
    cs, sn = phase(25, b)
    q = mul(radius, cs), mul(radius, sn)
    qp, product, e4 = UNIT, UNIT, UNIT
    for n in range(1, K + 1):
        qp = cmul(qp, q)
        product = cmul(product, (add(ONE, neg(qp[0])), neg(qp[1])))
        e4 = tuple(add(u, scale(v, 240 * SIGMA3[n])) for u, v in zip(e4, qp))
    # sigma_3(n) <= 2n^3, |q| < 1/200. Each component error is <= the disk radius.
    tail = ceildiv(960 * S * (K + 1)**3, 200**(K + 1))
    e4 = tuple(add(v, (-tail, tail)) for v in e4)
    value = cmul(cpow(e4, 3), crecip(cmul(q, cpow(product, 24))))
    # |log prod_{n>K}(1-q^n)^(-24)| <= 96 / 200^(K+1).
    # |exp(w)-1| <= 2|w| for |w| <= 1/2.
    error = ceildiv(192 * S, 200**(K + 1))
    return cmul(value, (add(ONE, (-error, error)), (-error, error)))


def lower_abs(interval):
    lo, hi = interval
    return max(lo, -hi, 0)


def permutation_bound(e, p, ratios):
    return prod(ratios[j]**sum(e[p[i]] - e[i] for i in range(j + 1))
                for j in range(3))


def main():
    values = [small_conjugate(b) for b in [25, 15, 5]]
    bounds = [(2365, 2366), (2846, 2847), (3701, 3703)]
    for z, (lo, hi) in zip(values, bounds):
        rlo, rhi = norm_squared(z)
        assert lo**2 * S < rlo and rhi < hi**2 * S
    assert exp_radius(4075, 1)[0] - 2079 * S > 10**80 * S
    ratios = (Fraction(2366, 2846), Fraction(2847, 3701), Fraction(3703, 10**80))
    for e in [(0, 12, 13, 14), (0, 1, 13, 14)]:
        error = sum(permutation_bound(e, p, ratios) for p in permutations(range(4))
                    if p != (0, 1, 2, 3))
        assert error < 1
    # Scale every conjugate by 1/4096. This simply rescales each exponent column.
    scaled = [tuple((v[0]//4096, ceildiv(v[1], 4096)) for v in z) for z in values]
    powers = [[cpow(z, e) for e in range(23)] for z in scaled]
    observed = None
    for g in range(1, 12):
        for h in range(1, 12):
            exponents = (0, g, g + h)
            det = [ZERO, ZERO]
            for p in permutations(range(3)):
                term = UNIT
                for i, j in enumerate(p):
                    term = cmul(term, powers[i][exponents[j]])
                inversions = sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
                det = [add(d, neg(t) if inversions % 2 else t) for d, t in zip(det, term)]
            lower = max(map(lower_abs, det))
            observed = min(observed, lower) if observed is not None else lower
            # After division by the top root to its largest exponent, the other
            # 18 terms cost at most 18*(3703/10^80), as the small scaled diagonal <=1.
            assert lower * 1000 > S
    print("Large gaps: both dominant-permutation bounds < 1.")
    print("Small gaps: 121 complex minor enclosures; minimum certified magnitude exceeds 1e-3.")
    print(f"Minimum certified component lower bound: {observed}/{S}")


if __name__ == "__main__":
    main()
