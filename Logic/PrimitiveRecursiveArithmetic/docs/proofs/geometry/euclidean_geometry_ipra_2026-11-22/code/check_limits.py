#!/usr/bin/env python3
"""Exact finite diagnostics for the observation chapter.

The checks use rational interval arithmetic and symbolic polynomial
identities. They are not a formal iPRA proof, do not establish analytic
identifications of pi, and never compare against a floating-point pi.
"""

from fractions import Fraction as F
from math import isqrt
import sympy as sp


def sqrt_bounds(x, bits=120):
    """Outward dyadic enclosure, using only integer arithmetic."""
    assert x >= 0
    den = 1 << bits
    m = isqrt((x.numerator * den * den) // x.denominator)
    lo = F(m, den)
    hi = lo if lo * lo == x else F(m + 1, den)
    assert lo * lo <= x <= hi * hi
    return lo, hi


def sqrt_interval(interval):
    lo, hi = interval
    return sqrt_bounds(lo)[0], sqrt_bounds(hi)[1]


def scale_interval(c, interval):
    assert c >= 0
    return c * interval[0], c * interval[1]


def product_interval(a, b):
    assert a[0] >= 0 and b[0] >= 0
    return a[0] * b[0], a[1] * b[1]


def quotient_interval(a, b):
    assert a[0] >= 0 and b[0] > 0
    return a[0] / b[1], a[1] / b[0]


def overlaps(a, b):
    return max(a[0], b[0]) <= min(a[1], b[1])


def sums(m):
    lower = F(sum(i * i for i in range(m)), m ** 3)
    upper = F(sum(i * i for i in range(1, m + 1)), m ** 3)
    return lower, upper


# Universal rational identities underlying the recurrence and error proofs.
a, L, U, m, p, q, S = sp.symbols("a L U m p q S")
expressions = {
    "chord refinement": 2 * (1 - a) - 4 * (1 - a * a) / (2 * (1 + a)),
    "upper perimeter decrease":
        L / a - 2 * L / (1 + a) - L * (1 - a) / (a * (1 + a)),
    "polygon area gap": U / 2 - U * a * a / 2 - U * (4 * (1 - a * a)) / 8,
    "sum-of-squares induction":
        (m + 1) * m * (2 * m + 1) - m * (m - 1) * (2 * m - 1) - 6 * m * m,
    "cone error decomposition":
        q * (S + 1 / m) - p * S - ((q - p) * S + q / m),
    "sphere error decomposition":
        2 * (q * (1 - S) - p * (1 - S - 1 / m))
        - 2 * ((q - p) * (1 - S - 1 / m) + q / m),
}
for name, expression in expressions.items():
    assert sp.cancel(expression) == 0, name


# Reproduce the polygon recursion with rigorous outward rational bounds.
levels = 13
c = [(F(0), F(0))]
for _ in range(levels + 1):
    prev = c[-1]
    c.append(sqrt_interval(((1 + prev[0]) / 2, (1 + prev[1]) / 2)))

rows = []
for k in range(levels):
    ell = sqrt_interval((2 - 2 * c[k][1], 2 - 2 * c[k][0]))
    apothem = c[k + 1]
    perimeter = scale_interval(4 * (1 << k), ell)
    outer = quotient_interval(perimeter, apothem)
    inner_area = scale_interval(F(1, 2), product_interval(perimeter, apothem))
    outer_area = scale_interval(F(1, 2), outer)
    if k == 0:
        # Exact base-case identities proved from the square coordinates.
        outer = (F(8), F(8))
        inner_area = (F(2), F(2))
        outer_area = (F(4), F(4))
    pi_lower, pi_upper = perimeter[0] / 2, outer[1] / 2
    assert 0 < pi_lower <= pi_upper <= 4
    assert outer[1] - perimeter[0] <= F(4, 1 << k)
    assert pi_upper - pi_lower <= F(2, 1 << k)
    assert outer_area[1] - inner_area[0] <= F(2, 1 << k)
    if rows:
        prev = rows[-1]
        assert perimeter[0] > prev["perimeter"][1]
        assert outer[1] < prev["outer"][0]
        assert inner_area[0] >= prev["inner_area"][1]
        assert outer_area[1] < prev["outer_area"][0]
        assert overlaps(inner_area, scale_interval(F(1, 2), prev["perimeter"]))
    sm, spm = sums(1 << k)
    cone_gap = pi_upper * spm - pi_lower * sm
    sphere_gap = 2 * (pi_upper * (1 - sm) - pi_lower * (1 - spm))
    assert cone_gap <= F(6, 1 << k)
    assert sphere_gap <= F(12, 1 << k)
    rows.append({
        "perimeter": perimeter, "outer": outer,
        "inner_area": inner_area, "outer_area": outer_area,
    })


# Integer/rational formulas for all these finite sample sizes.
for mm in range(1, 513):
    lower, upper = sums(mm)
    assert lower == F(1, 3) - F(1, 2 * mm) + F(1, 6 * mm * mm)
    assert upper == F(1, 3) + F(1, 2 * mm) + F(1, 6 * mm * mm)
    assert 0 <= lower <= F(1, 3) <= upper <= 1
    assert upper - lower == F(1, mm)
    lower2, upper2 = sums(2 * mm)
    assert lower2 - lower == F(2 * mm - 1, 8 * mm * mm)
    assert upper - upper2 == F(2 * mm + 1, 8 * mm * mm)

print(f"PASS: {len(expressions)} symbolic identity groups")
print(f"PASS: {levels} polygon levels with outward rational interval checks")
print("PASS: 512 exact quadratic-sum and dyadic-refinement checks")
print("Scope: finite diagnostics; the mathematical iPRA proof and precision schema are in limits.tex.")
