#!/usr/bin/env python3
"""Exact finite checks for the positive-ramp mean/pointwise sharpness model.

The mathematical proof is in ../sections/mean_pointwise.tex. These checks validate
derivative constants, moment identities, and a nontrivial discrete realization.
No downloaded or third-party research code is executed.
"""
from fractions import Fraction as Q
from math import sqrt
import json


def pmul(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


def ppow(a, n):
    out = [Q(1)]
    for _ in range(n):
        out = pmul(out, a)
    return out


def integral(a, lo, hi):
    return sum(c * (hi ** (j + 1) - lo ** (j + 1)) / (j + 1)
               for j, c in enumerate(a))


psi = [Q(1), Q(0), Q(-3), Q(0), Q(3), Q(0), Q(-1)]
# The extrema of psi'' are -6 at z=0, 24/5 at z^2=3/5,
# and zero at the support endpoints.  max |psi'|=96/(25 sqrt(5)).
assert Q(24, 5) < 6
assert 96 ** 2 < 4 * 25 ** 2 * 5
assert Q(27, 200) + Q(3, 5) * Q(1, 20) == Q(33, 200) < Q(1, 2)

X, h, L = Q(1000), Q(1, 400), Q(500)
assert L * L == 100 * X * X * h


def psi_prime(z):
    if abs(z) >= 1:
        return Q(0)
    return -6 * z * (1 - z * z) ** 2


def primitive(n):
    """x^2 R'(x); its increments are the coefficient perturbations."""
    n = Q(n)
    return n * n * h / L * psi_prime((n - X) / L)


left, right = int(X - L), int(X + L)
delta = {n: primitive(n + 1) - primitive(n)
         for n in range(left, right)}
assert sum(delta.values()) == 0
coeffs = [1 + d for d in delta.values()]
assert min(coeffs) >= Q(1, 2)
assert max(coeffs) <= Q(3, 2)

delta_c = sum(d / n for n, d in delta.items())
N = int(X)
discrete_bump_at_center = (
    sum(d * (Q(1, n) - Q(1, N)) for n, d in delta.items() if n <= N)
    - delta_c
)

moments = []
for p in (1, 2, 4):
    poly = ppow(psi, p)
    full_moment = integral(poly, Q(-1), Q(1))
    # [2X/3,2X] maps to z in [-2/3,1] within this support.
    local_moment = h ** p * L / X * integral(poly, Q(-2, 3), Q(1))
    cp = Q(2) ** (2 - p) / 9
    # Exact squared form of M >= cp*h^p*sqrt(3h), all sides nonnegative.
    assert local_moment ** 2 >= cp ** 2 * h ** (2 * p) * 3 * h
    alpha = Q(p, 2 * p + 1)  # gamma=1/2
    assert 1 - alpha * (Q(p) + Q(1, 2)) == 1 - Q(p, 2)
    assert 1 - 3 * alpha / 2 <= Q(1, 2)
    moments.append({
        "p": p,
        "integral_psi_power": str(full_moment),
        "sharp_peak_exponent_at_square_root_mean": str(alpha),
        "rightmost_possible_mellin_pole": str(1 - 3 * alpha / 2),
        "local_mass_bound_exact_check": True,
    })

result = {
    "status": "passed",
    "arithmetic": "exact rational, except displayed derivative decimal",
    "max_abs_psi_prime": 96 / (25 * sqrt(5)),
    "max_abs_psi_second": 6,
    "density_deviation_bound": str(Q(33, 200)),
    "discrete_example": {
        "center": str(X), "height": str(h), "half_width": str(L),
        "changed_integer_weights": len(delta),
        "total_weight_change": str(sum(delta.values())),
        "min_coefficient": str(min(coeffs)),
        "max_coefficient": str(max(coeffs)),
        "center_bump_component": float(discrete_bump_at_center),
        "note": "Full centered remainder also includes the known baseline H_N-log(N)-gamma-1/N.",
    },
    "moments": moments,
}
print(json.dumps(result, indent=2))
