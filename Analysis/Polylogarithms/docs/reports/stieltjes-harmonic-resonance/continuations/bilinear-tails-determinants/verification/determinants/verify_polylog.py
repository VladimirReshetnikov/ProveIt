#!/usr/bin/env python3
"""Exact Taylor coefficients and independent endpoint diagnostics.

Finite determinants are computed directly from their rational weights.
The endpoint check uses direct finite moment sums plus a harmonic
Euler--Maclaurin tail, not the MZV reduction being checked.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import sympy as sp


HERE = Path(__file__).resolve().parent
mp.mp.dps = 65
records = []


@lru_cache(None)
def nested_harmonic(n, indices):
    if not indices:
        return F(1)
    if not n:
        return F(0)
    return nested_harmonic(n - 1, indices) + F(1, n ** indices[0]) * nested_harmonic(n - 1, indices[1:])


def coefficient(indices, n):
    if n <= 0:
        return F(0)
    return F(1, n ** indices[0]) * nested_harmonic(n - 1, indices[1:])


def exact_cutoff(M):
    return sum(
        (k - n) ** 2
        * (F(1, (n + 1) ** 2) - F(1, (n + 2) ** 2))
        * (F(1, (k + 1) ** 2) - F(1, (k + 2) ** 2))
        for k in range(M)
        for n in range(k)
    )


def numerator_coefficient(n):
    li = lambda *indices: coefficient(indices, n)
    old = lambda *indices: coefficient(indices, n - 1)
    return (
        2 * li(1) - li(2) - (1 if n == 1 else 0) - old(4)
        + 2 * (li(1, 2) - li(2, 1) - old(1, 2) + old(2, 1))
        - li(2, 2) - old(2, 2)
    )


def primitive_coefficient(M):
    n = M + 1
    li = lambda *indices: coefficient(indices, n)
    out = lambda *indices: coefficient(indices, M)
    square = sum(coefficient((1,), j) * coefficient((1,), n - j) for j in range(1, n))
    return (
        square + 2 * li(2, 1) - li(1, 2) + li(2, 2) + li(2) - li(1)
        - out(5) - out(1, 4) - 2 * out(3, 2) - 2 * out(1, 2, 2)
    )


assert numerator_coefficient(0) == 0
for M in range(0, 41):
    actual = exact_cutoff(M) if M else F(0)
    generator = sum(numerator_coefficient(n) for n in range(1, M + 2))
    assert generator == actual
    records.append({"name": f"generator coefficient z^{M}", "status": "passed"})
    primitive = primitive_coefficient(M)
    assert primitive == (actual / M if M else F(0))
    records.append({"name": f"Euler primitive coefficient z^{M}", "status": "passed"})
    if M:
        H1 = nested_harmonic(M, (1,))
        H2 = nested_harmonic(M, (2,))
        formula = 2 * (1 - F(1, (M + 1) ** 2)) * H1 - H2**2 - F(M * M, (M + 1) ** 2) * (H2 + 1)
        assert formula == actual
        records.append({"name": f"direct pair sum cutoff M={M}", "status": "passed"})
print(f"Passed {len(records)} exact polylogarithm checks.", flush=True)


def direct_endpoint_head(cutoff):
    moment0 = moment1 = moment2 = mp.mpf(0)
    result = mp.mpf(0)
    for n in range(cutoff - 1):
        weight = mp.mpf(1) / (n + 1) ** 2 - mp.mpf(1) / (n + 2) ** 2
        moment0 += weight
        moment1 += n * weight
        moment2 += n * n * weight
        determinant = moment0 * moment2 - moment1**2
        result += determinant / (n + 1) ** 2
    return result


def asymptotic_endpoint_tail(cutoff, order):
    x, logarithm, gamma, zeta2 = sp.symbols("x L gamma zeta2")
    h1 = logarithm + gamma + x / 2
    h2 = zeta2 - x + x**2 / 2
    for j in range(1, (order + 1) // 2):
        h1 -= sp.bernoulli(2 * j) * x ** (2 * j) / (2 * j)
        h2 -= sp.bernoulli(2 * j) * x ** (2 * j + 1)
    expansion = sp.series(
        x**2 * (2 * (1 - x**2 / (1 + x) ** 2) * h1 - h2**2 - (h2 + 1) / (1 + x) ** 2),
        x, 0, order + 1,
    ).removeO().expand()
    result = mp.mpf(0)
    for k in range(2, order + 1):
        c = expansion.coeff(x, k)
        ca = sp.lambdify((gamma, zeta2), c.subs(logarithm, 0), "mpmath")(mp.euler, mp.zeta(2))
        cb = sp.lambdify((gamma, zeta2), c.diff(logarithm), "mpmath")(mp.euler, mp.zeta(2))
        result += ca * mp.zeta(k, cutoff)
        if cb:
            result -= cb * mp.diff(lambda s: mp.zeta(s, cutoff), k)
    return result


endpoint = (
    1 + 3 * mp.zeta(2) - 2 * mp.zeta(3) - mp.mpf(3) * mp.zeta(4) / 4
    - mp.zeta(3)**2 - mp.mpf(19) * mp.zeta(6) / 24
)
head = direct_endpoint_head(128)
numeric = []
for order, tolerance in [(20, mp.mpf("1e-35")), (24, mp.mpf("1e-40"))]:
    value = head + asymptotic_endpoint_tail(128, order)
    error = abs(value - endpoint)
    if error >= tolerance:
        raise AssertionError(f"endpoint order={order}: error={mp.nstr(error, 12)}")
    numeric.append({
        "name": f"endpoint direct moments plus asymptotic tail order={order}",
        "status": "passed",
        "value": mp.nstr(value, 50),
        "absolute_error": mp.nstr(error, 8),
        "tolerance": mp.nstr(tolerance, 8),
    })
    print(f"Endpoint order={order}: error {mp.nstr(error, 8)}", flush=True)


result = {
    "status": "passed",
    "exact_checks": records,
    "numeric_checks": numeric,
    "working_decimal_precision": mp.mp.dps,
    "endpoint_value": mp.nstr(endpoint, 60),
    "notes": [
        "The 122 exact checks compare nested-sum Taylor coefficients to directly enumerated rational pair sums.",
        "Endpoint tail checks use standard harmonic Euler--Maclaurin expansions and Hurwitz tail summation, not the weight-six MZV reductions.",
        "Numerical comparisons are diagnostics, not certified interval enclosures.",
    ],
}
(HERE / "polylog_results.json").write_text(json.dumps(result, indent=2) + "\n")
