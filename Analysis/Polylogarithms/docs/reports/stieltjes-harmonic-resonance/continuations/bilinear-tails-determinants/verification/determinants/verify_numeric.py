#!/usr/bin/env python3
"""Independent Mellin-integral diagnostics for the spectral hierarchy.

The integral route sums moment kernels before quadrature and does not use
the finite-endpoint/Hurwitz formula.  Laurent tests compare the continued
full determinant with an independently integrated lower-particle minor.
"""

from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path

import mpmath as mp


mp.mp.dps = 80
HERE = Path(__file__).resolve().parent
records = []


@lru_cache(None)
def euler_numerator(k):
    """P_k(q) with sum n^k q^n=P_k(q)/(1-q)^(k+1)."""
    values = [1]
    for m in range(k):
        nxt = [0] * (len(values) + 1)
        for j, value in enumerate(values):
            # q[(1-q)P'_m+(m+1)P_m].
            if j:
                nxt[j] += j * value
            nxt[j + 1] += (m + 1 - j) * value
        values = nxt
    return tuple(values)


def integral_moment(k, h, s, a):
    coeff = euler_numerator(k)

    def integrand(t):
        if not t:
            return mp.mpf(0)
        q = mp.exp(-t)
        one_minus_q = -mp.expm1(-t)
        numerator = mp.polyval(tuple(reversed(coeff)), q)
        return t ** (s - 1) * mp.exp(-a * t) * one_minus_q ** (h - k - 1) * numerator

    return mp.quad(integrand, [0, 1, mp.inf]) / (mp.factorial(h) * mp.gamma(s))


def b(k, h, a):
    if k < h:
        return mp.mpf(0)
    return mp.fsum((-1) ** j * mp.binomial(h, j) * (-a - j) ** k for j in range(h + 1)) / mp.factorial(h)


def endpoint(k, h, s, a):
    return -mp.fsum(
        (-1) ** j * mp.binomial(h, j) * (ell - j) ** k * (ell + a) ** (-s)
        for j in range(1, h + 1)
        for ell in range(j)
    ) / mp.factorial(h)


def continued_moment(k, h, s, a):
    return endpoint(k, h, s, a) + mp.fsum(
        mp.binomial(k, ell) * b(k - ell, h, a) * mp.zeta(s - ell, a)
        for ell in range(k - h + 1)
    )


def continued_partition(r, rho, s, a):
    h = 2 * r - rho - 1
    moments = [continued_moment(k, h, s, a) for k in range(2 * r - 1)]
    return mp.det(mp.matrix([[moments[i + j] for j in range(r)] for i in range(r)]))


def integral_partition(L, h, s, a):
    if not L:
        return mp.mpf(1)
    moments = [integral_moment(k, h, s, a) for k in range(2 * L - 1)]
    return mp.det(mp.matrix([[moments[i + j] for j in range(L)] for i in range(L)]))


def gamma_product(L, h, a):
    return mp.fprod(
        mp.factorial(j) ** 2 * mp.gamma(a + j) * mp.gamma(h - L + 1 - j)
        / (mp.gamma(h + 1 - j) * mp.gamma(a + h - j))
        for j in range(L)
    )


def record(name, actual, expected, tolerance):
    error = abs(actual - expected) / max(abs(expected), mp.mpf("1e-60"))
    if error >= tolerance:
        raise AssertionError(f"{name}: relative error {mp.nstr(error, 12)}")
    records.append({
        "name": name,
        "status": "passed",
        "value": mp.nstr(expected, 32),
        "relative_error": mp.nstr(error, 8),
        "tolerance": mp.nstr(tolerance, 8),
    })
    print(f"{name}: {mp.nstr(error, 5)}", flush=True)


for r, rho, s, a in [
    (2, 2, mp.mpf("3.2"), mp.mpf("1.3")),
    (3, 2, mp.mpf("3.25"), mp.mpf("0.8")),
    (3, 3, mp.mpc("4.2", "0.25"), mp.mpc("1.1", "0.15")),
    (4, 2, mp.mpf("3.25"), mp.mpf("1.2")),
]:
    h = 2 * r - rho - 1
    expected = integral_partition(r, h, s, a)
    actual = continued_partition(r, rho, s, a)
    record(f"Mellin closure r={r},rho={rho}", actual, expected, mp.mpf("1e-45"))


for L, h, a in [
    (1, 3, mp.mpf("1.3")),
    (2, 5, mp.mpf("0.8")),
    (3, 7, mp.mpf("1.2")),
    (2, 4, mp.mpf(1)),
]:
    record(
        f"Gamma product L={L},h={h}",
        gamma_product(L, h, a),
        integral_partition(L, h, 1, a),
        mp.mpf("1e-50"),
    )


# Fourth-order symmetric extrapolation avoids fitting an unknown residue.
def symmetric_limit(function, step=mp.mpf("1e-6")):
    average = (function(step) + function(-step)) / 2
    half_average = (function(step / 2) + function(-step / 2)) / 2
    return (4 * half_average - average) / 3


for r, rho in [(2, 2), (3, 2), (3, 3), (4, 2)]:
    a = mp.mpf("1.3")
    h = 2 * r - rho - 1
    for m in range(1, rho + 1):
        eta = rho - m + 1
        L = r - eta
        beta = mp.binomial(h + m - 1, m - 1)
        expected = (-1) ** (eta * (eta - 1) // 2) * beta ** eta * integral_partition(L, h, m, a)
        actual = symmetric_limit(lambda t: t**eta * continued_partition(r, rho, m + t, a))
        record(f"leading Laurent r={r},rho={rho},m={m}", actual, expected, mp.mpf("1e-18"))


a = mp.mpf("1.3")
c = 1 / a - 2
g0 = -mp.digamma(a)
g1 = mp.stieltjes(1, a)
fp1 = 2 * g1 - g0**2 + c * (g0 - mp.log(a) + 1)
actual1 = symmetric_limit(lambda t: continued_partition(2, 2, 1 + t, a) + 1 / t**2 - (c - 2 * g0) / t)
record("r2 Stieltjes finite part at 1", actual1, fp1, mp.mpf("1e-18"))
z2 = mp.zeta(2, a)
fp2 = 2 / a**2 * (g0 - mp.log(a)) + (1 - 2 * a) / a**2 * z2 - z2**2
actual2 = symmetric_limit(lambda t: continued_partition(2, 2, 2 + t, a) - 2 / (a**2 * t))
record("r2 polygamma finite part at 2", actual2, fp2, mp.mpf("1e-18"))


result = {
    "status": "passed",
    "mpmath_version": mp.__version__,
    "working_decimal_precision": mp.mp.dps,
    "checks": records,
    "scope": "Independent numerical diagnostics, not certified error bounds or formal proofs.",
}
(HERE / "numeric_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(f"Passed {len(records)} numerical checks.")
