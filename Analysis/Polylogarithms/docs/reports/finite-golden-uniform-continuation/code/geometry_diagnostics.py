#!/usr/bin/env python3
"""Numerical diagnostics for the real-weight signed-kernel theorems.

These checks are independent diagnostics, not interval proof certificates.
The accompanying article gives analytic proofs.  In particular, the exact
bound on a truncated power-series tail does not bound floating-point rounding.

Requires Python 3, numpy, scipy, mpmath.  Run from any directory:
    python geometry_diagnostics.py --output ../data/geometry_diagnostics.json
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import beta, gamma


def bernoulli_remainder(v: float) -> float:
    """v/(exp(v)-1)-1 without cancellation at v=0."""
    if v < 0.05:
        v2 = v * v
        return -v / 2 + v2 * (
            1 / 12 + v2 * (-1 / 720 + v2 * (1 / 30240 - v2 / 1209600))
        )
    if v > 700:
        return -1.0
    return v / math.expm1(v) - 1.0


def kernel_stable(a: float, b: float, T: float) -> float:
    """Evaluate k(T) for 0<a,b<1, or the exact a=b=1 example.

    For subunit orders put c(s)=g(s)/s and J=int c.  Then
        I(T) = q_T(1)*J + int c(s)*(q_T(s)-q_T(1)) ds.
    The second integrand is negative on each side of s=1.  This avoids
    cancellation of two terms of order 1/T at the critical line J=0.
    Algebraic endpoint weights are supplied explicitly to QUADPACK.
    """
    if a == 1 and b == 1:
        return -math.log(math.expm1(T))
    if not (0 < a < 1 and 0 < b < 1 and T > 0):
        raise ValueError("diagnostic evaluator expects 0<a,b<1 and T>0")

    r1 = bernoulli_remainder(T)
    q1 = (1 + r1) / T

    def q_difference(s: float) -> float:
        return (bernoulli_remainder(T * s) - r1) / T

    # s=1-y^(1/a) removes the singularity (1-s)^(a-1).
    # The remaining (1-y)^(b-1) is an explicit quadrature weight.
    def low_residual(y: float) -> float:
        if y == 0:
            return 0.0
        if y == 1:
            return -(1 - a) * a ** (-b) * (-r1 / T)
        log_y = math.log(y)
        s = -math.expm1(log_y / a)
        bracket = math.expm1((1 / a - 1) * log_y)
        return (
            bracket
            / a
            * s ** (b - 2)
            * q_difference(s)
            / (1 - y) ** (b - 1)
        )

    low, _ = quad(
        low_residual, 0, 1, weight="alg", wvar=(0, b - 1),
        epsabs=2e-10, epsrel=2e-11, limit=250,
    )

    # s=1/t gives the explicit endpoint weight t^(-b).
    def high_residual(t: float) -> float:
        if t == 0:
            return -q1
        return q_difference(1 / t)

    high, _ = quad(
        high_residual, 0, 1, weight="alg", wvar=(-b, 0),
        epsabs=2e-10, epsrel=2e-11, limit=250,
    )
    J = (a + b - 1) * beta(a, b) / (1 - b)
    I = q1 * J + low + high
    return T ** (a + b - 1) * (
        -1 / gamma(a + b) + I / (gamma(a) * gamma(b))
    )


def kernel_direct_mp(a: str, b: str, T: str) -> mp.mpf:
    """Original combined kernel integral, at 65 decimal digits.

    This independent representation is used only at moderate T, where
    cancellation remains easily resolvable by the chosen precision.
    """
    with mp.workdps(65):
        a0, b0, t0 = map(mp.mpf, (a, b, T))

        def low(s):
            if s == 0:
                return mp.mpf(0)
            return (
                s ** (b0 - 1)
                * (-mp.expm1((a0 - 1) * mp.log1p(-s)))
                / mp.expm1(t0 * s)
            )

        def high(s):
            return s ** (b0 - 1) / mp.expm1(t0 * s)

        I = mp.quad(low, [0, mp.mpf("0.5"), 1]) + mp.quad(
            high, [1, 2, 5, mp.inf]
        )
        return +(t0 ** (a0 + b0 - 1) * (
            -1 / mp.gamma(a0 + b0) + I / (mp.gamma(a0) * mp.gamma(b0))
        ))


def series_tail_bound(R: float, N: int) -> float:
    # m_n <= n for every a,b>0; bound sum_{n>N} n R^n exactly.
    return R ** (N + 1) * ((N + 1) - N * R) / (1 - R) ** 2


def angular_zero(a: float, b: float, R: float) -> dict:
    N = 100
    while series_tail_bound(R, N) > 1e-27:
        N += 100
    n = np.arange(1, N + 1, dtype=float)
    H = np.concatenate(([0.0], np.cumsum(n[:-1] ** (-b))))
    coefficients = H / n ** a * R ** n

    def imaginary(theta):
        return float(np.dot(coefficients, np.sin(n * theta)))

    theta = brentq(
        imaginary, math.acos(R), math.pi / 2, xtol=8e-15, rtol=9e-16
    )
    derivative = float(np.dot(n * coefficients, np.cos(n * theta)))
    assert derivative < 0
    assert math.acos(R) < theta < math.pi / 2
    row = {
        "a": a, "b": b, "R": R, "theta": theta,
        "x": R * math.cos(theta), "angular_derivative": derivative,
        "truncated_imaginary_residual": imaginary(theta),
        "N": N, "analytic_absolute_tail_bound": series_tail_bound(R, N),
    }
    if a == 1 and b == 1:
        expected = math.acos(R / 2)
        row["exact_example_theta"] = expected
        row["exact_example_error"] = abs(theta - expected)
        assert abs(theta - expected) < 5e-13
    return row


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parents[1] / "data/geometry_diagnostics.json",
    )
    args = parser.parse_args()

    direct_checks = []
    for a, b in [("0.4", "0.8"), ("0.5", "0.75"), ("0.5", "0.5")]:
        for T in ["0.25", "1.0", "4.0"]:
            stable = kernel_stable(float(a), float(b), float(T))
            direct = float(kernel_direct_mp(a, b, T))
            error = abs(stable - direct)
            assert error < 3e-8 * max(1, abs(direct))
            direct_checks.append({
                "a": a, "b": b, "T": T,
                "stable_kernel": stable,
                "independent_65_digit_quadrature": direct,
                "absolute_difference": error,
            })

    crossings = []
    for a, b in [(0.4, 0.8), (0.5, 0.75), (0.5005, 0.5), (1, 1)]:
        log_T = brentq(
            lambda t: kernel_stable(a, b, math.exp(t)), -35, 3,
            xtol=2e-12, rtol=2e-12,
        )
        T = math.exp(log_T)
        before, after = kernel_stable(a, b, T / 2), kernel_stable(a, b, 2 * T)
        assert before > 0 > after
        crossings.append({
            "a": a, "b": b, "T_crossing": T, "u_crossing": math.exp(-T),
            "kernel_at_half_T": before, "kernel_at_twice_T": after,
        })

    critical = []
    for a in [0.3, 0.5, 0.8]:
        b = 1 - a
        for T in [1e-4, 0.01, 0.1, 1, 10]:
            value = kernel_stable(a, b, T)
            assert value < -1
            critical.append({"a": a, "b": b, "T": T, "kernel": value})

    arcs = []
    for a, b in [(1, 1), (0.4, 0.8), (0.5, 0.5), (0.5005, 0.5)]:
        branch = [angular_zero(a, b, R) for R in [0.2, 0.5, 0.8, 0.97]]
        assert all(branch[i + 1]["x"] > branch[i]["x"] for i in range(3))
        arcs.extend(branch)

    mp.mp.dps = 60
    cm = []
    for astr in ["0.3", "0.5", "0.8"]:
        a = mp.mpf(astr)
        b = 1 - a
        for xstr in ["0.2", "1", "2", "10"]:
            x = mp.mpf(xstr)
            def deficit(t):
                return 1 / a - t ** (-a) * (mp.zeta(b) - mp.zeta(b, t))
            values = [(-1) ** j * mp.diff(deficit, x, j) for j in range(5)]
            assert all(v > 0 for v in values)
            assert values[0] > 1 / x
            cm.append({
                "a": astr, "x": xstr,
                "signed_derivatives_orders_0_through_4": [mp.nstr(v, 35) for v in values],
                "deficit_minus_1_over_x": mp.nstr(values[0] - 1 / x, 35),
            })

    result = {
        "status": "all diagnostic assertions passed",
        "proof_status": "Analytic theorems are proved in article/geometry.tex. These numerical checks are not interval certificates.",
        "direct_kernel_comparisons": direct_checks,
        "supercritical_density_crossings": crossings,
        "critical_negative_density": critical,
        "zero_arcs": arcs,
        "critical_complete_monotonicity": cm,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "output": str(args.output),
        "kernel_comparisons": len(direct_checks),
        "crossings": len(crossings),
        "critical_samples": len(critical),
        "arc_samples": len(arcs),
        "complete_monotonicity_samples": len(cm),
        "status": result["status"],
    }, indent=2))


if __name__ == "__main__":
    main()
