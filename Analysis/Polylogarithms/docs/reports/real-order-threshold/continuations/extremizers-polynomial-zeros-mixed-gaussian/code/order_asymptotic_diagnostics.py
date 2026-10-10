#!/usr/bin/env python3
"""High-precision diagnostics for the new Euler-order asymptotic constants.

These are numerical diagnostics, not interval certificates. The exact
strict inequalities are independently verified by verify_order_constants.py.
The boundary integral below uses the limiting residual exp(-z)-1+z;
it illustrates the unusually slow inverse-log convergence, not a direct
finite-N evaluation of C_N.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


def log_residual(w):
    """log(exp(-exp(w))-1+exp(w)) with stable endpoint evaluation."""
    z = mp.exp(w)
    if w < -4:
        # r(z)=z^2/2 * sum_{j>=0} 2(-z)^j/(j+2)!.
        term = mp.mpf(1)
        total = term
        for j in range(1, 32):
            term *= -z / (j + 2)
            total += term
        return 2 * w - mp.log(2) + mp.log(total)
    if w > 8:
        return w + mp.log1p(-mp.exp(-w))
    return mp.log(mp.expm1(-z) + z)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--digits", type=int, default=60)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" /
                        "order_asymptotic_diagnostics.json")
    args = parser.parse_args()
    mp.mp.dps = args.digits
    h = mp.log(mp.mpf(3) / 2)
    alpha = 1 / h
    p = alpha * mp.log(2)
    q = mp.log(3) / mp.log(2)
    d0 = alpha * mp.log(q)
    s = mp.mpf("0.5") - alpha
    kappa = mp.mpf("0.5") - alpha + alpha * mp.log(2 * alpha)
    c = (1 - 1 / q) * q ** (-p)
    D = mp.sqrt(alpha / (2 * mp.pi)) * (2 * alpha) ** (-d0) * mp.gamma(s)
    Q = mp.log(2) * h * q ** (-p)
    B = ((d0 - d0 * d0) / (2 * alpha) - 1 / (12 * alpha)
         - (d0 - 1) * mp.digamma(s)
         - alpha / 2 * (mp.polygamma(1, s) + mp.digamma(s) ** 2))
    constants = {
        "alpha": alpha, "p": p, "q": q, "d0": d0,
        "kappa": kappa, "c": c, "D": D, "Q": Q,
        "optimizer_shift_coefficient": D * mp.log(2 * alpha) / Q,
        "inverse_log_relative_coefficient_B": B,
    }
    # The infinite Mellin integral in logarithmic coordinates.
    mellin = mp.quad(lambda w: mp.exp(s * w + log_residual(w)),
                     [-mp.inf, -100, -30, -5, 0, 3, 8, mp.inf])
    gamma_value = mp.gamma(s)
    error = abs(mellin - gamma_value)
    if error > mp.mpf("1e-35"):
        raise AssertionError(f"Mellin identity diagnostic error {error}")
    ratios = []
    for logN in [100, 1000, 10000, 100000, 1000000]:
        L = mp.mpf(logN)
        b = alpha * L + d0
        def integrand(w):
            if w >= L:
                return mp.mpf(0)
            return mp.exp(mp.mpf("0.5") * w +
                          (b - 1) * mp.log1p(-w / L) + log_residual(w))
        # Values above 80 contribute much less than the displayed digits.
        boundary = mp.quad(integrand, [-mp.inf, -100, -30, -5, 0, 3, 8, 40, 80])
        ratios.append({
            "log_N": logN,
            "normalized_boundary_integral_over_Gamma": mp.nstr(boundary / gamma_value, 25),
            "description": "Limiting residual; exact finite-N residual replaced by exp(-z)-1+z",
        })
    result = {
        "status": "numerical diagnostics only",
        "precision_decimal_digits": args.digits,
        "constants": {name: mp.nstr(value, 45) for name, value in constants.items()},
        "mellin_identity_absolute_error": mp.nstr(error, 8),
        "slow_boundary_convergence": ratios,
        "scope": "Not a certified finite-N approximation or maximizer computation.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print("Numerical Mellin identity check passed.")
    print("Large inverse-log coefficient:", mp.nstr(B, 15))
    print(args.output)


if __name__ == "__main__":
    main()
