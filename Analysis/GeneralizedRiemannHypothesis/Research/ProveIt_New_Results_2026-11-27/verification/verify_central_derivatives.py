#!/usr/bin/env python3
"""Numerical checks of the central-derivative saddle formula.

This is an illustration, not an interval certificate or a proof.  It compares
the stated closed asymptotic with direct, scaled theta integrals at 60 decimal
digits.  The finite theta sum is truncated below a conservative exponential
cutoff; the mathematical proofs do not depend on these calculations.
"""
import json
from pathlib import Path
import mpmath as mp
from sympy import kronecker_symbol

mp.mp.dps = 60


def compute(discriminant, m):
    q = abs(discriminant)
    a = int(discriminant < 0)
    beta = mp.mpf(a) + mp.mpf("0.5")
    c = mp.pi / q
    N = 2 * m
    w = mp.lambertw(mp.mpf(N) / c)
    r = w / 2
    sig = w / (2 * mp.sqrt(N * (1 + w)))
    h0 = N * mp.log(r) + beta * r - c * mp.exp(2 * r)
    cutoff = mp.mpf(180)
    chi = [int(kronecker_symbol(discriminant, n)) for n in range(301)]

    def integrand(t, theta):
        if t <= 0:
            return mp.mpf(0)
        A = c * mp.exp(2 * t)
        h = N * mp.log(t) + beta * t - A
        if h - h0 < -180:
            return mp.mpf(0)
        R = mp.mpf(1)
        if theta:
            nmax = min(300, max(1, int(mp.ceil(mp.sqrt(1 + cutoff / A)))))
            R += mp.fsum(chi[n] * n**a * mp.exp(-A * (n * n - 1))
                         for n in range(2, nmax + 1))
        return mp.exp(h - h0) * R

    stop = max(r + 2, mp.log(2000 * q / mp.pi) / 2)
    points = sorted(set([mp.mpf(0), max(mp.mpf(0), r - 8 * sig),
                         max(mp.mpf(0), r - 3 * sig), r,
                         r + 3 * sig, r + 8 * sig, stop]))
    points = [x for x in points if x <= stop]
    exact_scaled = mp.quad(lambda t: integrand(t, True), points)
    universal_scaled = mp.quad(lambda t: integrand(t, False), points)
    leading_scaled = mp.sqrt(2 * mp.pi) * sig
    return {
        "discriminant": discriminant,
        "conductor": q,
        "parity": a,
        "m": m,
        "W": mp.nstr(w, 20),
        "A_over_asymptotic": mp.nstr(exact_scaled / leading_scaled, 25),
        "A_over_universal_integral": mp.nstr(exact_scaled / universal_scaled, 25),
        "log_A": mp.nstr(mp.log(4 * exact_scaled) + h0, 25),
    }


def main():
    def matrix_range_example(q, m):
        c = mp.pi / q
        T = max(mp.mpf(1), mp.log(mp.mpf(q) / mp.pi) / 2)
        U = mp.e * T
        V = mp.log(mp.mpf(m) / c) / 2 - mp.log(mp.log(m))
        alpha = 1 / (8 * mp.e * T)
        r = int(mp.floor(alpha * m * mp.log(m)))
        assert V > U
        Cq = 4 * q * T * mp.exp(3 * T / 2)
        lhs = 2 * m * mp.log(U / T)
        rhs = (c * mp.exp(2 * V)
               + mp.log(Cq * V / (V * V - U * U))
               + 2 * mp.log(r + 1)
               + 2 * r * mp.log((V + U) / (V - U)))
        assert lhs > rhs
        return {"conductor": q, "m": m, "hankel_degree_r": r,
                "matrix_dimension": r + 1,
                "alpha": mp.nstr(alpha, 20),
                "sufficient_inequality_slack": mp.nstr(lhs - rhs, 25)}

    data = {
        "status": "high_precision_numerical_illustration_not_interval_proof",
        "precision_decimal_digits": mp.mp.dps,
        "normalization": "(q/pi)^((s+a)/2) Gamma((s+a)/2) L(s,chi)",
        "cases": [compute(D, m) for D in (-3, 5, 53)
                  for m in (10, 50, 200)],
        "theta_53_at_1": mp.nstr(mp.fsum(
            int(kronecker_symbol(53, n)) * mp.exp(-mp.pi * n * n / 53)
            for n in range(1, 150)), 30),
        "hankel_range_illustrations_not_interval_certificates": [
            matrix_range_example(3, 10**6),
            matrix_range_example(53, 10**6),
            matrix_range_example(10007, 10**12),
        ],
    }
    out = Path(__file__).with_name("central_derivatives_checks.json")
    out.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
