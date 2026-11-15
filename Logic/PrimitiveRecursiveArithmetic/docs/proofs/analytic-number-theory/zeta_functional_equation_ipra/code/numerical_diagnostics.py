#!/usr/bin/env python3
"""Independent numerical diagnostics for the constructive zeta construction.

DIAGNOSTIC, NOT PROOF: these checks use mpmath floating-point arithmetic.
They do not certify intervals, establish primitive-recursive correctness,
produce iPRA proof objects, or replace the manuscript's error estimates.

The constructed numerator uses only a finite theta integral and reciprocal
Gamma.  mpmath.zeta is used solely as an independent comparison value.

Run:
    python3 numerical_diagnostics.py
    python3 numerical_diagnostics.py --dps 100 --output results.json

Dependencies: mpmath; sympy (for exact finite polynomial identity checks).
"""

from __future__ import annotations

import argparse
import json
import math
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import sympy as sp


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).with_name("numerical_diagnostics.json"),
    )
    args = parser.parse_args()
    if args.dps < 40:
        parser.error("Use at least 40 decimal digits.")
    mp.mp.dps = args.dps
    gaussian_terms = max(8, math.isqrt(args.dps) + 2)
    theta_terms = max(24, 2 * math.isqrt(args.dps) + 8)
    tolerance = mp.power(10, -min(50, args.dps - 20))

    def fmt(x):
        return mp.nstr(x, 24)

    def complex_record(z):
        return {"real": fmt(mp.re(z)), "imag": fmt(mp.im(z))}

    def psi(t):
        q = mp.exp(-mp.pi * t)
        return mp.fsum(q ** (n * n) for n in range(1, gaussian_terms + 1))

    @lru_cache(maxsize=None)
    def J(s):
        """Integral_1^infinity psi(t) t^(s/2-1) dt.

        Each of the finitely many Gaussian terms is integrated using the
        upper incomplete Gamma integral.  No zeta values occur here.  The
        first omitted term is already extremely small at t=1; this remains
        a floating-point diagnostic, not a certified truncation claim.
        """
        a = s / 2
        return mp.fsum(
            mp.gammainc(a, mp.pi * n * n, mp.inf)
            / mp.power(mp.pi * n * n, a)
            for n in range(1, gaussian_terms + 1)
        )

    def J_direct(s):
        return mp.quad(
            lambda t: psi(t) * mp.power(t, s / 2 - 1),
            [1, 2, 4, 8, 16, mp.inf],
        )

    @lru_cache(maxsize=None)
    def A(s):
        return 1 + s * (s - 1) * (J(s) + J(1 - s))

    def xi(s):
        return A(s) / 2

    @lru_cache(maxsize=None)
    def Z(s):
        """Entire numerator: zeta(s)=Z(s)/(s-1) meromorphically."""
        return mp.power(mp.pi, s / 2) * mp.rgamma(1 + s / 2) * A(s) / 2

    samples = [
        mp.mpc(0), mp.mpc(1), mp.mpc(2), mp.mpc(-2), mp.mpc(-4),
        mp.mpc(mp.mpf("0.5")),
        mp.mpc(mp.mpf("0.5"), 1),
        mp.mpc(mp.mpf("0.5"), mp.mpf("14.134725")),
        mp.mpc(mp.mpf("0.5"), 30),
        mp.mpc(mp.mpf("2.25"), mp.mpf("3.5")),
        mp.mpc(mp.mpf("-3.25"), mp.mpf("2.5")),
        mp.mpc(1, 1),
    ]
    rows = []
    max_zeta_error = mp.mpf(0)
    max_xi_error = mp.mpf(0)
    max_global_error = mp.mpf(0)
    max_global_scaled = mp.mpf(0)
    for s in samples:
        value = Z(s)
        # At s=1, the numerator is the zeta residue, exactly 1.  Do not
        # evaluate (s-1)*zeta(s), which would produce 0*infinity.
        expected = mp.mpc(1) if s == 1 else (s - 1) * mp.zeta(s)
        zeta_error = abs(value - expected)
        xi_error = abs(xi(s) - xi(1 - s))
        term_left = s * mp.rgamma(1 - s) * value
        term_right = (
            (s - 1) * mp.power(2, s) * mp.power(mp.pi, s - 1)
            * mp.sin(mp.pi * s / 2) * Z(1 - s)
        )
        residual = term_left + term_right
        global_error = abs(residual)
        global_scaled = global_error / (1 + abs(term_left) + abs(term_right))
        max_zeta_error = max(max_zeta_error, zeta_error)
        max_xi_error = max(max_xi_error, xi_error)
        max_global_error = max(max_global_error, global_error)
        max_global_scaled = max(max_global_scaled, global_scaled)
        rows.append({
            "s": complex_record(s),
            "constructed_Z": complex_record(value),
            "reference_Z": complex_record(expected),
            "Z_absolute_error": fmt(zeta_error),
            "xi_symmetry_absolute_error": fmt(xi_error),
            "global_E_absolute_residual": fmt(global_error),
            "global_E_scaled_residual": fmt(global_scaled),
        })

    def theta(t):
        return 1 + 2 * mp.fsum(
            mp.exp(-mp.pi * t * n * n) for n in range(1, theta_terms + 1)
        )

    theta_rows = []
    max_theta_error = mp.mpf(0)
    for t in [mp.mpf(1) / 4, mp.mpf(1) / 2, mp.mpf(1), mp.mpf(2), mp.mpf(4)]:
        error = abs(theta(t) - theta(1 / t) / mp.sqrt(t))
        max_theta_error = max(max_theta_error, error)
        theta_rows.append({"t": fmt(t), "absolute_residual": fmt(error)})

    quadrature_rows = []
    max_quadrature_error = mp.mpf(0)
    for s in [mp.mpc(0), mp.mpc(1), mp.mpc(mp.mpf("2.25"), mp.mpf("3.5"))]:
        error = abs(J(s) - J_direct(s))
        max_quadrature_error = max(max_quadrature_error, error)
        quadrature_rows.append({"s": complex_record(s), "absolute_error": fmt(error)})

    def finite_R(n, z):
        return z * mp.power(n, -z) * mp.fprod(1 + z / k for k in range(1, n + 1))

    finite_rows = []
    max_reflection_error = mp.mpf(0)
    max_duplication_error = mp.mpf(0)
    for n in [1, 2, 3, 7, 16]:
        for z in [mp.mpc(0), mp.mpc(1), mp.mpc(-1) / 2,
                  mp.mpc(mp.mpf(1) / 3, mp.mpf(2) / 5),
                  mp.mpc(-3, 2) / 2]:
            lhs_r = finite_R(n, z) * finite_R(n, 1 - z)
            rhs_r = z * (1 + (1 - z) / n) * mp.fprod(
                1 - z * z / (k * k) for k in range(1, n + 1)
            )
            lhs_d = finite_R(n, z) * finite_R(n, z + mp.mpf("0.5"))
            rhs_d = (
                mp.power(2, 2 * z - 1)
                * (1 + z / (n + mp.mpf("0.5")))
                * finite_R(n, mp.mpf("0.5")) * finite_R(2 * n, 2 * z)
            )
            err_r, err_d = abs(lhs_r - rhs_r), abs(lhs_d - rhs_d)
            max_reflection_error = max(max_reflection_error, err_r)
            max_duplication_error = max(max_duplication_error, err_d)
            finite_rows.append({
                "N": n, "z": complex_record(z),
                "reflection_absolute_error": fmt(err_r),
                "duplication_absolute_error": fmt(err_d),
            })

    # Exact checks: all exponential powers have been combined symbolically
    # beforehand. These are polynomial identities over Q, checked for the
    # listed finite N; they are not a proof for universally quantified N.
    x = sp.Symbol("x")

    def P(n, z):
        return z * sp.prod(1 + z / sp.Integer(k) for k in range(1, n + 1))

    exact_rows = []
    for n in range(1, 9):
        nQ = sp.Integer(n)
        reflection = (
            P(n, x) * P(n, 1 - x) / nQ
            - x * (1 + (1 - x) / nQ)
            * sp.prod(1 - x * x / sp.Integer(k * k) for k in range(1, n + 1))
        )
        duplication = (
            2 * P(n, x) * P(n, x + sp.Rational(1, 2))
            - (1 + x / (nQ + sp.Rational(1, 2)))
            * P(n, sp.Rational(1, 2)) * P(2 * n, 2 * x)
        )
        recurrence = x * P(n, x + 1) - (nQ + x + 1) * P(n, x)
        exact_rows.append({
            "N": n,
            "reflection_polynomial_identity": sp.cancel(reflection) == 0,
            "duplication_polynomial_identity": sp.cancel(duplication) == 0,
            "recurrence_polynomial_identity": sp.cancel(recurrence) == 0,
        })

    numerical_maxima = {
        "Z_vs_zeta_absolute_error": max_zeta_error,
        "xi_symmetry_absolute_error": max_xi_error,
        "global_E_absolute_residual": max_global_error,
        "global_E_scaled_residual": max_global_scaled,
        "theta_absolute_residual": max_theta_error,
        "J_integral_spotcheck_absolute_error": max_quadrature_error,
        "finite_reflection_absolute_error": max_reflection_error,
        "finite_duplication_absolute_error": max_duplication_error,
    }
    exact_ok = all(
        all(value for key, value in row.items() if key != "N")
        for row in exact_rows
    )
    numeric_ok = all(value <= tolerance for value in numerical_maxima.values())
    report = {
        "status": "DIAGNOSTIC, NOT PROOF",
        "limitations": [
            "Floating-point comparisons are not certified interval estimates.",
            "The finite Gaussian truncations here are not the manuscript's certified PR evaluator.",
            "Xi symmetry is built into its defining symmetric integral.",
            "Exact SymPy checks cover N=1,...,8, not universally quantified N.",
            "No iPRA proof object or Lean proof is produced by this script.",
        ],
        "precision_decimal_digits": args.dps,
        "gaussian_terms_for_J": gaussian_terms,
        "theta_terms_per_positive_half": theta_terms,
        "diagnostic_tolerance": fmt(tolerance),
        "all_diagnostics_passed": bool(numeric_ok and exact_ok),
        "maxima": {key: fmt(value) for key, value in numerical_maxima.items()},
        "zeta_samples": rows,
        "theta_samples": theta_rows,
        "direct_integral_spotchecks": quadrature_rows,
        "finite_product_numeric_checks": finite_rows,
        "finite_product_exact_checks": exact_rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "all_diagnostics_passed": report["all_diagnostics_passed"],
        "maxima": report["maxima"],
        "output": str(args.output.resolve()),
    }, indent=2))
    return 0 if report["all_diagnostics_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
