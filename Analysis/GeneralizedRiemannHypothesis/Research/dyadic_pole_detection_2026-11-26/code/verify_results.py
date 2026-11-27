#!/usr/bin/env python3
"""Reproduce exact identities and numerical checks for dyadic pole detection.

Run:
    python3 code/verify_results.py

Dependencies: Python >=3.10, sympy, mpmath. No network access is used.
The symbolic identities and exact root isolation below are algebraic checks.
The finite grids are sanity checks only, not proofs of global inequalities.
The analytic Landau argument and Jensen argument are proved in the paper.
"""

from __future__ import annotations

import argparse
import cmath
import csv
import json
import math
import platform
from pathlib import Path

import mpmath as mp
import sympy as sp


def bisect_mp(function, left, right):
    """A deterministic monotone/root-bracketing bisection."""
    left, right = mp.mpf(left), mp.mpf(right)
    fl, fr = function(left), function(right)
    if not fl * fr < 0:
        raise ValueError("Root must be strictly bracketed.")
    for _ in range(4 * mp.mp.dps + 40):
        middle = (left + right) / 2
        fm = function(middle)
        if fm == 0:
            return middle
        if fl * fm < 0:
            right, fr = middle, fm
        else:
            left, fl = middle, fm
    return (left + right) / 2


def exact_certificates():
    """Return exact zero identities plus rational positivity certificates."""
    checks = []
    x, u, t, M = sp.symbols("x u t M", real=True)
    alpha, L = sp.symbols("alpha L", real=True)
    d = sp.symbols("d", positive=True)
    w = sp.symbols("w", real=True)

    def zero(name, expression, modulus=None):
        value = sp.factor(sp.expand(expression))
        if modulus is not None:
            value = sp.rem(value, modulus, t)
        value = sp.simplify(value)
        if value != 0:
            raise AssertionError(f"Exact identity failed: {name}: {value}")
        checks.append({"name": name, "result": "exactly_zero"})

    # Exact triple squared-modulus formulas.
    A = 1 + 2*x + u
    B = (u - 1)**2 + 4*x**2
    C = (u**2 - 1)**2 + 4*(2*x**2 - u)**2
    zero("triple_C_in_terms_of_B",
         C - ((u**2 - 1)**2 + (B - 1 - u**2)**2))
    Q = lambda v: 2*v**2 - 2*M*v + M**2 - 3*M + 2
    zero("first_constraint_at_B_equals_M",
         (u - 1)**2 + (1 + u - M)**2 - M - Q(u))
    zero("fourth_power_constraint_at_B_equals_M",
         (u**2 - 1)**2 + (M - 1 - u**2)**2 - M - Q(u**2))
    zero("difference_of_two_feasibility_quadratics",
         Q(u) - Q(u**2) - 2*u*(1-u)*(u+u**2-M))

    quartic = t**4 - 2*t**2 - 3*t + 2
    x0 = (t**2 - 1)/2
    M0 = t + t**2
    weight = 4*t*(1-t**2)
    point = {x: x0, u: t}

    for name, expression in [("A", A), ("B", B), ("C", C)]:
        zero(f"triple_{name}_equals_M0_mod_quartic",
             expression.subs(point) - M0, quartic)
    zero("triple_imaginary_part_squared",
         t - x0**2 - (t+1)/4, quartic)
    zero("triple_quartic_from_interval_contact",
         Q(t).subs(M, t+t**2) - quartic)
    zero("triple_quartic_derivative_negative_on_0_1",
         sp.diff(quartic, t) - (-3 - 4*t*(1-t**2)))

    # Independent convexity certificate for the weighted triple objective.
    P = weight*A + 2*B + C
    zero("weighted_triple_x_stationary_mod_quartic",
         sp.diff(P, x).subs(point), quartic)
    zero("weighted_triple_u_stationary_mod_quartic",
         sp.diff(P, u).subs(point), quartic)
    zero("weighted_triple_value_mod_quartic",
         P.subs(point) - (weight+3)*M0, quartic)

    H = sp.hessian(P, (x, u))
    H_expected = sp.Matrix([
        [192*x**2 - 32*u + 16, -32*x],
        [-32*x, 12*u**2 + 8],
    ])
    for row in range(2):
        for col in range(2):
            zero(f"triple_Hessian_entry_{row}_{col}",
                 H[row, col] - H_expected[row, col])

    H_minus_2I = H - 2*sp.eye(2)
    determinant_certificate = (
        (2304*u**2 + 128)*(x**2-u**2/4)
        + 64*u**2*(3*u-1)**2
        + 136*(u-sp.Rational(12,17))**2
        + sp.Rational(276,17)
    )
    zero("triple_Hessian_minus_2I_determinant_certificate",
         H_minus_2I.det() - determinant_certificate)
    zero("triple_Hessian_minus_2I_first_diagonal_certificate",
         H_minus_2I[0,0] -
         (192*(x**2-u**2/4) + 48*(u-sp.Rational(1,3))**2
          + sp.Rational(26,3)))

    rational_left, rational_right = sp.Rational(1,2), sp.Rational(13,25)
    root_count = int(sp.Poly(quartic, t).count_roots(rational_left, rational_right))
    if root_count != 1:
        raise AssertionError("Triple quartic isolation failed.")
    ql, qr = quartic.subs(t, rational_left), quartic.subs(t, rational_right)
    assert ql > 0 and qr < 0
    checks.append({
        "name": "triple_quartic_exact_root_isolation",
        "interval": ["1/2", "13/25"],
        "count_roots": root_count,
        "left_value": str(ql),
        "right_value": str(qr),
        "uniqueness_on_0_1":
            "q'(t)=-3-4t(1-t^2)<0 for 0<t<1",
    })

    # The angular recurrence is algebraic after its branch condition is proved.
    zero("angular_recurrence_centered_at_pi_over_3",
         sp.pi - 2*(sp.pi/3 + alpha) - (sp.pi/3 - 2*alpha))
    zero("even_length_endpoint_angle_identity",
         L*alpha + ((L+1)*sp.pi/3-L*alpha) - (L+1)*sp.pi/3)
    ell = sp.symbols("ell", real=True)
    zero("weighted_Jensen_barycenter",
         (L*w + (ell-L*w))/(L+1) - ell/(L+1))

    # Here w is the centered logarithmic variable.
    g = sp.acos(sp.sqrt(d)*sp.cosh(w))
    second_derivative = sp.diff(g, w, 2)
    expected_second_derivative = (
        -sp.sqrt(d)*(1-d)*sp.cosh(w)
        / (1-d*sp.cosh(w)**2)**sp.Rational(3,2)
    )
    reduced = sp.simplify(sp.trigsimp(
        second_derivative - expected_second_derivative))
    if reduced != 0:
        raise AssertionError(f"Concavity identity failed: {reduced}")
    checks.append({
        "name": "logarithmic_angle_second_derivative",
        "result": "exactly_zero",
        "derivative":
            "-sqrt(d)*(1-d)*cosh(w)/(1-d*cosh(w)^2)^(3/2)",
        "sign_hypotheses": "0<d<1 and d*cosh(w)^2<1",
    })

    z = sp.symbols("z")
    zero("old_two_filter_Bezout_identity",
         (1+z**2) - (z-1)*(1+z) - 2)

    return {
        "all_checks_passed": True,
        "checks": checks,
        "triple_strong_convexity_domain":
            "D={(x,u):u>=0 and 2x+u<=0}; on D, x^2-u^2/4>=0.",
        "triple_certificate_conclusion":
            "Hessian(P)-2I is positive definite on D by the two displayed "
            "nonnegative decompositions with strictly positive constants. "
            "Taylor integration gives P-P(x0,t)>=(x-x0)^2+(u-t)^2.",
        "analytic_scope":
            "The branch condition for the angle recurrence, Jensen's inequality, "
            "and the Landau transfer are human-readable proofs in the paper, "
            "not assertions certified solely by symbolic computation.",
    }


def nstr(value, digits=65):
    return mp.nstr(value, digits)


def evaluate_max(z, N):
    power = z
    values = []
    for _ in range(N):
        values.append(abs(1+power))
        power *= power
    return max(values), values


def numerical_constants():
    rows = []
    details = []

    for N in (2, 4, 6, 8, 10, 12):
        L = 2**(N-1)
        r = bisect_mp(lambda x: x+x**L-1, "0.5", "0.999999999999")
        M = 1-r+r*r
        c = mp.sqrt(M)
        z = r*mp.exp(2*mp.pi*1j/3)
        peak, values = evaluate_max(z, N)
        tol = mp.mpf(10)**(-(mp.mp.dps-12))
        if abs(peak-c) > tol:
            raise AssertionError(f"Even-N extremizer check failed for N={N}.")
        if abs(r+r**L-1) > tol:
            raise AssertionError("Even-N defining equation failed.")
        rows.append({
            "family": "even_dyadic",
            "N": N,
            "last_exponent": L,
            "radial_minimizer": nstr(r),
            "sharp_constant_squared": nstr(M),
            "sharp_constant": nstr(c),
            "noise_amplification": nstr(1/c),
            "theta_radians": nstr(2*mp.pi/3),
            "theta_degrees": "120",
            "defining_equation": f"r+r^{L}=1",
        })
        details.append({
            "family": "even_dyadic", "N": N, "last_exponent": L,
            "r": nstr(r), "c": nstr(c), "c_squared": nstr(M),
            "endpoint_equation_residual": nstr(r+r**L-1),
            "extremizer_moduli": [nstr(value) for value in values],
            "peak_minus_constant": nstr(peak-c),
            "active_filter_indices": [0, N-1],
        })

    u = bisect_mp(lambda t: t**4-2*t**2-3*t+2, "0.5", "0.52")
    M = u+u*u
    c = mp.sqrt(M)
    z = (u*u-1+1j*mp.sqrt(u+1))/2
    peak, values = evaluate_max(z, 3)
    tol = mp.mpf(10)**(-(mp.mp.dps-12))
    if max(abs(value-c) for value in values) > tol:
        raise AssertionError("Triple all-active extremizer check failed.")
    rows.append({
        "family": "triple",
        "N": 3,
        "last_exponent": 4,
        "radial_minimizer": nstr(mp.sqrt(u)),
        "sharp_constant_squared": nstr(M),
        "sharp_constant": nstr(c),
        "noise_amplification": nstr(1/c),
        "theta_radians": nstr(mp.arg(z)),
        "theta_degrees": nstr(mp.arg(z)*180/mp.pi),
        "defining_equation": "u^4-2u^2-3u+2=0; r=sqrt(u)",
    })
    details.append({
        "family": "triple", "N": 3, "last_exponent": 4,
        "u": nstr(u), "z_real": nstr(mp.re(z)), "z_imag": nstr(mp.im(z)),
        "c": nstr(c), "c_squared": nstr(M),
        "quartic_residual": nstr(u**4-2*u**2-3*u+2),
        "extremizer_moduli": [nstr(value) for value in values],
        "peak_minus_constant": nstr(peak-c),
        "active_filter_indices": [0, 1, 2],
    })
    return rows, details


def deterministic_grid_checks(rows):
    """Binary-float sanity check, with no claim to prove the infimum."""
    results = []
    radial_count, angular_count = 61, 240
    for row in rows:
        N, constant = int(row["N"]), float(row["sharp_constant"])
        best, best_z = math.inf, None
        tested = 0
        for ir in range(radial_count):
            radius = 1.5*ir/(radial_count-1)
            for ia in range(angular_count):
                z = radius*cmath.exp(2j*math.pi*ia/angular_count)
                power, peak = z, 0.0
                for _ in range(N):
                    peak = max(peak, abs(1+power))
                    # A capped point cannot become a minimizing grid point.
                    # This also avoids overflow for large powers and |z|>1.
                    if peak > 2.0:
                        break
                    power *= power
                tested += 1
                if peak < best:
                    best, best_z = peak, z
        if best < constant-1e-11:
            raise AssertionError(f"Grid counterexample candidate for N={N}: {best}")
        results.append({
            "family": row["family"], "N": N, "points": tested,
            "grid": f"{radial_count} radii in [0,1.5] x {angular_count} angles",
            "grid_minimum": best,
            "grid_minimum_minus_exact_constant": best-constant,
            "grid_argmin_real": best_z.real,
            "grid_argmin_imag": best_z.imag,
            "interpretation": "Finite deterministic sanity check; not a global proof.",
        })
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outdir", type=Path,
                        default=Path(__file__).resolve().parents[1]/"data")
    parser.add_argument("--dps", type=int, default=100)
    args = parser.parse_args()
    if args.dps < 40:
        parser.error("--dps must be at least 40")
    mp.mp.dps = args.dps
    args.outdir.mkdir(parents=True, exist_ok=True)

    exact = exact_certificates()
    rows, numerical = numerical_constants()
    grids = deterministic_grid_checks(rows)
    verification = {
        "title": "Dyadic pole detection: exact identities and numerical checks",
        "as_of": "2026-11-26",
        "verification_status": "all implemented checks passed",
        "environment": {
            "python": platform.python_version(),
            "sympy": sp.__version__, "mpmath": mp.__version__,
            "mpmath_decimal_precision": mp.mp.dps,
        },
        "scope": {
            "exact": "Polynomial identities, quartic root isolation, "
                     "Hessian positivity decomposition, and concavity derivative.",
            "numerical": "Defining roots, extremizer substitution, and a finite grid.",
            "not_done": "Full Lean formalization, rebuilding the upstream RH proof, "
                        "or a machine-checked proof of the analytic Landau theorem.",
        },
        "exact_certificates": exact,
        "numerical_constants": numerical,
        "deterministic_grid_sanity_checks": grids,
        "proof_vs_computation":
            "The mathematical proofs are in the paper. Passing a grid check "
            "is not evidence sufficient to establish a global extremal claim.",
    }
    json_path = args.outdir/"verification.json"
    csv_path = args.outdir/"constants.csv"
    json_path.write_text(json.dumps(verification, indent=2)+"\n", encoding="utf-8")
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f"PASS: {len(exact['checks'])} exact checks.")
    print(f"PASS: {len(rows)} extremizer evaluations and {len(grids)} finite grids.")
    print(f"Wrote {json_path}")
    print(f"Wrote {csv_path}")


if __name__ == "__main__":
    main()

