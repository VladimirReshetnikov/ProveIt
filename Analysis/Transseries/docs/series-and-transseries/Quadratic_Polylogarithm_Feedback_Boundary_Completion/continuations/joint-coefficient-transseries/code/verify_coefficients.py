#!/usr/bin/env python3
"""Independent diagnostics for joint quadratic-polylogarithm coefficients.

The coefficient is obtained by finite positive recurrences, independently of
the asymptotic formula.  Selected cases are repeated with arbitrary precision.
Fraction arithmetic checks the original implicit equation against the
Lagrange coefficient identity.  Fourier quadrature checks selected order
derivatives of the parabolic-cylinder representation used in the expansion.

Floating-point results are diagnostics, not interval certificates.

Dependencies: Python >=3.10, mpmath >=1.3, numpy >=1.24.
Default run: python code/verify_coefficients.py

The recurrence method was inspected in the pinned ProveIt source
Analysis/Transseries/docs/series-and-transseries/
Quadratic_Polylogarithm_Feedback_Boundary_Completion/code/feedback_verify.py,
commit 8f5afd4d7565df808359f6a0c22f87f79a119bb9.  This file is standalone and
does not import, alter, or rerun a changing repository checkout.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import json
from pathlib import Path
import platform
import time

import mpmath as mp
import numpy as np


LD = np.longdouble
SNAPSHOT = "8f5afd4d7565df808359f6a0c22f87f79a119bb9"


def text_number(x, digits=35):
    if isinstance(x, np.generic):
        return np.format_float_scientific(x, precision=digits, unique=False)
    return mp.nstr(x, digits)


def ld_number(x):
    return LD(mp.nstr(x, 42))


def mp_from_ld(x):
    return mp.mpf(np.format_float_scientific(x, precision=28, unique=False))


def fraction_exp(coefficients, multiplier, degree):
    result = [Fraction(0)] * (degree + 1)
    result[0] = Fraction(1)
    for k in range(1, degree + 1):
        result[k] = multiplier * sum(
            (j * coefficients[j] * result[k-j] for j in range(1, k+1)),
            Fraction(0),
        ) / k
    return result


def exact_identity_check(degree=8):
    """Use the original equation and, separately, two-stage inversion."""
    u = Fraction(4)
    s = 3
    original = [Fraction(0)] * (degree + 1)
    inner = [Fraction(0)] * (degree + 1)
    lagrange = [Fraction(0)] * (degree + 1)
    for n in range(1, degree + 1):
        original_rhs = sum(
            (original[j] * original[n-j] for j in range(1, n)),
            Fraction(0),
        ) / 2
        for m in range(1, n+1):
            original_rhs += fraction_exp(original, Fraction(m), n-m)[n-m] / m**s
        original[n] = original_rhs / u
        inner[n] = (
            Fraction(1, n**s)
            + sum((inner[j] * inner[n-j] for j in range(1, n)), Fraction(0)) / 2
        ) / u
        lagrange[n] = fraction_exp(inner, Fraction(n), n)[n] / n
    assert original == lagrange
    assert all(x > 0 for x in original[1:])
    return {
        "s": s,
        "u": str(u),
        "degree": degree,
        "original_equation_equals_lagrange_exactly": True,
        "coefficients": [str(x) for x in original[1:]],
    }


class Parameters:
    """Order-dependent constants, with the pole paired before evaluation."""

    def __init__(self, n, lam):
        self.n = n
        self.lam = mp.mpf(lam)
        self.eps = 2 * self.lam / mp.log(n)
        self.s = 3 + self.eps
        self.A = mp.zeta(2 + self.eps)
        self.zeta_s = mp.zeta(self.s)
        if self.eps:
            self.log_e2 = (
                mp.loggamma(1-self.eps)
                - mp.log1p(self.eps)
                - mp.log1p(self.eps/2)
            )
            self.zeta_regular = mp.zeta(1+self.eps) - 1/self.eps
        else:
            self.log_e2 = mp.mpf(0)
            self.zeta_regular = mp.euler

    def V(self, H, b):
        nu = (self.A/b)**2
        if self.eps == 0:
            return H + mp.mpf("1.5") + nu
        return (
            self.zeta_regular
            - mp.expm1(self.log_e2-self.eps*H)/self.eps
            + nu
        )

    def e2_scaled(self, H):
        return mp.exp(self.log_e2-self.eps*H)

    def solve_scale(self, b):
        phi = -mp.expm1(-self.lam)/self.lam if self.lam else mp.mpf(1)
        start = mp.log(self.n * mp.log(self.n) * phi / (2*b)) / 2
        equation = lambda H: b * mp.exp(2*H) / self.n - self.V(H, b)
        derivative = lambda H: (
            2*b*mp.exp(2*H)/self.n - self.e2_scaled(H)
        )
        H = mp.findroot(equation, start, df=derivative,
                        solver="newton", tol=mp.mpf("1e-65"), maxsteps=60)
        assert H > 0
        return mp.exp(H)

    def solve_coordinate(self, xi):
        """Select the nearby critical branch by solving both equations."""
        xi = mp.mpf(xi)
        critical_scale = self.solve_scale(self.A)
        if xi == 0:
            b, B = self.A, critical_scale
        else:
            initial_b = self.A / (1-xi*critical_scale/self.n)
            def equations(H, K):
                trial_b, trial_B = mp.exp(K), mp.exp(H)
                return (
                    trial_b * trial_B**2/self.n - self.V(H, trial_b),
                    self.n*(1-self.A/trial_b) - xi*trial_B,
                )
            H, K = mp.findroot(
                equations, (mp.log(critical_scale), mp.log(initial_b)),
                tol=mp.mpf("1e-65"), maxsteps=60,
            )
            b, B = mp.exp(K), mp.exp(H)
        assert self.A/2 < b < 2*self.A
        H = mp.log(B)
        scale_residual = (b*B**2/self.n - self.V(H, b)) / self.V(H, b)
        xi_residual = self.n*(1-self.A/b)/B-xi
        assert abs(scale_residual) < mp.mpf("1e-55")
        assert abs(xi_residual) < mp.mpf("1e-55")
        q = self.e2_scaled(H)/self.V(H, b)
        u = mp.sqrt(b*b + 2*self.zeta_s)
        return {
            "n": self.n, "lambda": self.lam, "epsilon": self.eps,
            "s": self.s, "A": self.A, "xi": xi, "b": b, "u": u,
            "B": B, "q": q, "V": self.V(H, b), "vc": u-b,
            "Rb": mp.exp(b-u), "scale_residual": scale_residual,
            "coordinate_residual": xi_residual,
        }


def coefficient_ld(case):
    """Return Rb**n * a_n using only finite positive sums."""
    n = case["n"]
    u = ld_number(case["u"])
    ss = ld_number(case["s"])
    f = np.zeros(n+1, dtype=LD)
    powers = np.arange(1, n+1, dtype=LD)**(-ss)
    for k in range(1, n+1):
        f[k] = (
            powers[k-1] + LD("0.5") * np.dot(f[1:k], f[k-1:0:-1])
        ) / u
    assert np.all(f[1:] > 0)
    weighted = np.arange(n+1, dtype=LD) * f
    probability = np.zeros(n+1, dtype=LD)
    probability[0] = np.exp(-LD(n)*ld_number(case["vc"]))
    used_rescaling = bool(probability[0] == 0)
    if used_rescaling:
        probability[0] = LD(1)
        log_scale = LD(0)
        log_step = LD(100)*np.log(LD(10))
        for k in range(1, n+1):
            probability[k] = LD(n)/LD(k)*np.dot(
                weighted[1:k+1], probability[k-1::-1])
            if probability[k] > LD("1e100"):
                probability[:k+1] *= LD("1e-100")
                log_scale += log_step
        final = np.exp(
            np.log(probability[n])+log_scale-LD(n)*ld_number(case["vc"])
        ) / LD(n)
    else:
        for k in range(1, n+1):
            probability[k] = LD(n)/LD(k)*np.dot(
                weighted[1:k+1], probability[k-1::-1])
        final = probability[n]/LD(n)
    assert final > 0 and np.isfinite(final)
    return final, used_rescaling


def coefficient_mp(case, digits=75):
    """Repeat the finite recurrences using arbitrary-precision arithmetic."""
    with mp.workdps(digits):
        n, s, u = case["n"], case["s"], case["u"]
        inner = [mp.mpf(0)] * (n+1)
        for k in range(1, n+1):
            inner[k] = (
                mp.mpf(k)**(-s)
                + mp.fsum(inner[j]*inner[k-j] for j in range(1, k))/2
            ) / u
        probability = [mp.mpf(0)] * (n+1)
        probability[0] = mp.exp(-n*case["vc"])
        for k in range(1, n+1):
            probability[k] = mp.mpf(n)/k * mp.fsum(
                j*inner[j]*probability[k-j] for j in range(1, k+1)
            )
        return +probability[n]/n


def gaussian_order(alpha, xi):
    """Evaluate e**(-xi**2/4)*D_alpha(-xi)/sqrt(2*pi).

    This convergent Kummer/reciprocal-Gamma representation avoids mpmath's
    internal 2F0 branch, which can fail when pcfd is differentiated at an
    integer order.  Reciprocal Gamma is entire at its displayed zeros.
    """
    if mp.im(alpha) == 0 and mp.re(alpha) >= 0 and mp.isint(mp.re(alpha)):
        degree = int(mp.re(alpha))
        previous = mp.exp(-xi*xi/2)/mp.sqrt(2*mp.pi)
        if degree == 0:
            return previous
        current = -xi*previous
        for index in range(1, degree):
            previous, current = current, -xi*current-index*previous
        return current
    argument = -xi*xi/2
    return (
        mp.power(2, (alpha-1)/2)*mp.rgamma((1-alpha)/2)
        * mp.hyp1f1((alpha+1)/2, mp.mpf("0.5"), argument)
        + mp.power(2, alpha/2)*xi*mp.rgamma(-alpha/2)
        * mp.hyp1f1((alpha+2)/2, mp.mpf("1.5"), argument)
    )


def h_derivative(alpha, order, xi):
    # A Cauchy-circle derivative avoids both infinitesimal-order evaluations
    # and exact zeros of individual Kummer terms at integer alpha, xi=+/-1.
    value = mp.diff(lambda a: gaussian_order(a, xi), mp.mpf(alpha), order,
                    method="quad", radius=mp.mpf("0.125"))
    assert abs(mp.im(value)) < mp.mpf("1e-60")
    return mp.re(value)


def derivative_tables(coordinates, max_order):
    return {
        xi: {
            (j, k): h_derivative(2*k, j, mp.mpf(xi))
            for j in range(1, max_order+1) for k in range(1, j+1)
        }
        for xi in coordinates
    }


def fourier_derivative(alpha, order, xi):
    def integrand(y):
        if y == 0:
            return mp.mpf(0)
        z = mp.log(y)-mp.pi*1j/2
        return mp.re(mp.exp(-y*y/2-1j*xi*y+alpha*z)*z**order)
    return mp.quad(integrand, [0, 1, 2, 4, 8, 16, mp.inf]) / mp.pi


def h_identity_checks(tables):
    checked = []
    for xi, alpha, order in [(-1, 2, 1), (1, 4, 2), (0, 6, 3)]:
        special = tables[xi][(order, alpha//2)]
        quadrature = fourier_derivative(alpha, order, mp.mpf(xi))
        absolute_difference = abs(special-quadrature)
        assert absolute_difference < mp.mpf("1e-55")
        checked.append({
            "xi": xi, "alpha": alpha, "order_derivative": order,
            "parabolic_cylinder": text_number(special, 65),
            "direct_fourier_quadrature": text_number(quadrature, 65),
            "absolute_difference": text_number(absolute_difference),
        })
    for xi in [-1, 0, 1]:
        gaussian = mp.exp(-mp.mpf(xi)**2/2)/mp.sqrt(2*mp.pi)
        assert abs(gaussian_order(0, mp.mpf(xi))-gaussian) < mp.mpf("1e-65")
        assert abs(gaussian_order(2, mp.mpf(xi))-(xi*xi-1)*gaussian) < mp.mpf("1e-65")
        for alpha in [mp.mpf("0.5"), mp.mpf("1.3")]:
            cylinder = mp.exp(-mp.mpf(xi)**2/4)*mp.pcfd(alpha, -xi)/mp.sqrt(2*mp.pi)
            assert abs(gaussian_order(alpha, mp.mpf(xi))-cylinder) < mp.mpf("1e-65")
    return checked


def stirling_second(n, k):
    row = [1]
    for degree in range(1, n+1):
        previous = row
        row = [0] * (degree+1)
        for j in range(1, degree+1):
            row[j] = previous[j-1] + (j*previous[j] if j < len(previous) else 0)
    return row[k]


def approximations(case, table, max_order=3):
    q, eps, xi = case["q"], case["epsilon"], case["xi"]
    result = [gaussian_order(0, xi)]
    increments = []
    for j in range(1, max_order+1):
        increment = mp.fsum(
            stirling_second(j, k) * (-q/2)**k * eps**(j-k) * table[(j, k)]
            for k in range(1, j+1)
        ) / mp.factorial(j)
        increments.append(increment)
        result.append(result[-1] + increment)
    return result, increments


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--indices", default="128,512,2048,4096")
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent.parent/"data")
    parser.add_argument("--digits", type=int, default=75)
    args = parser.parse_args()
    if args.digits < 70:
        parser.error("at least 70 working digits are required for the check tolerances")
    indices = sorted(set(int(x) for x in args.indices.split(",")))
    if not indices or min(indices) < 128:
        parser.error("indices must be comma-separated integers at least 128")
    mp.mp.dps = args.digits
    started = time.perf_counter()
    exact = exact_identity_check()
    coordinates = [-1, 0, 1]
    tables = derivative_tables(coordinates, 3)
    h_checks = h_identity_checks(tables)
    rows, checks, csv_rows = [], [], []
    check_keys = {(128, -1, -1), (128, 0, 0), (128, 1, 1), (512, -1, 0)}
    for n in indices:
        for lam in [-1, 0, 1]:
            parameters = Parameters(n, lam)
            for xi in coordinates:
                case = parameters.solve_coordinate(xi)
                actual_ld, rescaled = coefficient_ld(case)
                actual = mp_from_ld(actual_ld)
                profile = n*case["B"]*actual
                predictions, increments = approximations(case, tables[xi])
                errors = [p-profile for p in predictions]
                relative = [e/profile for e in errors]
                row = {
                    k: text_number(v, 45) if isinstance(v, mp.mpf) else v
                    for k, v in case.items()
                }
                row.update({
                    "Rb_power_n_times_coefficient": text_number(actual_ld, 22),
                    "actual_normalized_profile_n_B_Rb_n_a_n": text_number(profile, 24),
                    "recurrence_dynamic_rescaling": rescaled,
                    "approximations_through_orders_0_1_2_3": [text_number(p, 30) for p in predictions],
                    "correction_increments_1_2_3": [text_number(p, 30) for p in increments],
                    "signed_errors_approximation_minus_actual": [text_number(e, 25) for e in errors],
                    "relative_errors_over_actual": [text_number(e, 25) for e in relative],
                    "absolute_errors": [text_number(abs(e), 25) for e in errors],
                })
                rows.append(row)
                csv_row = {"n": n, "lambda": lam, "xi": xi,
                           "epsilon": row["epsilon"], "b": row["b"],
                           "B": row["B"], "q": row["q"],
                           "actual_profile": row["actual_normalized_profile_n_B_Rb_n_a_n"]}
                for order in range(4):
                    csv_row[f"approximation_order_{order}"] = text_number(predictions[order], 25)
                    csv_row[f"relative_error_order_{order}"] = text_number(relative[order], 25)
                csv_rows.append(csv_row)
                if (n, lam, xi) in check_keys:
                    reference = coefficient_mp(case, args.digits)
                    reference_lower = coefficient_mp(case, 60)
                    relative_precision_difference = reference_lower/reference-1
                    relative_recurrence_difference = actual/reference-1
                    tolerance = (mp.mpf("5e-14") if np.finfo(LD).precision >= 18
                                 else mp.mpf("5e-11"))
                    assert abs(relative_recurrence_difference) < tolerance
                    assert abs(relative_precision_difference) < mp.mpf("1e-52")
                    checks.append({
                        "n": n, "lambda": lam, "xi": xi,
                        "reference_digits": args.digits,
                        "comparison_digits": 60,
                        "reference_scaled_coefficient": text_number(reference, 65),
                        "longdouble_scaled_coefficient": text_number(actual_ld, 24),
                        "longdouble_relative_difference": text_number(relative_recurrence_difference),
                        "sixty_digit_relative_difference": text_number(relative_precision_difference),
                        "longdouble_acceptance_tolerance": text_number(tolerance),
                    })
                print(
                    f"n={n}, lambda={lam:+d}, xi={xi:+d}: relative errors "
                    + ", ".join(mp.nstr(e, 7) for e in relative), flush=True,
                )
    maxima = {
        str(n): [
            max(abs(mp.mpf(r["relative_errors_over_actual"][order]))
                for r in rows if r["n"] == n)
            for order in range(4)
        ] for n in indices
    }
    output = {
        "status": "completed: exact identities and finite-index numerical diagnostics",
        "interval_certified": False,
        "meaning": "Actual coefficients use finite recurrences. Approximation errors are observed, not rigorous error bounds.",
        "source_snapshot": SNAPSHOT,
        "recurrence_source_path": "Analysis/Transseries/docs/series-and-transseries/Quadratic_Polylogarithm_Feedback_Boundary_Completion/code/feedback_verify.py",
        "grid": {"indices": indices, "lambda": [-1, 0, 1], "exact_xi": coordinates},
        "normalization": "n B Rb^n a_n, with B from the pole-paired exact resonant scale and xi=n(1-A/b)/B",
        "error_convention": "signed error=approximation-actual; relative error=signed error/actual",
        "environment": {
            "python": platform.python_version(), "numpy": np.__version__,
            "mpmath": mp.__version__, "mpmath_working_digits": mp.mp.dps,
            "longdouble_precision_digits": int(np.finfo(LD).precision),
            "longdouble_min_exponent": int(np.finfo(LD).minexp),
        },
        "exact_original_equation_check": exact,
        "parabolic_cylinder_vs_fourier_checks": h_checks,
        "precision_reference_checks": checks,
        "max_absolute_relative_error_by_n_and_order": {
            key: [text_number(x, 25) for x in values] for key, values in maxima.items()
        },
        "rows": rows,
        "elapsed_seconds": time.perf_counter()-started,
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    json_path = args.output_dir/"coefficient_validation.json"
    json_path.write_text(json.dumps(output, indent=2)+"\n", encoding="utf-8")
    with (args.output_dir/"coefficient_validation.csv").open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(csv_rows[0]))
        writer.writeheader()
        writer.writerows(csv_rows)
    print(f"Completed {len(rows)} coefficient comparisons in {output['elapsed_seconds']:.2f} seconds.", flush=True)
    print(json_path, flush=True)


if __name__ == "__main__":
    main()
