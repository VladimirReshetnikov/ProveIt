#!/usr/bin/env python3
"""Reproducible floating diagnostics for the Ford renewal recurrence.

The computations in this program are NOT proofs or interval certificates.
The formal symbolic identities for asymptotic coefficients are exact; numerical
evaluations, root finding, truncation, quadrature, and eigenvalues are floating.

Run from the package root:
    python code/verify_recurrence.py --nmax 1000

Outputs default to rerun/. Use --out data explicitly to replace recorded data.

Dependencies: mpmath, sympy, numpy, scipy (versions recorded in diagnostics.json).
No network access or unpublished input is required.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
import platform
import sys
import time

import mpmath as mp
import numpy as np
import scipy
from scipy.linalg import eigh
from scipy.special import roots_legendre
import sympy as sp


def decimal(value, digits=60):
    return mp.nstr(value, digits)


def write_csv(path, fields, rows):
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def asymptotic_coefficients(order):
    """c_j=(j+1)![u^(j+1)] e^(gamma*u)/Gamma(-1-u).

    The identity e^(gamma*u)/Gamma(-1-u)
      =u(1+u) exp(-sum(zeta(k)*u^k/k,k>=2))
    cancels Euler's constant before any numerical computation.
    """
    e = [sp.Integer(1), sp.Integer(0)]
    for n in range(2, order + 1):
        e.append(sp.expand(-sum(sp.zeta(k) * e[n-k]
                                for k in range(2, n+1)) / n))
    result = []
    for j in range(order + 1):
        value = sp.factor(sp.factorial(j+1) * (e[j] + (e[j-1] if j else 0)))
        result.append(value)
    return result


def solve_recurrence(nmax, dps):
    mp.mp.dps = dps
    # The extra terms put the root-series truncation far below working epsilon
    # for roots in the small bracket used here. This is a numerical margin,
    # not a formally certified truncation-error enclosure.
    series_cutoff = max(nmax, math.ceil((dps + 60) * math.log(10) / -math.log(.55)))
    logarithms = [mp.mpf(0)] + [mp.log(k) for k in range(1, series_cutoff + 2)]
    a = [mp.mpf(0)] + [(k+1)*logarithms[k+1] - k*logarithms[k] - 1
                       for k in range(1, series_cutoff + 1)]

    def generating(z):
        value = mp.mpf(0)
        for coefficient in reversed(a[1:]):
            value = (value + coefficient) * z
        return value

    rho = mp.findroot(lambda z: generating(z) - 1, (mp.mpf("0.54"), mp.mpf("0.55")))
    rho_powers = [mp.mpf(1)]
    for k in range(1, series_cutoff + 1):
        rho_powers.append(rho_powers[-1]*rho)
    probabilities = [a[k] * rho_powers[k] for k in range(series_cutoff + 1)]
    gamma = 1 / mp.fsum(k * probabilities[k] for k in range(1, series_cutoff + 1))

    # h_n = rho^n g_n satisfies a well-scaled convolution recurrence.
    # Recovering b_n=(gamma-h_n)/rho^n still requires linearly growing precision.
    h = [mp.mpf(1)]
    residuals = [gamma-1]
    for n in range(1, nmax + 1):
        h.append(mp.fsum(probabilities[k] * h[n-k] for k in range(1, n+1)))
        residuals.append((gamma-h[n]) / rho_powers[n])
    return rho, gamma, h, residuals, rho_powers, series_cutoff


def spectral_diagnostics(residuals, nmax, resolutions):
    """Independent positive spectral moments, in IEEE double precision.

    Approximate Q(t)=t-c-integral w(u)/(t-u)du by a positive quadrature.
    The corresponding Cauchy transform is the top-left resolvent entry of
    the real symmetric arrowhead matrix. Remove its largest atom and sum
    the remaining spectral moments. No dominant exponentials are subtracted.
    """
    indices = [n for n in (1, 2, 5, 10, 25, 50, 100, 250, 500, 1000) if n <= nmax]
    rows = []
    summaries = []
    for resolution in resolutions:
        start = time.monotonic()
        x, quadrature_weights = roots_legendre(resolution)
        u = (x+1)/2
        quadrature_weights = quadrature_weights/2
        w = ((1-u)/np.log(u))**2
        matrix = np.diag(np.r_[2*np.log(2), u])
        off_diagonal = np.sqrt(quadrature_weights*w)
        matrix[0, 1:] = off_diagonal
        matrix[1:, 0] = off_diagonal
        eigenvalues, eigenvectors = eigh(matrix, driver="evd", check_finite=True)
        masses = eigenvectors[0, :]**2
        atom = eigenvalues[-1]
        rho_approx = 1/atom
        gamma_approx = masses[-1]*(1-rho_approx)
        continuous_nodes = eigenvalues[:-1]
        continuous_weights = masses[:-1]*(1-continuous_nodes)
        for n in indices:
            value = float(np.dot(continuous_weights, continuous_nodes**(n-1)))
            reference = float(residuals[n])
            rows.append({"quadrature_nodes": resolution, "n": n,
                         "spectral_b_n": f"{value:.17g}",
                         "recurrence_b_n": f"{reference:.17g}",
                         "relative_difference": f"{(value-reference)/reference:.8g}"})
        summaries.append({"quadrature_nodes": resolution,
                          "rho_approx": float(rho_approx),
                          "gamma_approx": float(gamma_approx),
                          "smallest_eigenvalue": float(eigenvalues[0]),
                          "continuous_largest_eigenvalue": float(eigenvalues[-2]),
                          "sum_spectral_masses": float(np.sum(masses)),
                          "seconds": time.monotonic()-start})
    return rows, summaries


def endpoint_spectral_diagnostics(residuals, nmax, dps=70, terms=24, cutoff=120,
                                  selected_indices=None):
    """Scaled real integral, using the convergent local series for the density.

    P(t) = (t/(2sinh(t/2)))^2 - 1
             + sum_{k>=0} zeta'(-1-k)t^(k+2)/k!.
    The series converges for |t| < 2*pi. Its stable coefficients are
      p_k=zeta'(1-k)/(k-2)!-(k-1)B_k/k!,  k>=2.
    At the smallest n=50 and chosen cutoff=120, |t|<=2.4<2*pi.
    The omitted series terms and infinite integration tail are NOT enclosed
    rigorously. Increasing precision, cutoff, and order supplies diagnostics.
    """
    saved_precision = mp.mp.dps
    mp.mp.dps = dps
    coefficients = [mp.mpf(0), mp.mpf(0)]
    for k in range(2, terms+1):
        derivative = mp.diff(mp.zeta, 1-k)
        coefficients.append(derivative/mp.factorial(k-2)
                            -(k-1)*mp.bernoulli(k)/mp.factorial(k))
    p2 = coefficients[2]
    pieces = [mp.mpf(0), mp.mpf("0.05"), mp.mpf("0.2"), mp.mpf(1),
              mp.mpf(3), mp.mpf(10), mp.mpf(30), mp.mpf(cutoff)]

    def p_series(t):
        value = mp.mpf(0)
        for coefficient in reversed(coefficients[2:]):
            value = value*t + coefficient
        return value*t*t

    def exact_scaled(n):
        logn = mp.log(n)
        def integrand(y):
            if not y:
                return mp.mpf(0)
            t = y/n
            center = logn-mp.log(y)-mp.euler-p_series(t)
            stable_prefactor = y*t/(-mp.expm1(-t))
            return mp.exp(-y)*stable_prefactor/(center*center+mp.pi**2)
        return mp.quad(integrand, pieces)

    def resummed(n, k, derivative=False):
        logn = mp.log(n)
        def integrand(y):
            if not y:
                return mp.mpf(0)
            center = logn-mp.log(y)-mp.euler
            denominator = center*center+mp.pi**2
            weight = y**(k-1)*mp.exp(-y)
            if derivative:
                return -2*center*weight/denominator**2
            return weight/denominator
        return mp.quad(integrand, pieces)

    indices = selected_indices or [50, 100, 256, 500, 1000, 10000, 10**6,
                                   10**10, 10**20, 10**50, 10**100]
    rows = []
    for integer_n in indices:
        n = mp.mpf(integer_n)
        scaled = exact_scaled(n)
        f2, f3, f4, f4_prime = (resummed(n, k, derivative)
                              for k, derivative in ((2,False),(3,False),(4,False),(4,True)))
        s0 = f2
        s1 = f2+f3/(2*n)
        third = f4/12-p2*f4_prime
        s2 = s1+third/n**2
        row = {"n": str(integer_n), "log_n": decimal(mp.log(n), 35),
               "b_n_local_integral": decimal(scaled/n**2, 50),
               "normalized_b_n": decimal(scaled*mp.log(n)**2, 40),
               "n2_b_n": decimal(scaled, 50),
               "F2": decimal(f2, 50), "F3": decimal(f3, 50),
               "F4": decimal(f4, 50), "F4_prime": decimal(f4_prime, 50),
               "third_sector_coefficient": decimal(third, 50),
               "relative_error_sector0": decimal((s0-scaled)/scaled, 30),
               "relative_error_sectors01": decimal((s1-scaled)/scaled, 30),
               "relative_error_sectors012": decimal((s2-scaled)/scaled, 30),
               "n4_times_error_sectors01": decimal((s1-scaled)*n**2, 40),
               "n5_times_error_sectors012": decimal((s2-scaled)*n**3, 40)}
        if integer_n <= nmax:
            row["relative_difference_from_recurrence"] = decimal(
                (scaled/n**2-residuals[integer_n])/residuals[integer_n], 30)
        # For huge n, an algebraic correction below precision cannot be resolved.
        if integer_n > 10**10:
            for field in ("relative_error_sector0", "relative_error_sectors01",
                          "relative_error_sectors012", "n4_times_error_sectors01",
                          "n5_times_error_sectors012"):
                row[field] = "below_precision_for_algebraic_sector_comparison"
        rows.append(row)
    mp.mp.dps = saved_precision
    metadata = {"status": "Floating local-series quadrature, not an interval certificate.",
                "decimal_precision": dps, "P_series_degree": terms,
                "scaled_integral_cutoff": cutoff,
                "F_k_definition": "integral_0^infinity y^(k-1)exp(-y)/((log(n)-log(y)-EulerGamma)^2+pi^2) dy",
                "p2": decimal(p2, 50)}
    return rows, metadata


def run(args):
    start = time.monotonic()
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    dps = args.dps or math.ceil(.27*args.nmax)+100
    exact_c = asymptotic_coefficients(args.order)
    print(f"Computing n <= {args.nmax} at {dps} decimal digits", flush=True)
    rho, gamma, h, b, powers, cutoff = solve_recurrence(args.nmax, dps)
    numerical_c = [mp.mpf(str(sp.N(c, dps))) for c in exact_c]

    coefficient_records = [{"j": j, "exact": str(c), "latex": sp.latex(c),
                            "decimal": decimal(numerical_c[j], 60)}
                           for j, c in enumerate(exact_c)]
    (output / "asymptotic_coefficients.json").write_text(json.dumps({
        "definition": "b_n ~ n^(-2) sum_{j>=0} c_j/(log n)^(j+2)",
        "generator": "c_j=(j+1)![u^(j+1)] u(1+u)exp(-sum_{k>=2}zeta(k)u^k/k)",
        "status": "Exact symbolic coefficient identities; not a proof of the asymptotic expansion.",
        "coefficients": coefficient_records}, indent=2) + "\n", encoding="utf-8")

    rows = []
    approximation_order = min(6, args.order)
    for n in range(1, args.nmax+1):
        row = {"n": n, "g_n": decimal(h[n]/powers[n], 50),
               "scaled_g_n": decimal(h[n], 60), "b_n": decimal(b[n], 60)}
        if n >= 2:
            logn = mp.log(n)
            row["normalized_b_n"] = decimal(b[n]*n*n*logn*logn, 30)
            total = mp.mpf(0)
            for j in range(approximation_order+1):
                total += numerical_c[j]/(n*n*logn**(j+2))
                row[f"expansion_K{j}"] = decimal(total, 40)
                row[f"relative_error_K{j}"] = decimal((total-b[n])/b[n], 30)
        rows.append(row)
    fields = ["n", "g_n", "scaled_g_n", "b_n", "normalized_b_n"]
    for j in range(approximation_order+1):
        fields += [f"expansion_K{j}", f"relative_error_K{j}"]
    write_csv(output / "recurrence.csv", fields, rows)

    product_rows = []
    logarithmic_product = mp.mpf(0)
    checkpoints = sorted(set(n for n in (1, 2, 5, 10, 25, 50, 100, 250, 500, args.nmax)
                             if n <= args.nmax))
    for n in range(1, args.nmax+1):
        logarithmic_product += mp.log(h[n]/gamma)
        if n in checkpoints:
            product_rows.append({"N": n, "C_N": decimal(mp.exp(logarithmic_product), 90),
                                 "log_C_N": decimal(logarithmic_product, 90)})
    write_csv(output / "product_convergence.csv", ["N", "C_N", "log_C_N"], product_rows)

    difference_rows = []
    for n in (1, 2, 5, 10, 25, 50, 100, 250, 500):
        for r in range(7):
            if n+r <= args.nmax:
                signed_difference = mp.fsum((-1)**k * math.comb(r, k)*b[n+k]
                                             for k in range(r+1))
                difference_rows.append({"n": n, "r": r,
                                        "minus_delta_r_b_n": decimal(signed_difference, 60),
                                        "positive": bool(signed_difference > 0)})
    write_csv(output / "finite_differences.csv",
              ["n", "r", "minus_delta_r_b_n", "positive"], difference_rows)

    print("Computing independent double-precision spectral diagnostics", flush=True)
    spectral_rows, spectral_summary = spectral_diagnostics(b, args.nmax, args.spectral)
    write_csv(output / "spectral_comparison.csv",
              ["quadrature_nodes", "n", "spectral_b_n", "recurrence_b_n", "relative_difference"],
              spectral_rows)

    print("Computing resummed endpoint-density integrals through n=10^100", flush=True)
    endpoint_rows, endpoint_metadata = endpoint_spectral_diagnostics(b, args.nmax)
    write_csv(output / "endpoint_spectral_integral.csv",
              ["n", "log_n", "b_n_local_integral", "normalized_b_n", "n2_b_n",
               "F2", "F3", "F4", "F4_prime", "third_sector_coefficient",
               "relative_error_sector0", "relative_error_sectors01", "relative_error_sectors012",
               "n4_times_error_sectors01", "n5_times_error_sectors012",
               "relative_difference_from_recurrence"], endpoint_rows)
    stronger_endpoint_rows, stronger_endpoint_metadata = endpoint_spectral_diagnostics(
        b, args.nmax, dps=90, terms=32, cutoff=160, selected_indices=[50, 256, 1000])
    baseline_endpoint = {row["n"]: row for row in endpoint_rows}
    endpoint_sensitivity = []
    for row in stronger_endpoint_rows:
        old = mp.mpf(baseline_endpoint[row["n"]]["n2_b_n"])
        new = mp.mpf(row["n2_b_n"])
        endpoint_sensitivity.append({
            "n": row["n"], "relative_change_after_precision_order_cutoff_increase": decimal(
                abs(new-old)/abs(new), 20),
            "stronger_relative_difference_from_recurrence": row.get(
                "relative_difference_from_recurrence", "not_computed")})
    endpoint_metadata["stronger_run"] = stronger_endpoint_metadata
    endpoint_metadata["sensitivity_diagnostics"] = endpoint_sensitivity

    # A second higher-precision computation tests numerical sensitivity, not
    # mathematical correctness or a rigorous error enclosure.
    check_n = min(args.nmax, 250)
    original_samples = {n: b[n] for n in (1, 10, 50, 100, 250) if n <= check_n}
    rho_check, gamma_check, _, b_check, _, _ = solve_recurrence(check_n, dps+40)
    precision_check = [{"n": n,
                        "relative_difference": decimal(abs(b_check[n]-value)/abs(value), 20)}
                       for n, value in original_samples.items()]
    mp.mp.dps = dps

    diagnostics = {
        "status": "Floating-point diagnostics only; not proofs or interval certificates.",
        "date": "2026-10-08",
        "nmax": args.nmax,
        "python_optimization_level": sys.flags.optimize,
        "working_decimal_precision": dps,
        "root_series_cutoff": cutoff,
        "rho": decimal(rho, 100),
        "gamma": decimal(gamma, 100),
        "continuous_spectral_mass": decimal(1-gamma/(1-rho), 100),
        "sum_b_n_to_nmax": decimal(mp.fsum(b[1:]), 80),
        "theoretical_total_sum_b_n": decimal(1-gamma/(1-rho), 80),
        "sum_n_b_n_to_nmax": decimal(mp.fsum(n*b[n] for n in range(1, args.nmax+1)), 80),
        "theoretical_total_sum_n_b_n": decimal(gamma*rho/(1-rho)**2, 80),
        "C_N_at_nmax": product_rows[-1]["C_N"],
        "all_sampled_residuals_positive": bool(all(value > 0 for value in b[1:])),
        "all_sampled_differences_positive": all(row["positive"] for row in difference_rows),
        "precision_check": precision_check,
        "rho_precision_difference": decimal(abs(rho-rho_check), 20),
        "gamma_precision_difference": decimal(abs(gamma-gamma_check), 20),
        "spectral_runs": spectral_summary,
        "endpoint_spectral_integral": endpoint_metadata,
        "elapsed_seconds": time.monotonic()-start,
        "versions": {"python": platform.python_version(), "mpmath": mp.__version__,
                     "sympy": sp.__version__, "numpy": np.__version__, "scipy": scipy.__version__},
        "limitations": [
            "No directed rounding or interval arithmetic is used.",
            "The root uses a truncated defining series with a generous but uncertified precision margin.",
            "Spectral quadrature convergence is empirical at the reported resolutions.",
            "C_N is a finite product, not an independently certified value of the infinite product.",
            "Fixed-order asymptotic expansions need not improve monotonically at moderate n."
        ]
    }
    (output / "diagnostics.json").write_text(json.dumps(diagnostics, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"rho": decimal(rho, 35), "gamma": decimal(gamma, 35),
                      "C_N": diagnostics["C_N_at_nmax"],
                      "normalized_last_residual": rows[-1].get("normalized_b_n"),
                      "seconds": diagnostics["elapsed_seconds"]}, indent=2), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nmax", type=int, default=1000)
    parser.add_argument("--dps", type=int, default=None)
    parser.add_argument("--order", type=int, default=10)
    parser.add_argument("--spectral", type=int, nargs="+", default=[128, 256, 512])
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1]/"rerun")
    arguments = parser.parse_args()
    if arguments.nmax < 10 or arguments.order < 2:
        parser.error("Use nmax >= 10 and order >= 2.")
    run(arguments)
