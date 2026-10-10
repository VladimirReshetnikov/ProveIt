#!/usr/bin/env python3
"""Diagnostics for angular-zero parameter order; not interval certificates.

The proof is in monotonicity_notes.tex. This independent implementation
uses the defining Fourier coefficients at radii strictly below one.
No quadrature of the proof's positive kernel is used for these roots.
"""

import json
from package_io import write_json_new_or_compare
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.optimize import brentq


def main(output=None):
    max_n = 4096
    orders = [1, 2, 3, 5, 8, 12]
    exponents = [0.02, 0.1, 0.3, 0.7, 1.0, 1.5, 2.0, 4.0, 10.0, 30.0]
    radii = [0.05, 0.15, 0.35, 0.6, 0.85, 0.98]
    n = np.arange(2, max_n + 1, dtype=float)
    roots = {}
    rows = []
    checks = {}

    for b in exponents:
        harmonic = np.cumsum(np.arange(1, max_n, dtype=float) ** (-b))
        for a in orders:
            coeff = harmonic * (2.0 / n) ** a
            for radius in radii:
                scaled = coeff * radius ** (n - 2)

                def value(c):
                    return float(np.dot(scaled, np.sin(n * np.arccos(c))))

                c = brentq(value, 0.0, radius, xtol=2e-15, rtol=1e-14)
                theta = float(np.arccos(c))
                roots[(a, b, radius)] = theta
                rows.append({"a": a, "b": b, "radius": radius,
                             "theta": theta, "cos_theta": c,
                             "fourier_residual": value(c)})

    a_gaps = [roots[(orders[j + 1], b, r)] - roots[(orders[j], b, r)]
              for j in range(len(orders) - 1)
              for b in exponents for r in radii]
    b_gaps = [roots[(a, exponents[j + 1], r)] - roots[(a, exponents[j], r)]
              for j in range(len(exponents) - 1)
              for a in orders for r in radii]
    r_gaps = [roots[(a, b, radii[j])] - roots[(a, b, radii[j + 1])]
              for j in range(len(radii) - 1)
              for a in orders for b in exponents]
    threshold_gaps = [roots[(a, b, r)] - np.arccos(r / 2)
                      for a in orders if a >= 2
                      for b in exponents for r in radii]
    exact_errors = [abs(roots[(1, 1.0, r)] - np.arccos(r / 2))
                    for r in radii]
    checks["minimum_strict_a_gap"] = min(a_gaps)
    checks["minimum_strict_b_gap"] = min(b_gaps)
    checks["minimum_strict_radius_gap"] = min(r_gaps)
    checks["minimum_sixth_root_threshold_gap_a_ge_2"] = min(threshold_gaps)
    checks["maximum_error_exact_a1_b1_root"] = max(exact_errors)
    assert min(a_gaps) > 0 and min(b_gaps) > 0 and min(r_gaps) > 0
    assert min(threshold_gaps) > 0 and max(exact_errors) < 2e-13

    # Uniform truncation bound for the normalized Fourier sum:
    # H_{n-1}^{(b)} (2/n)^a <= 2 for every a>=1,b>0.
    checks["uniform_fourier_tail_upper_bound"] = (
        2 * max(radii) ** (max_n - 1) / (1 - max(radii)))

    mp.mp.dps = 55
    logconcavity = []
    for b_string in ["0.05", "0.3", "0.9", "1", "1.3", "1.9", "2", "5", "20"]:
        b = mp.mpf(b_string)
        for t_string in ["0.01", "0.2", "1", "3", "10", "40"]:
            t = mp.mpf(t_string)
            integral = mp.quad(lambda s: s ** (b - 1) / mp.expm1(s),
                               [t, max(t + 1, b + 1), mp.inf])
            R = integral / t ** (b - 1)
            discriminant = R ** 2 + (1 - t / b) * R + t / (b * mp.expm1(t))
            assert discriminant > 0
            logconcavity.append({"b": b_string, "T": t_string,
                                  "normalized_discriminant": mp.nstr(discriminant, 35)})

    alpha = mp.findroot(lambda theta: mp.cot(theta / 2) - (mp.pi - theta), (0.5, 1.2))
    beta = mp.findroot(lambda theta: 2 * mp.sin(theta) - (mp.pi - theta), (1, 1.5))
    report = {"status": "floating-point diagnostics, not formal or interval certificates",
              "fourier_term_count": max_n - 1,
              "root_count": len(rows), "checks": checks,
              "sharp_lower_endpoint_alpha": mp.nstr(alpha, 45),
              "a1_b_infinity_endpoint_beta": mp.nstr(beta, 45),
              "logconcavity_diagnostics": logconcavity,
              "angular_roots": rows}
    if output is not None:
        write_json_new_or_compare(output, report)
    print(json.dumps({key: report[key] for key in ["status", "root_count", "checks",
          "sharp_lower_endpoint_alpha", "a1_b_infinity_endpoint_beta"]}, indent=2))

    return report


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    main(args.output)
