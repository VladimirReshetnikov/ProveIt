#!/usr/bin/env python3
"""OPTIONAL FLOATING-POINT sanity checks, separate from exact certificates.

Requires mpmath (not required by any exact-suite script).
    python3 code/sanity_moving_bounds.py
    python3 code/sanity_moving_bounds.py --output code/floating_sanity_results.json

Samples the frozen eigenvector, fixed-band bound, and uncorrected moving
potential inequality, and reproduces the finite ratio table from exact terms.
These numerical samples do not certify the uniform bound, the quadratic
corrector estimates, or any asymptotic theorem. Results are approximate.
"""
import argparse
import json
from pathlib import Path
import sys


def run():
    import mpmath as mp
    mp.mp.dps = 80
    mu = 6 / mp.pi ** 2
    tolerance = mp.mpf("1e-60")

    def chi_q(q):
        if q == 0:
            return mp.pi ** 2 / 6
        x = mp.exp(-q)
        return mp.polylog(2, x) - q * mp.log1p(-x)

    def calibration(n, s):
        if n == s:
            return mp.mpf(0), n * mu
        lower = mp.mpf(0)
        upper = 2 * mp.log(mp.mpf(n) / s) + 2
        for unused in range(280):
            middle = (lower + upper) / 2
            if n * mu * chi_q(middle) > s:
                lower = middle
            else:
                upper = middle
        q = (lower + upper) / 2
        return q, n * mu * q / mp.expm1(q)

    frozen_checks = shifted_checks = 0
    maximum_eigen_relative_error = mp.mpf(0)
    maximum_shifted_excess = mp.ninf
    for M in (1, 2, 3, 5, 10, 25):
        for text_value in ("0.1", "0.5", "1", "2", "10", "100"):
            v = mp.mpf(text_value)
            q = mp.log(v)
            vector = [mp.exp(-q*j/M) for j in range(M)]
            eigenvalue = mp.mpf(M) if v == 1 else (v-1)/(-mp.expm1(-q/M))
            for last in range(M):
                action = sum((v if j >= last else 1)*vector[j] for j in range(M))
                relative_error = abs(action/(eigenvalue*vector[last])-1)
                maximum_eigen_relative_error = max(maximum_eigen_relative_error, relative_error)
                if relative_error >= tolerance:
                    raise RuntimeError("sampled eigenvector residual exceeds tolerance")
                frozen_checks += 1
                for d in (0, 1, 2, 5, 30):
                    shifted = sum((v if j > last-d else 1)*vector[j] for j in range(M))
                    majorant = eigenvalue + abs(d-1)*abs(v-1)*max(v, 1/v)
                    excess = shifted/vector[last]-majorant
                    maximum_shifted_excess = max(maximum_shifted_excess, excess)
                    if excess >= tolerance:
                        raise RuntimeError("sampled fixed-band bound failed")
                    shifted_checks += 1

    checks = calibration_checks = 0
    maximum_excess = mp.ninf
    maximum_calibration_residual = mp.mpf(0)
    for n in (10, 30, 100, 1000):
        for i in sorted({1, 2, n//3, n//2, n-1}):
            qi, Si = calibration(n, i)
            q, S = calibration(n, i+1)
            for qvalue, svalue, target in ((qi, Si, i), (q, S, i+1)):
                residual = abs(n * mu * chi_q(qvalue) - target)
                maximum_calibration_residual = max(maximum_calibration_residual, residual)
                if residual > tolerance:
                    raise RuntimeError("approximate calibration residual exceeds tolerance")
                if not mp.mpf(target)/2-tolerance <= svalue <= target+tolerance:
                    raise RuntimeError("sampled calibration range failed")
                calibration_checks += 1
            for K in sorted({0, 1, min(5, i-1), i//2, i-1}):
                if K < 0 or K > i-1:
                    continue
                M = K+2
                for last in sorted({0, K//2, K}):
                    current = mp.exp(qi*K - qi*last/M)
                    actual = mp.mpf(0)
                    for letter in range(M):
                        ascent = int(letter >= last)
                        actual += mp.exp(q*(K+ascent)-q*letter/(M+ascent))
                    ratio = mp.mpf(M)/S
                    alpha = 3*q/(2*S)
                    upper = mp.log(n*mu)-1+mp.log(ratio)-ratio+1+alpha/ratio+mp.mpf(6)/i
                    excess = mp.log(actual/current)-upper
                    maximum_excess = max(maximum_excess, excess)
                    if excess >= tolerance:
                        raise RuntimeError("sampled moving-potential inequality failed")
                    checks += 1
    from verify_exact import parse_terms
    from hashlib import sha256
    raw_terms, terms = parse_terms(Path(__file__).resolve().parents[1]/"data"/"weak_ascent_terms.txt")

    def decimal_places(value, digits):
        scale = 10**digits
        rounded = int(mp.nint(value*scale))
        sign = "-" if rounded < 0 else ""
        integer, fractional = divmod(abs(rounded), scale)
        return sign + str(integer) + "." + str(fractional).zfill(digits)

    diagnostics = []
    for n in (20, 50, 100, 200, 300, 400, 500):
        ratio = mp.mpf(terms[n]) / (n*terms[n-1])
        B = n*(ratio/mu-1)
        diagnostics.append({"n": n, "r_n": str(ratio), "B_n": str(B),
            "r_n_report_15_decimals": decimal_places(ratio, 15),
            "B_n_report_11_decimals": decimal_places(B, 11)})
    return {"status": "floating_sanity_passed", "arithmetic": "mpmath_floating_point",
        "precision_decimal_digits": mp.mp.dps, "mpmath_version": mp.__version__,
        "calibration_samples": calibration_checks, "moving_potential_samples": checks,
        "frozen_eigenvector_samples": frozen_checks, "fixed_band_samples": shifted_checks,
        "maximum_eigenvector_relative_error": str(maximum_eigen_relative_error),
        "maximum_fixed_band_excess": str(maximum_shifted_excess),
        "terms_sha256": sha256(raw_terms).hexdigest(), "ratio_diagnostics": diagnostics,
        "maximum_calibration_residual": str(maximum_calibration_residual),
        "maximum_moving_log_bound_excess": str(maximum_excess),
        "tolerance": str(tolerance),
        "scope": "Approximate finite sanity samples only; not certified inequalities or analytic proofs."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = run()
        encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if args.output:
            args.output.write_text(encoded, encoding="ascii")
    except Exception as error:
        print(json.dumps({"status": "failed", "error_type": type(error).__name__,
                          "error": str(error)}), file=sys.stderr)
        return 1
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
