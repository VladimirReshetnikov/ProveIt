#!/usr/bin/env python3
"""Floating-point regression checks for the proportional-mask TV coefficient.

Run from any directory with Python 3, NumPy, and SciPy installed:

    python check_proportional_tv.py --output numerical_results.json

The finite-n identities evaluated here are exact Gamma/Beta identities. Their
evaluation uses floating point, not interval arithmetic. These checks test the
derived coefficients; they do not prove the asymptotic or its uniform error.
"""

from __future__ import annotations

import argparse
import json
import math
import platform
from pathlib import Path

import numpy as np
import scipy
from scipy.optimize import brentq
from scipy.special import betainc, gammainc, gammaln, ndtr
from scipy.stats import norm


PROPORTIONS = (0.3, 0.5, 0.8)
GAMMA_SIZES = (200, 1000, 5000, 10000)
ONE_CAP_SIZES = (1000, 5000, 10000)
CAP = 2.0


def gaussian_data(eta: float) -> tuple[float, float, float]:
    """Return crossing c, Gaussian TV V(eta), and universal coefficient U."""
    alpha = 1.0 - eta
    c = math.sqrt(-eta * math.log(eta) / alpha)
    leading = 2.0 * (ndtr(c / math.sqrt(eta)) - ndtr(c))
    universal = norm.pdf(c) * c * (
        2.0 * c**4 - c**2 - 3.0 * eta * alpha
    ) / (18.0 * eta**2)
    return float(c), float(leading), float(universal)


def gamma_log_pdf(x: float, shape: int) -> float:
    if x <= 0.0:
        return -math.inf
    return float((shape - 1) * math.log(x) - x - gammaln(shape))


def one_cap_log_factor(x: float, power: int, cap: float) -> float:
    """Log of [1-(1-cap/x)_+^power]/[1-exp(-cap)].

    This is the multiplicative correction to a Gamma(power+1, 1)
    density from convolution with nu_cap. log1p/expm1 avoid avoidable
    cancellation in the signed representation.
    """
    denominator_log = math.log(-math.expm1(-cap))
    if x <= cap:
        return -denominator_log
    return math.log(-math.expm1(power * math.log1p(-cap / x))) - denominator_log


def root_pair(log_likelihood, c: float, h: int, k: int):
    """Find both crossings in standardized observed-sum coordinates."""
    left = brentq(log_likelihood, -2.0 * c, 0.0)
    right_limit = min(2.0 * c, 0.999 * h / math.sqrt(k))
    right = brentq(log_likelihood, 0.0, right_limit)
    return float(left), float(right)


def run_gamma_case(eta_requested: float) -> dict:
    """Untruncated model: Q sum is Gamma(k); P sum/n is Beta(k,h+1)."""
    records = []
    for n in GAMMA_SIZES:
        h = round(eta_requested * n)
        k = n - h
        eta = h / n
        c, leading, coefficient = gaussian_data(eta)

        def log_likelihood(z):
            observed_sum = k + math.sqrt(k) * z
            return (
                gamma_log_pdf(n - observed_sum, h + 1)
                - gamma_log_pdf(n, n + 1)
            )

        left, right = root_pair(log_likelihood, c, h, k)
        lower = k + math.sqrt(k) * left
        upper = k + math.sqrt(k) * right
        p_interval = betainc(k, h + 1, upper / n) - betainc(k, h + 1, lower / n)
        q_interval = gammainc(k, upper) - gammainc(k, lower)
        tv = float(p_interval - q_interval)
        scaled = n * (tv - leading)
        records.append({
            "n": n,
            "h": h,
            "k": k,
            "eta": eta,
            "tv": tv,
            "leading_tv": leading,
            "predicted_coefficient": coefficient,
            "n_times_tv_minus_leading": scaled,
            "coefficient_error": scaled - coefficient,
            "standardized_crossings": [left, right],
            "scaled_crossing_midpoint": math.sqrt(n) * (left + right) / 2.0,
            "predicted_scaled_crossing_midpoint": math.log(eta) / (3.0 * math.sqrt(1.0 - eta)),
            "maximum_log_likelihood_root_residual": max(
                abs(log_likelihood(left)), abs(log_likelihood(right))
            ),
        })
    return {"eta_requested": eta_requested, "records": records}


def run_one_cap_case(eta_requested: float, cap_hidden: bool, cap: float) -> dict:
    """One truncated coordinate with otherwise untruncated exponentials.

    mu=n+b, b=-cap/(exp(cap)-1). The uniform-simplex conditional CDF is
    obtained by inclusion/exclusion with weight (1-cap/mu)^n. The beta
    argument in the removed simplex is s/(mu-cap) for a hidden cap and
    (s-cap)/(mu-cap) for an observed cap.
    """
    mean_defect = -cap / math.expm1(cap)
    variance_defect = -(cap**2) * math.exp(cap) / math.expm1(cap)**2
    records = []
    for n in ONE_CAP_SIZES:
        h = round(eta_requested * n)
        k = n - h
        eta = h / n
        alpha = 1.0 - eta
        c, leading, universal = gaussian_data(eta)
        vh = variance_defect if cap_hidden else 0.0
        vo = 0.0 if cap_hidden else variance_defect
        coefficient = universal + norm.pdf(c) * c * (vo - alpha * vh / eta)
        mu = n + mean_defect
        observed_mean = k + (0.0 if cap_hidden else mean_defect)
        log_denominator = gamma_log_pdf(mu, n + 1) + one_cap_log_factor(mu, n, cap)

        def log_likelihood(z):
            observed_sum = observed_mean + math.sqrt(k) * z
            hidden_input = mu - observed_sum
            numerator = gamma_log_pdf(hidden_input, h + 1)
            if cap_hidden:
                numerator += one_cap_log_factor(hidden_input, h, cap)
            return numerator - log_denominator

        left, right = root_pair(log_likelihood, c, h, k)
        lower = observed_mean + math.sqrt(k) * left
        upper = observed_mean + math.sqrt(k) * right
        log_weight = n * math.log1p(-cap / mu)
        weight = math.exp(log_weight)
        one_minus_weight = -math.expm1(log_weight)

        def p_cdf(s):
            removed_argument = (s if cap_hidden else s - cap) / (mu - cap)
            removed_argument = min(1.0, max(0.0, removed_argument))
            return (
                betainc(k, h + 1, s / mu)
                - weight * betainc(k, h + 1, removed_argument)
            ) / one_minus_weight

        def q_cdf(s):
            if cap_hidden:
                return gammainc(k, s)
            return (
                gammainc(k, s) - math.exp(-cap) * gammainc(k, max(0.0, s - cap))
            ) / (-math.expm1(-cap))

        tv = float(p_cdf(upper) - p_cdf(lower) - q_cdf(upper) + q_cdf(lower))
        scaled = n * (tv - leading)
        records.append({
            "n": n,
            "h": h,
            "k": k,
            "eta": eta,
            "mu": mu,
            "v_H": vh,
            "v_O": vo,
            "tv": tv,
            "leading_tv": leading,
            "predicted_coefficient": float(coefficient),
            "n_times_tv_minus_leading": scaled,
            "coefficient_error": float(scaled - coefficient),
            "standardized_crossings": [left, right],
            "maximum_log_likelihood_root_residual": max(
                abs(log_likelihood(left)), abs(log_likelihood(right))
            ),
        })
    return {
        "eta_requested": eta_requested,
        "cap_location": "hidden" if cap_hidden else "observed",
        "cap": cap,
        "mean_defect": mean_defect,
        "variance_defect": variance_defect,
        "records": records,
    }


def regression_checks(gamma_cases: list, one_cap_cases: list) -> dict:
    """Loose, platform-tolerant regression gates, not rigorous error bounds."""
    checks = []
    for family, cases, tolerance in (
        ("gamma", gamma_cases, 1.0e-5),
        ("one_cap", one_cap_cases, 3.0e-5),
    ):
        for case in cases:
            records = case["records"]
            first = next(r for r in records if r["n"] == 1000)
            last = records[-1]
            root_residual = max(r["maximum_log_likelihood_root_residual"] for r in records)
            finite = all(
                math.isfinite(r["tv"]) and 0.0 <= r["tv"] <= 1.0
                for r in records
            )
            within_tolerance = abs(last["coefficient_error"]) < tolerance
            error_decreased = abs(last["coefficient_error"]) < abs(first["coefficient_error"])
            roots_resolved = root_residual < 1.0e-8
            checks.append({
                "family": family,
                "eta_requested": case["eta_requested"],
                "cap_location": case.get("cap_location"),
                "finite_tv_in_unit_interval": finite,
                "coefficient_absolute_tolerance_at_n_10000": tolerance,
                "coefficient_within_tolerance": within_tolerance,
                "absolute_coefficient_error_decreased_from_n_1000_to_10000": error_decreased,
                "log_likelihood_roots_resolved_to_1e_minus_8": roots_resolved,
                "passed": finite and within_tolerance and error_decreased and roots_resolved,
            })
    return {
        "purpose": "Platform-tolerant floating-point regression only; no rigorous asymptotic error certification.",
        "all_passed": all(check["passed"] for check in checks),
        "cases": checks,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().with_name("numerical_results.json"),
        help="Destination for detailed machine-readable results.",
    )
    args = parser.parse_args()
    gamma_cases = [run_gamma_case(eta) for eta in PROPORTIONS]
    one_cap_cases = [
        run_one_cap_case(eta, cap_hidden, CAP)
        for eta in PROPORTIONS for cap_hidden in (True, False)
    ]
    checks = regression_checks(gamma_cases, one_cap_cases)
    result = {
        "schema_version": 1,
        "scope": (
            "Exact finite-n Gamma/Beta distribution identities evaluated in floating point. "
            "Tests the explicit proportional-mask coefficient and first crossing shift. "
            "The one-cap family tests nonzero variance defects and exact-mean cancellation. "
            "These checks do not prove or rigorously certify the uniform remainder."
        ),
        "environment": {
            "python": platform.python_version(),
            "numpy": np.__version__,
            "scipy": scipy.__version__,
            "floating_point": "IEEE-754 binary64 in NumPy/SciPy calls",
        },
        "gamma_cases": gamma_cases,
        "one_cap_cases": one_cap_cases,
        "regression_checks": checks,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
    print(f"Wrote {args.output}")
    print(f"Regression checks: {sum(c['passed'] for c in checks['cases'])}/{len(checks['cases'])} passed")
    for family, cases in (("Gamma", gamma_cases), ("one-cap", one_cap_cases)):
        for case in cases:
            last = case["records"][-1]
            location = case.get("cap_location", "")
            print(
                f"{family:7s} eta={case['eta_requested']:.1f} {location:8s} "
                f"predicted={last['predicted_coefficient']:.11f} "
                f"at n=10000={last['n_times_tv_minus_leading']:.11f} "
                f"error={last['coefficient_error']:.3g}"
            )
    return 0 if checks["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
