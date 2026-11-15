#!/usr/bin/env python3
"""Exact arithmetic checks for the cutoffs in the iPRA zeta manuscript.

The formulas are intentionally conservative.  This program checks their
numerical error budgets with fractions.Fraction; it does not evaluate the
enormous quadrature grids, prove the analytic estimates, certify primitive
recursiveness, or produce an iPRA/Lean proof.

Usage:
    python3 quantitative_bounds.py
    python3 quantitative_bounds.py --max-b 8 --max-p 12 \
        --sample-b 4 --sample-p 20 --output quantitative_bounds_check.json

All Python arithmetic used in the checks is exact.  Decimal values in the
JSON are explicitly labelled as approximate summaries.  Huge fractions are
summarized by their exact binary order instead of printing thousands of
digits.  Mathematical function arguments have no artificial upper bound;
the CLI limits its requested diagnostic grid to modest values.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import factorial
from pathlib import Path
from typing import Any


def ceil_log2(n: int) -> int:
    """The integer lambda(n) = ceil(log_2(n)), for n >= 1."""
    if n < 1:
        raise ValueError("ceil_log2 requires a positive integer")
    return (n - 1).bit_length()


def two_power(exponent: int) -> Fraction:
    """Return 2**exponent as an exact rational, including negative exponents."""
    if exponent >= 0:
        return Fraction(1 << exponent)
    return Fraction(1, 1 << (-exponent))


def _domain(B: int, p: int, minimum_B: int) -> None:
    if B < minimum_B or p < 0:
        raise ValueError(f"requires B >= {minimum_B} and p >= 0")


def theta_cutoffs(B: int, p: int) -> dict[str, int]:
    """Finite Fejer orders for t in [1/B, B], from the theta proof.

    Here M bounds the periodized Gaussian, L is its Lipschitz constant,
    h defines the split delta=1/h, and m is the Fejer order.  The symbol M
    in this dictionary is unrelated to the rectangle count in j_cutoffs.
    """
    _domain(B, p, 2)
    M = 8 * B
    L = 128 * B**3
    h = (1 << (p + 3)) * (L + 1)
    m = (1 << (p + 3)) * (4 * M * h + 32 * B**3 + 1)
    return {"M": M, "L": L, "h": h, "m": m}


def theta_budget(B: int, p: int) -> dict[str, Fraction]:
    """The three exact rational terms in the theta-recovery error bound."""
    c = theta_cutoffs(B, p)
    return {
        "near_kernel": Fraction(c["L"], c["h"]),
        "far_kernel": Fraction(4 * c["M"] * c["h"], c["m"]),
        "weighted_gaussian_sum": Fraction(32 * B**3, c["m"]),
    }


def j_cutoffs(B: int, p: int) -> dict[str, int]:
    """Cutoffs for J(s), uniformly for the manuscript's input box |s| <= B.

    T is the integration endpoint; N is the Gaussian-series cutoff; q and
    r are binary precision exponents; M=(T-1)*2**q is the rectangle count.
    D is the supplied derivative bound.  The formulas, not numerical
    sampling of the integrand, are what this module checks.
    """
    _domain(B, p, 1)
    T = p + ceil_log2(factorial(B)) + 4
    N = p + (B + 1) * ceil_log2(T) + 4
    D = 2 * (B + 2) * T**B
    q = p + ceil_log2(T * D) + 4
    r = p + ceil_log2(T) + 4
    M = (T - 1) * (1 << q)
    return {"T": T, "N": N, "D": D, "q": q, "r": r, "M": M}


def j_budget(B: int, p: int) -> dict[str, Fraction]:
    """The four exact rational terms in the l1 error bound for J(s)."""
    c = j_cutoffs(B, p)
    T, N, D, q, r = (c[key] for key in ("T", "N", "D", "q", "r"))
    return {
        "infinite_interval_tail": 2 * factorial(B) * two_power(-2 * T),
        "gaussian_series_tail": 4 * T ** (B + 1)
        * two_power(-3 * (N + 1) ** 2),
        "rectangle_error": T * D * two_power(-q),
        "rational_sample_error": T * two_power(-r),
    }


def gaussian_quadrature_cutoffs(B: int, p: int, K: int) -> dict[str, int]:
    """Auxiliary Fourier-integral quadrature for rational |xi| <= K.

    q_count is a subdivision count, unlike the precision exponent q in
    j_cutoffs.  Only the cutoff arithmetic is computed.
    """
    _domain(B, p, 2)
    if K < 0:
        raise ValueError("requires K >= 0")
    R = B * (p + B + 4)
    D = 8 * (B * R + K + 1)
    q_count = (1 << (p + 4)) * (2 * R) ** 2 * D
    sample_precision = p + R + 5
    return {"R": R, "D": D, "q_count": q_count,
            "sample_precision": sample_precision}


def gaussian_quadrature_budget(B: int, p: int, K: int) -> dict[str, Fraction]:
    """The pre-rounding Fourier quadrature budget from the theta note."""
    c = gaussian_quadrature_cutoffs(B, p, K)
    R, D, q_count = (c[key] for key in ("R", "D", "q_count"))
    return {
        "infinite_interval_tail": 2 * B * two_power(-(R // B)),
        "rectangle_error": Fraction(D * (2 * R) ** 2, 2 * q_count),
        "rational_sample_error": 2 * R * two_power(-c["sample_precision"]),
    }


def _sum(terms: dict[str, Fraction]) -> Fraction:
    return sum(terms.values(), Fraction(0))


def _binary_order(x: Fraction) -> int:
    """Return floor(log2(x)) exactly, for positive rational x."""
    if x <= 0:
        raise ValueError("binary order requires a positive fraction")
    candidate = x.numerator.bit_length() - x.denominator.bit_length()
    if x < two_power(candidate):
        candidate -= 1
    return candidate


def _fraction_summary(x: Fraction) -> dict[str, Any]:
    if x == 0:
        return {"exact": "0"}
    order = _binary_order(x)
    answer: dict[str, Any] = {
        "floor_log2_exact": order,
        "binary_interval": f"[2^{order}, 2^{order + 1})",
    }
    if max(x.numerator.bit_length(), x.denominator.bit_length()) <= 192:
        answer["exact"] = str(x)
    if -1000 <= order <= 1000:
        answer["decimal_approximation"] = float(x)
    return answer


def _budget_report(terms: dict[str, Fraction], p: int) -> dict[str, Any]:
    target = two_power(-p)
    total = _sum(terms)
    return {
        "target": f"2^-{p}",
        "strictly_below_target": total < target,
        "total_ratio_to_target": _fraction_summary(total / target),
        "component_ratios_to_target": {
            name: _fraction_summary(value / target)
            for name, value in terms.items()
        },
    }


def run_checks(max_b: int, max_p: int) -> dict[str, Any]:
    """Check a finite parameter grid using exact fractions.

    This function intentionally reports bounded sanity checks, not a
    universally quantified theorem.  The simple majorants shown below
    are the ones whose general proof is supplied in the manuscript.
    """
    theta_cases = 0
    j_cases = 0
    theta_max_ratio = Fraction(0)
    j_max_ratio = Fraction(0)
    theta_max_at: tuple[int, int] | None = None
    j_max_at: tuple[int, int] | None = None
    j_majorants = {
        "infinite_interval_tail": Fraction(1, 128),
        "gaussian_series_tail": Fraction(1, 32),
        "rectangle_error": Fraction(1, 16),
        "rational_sample_error": Fraction(1, 16),
    }
    failures: list[dict[str, Any]] = []

    for B in range(1, max_b + 1):
        for p in range(max_p + 1):
            target = two_power(-p)
            jt = j_budget(B, p)
            jratio = _sum(jt) / target
            j_cases += 1
            if not jratio < 1:
                failures.append({"family": "J", "B": B, "p": p,
                                 "condition": "total < target"})
            for name, cap in j_majorants.items():
                if jt[name] > cap * target:
                    failures.append({"family": "J", "B": B, "p": p,
                                     "condition": f"component {name}"})
            if jratio > j_max_ratio:
                j_max_ratio, j_max_at = jratio, (B, p)

            if B >= 2:
                tt = theta_budget(B, p)
                tratio = _sum(tt) / target
                theta_cases += 1
                if not tratio < Fraction(1, 4):
                    failures.append({"family": "theta", "B": B, "p": p,
                                     "condition": "total < target/4"})
                if not tt["near_kernel"] < target / 8:
                    failures.append({"family": "theta", "B": B, "p": p,
                                     "condition": "near term < target/8"})
                if not (tt["far_kernel"] + tt["weighted_gaussian_sum"]
                        < target / 8):
                    failures.append({"family": "theta", "B": B, "p": p,
                                     "condition": "other terms < target/8"})
                if tratio > theta_max_ratio:
                    theta_max_ratio, theta_max_at = tratio, (B, p)

    return {
        "status": "PASS" if not failures else "FAIL",
        "scope": "Finite exact-rational sanity checks; not a universal proof.",
        "parameter_grid": {"J_B": [1, max_b], "theta_B": [2, max_b],
                           "p": [0, max_p]},
        "J": {
            "cases": j_cases,
            "component_majorant_ratios": {k: str(v) for k, v in j_majorants.items()},
            "sum_of_majorant_ratios": str(sum(j_majorants.values(), Fraction(0))),
            "largest_observed_ratio": _fraction_summary(j_max_ratio),
            "largest_observed_at_B_p": j_max_at,
        },
        "theta": {
            "cases": theta_cases,
            "total_majorant_ratio": "1/4",
            "largest_observed_ratio": _fraction_summary(theta_max_ratio),
            "largest_observed_at_B_p": theta_max_at,
        },
        "failures": failures,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-b", type=int, default=8)
    parser.add_argument("--max-p", type=int, default=12)
    parser.add_argument("--sample-b", type=int, default=4)
    parser.add_argument("--sample-p", type=int, default=20)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not 2 <= args.max_b <= 16 or not 0 <= args.max_p <= 64:
        parser.error("diagnostic grid requires 2 <= max-b <= 16 and 0 <= max-p <= 64")
    if not 2 <= args.sample_b <= 16 or not 0 <= args.sample_p <= 64:
        parser.error("sample requires 2 <= sample-b <= 16 and 0 <= sample-p <= 64")

    result = run_checks(args.max_b, args.max_p)
    B, p = args.sample_b, args.sample_p
    jc = j_cutoffs(B, p)
    gc = gaussian_quadrature_cutoffs(B, p, K=3)
    gaussian_report = _budget_report(gaussian_quadrature_budget(B, p, K=3), p)
    if not gaussian_report["strictly_below_target"]:
        result["status"] = "FAIL"
        result["failures"].append({"family": "Gaussian quadrature", "B": B,
                                   "p": p, "condition": "sample budget"})

    result["sample"] = {
        "B": B,
        "p": p,
        "theta": {
            "cutoffs": theta_cutoffs(B, p),
            "budget": _budget_report(theta_budget(B, p), p),
        },
        "J": {
            "cutoffs": jc,
            "grid_spacing": f"2^-{jc['q']}",
            "sample_accuracy": f"2^-{jc['r']}",
            "direct_gaussian_summands_at_all_rectangle_nodes": str(jc["M"] * jc["N"]),
            "budget": _budget_report(j_budget(B, p), p),
        },
        "Gaussian_Fourier_quadrature": {
            "frequency_bound_K": 3,
            "cutoffs": gc,
            "budget_before_final_rounding": gaussian_report,
        },
        "workload_notice": "Counts are reported only; no quadrature grid was evaluated.",
    }
    output = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    print(output, end="")
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
