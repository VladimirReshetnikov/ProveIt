#!/usr/bin/env python3
"""Independent exact checks for the schedule and displayed constants.

Finite checks support the mathematical proof; they do not prove the upstream
contraction theorem and do not execute an end-to-end SAT solver.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path
import sys

from schedule_analysis import (certificate, ceil_log2, constants, guard_bits,
                               schedule, PI_TEXT)


def require(condition: bool, explanation: str) -> None:
    if not condition:
        raise AssertionError(explanation)


def run_checks() -> dict:
    count = 0
    guard_cases = 0
    for exponent in range(2, 161):
        for offset in (-3, -2, -1, 0, 1, 2, 3):
            lam = 2**exponent + offset
            if lam < 2:
                continue
            root = ceil_log2(lam + 2)
            require(2 ** (root - 1) < lam + 2 <= 2 ** root,
                    "guard logarithm is not the exact ceiling")
            require(guard_bits(lam) == root * root, "guard is not the squared exact ceiling")
            count += 2
            guard_cases += 1

    require(54**50 < 2**288, "integer logarithm certificate failed")
    log_bound = Fraction(144, 25)
    a_limit = Fraction(1, 132) / (1 - Fraction(1, 9))
    require(a_limit == Fraction(3, 352), "geometric sum differs from stated packet budget")
    margin = 1 - Fraction(9, 10) - 2 * log_bound * a_limit
    require(margin == Fraction(1, 550), "strict packing margin is not 1/550")
    count += 3

    parameter_cases = [132, 10**4, 10**6, 10**8, 10**10, 10**12,
                       10**24, 10**48, 10**100, 2**4096]
    cases = []
    for lam in parameter_cases:
        rows = schedule(lam)
        g = guard_bits(lam)
        require(rows, "empty active-depth list")
        require(26**(len(rows) - 1) < lam <= 26**len(rows),
                "bootstrap depth interval is incorrect")
        actual_sum = 0
        unrounded_sum = Fraction(0)
        for d, row in enumerate(rows):
            denominator = 132 * 9**d
            u = row["u"]
            require(u * denominator <= lam < (u + 1) * denominator,
                    "u is not the exact scheduled floor")
            actual_sum += u
            unrounded_sum += Fraction(lam, denominator)
            require(row["a"] == actual_sum + (d + 1) * g,
                    "cumulative a does not match guarded increments")
            require(row["a"] - u + 1 == row["minimum_log2_D_t"],
                    "minimum D_t exponent does not use i<=u-1")
            require(Fraction(actual_sum) <= unrounded_sum <= a_limit * lam,
                    "finite geometric upper bound is incorrect")
            count += 4
        cert = certificate(lam, include_rows=False)
        if lam >= 10**8:
            require(cert["all_sufficient_checks_pass"],
                    f"large-parameter sufficient checks failed at lambda with {lam.bit_length()} bits")
            count += 1
        cases.append({"lambda_decimal_digits": len(str(lam)),
                      "lambda_bit_length": lam.bit_length(),
                      "active_depth_count": len(rows),
                      "all_sufficient_checks_pass": cert["all_sufficient_checks_pass"],
                      "failed_sufficient_checks": [k for k, v in cert["tests"].items() if not v]})
        count += 2

    # Negative controls ensure the finite checker does not silently certify
    # parameters where the logarithmic guard overwhelms the asymptotic budget.
    require(not certificate(132, include_rows=False)["all_sufficient_checks_pass"],
            "small-parameter negative control was incorrectly certified")
    require(not certificate(10**4, include_rows=False)["all_sufficient_checks_pass"],
            "second small-parameter negative control was incorrectly certified")
    count += 2

    values = constants()["values"]
    with localcontext() as ctx:
        ctx.prec = 50
        pi = Decimal(PI_TEXT)
        ln2 = Decimal(2).ln()
        alpha = 2 * pi * (Decimal(2) / 3).sqrt()
        independent_new = alpha * Decimal(132).sqrt() / (ln2 * (1 - Decimal(1) / 9))
        require(abs(independent_new - Decimal(values["new_fixed_schedule"])) < Decimal("1e-45"),
                "new coefficient expressions disagree")
        require(Decimal("95.66394047289") < independent_new < Decimal("95.66394047291"),
                "new displayed constant lies outside independent numeric interval")
        old = Decimal(values["existing_schedule_geometric"])
        combined = Decimal(values["existing_schedule_plus_factorial_Cauchy"])
        require(abs(combined * Decimal(3).sqrt() - old) < Decimal("1e-45"),
                "combined prior baseline omits the Cauchy factor")
        require(independent_new < combined < old,
                "claimed ordering of certificate constants is false")
        require(Decimal(values["r54_boundary_family_infimum"]) < independent_new,
                "fixed schedule confused with family infimum")
        count += 5

    return {"status": "passed",
            "python_optimization_level": sys.flags.optimize,
            "scope": "Finite exact schedule checks and numerical evaluation of analytic upper-bound certificates; no SAT benchmark or Lean verification.",
            "guard_boundary_cases": guard_cases,
            "parameter_cases": cases,
            "checks_passed": count,
            "integer_packing_certificate": "54^50 < 2^288",
            "rational_asymptotic_packing_margin": "1/550",
            "negative_controls_rejected": 2,
            "new_coefficient": values["new_fixed_schedule"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results" / "schedule_verification.json")
    args = parser.parse_args()
    result = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(args.output), "status": result["status"],
                      "checks_passed": result["checks_passed"],
                      "negative_controls_rejected": result["negative_controls_rejected"]}))


if __name__ == "__main__":
    main()
