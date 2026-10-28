#!/usr/bin/env python3
"""Exact schedule arithmetic and numerical upper-bound constants.

This is a parameter-analysis program, not a SAT solver or a runtime benchmark.
The input is lambda = ceil(log2(s)); the program never constructs 2**lambda.
All schedule and finite feasibility decisions use integers or Fractions.
Decimal or floating arithmetic is used only for displayed analytic constants.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path
import math
from typing import Any


GROUPS = 54
DECAY = 9
EPSILON_DENOMINATOR = 132
BOOTSTRAP_SHRINK_DENOMINATOR = 26
LOG2_GROUPS_UPPER = Fraction(144, 25)
PACKET_EXPONENT_LIMIT = Fraction(3, 352)
PI_TEXT = "3.141592653589793238462643383279502884197169399375105820974944592307816406286"


def ceil_log2(n: int) -> int:
    if not isinstance(n, int) or isinstance(n, bool) or n <= 0:
        raise ValueError("ceil_log2 requires a positive integer")
    return (n - 1).bit_length()


def guard_bits(lam: int) -> int:
    if lam < 2:
        raise ValueError("lambda must be at least 2")
    return ceil_log2(lam + 2) ** 2


def fraction_record(x: Fraction) -> dict[str, str]:
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def schedule(lam: int) -> list[dict[str, int]]:
    """All potentially active depths under the bootstrap M_d <= s/26**d.

    Since an active call has M_d > s/lambda, it necessarily has 26**d < lambda.
    Small inputs can produce u_d=0; they are explicitly marked infeasible in
    certificate(), and the mathematical algorithm uses its finite-size fallback.
    """
    if not isinstance(lam, int) or isinstance(lam, bool) or lam < 2:
        raise ValueError("lambda must be an integer at least 2")
    g = guard_bits(lam)
    rows: list[dict[str, int]] = []
    depth = 0
    shrink_power = 1
    decay_power = 1
    a = 0
    while shrink_power < lam:
        u = lam // (EPSILON_DENOMINATOR * decay_power)
        previous_a = a
        a += u + g
        rows.append({
            "depth": depth,
            "u": u,
            "a": a,
            "previous_a": previous_a,
            "guard": g,
            "minimum_log2_D_t": previous_a + g + 1,
            "bootstrap_shrink_power": shrink_power,
        })
        depth += 1
        shrink_power *= BOOTSTRAP_SHRINK_DENOMINATOR
        decay_power *= DECAY
    return rows


def certificate(lam: int, include_rows: bool = True) -> dict[str, Any]:
    """Sufficient exact finite parameter checks, with all scope recorded.

    The rational bound log2(54)<144/25 follows from 54**50<2**288.
    If s is any integer with 2**(lambda-1)<s<=2**lambda and M>s/lambda,
    the two gap tests ensure
      D_arr*Delta*lambda**2/M <= lambda**(-2),
      L*D_arr/M <= lambda**(-2),
    using Delta=ceil(s**(9/10))<=2*s**(9/10).  The bound on the padding
    excess is then <=1/lambda+4/lambda**2.  These are sufficient checks,
    not a claim that smaller parameters fail the actual algorithm.
    """
    rows = schedule(lam)
    a_max = rows[-1]["a"]
    g = guard_bits(lam)
    h = ceil_log2(lam)
    a_bound = PACKET_EXPONENT_LIMIT * lam + len(rows) * g
    packing_gap = Fraction(lam, 10) - 2 * LOG2_GROUPS_UPPER * a_max
    rounding_gap = Fraction(lam) - (1 + 2 * LOG2_GROUPS_UPPER) * a_max
    degree_gap = Fraction(9 * (lam - 1), 10) - 1 - a_max
    padding_excess = Fraction(1, lam) + Fraction(4, lam * lam)
    tests = {
        "all_retained_tapers_positive": all(row["u"] >= 1 for row in rows),
        "cumulative_packet_bound": Fraction(a_max) <= a_bound,
        "potential_packing_gap": packing_gap >= 2 + 5 * h,
        "padding_rounding_gap": rounding_gap >= 1 + 3 * h,
        "new_packet_degree_at_most_Delta": degree_gap >= 0,
        "bootstrap_shrink_at_most_one_over_26": padding_excess <= Fraction(1, 26),
        "guard_at_least_eight_log2_lambda": g >= 8 * h,
    }
    result: dict[str, Any] = {
        "lambda": str(lam),
        "active_depth_count_upper_bound": len(rows),
        "guard": g,
        "minimum_u": str(min(row["u"] for row in rows)),
        "maximum_a": str(a_max),
        "a_upper_bound": fraction_record(a_bound),
        "packing_gap": fraction_record(packing_gap),
        "rounding_gap": fraction_record(rounding_gap),
        "degree_gap": fraction_record(degree_gap),
        "relative_padding_excess_upper_bound": fraction_record(padding_excess),
        "tests": tests,
        "all_sufficient_checks_pass": all(tests.values()),
    }
    if include_rows:
        result["depths"] = [
            {key: str(value) if key in {"u", "a", "previous_a", "minimum_log2_D_t", "bootstrap_shrink_power"} else value
             for key, value in row.items()}
            for row in rows
        ]
    return result


def constants() -> dict[str, Any]:
    with localcontext() as ctx:
        ctx.prec = 55
        pi = Decimal(PI_TEXT)
        ln2 = Decimal(2).ln()
        old = 2 * pi * Decimal(4320).sqrt() / (
            ln2 * (1 - Decimal(3) * Decimal(12).sqrt() / 128)
        )
        combined = old / Decimal(3).sqrt()
        new = 9 * pi * Decimal(22).sqrt() / (2 * ln2)
        new_general_formula = (
            2 * pi * (Decimal(2) * EPSILON_DENOMINATOR / 3).sqrt()
            / (ln2 * (1 - Decimal(2) * Decimal(DECAY).sqrt() / GROUPS))
        )
        old_to_new = old / new
        combined_to_new = combined / new
        fixed_r_boundary = (
            2 * pi * (Decimal(40) * (Decimal(54).ln() / ln2) / 3).sqrt()
            / (ln2 * (1 - Decimal(1) / 9) ** (Decimal(3) / 2))
        )
        values = {
            "existing_schedule_geometric": str(+old),
            "existing_schedule_plus_factorial_Cauchy": str(+combined),
            "new_fixed_schedule": str(+new),
            "new_fixed_schedule_general_formula": str(+new_general_formula),
            "existing_certificate_divided_by_new": str(+old_to_new),
            "combined_prior_certificate_divided_by_new": str(+combined_to_new),
            "r54_boundary_family_infimum": str(+fixed_r_boundary),
        }
    return {
        "scope": "Coefficients in certified base-two upper bounds for normalized tensor size s; not measured runtimes or runtime ratios.",
        "numerical_precision_digits": 50,
        "values": values,
        "exact_new_expression": "9*pi*sqrt(22)/(2*ln(2))",
        "exact_packing_margin_using_log_upper_bound": fraction_record(Fraction(1, 550)),
        "log_upper_bound_integer_certificate": {
            "inequality": "54^50 < 2^288",
            "left": str(54 ** 50),
            "right": str(2 ** 288),
            "holds": 54 ** 50 < 2 ** 288,
        },
    }


def optimized_family_samples() -> dict[str, Any]:
    """Numerical optimization of the stated certificate family only."""
    candidates = []
    for r in range(3, 513):
        b = (r / 2) ** (2 / 3)
        epsilon_boundary = (b - 1) / (20 * b * math.log2(r))
        value = (
            2 * math.pi * math.sqrt(2 / (3 * epsilon_boundary))
            / (math.log(2) * (1 - (2 / r) * math.sqrt(b)))
        )
        candidates.append({"groups": r, "decay": b,
                           "epsilon_boundary": epsilon_boundary,
                           "boundary_coefficient": value})
    candidates.sort(key=lambda row: row["boundary_coefficient"])
    low, high = 3.0, 512.0
    for _ in range(100):
        mid = (low + high) / 2
        value = (mid / 2) ** (2 / 3) - 1 - 2 * math.log(mid)
        if value < 0:
            low = mid
        else:
            high = mid
    r_star = (low + high) / 2
    return {
        "scope": "Numerical stationary point and boundary infima of this analysis family; not a claim of globally optimal contraction or an implemented boundary schedule.",
        "continuous_stationary_groups": r_star,
        "best_integer_group_samples": candidates[:8],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lambdas", nargs="+", type=int,
                        default=[10**6, 10**8, 10**12, 10**24, 10**48])
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results" / "schedule_analysis.json")
    args = parser.parse_args()
    result = {
        "status": "Exact finite parameter checks plus analytic-certificate calculations. No end-to-end SAT execution or formal proof is claimed.",
        "parameters": {"groups": GROUPS, "decay": DECAY,
                       "epsilon": f"1/{EPSILON_DENOMINATOR}",
                       "guard": "ceil(log2(lambda+2))^2",
                       "leaf_threshold": "ceil(s/lambda)",
                       "bootstrap_shrink": "1/26"},
        "constants": constants(),
        "schedules": [certificate(lam) for lam in args.lambdas],
        "family_optimization": optimized_family_samples(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(args.output),
                      "schedules": len(result["schedules"]),
                      "sufficient_checks_pass": [x["all_sufficient_checks_pass"] for x in result["schedules"]],
                      "new_coefficient": result["constants"]["values"]["new_fixed_schedule"]}))


if __name__ == "__main__":
    main()
