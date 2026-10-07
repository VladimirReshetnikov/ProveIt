"""Exact auxiliary arithmetic and sign counts for the norm-gap proof.

Usage: python verification/verify_norm_gap.py --output verification/norm_gap_checks.json

The article supplies the mathematical proof for arbitrary finite groups.
This program uses only the Python standard library and no floating point.
It verifies the 17 rational comparisons in the scalar estimate and the
two complete finite sign-enumeration identities.
"""

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def check_rational_bounds():
    half = F(1, 2)
    small_d_bound = F(21, 25) * F(899, 900) - F(273, 10) * F(203, 1000) / 111
    large_d_bound = F(4199, 5000) - (F(27, 5) + F(203, 1000)) / 111
    specifications = [
        ("a_lower_21_over_25", "a=2^(-1/4) exceeds 21/25", F(21, 25) ** 4, "<", half),
        ("a_lower_1051_over_1250", "a exceeds 1051/1250", F(1051, 1250) ** 4, "<", half),
        ("a_cubed_upper", "a^3 is smaller than 3/5", F(1, 8), "<", F(3, 5) ** 4),
        ("sqrt_five_upper", "sqrt(5) is smaller than 56/25", F(5), "<", F(56, 25) ** 2),
        ("order_three_contradiction", "The order-three lower bound exceeds 5", F(131, 8) * F(23, 25) ** 4, ">", F(5)),
        ("largest_pair_cutoff", "The p<=19/20 case exceeds the available energy", F(57, 200), ">", F(6, 25)),
        ("holder_constant_upper", "82^(3/4) is smaller than 273/10", F(82 ** 3), "<", F(273, 10) ** 4),
        ("tail_fourth_root_upper", "(1/600)^(1/4) is smaller than 203/1000", F(1, 600), "<", F(203, 1000) ** 4),
        ("small_D_bracket", "The small-D bracket exceeds 789/1000", small_d_bound, ">", F(789, 1000)),
        ("derivative_power_upper", "300^(3/4) is smaller than 73", F(300 ** 3), "<", F(73 ** 4)),
        ("positive_derivative_margin", "The derivative margin is exactly 1/111", F(225, 444) - F(1, 3) - F(73, 444), "=", F(1, 111)),
        ("large_D_anchor_lower", "The linear amplitude bound at D=1/300 exceeds 4199/5000", F(1051, 1250) * F(899, 900), ">", F(4199, 5000)),
        ("large_D_B_upper", "The squared B bound at D=1/300 is smaller than 1/25", F(221, 1000), "<", F(16, 25) * F(21, 25) ** 6 * F(899, 900) ** 6),
        ("large_D_bracket", "The large-D bracket exceeds 789/1000", large_d_bound, ">", F(789, 1000)),
        ("final_contradiction", "222*(789/1000)^16 exceeds 5", 222 * F(789, 1000) ** 16, ">", F(5)),
        ("improves_logarithmic_report", "5 exceeds the earlier coefficient (323/160)^2", F(5), ">", F(323, 160) ** 2),
        ("improves_latest_moments", "5 exceeds the latest preceding coefficient 35/8", F(5), ">", F(35, 8)),
    ]
    checks = []
    for identifier, name, lhs, relation, rhs in specifications:
        passed = {"<": lhs < rhs, ">": lhs > rhs, "=": lhs == rhs}[relation]
        checks.append({
            "id": identifier,
            "name": name,
            "status": "pass" if passed else "fail",
            "lhs": str(lhs),
            "relation": relation,
            "rhs": str(rhs),
            "arithmetic": "exact rational",
        })
    if len(checks) != 17:
        raise AssertionError("The verification record must contain exactly 17 rational checks")
    return checks


def check_cosine_counts():
    vertices = list(product((0, 1), repeat=4))
    nonzero = vertices[1:]
    dual_counts = Counter()
    for signs in product((-1, 1), repeat=15):
        if all(sum(s * v[j] for s, v in zip(signs, nonzero)) == 0 for j in range(4)):
            dual_counts[sum(signs)] += 1
    expected_dual = {-5: 1, -3: 27, -1: 111, 1: 111, 3: 27, 5: 1}
    ternary_counts = Counter()
    for signs in product((-1, 1), repeat=16):
        if sum(signs) % 3 != 0:
            continue
        if all(sum(s * v[j] for s, v in zip(signs, vertices)) % 3 == 0 for j in range(4)):
            ternary_counts[sum(signs)] += 1
    expected_ternary = {-12: 8, -6: 16, 0: 286, 6: 16, 12: 8}
    def coefficient_list(counts):
        return [{"frequency": frequency, "count": count}
                for frequency, count in sorted(counts.items())]
    return [
        {
            "id": "fourth_order_cosine_dual",
            "name": "Complete sign enumeration for D4 of a cosine",
            "status": "pass" if dual_counts == expected_dual else "fail",
            "sign_assignments_tested": 1 << 15,
            "sign_assignments_retained": sum(dual_counts.values()),
            "constraint": "Each of the four coordinate-face sign sums equals zero as an integer",
            "coefficients": coefficient_list(dual_counts),
            "expected_coefficients": coefficient_list(expected_dual),
            "consequence": "D4(g1)=111*g1+27*g3+g5; the full-cube cosine count is 2*111=222",
        },
        {
            "id": "order_three_full_cube",
            "name": "Complete sign enumeration for the order-three full four-cube",
            "status": "pass" if ternary_counts == expected_ternary else "fail",
            "sign_assignments_tested": 1 << 16,
            "sign_assignments_retained": sum(ternary_counts.values()),
            "constraint": "The total sign sum and each of four coordinate-face sign sums equal zero modulo 3",
            "coefficients": coefficient_list(ternary_counts),
            "expected_coefficients": coefficient_list(expected_ternary),
            "consequence": "U4(g1)^16=286+32*cos(6*theta)+16*cos(12*theta)",
        },
    ]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the complete verification record as JSON")
    arguments = parser.parse_args()
    checks = check_rational_bounds()
    enumerations = check_cosine_counts()
    passed = all(item["status"] == "pass" for item in checks + enumerations)
    report = {
        "schema_version": 1,
        "verification": "real_centered_fourth_order_gowers_norm_gap",
        "status": "pass" if passed else "fail",
        "rational_check_count": len(checks),
        "rational_checks": checks,
        "enumerations": enumerations,
        "scope": {
            "arithmetic": "Python integers and fractions.Fraction only; no floating-point decisions",
            "dependencies": "Python standard library only",
            "verified": [
                "All 17 auxiliary rational comparisons used in the scalar proof",
                "All 32768 sign assignments for the fourth-order cosine dual identity",
                "All 65536 sign assignments for the order-three full-cube identity",
            ],
            "not_verified_by_this_program": [
                "The general finite-group theorem, which is proved mathematically in the article",
                "Literature priority or optimality of the coefficient 5",
                "Lean formalization or a global Szemeredi bound",
            ],
        },
    }
    if arguments.output is not None:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    if not passed:
        failures = [item["id"] for item in checks + enumerations if item["status"] != "pass"]
        raise AssertionError("Verification failed: " + ", ".join(failures))
    print(f"Passed {len(checks)} exact rational checks.")
    for enumeration in enumerations:
        coefficients = {row["frequency"]: row["count"] for row in enumeration["coefficients"]}
        print(enumeration["name"] + ":", coefficients)
    if arguments.output is not None:
        print("JSON verification record:", arguments.output)
