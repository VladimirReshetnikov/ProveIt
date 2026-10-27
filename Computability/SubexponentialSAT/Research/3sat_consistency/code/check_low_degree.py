#!/usr/bin/env python3
"""Exact arithmetic audit of the degree-at-most-ceil(s^0.51) specialization.

This verifies the schedule, packing exponents, paid recurrence and interval
comparisons. The contraction interface, inherited local menus, and main
support/potential certificate remain explicit mathematical dependencies.
Standard library only; no floating-point acceptance tests.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NEW_BETA2 = F(283611964650596186827, 875000000000000000000)
OLD_BETA2 = F(15952347164548384057, 49000000000000000000)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sqrt_bounds(x, places=55):
    require(x >= 0, "Negative square-root argument")
    d = 10 ** places
    n = isqrt(x.numerator * d * d // x.denominator)
    return F(n, d), F(n + 1, d)


def atan_bounds(q, n=120):
    a = sum((F((-1) ** k, (2 * k + 1) * q ** (2 * k + 1))
             for k in range(n)), F(0))
    b = a + F((-1) ** n, (2 * n + 1) * q ** (2 * n + 1))
    return min(a, b), max(a, b)


def pi_over_ln2_bounds():
    a, b = atan_bounds(5)
    c, d = atan_bounds(239)
    pi = (16 * a - 4 * d, 16 * b - 4 * c)
    n = 140
    lnlo = 2 * sum((F(1, (2 * k + 1) * 3 ** (2 * k + 1))
                    for k in range(n)), F(0))
    tail = 2 * F(1, (2 * n + 1) * 3 ** (2 * n + 1)) / (1 - F(1, 9))
    return pi[0] / (lnlo + tail), pi[1] / lnlo


def coefficient(radicals):
    lo, hi = pi_over_ln2_bounds()
    roots = [sqrt_bounds(r) for r in radicals]
    return lo * sum((a for a, _ in roots), F(0)), hi * sum((b for _, b in roots), F(0))


def verify(certificate):
    require(F(certificate["beta_squared"]) == NEW_BETA2,
            "Unexpected main support coefficient")
    delta = F(51, 100)
    eta0, eta1, eta2 = F(59, 800), F(181, 4000), F(89, 5000)
    qtail = F(4, 9)
    stage_alphabets = [10, 13, 7]
    log_upper = {10: F(1661, 500), 13: F(3701, 1000), 7: F(281, 100)}
    for base, bound in log_upper.items():
        require(base ** bound.denominator < 2 ** bound.numerator,
                "Invalid logarithm upper bound")
    a1 = eta0 + eta1
    atotal = a1 + eta2 / (1 - qtail)
    require(a1 == F(119, 1000) and atotal == F(472, 3125), "Taper sum mismatch")
    sums = [eta0, a1, atotal]
    expected_degree_gaps = [F(1, 200000), F(49581, 1000000), F(20493, 312500)]
    expected_rounding_gaps = [F(87251, 200000), F(81, 500000), F(9, 78125)]
    gates = []
    for depth, (alphabet, cumulative) in enumerate(zip(stage_alphabets, sums)):
        degree_gap = 1 - delta - (2 if depth == 0 else 1) * cumulative * log_upper[alphabet]
        rounding_gap = 1 - (1 + 2 * log_upper[alphabet]) * cumulative
        require(degree_gap == expected_degree_gaps[depth] > 0,
                "Retained-side or root packing gate failed")
        require(rounding_gap == expected_rounding_gaps[depth] > 0,
                "Packet-capacity packing gate failed")
        # The fresh-side exponent is 2 log_2(r) A_d + A_{d-1};
        # A_{d-1}<=A_d bounds it by the checked packet-capacity exponent.
        gates.append({"stage": depth, "alphabet": alphabet,
                      "cumulative_taper_upper": str(cumulative),
                      "degree_gap": str(degree_gap), "rounding_gap": str(rounding_gap)})
    require(atotal < delta, "New packet degree exceeds retained-degree budget")
    require(F(9, 4) ** 3 < 3 ** 4, "Provisional active tail tapers fail to grow")
    gamma = F(3, 7)  # (2/7) / sqrt(4/9)
    require(F(2, 7) ** 2 / qtail == gamma ** 2, "Tail ratio mismatch")
    alpha2 = {10: F(18, 100), 13: F(24, 169), 7: F(12, 49)}
    beta13sq, beta7sq = F(1572, 4225), F(632, 1225)
    tail_multiplier2 = alpha2[7] / (1 - gamma) ** 2
    require(tail_multiplier2 == F(3, 4) > beta7sq, "Tail terminal route not dominant")

    root_new_rad = [2 * NEW_BETA2 / eta0]
    root_old_rad = [2 * OLD_BETA2 / eta0]
    depth1_rad = [2 * alpha2[10] / eta0, 2 * beta13sq / (25 * eta1)]
    terminal_rad = [2 * alpha2[10] / eta0, 2 * alpha2[13] / (25 * eta1),
                    2 * tail_multiplier2 * F(4, 4225) / eta2]
    require(depth1_rad == [F(288, 59), F(100608, 152945)], "Depth-one radicals differ")
    require(terminal_rad == [F(288, 59), F(7680, 30589), F(1200, 15041)],
            "Terminal radicals differ")
    branches = {"new_root": coefficient(root_new_rad),
                "old_root_same_schedule": coefficient(root_old_rad),
                "depth_one": coefficient(depth1_rad),
                "terminal": coefficient(terminal_rad)}
    time = branches["depth_one"]
    for name in ("new_root", "old_root_same_schedule", "terminal"):
        require(branches[name][1] < time[0], "Unexpected dominant time branch")
    require(time[1] < F(1369, 100), "Time coefficient not below 13.690")
    # Joint selector max(F,21 G/20) from the separately verified certificate.
    root_space = coefficient([root_new_rad[0] * F(400, 441)])
    child_space = coefficient([2 * beta13sq / (25 * eta1)])
    tail_space = coefficient([2 * beta7sq * F(4, 4225) / eta2])
    require(child_space[1] < root_space[0] and tail_space[1] < root_space[0],
            "Root no longer dominates local space")
    require(root_space[1] < F(6399, 500), "Space coefficient not below 12.798")

    # Explicit false claims are rejected independently of Python assertions.
    require(time[0] > F(342, 25), "Incorrect time-below-13.68 control accepted")
    require(not F(52, 100) + 2 * eta0 * log_upper[10] < 1,
            "Incorrect degree-0.52 control accepted")
    bad_a1 = eta0 + F(23, 500)
    require(not (1 + 2 * log_upper[13]) * bad_a1 < 1,
            "Incorrect enlarged-depth-one-taper control accepted")

    # Uniformly enlarge the old generic tapers before comparing schedules.
    scale = F(17, 4)
    old_eta0 = scale * F(301, 20000)
    old_eta1 = scale * F(119, 10000)
    old_eta2 = scale * F(1549, 324000)
    old_sums = [old_eta0, old_eta0 + old_eta1,
                old_eta0 + old_eta1 + old_eta2 / (1 - qtail)]
    old_logs = {10: F(1661, 500), 13: F(3701, 1000), 7: F(14037, 5000)}
    require(7 ** 5000 < 2 ** 14037, 'Comparator logarithm upper bound failed')
    old_gates = []
    for depth, (alphabet, cumulative) in enumerate(zip(stage_alphabets, old_sums)):
        degree_gap = 1 - delta - (2 if depth == 0 else 1) * cumulative * old_logs[alphabet]
        capacity_gap = 1 - (1 + 2 * old_logs[alphabet]) * cumulative
        require(degree_gap > 0 and capacity_gap > 0, 'Scaled old schedule gate failed')
        old_gates.append({'stage': depth, 'degree_gap': str(degree_gap),
                          'capacity_gap': str(capacity_gap)})
    require(old_sums[-1] < delta, 'Scaled old schedule fresh degrees too large')
    baseline = coefficient([2 * OLD_BETA2 / old_eta0])
    baseline_child = coefficient([2 * alpha2[10] / old_eta0,
                                  2 * beta13sq / (25 * old_eta1)])
    baseline_terminal = coefficient([2 * alpha2[10] / old_eta0,
                                     2 * alpha2[13] / (25 * old_eta1),
                                     2 * tail_multiplier2 * F(4, 4225) / old_eta2])
    require(baseline[0] > baseline_child[1] and baseline[0] > baseline_terminal[1],
            'Scaled old schedule root not dominant')
    require(time[1] < baseline[0], 'No improvement over scaled old schedule')

    return {
        "status": "PASS",
        "scope": "Normalized networks with maximum initial degree <= ceil(s^(51/100))",
        "imported_dependencies": ["exact contraction and entry-access interface",
                                  "main joint support certificate with rho=21/20",
                                  "legacy 13- and 7-group local menus"],
        "alphabets": stage_alphabets,
        "tapers": [str(eta0), str(eta1), str(eta2)],
        "tail_taper_ratio": str(qtail),
        "cumulative_tapers": list(map(str, sums)),
        "leaf_threshold": "ceil(s/lambda^(3/4))",
        "precision_guard": "ceil(6 log2(lambda))",
        "relative_padding_slack": "lambda^(-3)",
        "packing_gates": gates,
        "degree_bound_dominates_fresh_degrees": True,
        "gamma": str(gamma),
        "new_root_beta_squared": str(NEW_BETA2),
        "old_root_beta_squared": str(OLD_BETA2),
        "branch_intervals": {key: list(map(str, bounds)) for key, bounds in branches.items()},
        "time_radicals": list(map(str, depth1_rad)),
        "terminal_radicals": list(map(str, terminal_rad)),
        "space_interval": list(map(str, root_space)),
        "child_space_interval": list(map(str, child_space)),
        "tail_space_interval": list(map(str, tail_space)),
        "dominant_time_branch": "depth_one",
        "same_schedule_old_and_new_time_coefficients_are_equal": True,
        "scaled_inherited_comparator": {
            "scale": str(scale), 'tapers': list(map(str, [old_eta0, old_eta1, old_eta2])),
            'gates': old_gates, 'time_interval': list(map(str, baseline)),
            'display_only_time': float(baseline[0]),
            'status': 'Newly evaluated inherited composition, not a printed source theorem'},
        "interpretation": "Time improvement is a degree-aware specialization; new root potentials do not change the dominant time branch on this schedule.",
        "eventual_time_coefficient": "13.690",
        "eventual_space_coefficient": "12.798",
        "display_only": {**{key: float(bounds[0]) for key, bounds in branches.items()},
                         "space": float(root_space[0]),
                         "child_space": float(child_space[0]),
                         "tail_space": float(tail_space[0])},
        "negative_controls_rejected": ["time < 13.68", "initial degree exponent 0.52",
                                       "eta_1=23/500"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=ROOT / "data/support_consistency_certificate.json")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/low_degree_schedule.json")
    args = parser.parse_args()
    result = verify(json.loads(args.certificate.read_text()))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "display_only": result["display_only"],
                      "eventual_time_coefficient": result["eventual_time_coefficient"],
                      "eventual_space_coefficient": result["eventual_space_coefficient"],
                      "same_schedule_old_and_new_time_coefficients_are_equal": True}, indent=2))


if __name__ == "__main__":
    main()
