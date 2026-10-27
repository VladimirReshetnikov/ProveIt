#!/usr/bin/env python3
"""Verify directed mode-graph aggregation and its declared schedule constants.

Run: python3 code/verify_mode_graph.py
No assertions are used. The exact finite checks compare literal summation,
three-block summation, cached factors, and division-free Strassen contraction.
The displayed asymptotic constants are evaluations of the report's formulas,
not measured SAT performance and not a proof of the full SAT algorithm.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
from dataclasses import asdict
from fractions import Fraction
from pathlib import Path
from time import perf_counter

from mode_graph import (ContractionStats, PairState, blocked_sum, literal_sum,
                        rectangular_strassen, table_factor, triangle_strassen)

CHECKS: dict[str, int] = {}


def check(condition: bool, name: str, detail: str = "") -> None:
    if not condition:
        raise ArithmeticError(f"{name} failed: {detail}")
    CHECKS[name] = CHECKS.get(name, 0) + 1


def factors_for(group_count, domains):
    factors = []
    for group in range(group_count):
        incident = tuple(pair for pair in sorted(domains) if group in pair)

        def evaluate(assignment, group=group, incident=incident):
            if set(assignment) != set(incident):
                raise ArithmeticError("factor received a nonincident or missing pair")
            linear = sum((7 * pair[0] + 3 * pair[1] + 1) * (state.value + 1)
                         for pair, state in assignment.items())
            nonlinear = math.prod(state.value - group for state in assignment.values())
            return group + 2 + linear + 2 * nonlinear

        if group % 2 == 0:
            table = {}
            for states in itertools.product(*(domains[pair] for pair in incident)):
                table[tuple(state.value for state in states)] = evaluate(dict(zip(incident, states)))
            factors.append(table_factor(incident, table))
        else:
            factors.append(evaluate)
    return factors


def graph_cases():
    for r in range(3, 7):
        pairs = {(j, (j + 1) % r) for j in range(r)}
        pairs.update({(1, 0), (0, r - 1)})
        if r >= 5:
            pairs.add((0, 2))
        domains = {}
        for h, pair in enumerate(sorted(pairs)):
            # Duplicate weights with distinct values test exact-budget allocation.
            if h == 0:
                domains[pair] = (PairState(-1, 0), PairState(2, 0), PairState(4, 2))
            else:
                domains[pair] = (PairState(h % 3 - 1, 0), PairState(h + 2, 1 + h % 2))
        yield f"asymmetric_directed_r{r}", r, domains
    yield "missing_reverse_and_isolated_group", 4, {
        (0, 1): (PairState(-2, 0), PairState(3, 2)),
        (2, 1): (PairState(1, 0), PairState(4, 1))}
    yield "no_pairs", 3, {}
    yield "empty_pair_domain", 4, {(0, 1): (), (1, 2): (PairState(0, 0),)}
    yield "all_pair_weights_zero", 3, {
        (0, 1): (PairState(0, 0), PairState(1, 0)),
        (1, 0): (PairState(2, 0), PairState(3, 0)),
        (1, 2): (PairState(-1, 0), PairState(2, 0))}


def partitions(r):
    # Three nonempty blocks, including unequal sizes and noncontiguous labels.
    first = ((0,), (1,), tuple(range(2, r)))
    second = tuple(tuple(j for j in range(r) if j % 3 == b) for b in range(3))
    return tuple(dict.fromkeys((first, second)))


def verify_graphs():
    results = []
    for name, r, domains in graph_cases():
        factors = factors_for(r, domains)
        for budget in (None, 0, 1, 3):
            for modulus in (None, 16):
                literal_stats = ContractionStats()
                expected = literal_sum(r, domains, factors, weight_budget=budget,
                                       modulus=modulus, stats=literal_stats)
                for blocks in partitions(r):
                    for cache, method in ((False, "direct"), (True, "direct"), (True, "strassen")):
                        stats = ContractionStats()
                        actual = blocked_sum(r, domains, factors, blocks, weight_budget=budget,
                                             modulus=modulus, stats=stats,
                                             cache_groups=cache, method=method)
                        check(actual == expected, "literal_equals_blocked",
                              f"{name}, budget={budget}, modulus={modulus}, blocks={blocks}, method={method}")
                        if cache:
                            check(stats.factor_evaluations == stats.cached_group_entries,
                                  "cached_factor_calls_only")
                        if budget == 0 or name == "empty_pair_domain":
                            check(actual == 0, "empty_feasible_domain")
                        results.append({"case": name, "groups": r, "blocks": blocks,
                                        "weight_budget": budget, "modulus": modulus,
                                        "cache_groups": cache, "method": method,
                                        "result": actual, "stats": asdict(stats),
                                        "literal_assignments": literal_stats.literal_assignments})
    return results


def naive_multiply(A, B, modulus):
    result = [[sum(A[i][k] * B[k][j] for k in range(len(B)))
               for j in range(len(B[0]))] for i in range(len(A))]
    return result if modulus is None else [[entry % modulus for entry in row] for row in result]


def verify_rectangular_strassen():
    results = []
    shapes = ((1, 1, 1), (1, 3, 5), (2, 3, 5), (3, 5, 2),
              (5, 3, 4), (4, 4, 4), (5, 5, 5), (3, 8, 7))
    for m, k, n in shapes:
        A = [[((i + 2) * (j + 3) + 7 * i - j) % 11 - 5 for j in range(k)] for i in range(m)]
        B = [[((i + 3) * (j + 1) - 2 * i + 3 * j) % 13 - 6 for j in range(n)] for i in range(k)]
        C = [[((i + 4) * (j + 2) + i - 4 * j) % 7 - 3 for j in range(m)] for i in range(n)]
        for modulus in (None, 2, 16):
            expected = naive_multiply(A, B, modulus)
            actual = rectangular_strassen(A, B, modulus=modulus)
            check(actual == expected, "rectangular_strassen_equals_naive")
            triangle = sum(expected[i][j] * C[j][i] for i in range(m) for j in range(n))
            if modulus is not None:
                triangle %= modulus
            check(triangle_strassen(A, B, C, modulus=modulus) == triangle,
                  "strassen_triangle_equals_naive")
            results.append({"m": m, "k": k, "n": n, "modulus": modulus,
                            "square_block_size": 1 << (min(m, k, n).bit_length() - 1),
                            "triangle": triangle})
    return results


def schedule_constants():
    r = 256
    blocks = (85, 85, 86)
    incident_counts = [2 * r * b - b * b - b for b in blocks]
    boundary_counts = [2 * b * (r - b) for b in blocks]
    pair_counts = [2 * blocks[i] * blocks[j] for i, j in ((0, 1), (1, 2), (0, 2))]
    crossing_count = r * r - sum(b * b for b in blocks)
    check(max(incident_counts) == 36550, "block_incident_count")
    check(max(boundary_counts) == 29240, "block_boundary_count")
    check(crossing_count == 43690, "total_crossing_count")
    check(sorted(pair_counts) == [14450, 14620, 14620], "triangle_pair_counts")
    A2 = Fraction(max(incident_counts), r * r)
    B2 = Fraction(crossing_count, r * r)
    J2 = Fraction(max(boundary_counts), r * r)
    a2 = Fraction(2 * (r - 1), r * r)
    gamma_upper = Fraction(13, 160)
    check(Fraction(52, 15)**2 > 12, "rational_sqrt12_upper_bound")
    check(A2 / B2 < (1 - gamma_upper)**2, "direct_recurrence_dominated_exact")
    epsilon = Fraction(1, 700)
    a_schedule = 2 * epsilon / (1 - Fraction(1, 12))
    packing_exponent = Fraction(9, 10) + 32 * a_schedule
    check(a_schedule == Fraction(6, 1925), "cumulative_schedule_exact")
    check(packing_exponent == Fraction(3849, 3850) < 1, "packing_slack_exact")
    gamma = 3 * math.sqrt(12) / 128
    A, B, J, group_a = (math.sqrt(float(x)) for x in (A2, B2, J2, a2))
    omega = math.log2(7)
    B_strassen_squared = (crossing_count - (1 - (omega - 2)**2) * min(pair_counts)) / (r * r)
    B_strassen = math.sqrt(B_strassen_squared)
    # 7^5>2^14 proves omega>14/5, hence (omega-2)^2>16/25.
    # This yields a rational lower bound that certifies both dominances.
    check(7**5 > 2**14, "strassen_omega_exact_lower_bound")
    B_strassen_lower_squared = (Fraction(crossing_count)
                               - Fraction(9, 25) * min(pair_counts)) / (r * r)
    check(B_strassen_lower_squared == Fraction(38488, 65536),
          "strassen_coefficient_exact_lower_bound")
    check(B_strassen_lower_squared > A2
          and B_strassen_lower_squared > a2 / (1 - gamma_upper)**2,
          "strassen_recurrence_dominated_exact")
    root4 = math.pi * math.sqrt(4200) / math.log(2)
    root3 = math.pi * math.sqrt(5600) / math.log(2)
    root3_old = math.pi * math.sqrt(5760) / math.log(2)
    root1_old = math.pi * math.sqrt(17280) / math.log(2)
    return {
        "interpretation": "Coefficients multiplying s/sqrt(log2(s)) in declared asymptotic upper bounds; not measured running times.",
        "r": r, "blocks": blocks, "epsilon": str(epsilon),
        "a_schedule_over_lambda": str(a_schedule), "packing_exponent": str(packing_exponent),
        "incident_counts": incident_counts, "boundary_counts": boundary_counts,
        "crossing_count": crossing_count, "triangle_pair_counts": pair_counts,
        "A_squared": str(A2), "B_squared": str(B2), "J_squared": str(J2),
        "group_a_squared": str(a2), "A": A, "B": B, "J": J, "group_a": group_a,
        "gamma": gamma, "omega": omega, "B_strassen_squared": B_strassen_squared,
        "B_strassen_lower_squared": str(B_strassen_lower_squared),
        "B_strassen": B_strassen,
        "A_over_one_minus_gamma": A / (1 - gamma),
        "group_a_over_one_minus_gamma": group_a / (1 - gamma),
        "root_slope4_constant": root4,
        "known_geometric_eps1over720_polynomial_space": root1_old / (1 - gamma),
        "known_combination_slope3_eps1over720_polynomial_space": root3_old / (1 - gamma),
        "retuned_slope3_polynomial_space": root3 / (1 - gamma),
        "retuned_slope4_polynomial_space": root4 / (1 - gamma),
        "retuned_slope4_three_block_direct_time": root4 * B,
        "retuned_slope4_cached_strassen_time": root4 * B_strassen,
        "retuned_three_block_space": root4 * J}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results" / "mode_graph_validation.json")
    args = parser.parse_args()
    started = perf_counter()
    graph_results = verify_graphs()
    matrix_results = verify_rectangular_strassen()
    constants = schedule_constants()
    result = {"status": "PASS", "python": platform.python_version(),
              "optimized_python": not __debug__, "elapsed_seconds": round(perf_counter() - started, 4),
              "scope": "Exact finite mode-graph aggregation and ring multiplication checks, with separately labeled analytic constant evaluations.",
              "checks": CHECKS, "graph_cases": graph_results,
              "matrix_cases": matrix_results, "schedule_constants": constants}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "elapsed_seconds": result["elapsed_seconds"],
                      "graph_comparisons": len(graph_results), "checks": CHECKS,
                      "time_constant": constants["retuned_slope4_cached_strassen_time"],
                      "space_constant": constants["retuned_three_block_space"],
                      "output": str(args.output)}, sort_keys=True))


if __name__ == "__main__":
    main()

