#!/usr/bin/env python3
"""Deterministic exact-rational checks for the quantitative IFT reference code.

All pass/fail comparisons use integers and Fraction, never floating point.
Finite experiments do not prove universal hypotheses or iPRA derivability.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from math import isqrt
from pathlib import Path

from implicit_solver import (
    CIRCLE, SYSTEM, Trace, add, clip_box, clock_shift, distance, dyadic,
    example_problems, floor_dyadic, identity, matrix_add, matrix_apply,
    matrix_mul, matrix_neg, matrix_norm, matrix_sub, neumann, oracle,
    rational_inverse, solve, sub, sup, vector,
)


class Checks:
    def __init__(self):
        self.counts = Counter()

    def check(self, category: str, assertion: bool, detail: str = ""):
        self.counts[category] += 1
        if not assertion:
            raise AssertionError(f"{category}: {detail}")


def qtext(value: Q) -> str:
    return str(value)


def sqrt_bracket(value: Q, precision: int) -> tuple[Q, Q]:
    scale = 1 << precision
    numerator = (value.numerator * scale * scale) // value.denominator
    root = isqrt(numerator)
    return Q(root, scale), Q(root + 1, scale)


def validate_trace(problem, trace: Trace, checks: Checks):
    k, p, eps, x = trace.demand, trace.precision, trace.epsilon, trace.parameter
    checks.check("fixed_iteration_count", trace.iterations == k + trace.shift + 4)
    checks.check("clock_dominates_diameter", 2 * problem.root_radius <= 1 << trace.shift)
    checks.check("precision_schedule", p == k + 5 and eps == 2 * dyadic(p))
    checks.check("initial_center", trace.states[0] == problem.root_center)
    for before, after in zip(trace.states, trace.states[1:]):
        exact_h = problem.exact(x, before)
        observed_h = oracle(problem, x, before, p, trace.oracle_mode)
        target = sub(before, exact_h)
        rounded = tuple(floor_dyadic(v, p) for v in sub(before, observed_h))
        checks.check("oracle_error", distance(observed_h, exact_h) <= dyadic(p))
        checks.check("floor_error", distance(rounded, sub(before, observed_h)) <= dyadic(p))
        checks.check("exact_step_in_box", problem.in_root_box(target))
        checks.check("rounded_step_in_box", problem.in_root_box(after))
        checks.check("local_step_defect", distance(after, target) <= eps)
        U, V = problem.jacobian(x, before)
        checks.check("sampled_derivative_contraction",
                     matrix_norm(matrix_sub(identity(len(V)), V)) <= problem.actual_contraction_bound)
        checks.check("sampled_parameter_gain", matrix_norm(U) <= problem.parameter_gain)
    residual = sup(problem.exact(x, trace.result))
    checks.check("terminal_residual", residual <= 4 * eps,
                 f"{problem.name} k={k} mode={trace.oracle_mode}: {residual} > {4*eps}")
    if problem is CIRCLE:
        lo, hi = sqrt_bracket(1 - x[0] ** 2, k + 12)
        checks.check("independent_circle_root_bracket", lo * lo <= 1 - x[0] ** 2 <= hi * hi)
        checks.check("circle_root_accuracy", max(abs(trace.result[0] - lo), abs(trace.result[0] - hi))
                     <= dyadic(k) + dyadic(k + 12))


def compare_traces(problem, coarse: Trace, fine: Trace, checks: Checks):
    checks.check("comparison_order", coarse.demand <= fine.demand)
    length = coarse.iterations
    tail = fine.states[fine.iterations - length:]
    dx = distance(coarse.parameter, fine.parameter)
    local_noise = coarse.epsilon + fine.epsilon + problem.parameter_gain * dx
    E0 = distance(coarse.states[0], tail[0])
    checks.check("comparison_initial_diameter", E0 <= 2 * problem.root_radius)
    for j in range(length):
        old = distance(coarse.states[j], tail[j])
        new = distance(coarse.states[j + 1], tail[j + 1])
        checks.check("comparison_step_recurrence", new <= old / 2 + local_noise)
        checks.check("cleared_qf_error_invariant",
                     (1 << (j + 1)) * new <= E0 + 2 * local_noise * ((1 << (j + 1)) - 1))
    final = distance(coarse.result, fine.result)
    bound = 3 * coarse.epsilon + 2 * fine.epsilon + 2 * problem.parameter_gain * dx
    checks.check("pairwise_cauchy_or_lipschitz_bound", final <= bound)


def validate_neumann(problem, trace: Trace, checks: Checks):
    U, V = problem.jacobian(trace.parameter, trace.result)
    unit = identity(len(V))
    E = matrix_sub(unit, V)
    inverse = rational_inverse(V)
    checks.check("independent_inverse_left", matrix_mul(inverse, V) == unit)
    checks.check("independent_inverse_right", matrix_mul(V, inverse) == unit)
    checks.check("inverse_norm_bound", matrix_norm(inverse) <= 2)
    G = matrix_neg(matrix_mul(inverse, U))
    checks.check("graph_derivative_linear_equation", matrix_add(matrix_mul(V, G), U)
                 == tuple(tuple(Q(0) for _ in row) for row in U))
    if problem is CIRCLE:
        checks.check("circle_derivative_formula", G == ((-trace.parameter[0] / trace.result[0],),))
    else:
        y1, y2 = trace.result
        determinant = 1 + y2 / 4 - y1 * y1 / 8
        direct = (((1 - y1 / 8) / determinant,),
                  ((Q(1, 2) + y2 / 8 - y1 / 2) / determinant,))
        checks.check("system_derivative_formula", G == direct)
    for terms in (0, 1, 2, 4, 8, 16, 32):
        total, power = neumann(E, terms)
        residual = matrix_sub(unit, power)
        checks.check("neumann_left_identity", matrix_mul(V, total) == residual)
        checks.check("neumann_right_identity", matrix_mul(total, V) == residual)
        checks.check("neumann_power_bound", matrix_norm(power) <= dyadic(terms))
        approximate_G = matrix_neg(matrix_mul(total, U))
        checks.check("neumann_derivative_error", matrix_norm(matrix_sub(G, approximate_G))
                     <= 2 * problem.parameter_gain * dyadic(terms))


def validate_taylor(problem, left: Trace, right: Trace, checks: Checks):
    dx = sub(right.parameter, left.parameter)
    dy = sub(right.result, left.result)
    U, V = problem.jacobian(left.parameter, left.result)
    Hdiff = sub(problem.exact(right.parameter, right.result),
                problem.exact(left.parameter, left.result))
    linear = add(matrix_apply(U, dx), matrix_apply(V, dy))
    remainder = sub(Hdiff, linear)
    if problem is CIRCLE:
        exact_remainder = ((dx[0] ** 2 + dy[0] ** 2) / 2,)
    else:
        exact_remainder = (dy[0] * dy[1] / 4, dy[0] ** 2 / 4)
    checks.check("polynomial_taylor_identity", remainder == exact_remainder)
    joint_step = max(sup(dx), sup(dy))
    checks.check("polynomial_taylor_bound",
                 sup(remainder) <= problem.taylor_quadratic_bound * joint_step ** 2)
    G = matrix_neg(matrix_mul(rational_inverse(V), U))
    derivative_remainder = sub(dy, matrix_apply(G, dx))
    bound = 2 * (sup(problem.exact(right.parameter, right.result))
                 + sup(problem.exact(left.parameter, left.result))
                 + problem.taylor_quadratic_bound * joint_step ** 2)
    checks.check("finite_derivative_remainder_bound", sup(derivative_remainder) <= bound)


def primitive_edge_checks(checks: Checks):
    for radius in (Q(1, 64), Q(1, 3), Q(1, 2), Q(1), Q(3, 2), Q(2), Q(4097, 3)):
        shift = clock_shift(radius)
        checks.check("clock_edge_cases", 2 * radius <= (1 << shift)
                     and (shift == 0 or (1 << (shift - 1)) < 2 * radius))
    for value in (Q(-17, 13), Q(-1, 3), Q(-1, 64), Q(0), Q(1, 64), Q(1, 3), Q(17, 13)):
        for p in (0, 1, 5, 17, 64):
            rounded = floor_dyadic(value, p)
            checks.check("negative_and_positive_floor", rounded <= value < rounded + dyadic(p))
    center, radius, p = vector([0]), Q(1, 3), 5
    for sign in (-1, 1):
        target = vector([sign * radius])
        noisy = vector([target[0] + sign * dyadic(p)])
        rounded = vector([floor_dyadic(noisy[0], p)])
        clipped = clip_box(rounded, center, radius)
        checks.check("clipping_is_exercised", clipped != rounded)
        checks.check("clipping_keeps_rational_endpoint", clipped == target)
        checks.check("clipping_nonexpansive_at_boundary", distance(clipped, target) <= distance(rounded, target))


def run_validation() -> dict:
    checks = Checks()
    primitive_edge_checks(checks)
    modes = ("exact", "plus", "minus", "signed")
    cache = {}
    case_reports = []
    for problem in example_problems():
        grid = tuple((Q(j, 4) * problem.parameter_radius,) for j in range(-4, 5))
        max_residual_ratio = Q(0)
        for x in grid:
            for k in range(65):
                for mode in modes:
                    trace = solve(problem, x, k, mode)
                    cache[(problem.name, x, k, mode)] = trace
                    validate_trace(problem, trace, checks)
                    max_residual_ratio = max(max_residual_ratio,
                                             sup(problem.exact(x, trace.result)) / trace.epsilon)
        mode_pairs = (("exact", "plus"), ("plus", "minus"),
                      ("minus", "signed"), ("signed", "exact"))
        for x in grid:
            for k in (0, 1, 4, 8, 16, 32, 48, 60):
                for ell in (k, k + 1, k + 4):
                    for first, second in mode_pairs:
                        compare_traces(problem, cache[(problem.name, x, k, first)],
                                       cache[(problem.name, x, ell, second)], checks)
        for x, other in zip(grid, grid[1:]):
            for k in (0, 4, 16, 32, 60):
                for first, second in mode_pairs:
                    compare_traces(problem, cache[(problem.name, x, k, first)],
                                   cache[(problem.name, other, k + 4, second)], checks)
        for x in (grid[0], grid[4], grid[-1]):
            for k in (8, 32, 64):
                validate_neumann(problem, cache[(problem.name, x, k, "signed")], checks)
        for x in ((Q(0),), (problem.parameter_radius / 2,)):
            for h in (dyadic(10), dyadic(16)):
                left = solve(problem, x, 64, "plus")
                right = solve(problem, add(x, (h,)), 64, "minus")
                validate_taylor(problem, left, right, checks)
        sample = cache[(problem.name, grid[-1], 32, "signed")]
        case_reports.append({
            "problem": problem.name,
            "parameter_grid": [qtext(x[0]) for x in grid],
            "demand_range_inclusive": [0, 64],
            "oracle_modes": list(modes),
            "trace_count": len(grid) * 65 * len(modes),
            "actual_contraction_bound": qtext(problem.actual_contraction_bound),
            "max_terminal_residual_div_epsilon": qtext(max_residual_ratio),
            "sample_k32": {"x": [qtext(v) for v in sample.parameter],
                           "y": [qtext(v) for v in sample.result],
                           "iterations": sample.iterations,
                           "residual": qtext(sup(problem.exact(sample.parameter, sample.result)))},
        })
    source_dir = Path(__file__).resolve().parent
    return {
        "status": "passed",
        "arithmetic": "Python integers and fractions.Fraction; no floating-point pass/fail checks",
        "proof_status": "Finite computational validation, not an iPRA derivation or a Lean proof",
        "scope": "Two fixed polynomial providers, finite parameter/precision grids, adversarial bounded oracle errors",
        "schedule": {"precision": "p(k) = k+5", "step_error": "epsilon(k) = 2^(-(k+4))",
                     "iterations": "N(k) = k+s+4", "shift": "least s>=0 with 2*r<=2^s, bounded by numerator(2*r)"},
        "comparison_bound": "3*epsilon(k) + 2*epsilon(l) + 2*M*||x-xprime||, l>=k",
        "total_assertions": sum(checks.counts.values()),
        "assertions_by_category": dict(sorted(checks.counts.items())),
        "cases": case_reports,
        "source_sha256": {name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
                          for name in ("implicit_solver.py", "validate.py")},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "validation" / "python_validation.json")
    args = parser.parse_args()
    report = run_validation()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "total_assertions": report["total_assertions"],
                      "traces": sum(case["trace_count"] for case in report["cases"]),
                      "output": str(args.output)}, sort_keys=True))


if __name__ == "__main__":
    main()
