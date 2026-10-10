#!/usr/bin/env python3
"""Exact finite audits for the effective Lerch zero theorem.

The all-index theorem is proved in the accompanying TeX text.  This program
independently isolates the rational finite-product polynomial roots by Sturm
arithmetic and checks exact gamma-moment controls.  It uses no floating-point
acceptance criteria and does not pretend to certify numerical Lerch roots.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path


def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def derivative(p):
    return [F(i) * p[i] for i in range(1, len(p))] or [F(0)]


def evaluate(p, x):
    value = F(0)
    for a in reversed(p):
        value = value * x + a
    return value


def remainder(p, q):
    r = p[:]
    while len(r) >= len(q) and r != [0]:
        degree = len(r) - len(q)
        scale = r[-1] / q[-1]
        for i, a in enumerate(q):
            r[degree + i] -= scale * a
        trim(r)
    return r


def sturm(p):
    sequence = [p[:], derivative(p)]
    while sequence[-1] != [0]:
        r = [-a for a in remainder(sequence[-2], sequence[-1])]
        if r == [0]:
            break
        positive_scale = abs(r[-1])
        sequence.append([a / positive_scale for a in r])
    return sequence


def finite_product_polynomial(n):
    p = [F(0)] * n + [F(1)]
    for j in range(1, n):
        dp = derivative(p)
        p = [a + (dp[i] / j if i < len(dp) else 0)
             for i, a in enumerate(p)]
    return p


def isolate_nonzero_roots(p, left, right):
    sequence = sturm(p)

    @lru_cache(maxsize=None)
    def variations(x):
        signs = []
        for q in sequence:
            y = evaluate(q, x)
            if y:
                signs.append(1 if y > 0 else -1)
        return sum(a != b for a, b in zip(signs, signs[1:]))

    def count(a, b):
        return variations(a) - variations(b)

    assert count(left, right) == len(p) - 1
    queue = [(left, right, len(p) - 1)]
    intervals = []
    while queue:
        a, b, number = queue.pop()
        if not number:
            continue
        if number == 1 and b - a <= F(1, 4096):
            intervals.append((a, b))
            continue
        midpoint = (a + b) / 2
        left_number = count(a, midpoint)
        right_number = count(midpoint, b)
        assert left_number + right_number == number
        queue.append((a, midpoint, left_number))
        queue.append((midpoint, b, right_number))
    return sorted(intervals), len(sequence)


def fraction_record(value):
    return {"numerator": str(value.numerator),
            "denominator": str(value.denominator)}


def mesh_audit(n):
    p = finite_product_polynomial(n)
    assert len(p) == n + 1 and p[-1] == 1
    assert p[0] == 0 and p[1] != 0
    # All roots are nonpositive by the elementary operator proof.  Their
    # absolute sum is n H_(n-1), giving the rational enclosure below.
    harmonic = sum((F(1, j) for j in range(1, n)), F(0))
    left = -F((n * harmonic).__ceil__() + 1)
    intervals, sturm_length = isolate_nonzero_roots(p[1:], left, F(0))
    intervals.append((F(0), F(0)))
    assert len(intervals) == n
    lower_mesh = min(b[0] - a[1]
                     for a, b in zip(intervals, intervals[1:]))
    delta = F(1, (3 * n) ** (n - 2))
    assert lower_mesh >= delta
    threshold = 576 * n * n * (3 * n) ** (2 * n - 4)
    certified_threshold = max(
        256, (F(24 * n) / lower_mesh) ** 2).__ceil__()
    assert certified_threshold >= 256
    assert F(certified_threshold) >= (F(24 * n) / lower_mesh) ** 2
    if certified_threshold > 256:
        assert F(certified_threshold - 1) < (F(24 * n) / lower_mesh) ** 2
    return {
        "n": n,
        "status": "EXACT_STURM_FINITE_PRODUCT_ONLY",
        "polynomial_coefficients_ascending": [fraction_record(a) for a in p],
        "sturm_sequence_length": sturm_length,
        "isolating_intervals": [
            {"lower": fraction_record(a), "upper": fraction_record(b)}
            for a, b in intervals],
        "certified_mesh_lower_bound": fraction_record(lower_mesh),
        "theorem_delta_n": fraction_record(delta),
        "mesh_bound_passed": True,
        "theorem_K_n": str(threshold),
        "threshold_from_certified_finite_product_mesh": str(certified_threshold),
    }


def gamma_moment(k, power):
    result = F(1)
    if power >= 0:
        for j in range(1, power + 1):
            result *= F(k + j, k)
    else:
        assert -power <= k
        for j in range(-power):
            result *= F(k, k - j)
    return result


def gamma_control(m, k):
    value = (gamma_moment(k, 2 * m) + gamma_moment(k, -2 * m)
             - 2 * gamma_moment(k, m) - 2 * gamma_moment(k, -m) + 2)
    return value


def run(max_n):
    meshes = [mesh_audit(n) for n in range(2, max_n + 1)]
    gamma_checks = []
    for m in (1, 2, 4, 8, 16, 32):
        k = 16 * m * m
        value = gamma_control(m, k)
        assert F(0) < value < F(2, 3)
        gamma_checks.append({
            "m": m, "k": k,
            "squared_Cauchy_Schwarz_bound": fraction_record(value),
            "strictly_below_two_thirds": True})
    negative_value = gamma_control(2, 4)
    assert negative_value > F(2, 3)
    return {
        "schema": "proveit.lerch-effective-audit.v1",
        "method": "Python standard-library exact Fraction and Sturm arithmetic",
        "acceptance_uses_floating_point": False,
        "proof_scope": (
            "Finite implementation audit only. The all-index mesh, uniform "
            "Lerch transfer, zero completeness, and joint limit are ordinary "
            "mathematical theorems in lerch_effective.tex."),
        "finite_product_mesh_checks": meshes,
        "exact_gamma_moment_positive_controls": gamma_checks,
        "gamma_moment_negative_control": {
            "m": 2, "k": 4,
            "outside_hypothesis": "4 < 16 * 2^2",
            "squared_Cauchy_Schwarz_bound": fraction_record(negative_value),
            "two_thirds_bound_rejected": True},
        "all_assertions_passed": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=12)
    parser.add_argument("--output", type=Path,
                        default=Path("lerch_effective_verification.json"))
    args = parser.parse_args()
    if args.max_n < 2:
        parser.error("--max-n must be at least 2")
    result = run(args.max_n)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "all_assertions_passed": result["all_assertions_passed"],
        "finite_product_indices": [2, args.max_n],
        "exact_gamma_positive_controls": 6,
        "negative_control_rejected": True,
        "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
