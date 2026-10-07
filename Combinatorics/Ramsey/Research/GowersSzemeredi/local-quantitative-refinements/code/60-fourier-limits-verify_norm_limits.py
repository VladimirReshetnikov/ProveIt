#!/usr/bin/env python3
"""Reproducible finite checks for the Gowers-norm limit article.

The compactness and asymptotic theorems have analytic proofs. This script
checks their finite counting and optimization ingredients. Exhaustive
optimization is exact; the trigonometric coefficient checks are explicitly
floating-point cross-checks of a separately proved formula.

Usage:
    python3 verify_norm_limits.py --output norm_verification.json

Only the Python standard library is required. Do not use python -O.
"""

from __future__ import annotations

import argparse
import cmath
from fractions import Fraction
from itertools import combinations, permutations, product
import json
import math
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def group_addition(moduli: tuple[int, ...]) -> list[list[int]]:
    elements = list(product(*(range(m) for m in moduli)))
    indices = {x: i for i, x in enumerate(elements)}
    return [
        [indices[tuple((x + y) % m for x, y, m in zip(a, b, moduli))]
         for b in elements]
        for a in elements
    ]


def energy_integer(values: list[int], addition: list[list[int]]) -> int:
    q = len(values)
    return sum(
        sum(values[j] * values[addition[j][h]] for j in range(q)) ** 2
        for h in range(q)
    )


def exact_bounded_extremum(moduli: tuple[int, ...]) -> dict:
    """Optimize U2^4 over every centered [-1,1] vector on this group.

    U2^4 is convex, so a maximum occurs at a polytope vertex: equal numbers
    of +1 and -1 and one zero. Translation invariance fixes the zero at 0.
    All remaining vertices are enumerated, with no heuristic pruning.
    """
    addition = group_addition(moduli)
    q = len(addition)
    require(q % 2 == 1, "Group must have odd order")
    best = -1
    best_positive = None
    maximizers = 0
    vertices = 0
    for positive in combinations(range(1, q), (q - 1) // 2):
        values = [-1] * q
        values[0] = 0
        for j in positive:
            values[j] = 1
        value = energy_integer(values, addition)
        vertices += 1
        if value > best:
            best = value
            best_positive = positive
            maximizers = 1
        elif value == best:
            maximizers += 1
    require(vertices == math.comb(q - 1, (q - 1) // 2), "Vertex count")
    return {
        "moduli": list(moduli),
        "group_order": q,
        "vertices_with_zero_fixed": vertices,
        "maximizers_with_zero_fixed": maximizers,
        "maximum_integer_energy": best,
        "exact_beta": str(Fraction(best, q ** 3)),
        "positive_indices_of_witness": list(best_positive),
        "arithmetic": "exact integers and rational numbers",
    }


def check_cyclic_models() -> list[dict]:
    results = []
    for q in range(3, 32, 2):
        n = (q - 1) // 2
        values = [0] + [1] * n + [-1] * n
        addition = group_addition((q,))
        correlations = [
            sum(values[j] * values[addition[j][h]] for j in range(q))
            for h in range(q)
        ]
        expected = [q - 1] + [q - 4 * h for h in range(1, n + 1)]
        expected += list(reversed(expected[1:]))
        require(correlations == expected, f"Autocorrelations q={q}")
        energy = sum(c * c for c in correlations)
        require(3 * energy == q ** 3 - 4 * q + 3, "Energy polynomial")
        beta = Fraction(energy, q ** 3)
        require(beta == Fraction(1, 3) - Fraction(4, 3 * q * q)
                + Fraction(1, q ** 3), "Lower model identity")
        results.append({"q": q, "autocorrelation_sums": correlations,
                        "integer_energy": energy, "U2_fourth_power": str(beta)})
    return results


def check_coefficient_polytope() -> list[dict]:
    results = []
    for q in range(3, 18, 2):
        roots = [cmath.exp(2j * math.pi * j / q) for j in range(q)]
        best = max(
            abs(1 + 2 * sum(roots[j] for j in positive)) / q
            for positive in combinations(range(1, q), (q - 1) // 2)
        )
        formula = 1 / (q * math.tan(math.pi / (2 * q)))
        require(abs(best - formula) < 5e-14, f"Fourier coefficient cap q={q}")
        results.append({
            "q": q, "enumerated_maximum": best, "cotangent_formula": formula,
            "absolute_error": abs(best - formula),
            "arithmetic": "floating-point check; formula proved analytically",
        })
    return results


def check_distinct_pair_bound() -> dict:
    checks = 0
    # All integer weight vectors of lengths 1 through 6 over {0,1,2};
    # their scaling is irrelevant to the homogeneous counting inequality.
    for length in range(1, 7):
        for weights in product(range(3), repeat=length):
            total = sum(weights)
            maximum = max(weights)
            for m in range(1, min(length, 4) + 1):
                ordered = sum(math.prod(weights[i] for i in indices)
                              for indices in permutations(range(length), m))
                lower = max(0, total - (m - 1) * maximum) ** m
                require(ordered >= lower, "Distinct sampling lower bound")
                elementary = sum(math.prod(weights[i] for i in indices)
                                 for indices in combinations(range(length), m))
                require(ordered == math.factorial(m) * elementary,
                        "Ordered/unordered multiplicity")
                checks += 1
    for m in range(1, 101):
        require(math.factorial(2 * m) >= math.factorial(m) * (m + 1) ** m,
                "Factorial tail simplification")
    return {"exact_weight_vector_and_m_checks": checks,
            "factorial_checks": 100,
            "arithmetic": "exact integers",
            "status": "passed"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    pair_cap = 4 / math.pi ** 2
    cap = 2 * (pair_cap ** 2 + (0.5 - pair_cap) ** 2)
    report = {
        "status": "passed",
        "scope": "Finite checks supplement, and do not replace, analytic proofs.",
        "asymptotic_upper_bound": float(cap),
        "coefficient_polytope": check_coefficient_polytope(),
        "distinct_pair_counting": check_distinct_pair_bound(),
        "cyclic_lower_models": check_cyclic_models(),
        "exact_bounded_extrema": [],
    }
    for q in range(3, 18, 2):
        result = exact_bounded_extremum((q,))
        require(result["maximum_integer_energy"] == (q ** 3 - 4 * q + 3) // 3,
                f"Cyclic extrema agree with witness q={q}")
        report["exact_bounded_extrema"].append(result)
    rank_two = exact_bounded_extremum((3, 3))
    require(rank_two["exact_beta"] == "56/243", "F3^2 exact extremum")
    report["exact_bounded_extrema"].append(rank_two)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print("All finite checks passed.")
    print(f"Asymptotic upper endpoint: {float(cap):.16f}")
    print("Exact bounded extrema: C_q for odd q=3,...,17; C_3 x C_3.")
    print(f"Report: {args.output}")


if __name__ == "__main__":
    main()
