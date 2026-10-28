#!/usr/bin/env python3
"""Exact lower bound for weighted norm certificates on the fixed nine plans.

Standard-library only. This is not a lower bound for SAT, all tensor
contractions, or even the true adaptive minimum of these plans. It bounds
only the weighted-average Euclidean-support proof method on this fixed menu.
The main support certificate must be replayed separately.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import combinations, permutations
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TRIPLES = sorted(set(permutations((1_400_007, 1_400_007, 0))) |
                 set(permutations((1_400_000, 1_175_014, 750_000))))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reconstruct_supports(r, plan):
    require(len(plan) == 3 and all(plan), "Invalid block count")
    require(sorted(x for block in plan for x in block) == list(range(r)),
            "Plan must partition the vertex set")
    parts = []
    universe = set(range(r))

    def visit(block):
        if len(block) < 2:
            return
        cut = len(block) // 2
        left, right = block[:cut], block[cut:]
        visit(left)
        visit(right)
        parts.append((left, right, sorted(universe - set(block))))

    for block in plan:
        visit(block)
    parts.append(plan)
    rows = []
    for partition in parts:
        label = {vertex: k for k, block in enumerate(partition) for vertex in block}
        for triple in TRIPLES:
            coeff = dict(zip(((0, 1), (0, 2), (1, 2)), triple))
            rows.append(tuple(0 if label[x] == label[y] else
                              coeff[tuple(sorted((label[x], label[y])))]
                              for x, y in combinations(range(r), 2)))
    require(len(rows) == 9 * (r - 2), "Wrong support count")
    return rows


def dot(left, right):
    return sum(a * b for a, b in zip(left, right))


def sqrt_interval(value, digits=55):
    require(value >= 0, "Negative square-root input")
    scale = 10 ** digits
    lower = isqrt(value.numerator * scale * scale // value.denominator)
    return F(lower, scale), F(lower + 1, scale)


def atan_interval(inverse, terms=120):
    partial = sum((F((-1) ** k, (2 * k + 1) * inverse ** (2 * k + 1))
                   for k in range(terms)), F(0))
    next_term = F((-1) ** terms, (2 * terms + 1) * inverse ** (2 * terms + 1))
    return min(partial, partial + next_term), max(partial, partial + next_term)


def coefficient_interval(u):
    # C = (pi/ln 2) sqrt(U/(25 eta_0)), eta_0=301/20000.
    a, b = atan_interval(5)
    c, d = atan_interval(239)
    pi = (16 * a - 4 * d, 16 * b - 4 * c)
    terms = 140
    lower = 2 * sum((F(1, (2 * k + 1) * 3 ** (2 * k + 1))
                     for k in range(terms)), F(0))
    tail = 2 * F(1, (2 * terms + 1) * 3 ** (2 * terms + 1)) / (1 - F(1, 9))
    ln2 = (lower, lower + tail)
    lo, hi = sqrt_interval(u / (25 * F(301, 20000)))
    return pi[0] * lo / ln2[1], pi[1] * hi / ln2[0]


def check(certificate, gram_data):
    r = certificate["r"]
    require(r == 10 and certificate["q"] == 9, "Unexpected finite menu")
    scale = certificate["support_scale"]
    require(scale == 1_400_000, "Unexpected support scale")
    menus = [reconstruct_supports(r, plan) for plan in certificate["plans"]]
    indices = gram_data["chosen_supports"]
    require(indices == [67, 67, 69, 69, 67, 69, 67, 69, 69],
            "Unexpected simultaneous witness")
    vectors = [menu[index] for menu, index in zip(menus, indices)]
    gram = [[dot(x, y) for y in vectors] for x in vectors]
    require(gram == gram_data["gram"], "Stored Gram matrix disagrees with supports")
    # Exact LDL^T factorization also certifies positive definiteness.
    lower = [[F(int(i == j)) for j in range(9)] for i in range(9)]
    pivots = []
    for i in range(9):
        pivot = F(gram[i][i]) - sum(lower[i][k] ** 2 * pivots[k] for k in range(i))
        require(pivot > 0, "Gram matrix is not positive definite")
        pivots.append(pivot)
        for j in range(i + 1, 9):
            lower[j][i] = (F(gram[j][i]) - sum(
                lower[j][k] * lower[i][k] * pivots[k] for k in range(i))) / pivot

    denominator = gram_data["mixing_denominator"]
    weights = [F(a, denominator) for a in gram_data["mixing_weights"]]
    require(len(weights) == 9 and sum(weights) == 1 and all(a > 0 for a in weights),
            "Invalid positive stationary mixture")
    u_lower = F(gram_data["U"])
    mu = u_lower * scale * scale
    for row in gram:
        require(sum(a * b for a, b in zip(row, weights)) == mu,
                "Exact Gram stationarity fails")
    # G is a Gram matrix by reconstruction. Thus it is positive semidefinite.
    # For any w with sum(w)=1, (w-w*)^T G(w-w*)>=0 and G w*=mu 1 imply
    # w^T G w>=mu. No floating-point eigenvalue test is needed.
    main_weights = [F(a, certificate["mixing_denominator"])
                    for a in certificate["mixing_weights"]]
    require(sum(main_weights) == 1, "Main mixture does not sum to one")
    u_upper = sum((main_weights[i] * main_weights[j] * gram[i][j]
                   for i in range(9) for j in range(9)), F(0)) / (scale * scale)
    require(2 * u_upper / (r * r) == F(certificate["beta_squared"]),
            "Simultaneous tuple fails to attain main norm certificate")
    lower_interval = coefficient_interval(u_lower)
    upper_interval = coefficient_interval(u_upper)
    gap = upper_interval[1] - lower_interval[0]
    require(F(0) <= u_upper - u_lower, "Impossible quadratic gap")
    require(gap < F(43, 10 ** 11), "Coefficient gap is not below 4.3e-10")
    return {
        "status": "PASS",
        "scope": "Weighted Euclidean-norm averaging for the fixed nine-plan menu only",
        "chosen_supports": indices,
        "gram_entries_reconstructed": 81,
        "positive_LDL_pivots_checked": len(pivots),
        "stationarity_equalities": 9,
        "positive_stationary_weights": True,
        "main_tuple_exactly_attains_certificate": True,
        "lower_U": str(u_lower),
        "upper_U": str(u_upper),
        "U_gap": str(u_upper - u_lower),
        "lower_C_interval": [str(x) for x in lower_interval],
        "upper_C_interval": [str(x) for x in upper_interval],
        "certified_C_gap_bound": "43/100000000000",
        "display_only": {
            "lower_C": float(lower_interval[0]),
            "upper_C": float(upper_interval[0]),
            "C_gap_upper": float(gap),
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=ROOT / "data/support_consistency_certificate.json")
    parser.add_argument("--gram", type=Path,
                        default=ROOT / "data/exact_optimal_weights.json")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/weight_lower_bound.json")
    args = parser.parse_args()
    certificate = json.loads(args.certificate.read_text())
    gram_data = json.loads(args.gram.read_text())
    result = check(certificate, gram_data)
    # Two explicit negative controls; no assertions that python -O can remove.
    bad = json.loads(json.dumps(gram_data))
    bad["gram"][0][0] += 1
    try:
        check(certificate, bad)
    except ValueError:
        pass
    else:
        raise ValueError("Corrupted Gram entry was accepted")
    bad = json.loads(json.dumps(gram_data))
    bad["mixing_weights"][0] += 1
    try:
        check(certificate, bad)
    except ValueError:
        pass
    else:
        raise ValueError("Corrupted stationary mixture was accepted")
    result["negative_controls_rejected"] = ["Gram entry +1", "stationary weight +1"]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"],
                      "display_only": result["display_only"],
                      "certified_C_gap_bound": result["certified_C_gap_bound"]}, indent=2))


if __name__ == "__main__":
    main()
