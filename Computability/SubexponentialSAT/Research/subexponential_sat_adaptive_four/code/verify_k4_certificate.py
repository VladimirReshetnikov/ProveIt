#!/usr/bin/env python3
"""Exact, independent audit of the adaptive four-block contraction bound.

The three matchings each admit six linear cost forms, coming from two
matrix merges and the three choices of smallest matrix dimension.
This script checks the uniform averaging certificate over all 216 choices,
its simple combinatorial proof inequalities, and an exact sharpness witness.
It is not a SAT solver or an implementation of fast matrix multiplication.
"""
from fractions import Fraction as Q
from itertools import combinations, product
import json


EDGES = tuple(combinations(range(4), 2))
EDGE_INDEX = {e: i for i, e in enumerate(EDGES)}
MATCHINGS = ((0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2))


def edge(a, b):
    return EDGE_INDEX[tuple(sorted((a, b)))]


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), Q(0))


def forms(matching):
    a, b, c, d = matching
    crossing = {edge(a, c), edge(a, d), edge(b, c), edge(b, d)}
    result = []
    for x, y, z, t in ((a, b, c, d), (c, d, a, b)):
        internal = edge(x, y)
        base = [Q(i in crossing) for i in range(6)]
        base[internal] += Q(2, 5)
        result.append((tuple(base), internal, None))
        for endpoint in (x, y):
            discount = {edge(endpoint, z), edge(endpoint, t)}
            correction = [Q(0)] * 6
            correction[internal] = 1
            for i in discount:
                correction[i] -= 1
            row = [b0 + Q(3, 5) * delta for b0, delta in zip(base, correction)]
            result.append((tuple(row), internal, tuple(correction)))
    return result


def local_cost(rows, weighting):
    return min(max(dot(row, weighting) for row, _, _ in block) for block in rows)


def run():
    rows = [forms(matching) for matching in MATCHINGS]
    maxima = Q(0)
    extremizers = []
    by_b_count = {}
    analytic_checks = 0
    for choices in product(range(6), repeat=3):
        selected = [rows[j][choice] for j, choice in enumerate(choices)]
        mean = [sum((selected[j][0][i] for j in range(3)), Q(0)) / 3
                for i in range(6)]
        squared = dot(mean, mean)
        if squared > maxima:
            maxima, extremizers = squared, [choices]
        elif squared == maxima:
            extremizers.append(choices)

        z = [Q(0)] * 6
        for _, internal, _ in selected:
            z[internal] += 1
        if sorted(z) != [0, 0, 0, 1, 1, 1]:
            raise ArithmeticError("Three internal matching edges were not distinct")
        base = [2 + Q(2, 5) * value for value in z]
        corrections = [correction for _, _, correction in selected if correction is not None]
        k = len(corrections)
        total = [sum((correction[i] for correction in corrections), Q(0))
                 for i in range(6)]
        if any(dot(x, y) > 1 for x, y in combinations(corrections, 2)):
            raise ArithmeticError("Correction overlap bound failed")
        if dot(base, total) > -Q(8, 5) * k:
            raise ArithmeticError("Base/correction bound failed")
        if dot(total, total) > k * (k + 2):
            raise ArithmeticError("Correction norm bound failed")
        reconstructed = [base[i] + Q(3, 5) * total[i] for i in range(6)]
        if tuple(reconstructed) != tuple(3 * value for value in mean):
            raise ArithmeticError("Certificate did not reconstruct the cost vector")
        if dot(reconstructed, reconstructed) > dot(base, base) - Q(3, 25) * k:
            raise ArithmeticError("Analytic norm bound failed")
        by_b_count[k] = max(by_b_count.get(k, Q(0)), squared)
        analytic_checks += 1

    if maxima != Q(244, 75):
        raise ArithmeticError("Wrong exact certificate maximum")
    # Three edges incident to vertex zero have weight 4/5; the other three 2/3.
    witness = tuple(Q(4, 5) if a == 0 else Q(2, 3) for a, _ in EDGES)
    witness_cost = local_cost(rows, witness)
    witness_norm_squared = dot(witness, witness)
    if witness_cost ** 2 != Q(244, 75) * witness_norm_squared:
        raise ArithmeticError("Sharpness witness did not attain the bound")

    return {
        "status": "passed",
        "statement": "min_matching max_merge_form <= sqrt(244/75) * l2_norm",
        "choice_count": analytic_checks,
        "uniform_mean_squared_norm_maximum": str(maxima),
        "equality_choice_count": len(extremizers),
        "maxima_by_number_of_B_forms": {str(k): str(v) for k, v in by_b_count.items()},
        "equality_choices": extremizers,
        "sharpness_witness": {str(edge): str(value) for edge, value in zip(EDGES, witness)},
        "witness_cost": str(witness_cost),
        "witness_norm_squared": str(witness_norm_squared),
        "equal_cluster_directed_entropy_coefficient_squared": str(Q(61, 150)),
        "arithmetic": "Python fractions.Fraction; no floating-point decisions",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
