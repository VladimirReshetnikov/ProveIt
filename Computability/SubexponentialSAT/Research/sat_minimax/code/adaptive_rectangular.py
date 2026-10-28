#!/usr/bin/env python3
"""Exact support, convex-hull, and plan-selection certificates.

Python standard library only. This is a finite certificate/selection kernel,
not a SAT solver or an implementation of a fast matrix-multiplication backend.
All arithmetic used for the mathematical certificates is integral or Fraction.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import combinations, permutations
import json
from math import prod
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def data():
    return json.loads((ROOT / "data" / "menus.json").read_text())


def operations(n, plan):
    require(len(plan) == 3 and all(plan), "Three nonempty blocks required")
    require(sorted(x for a in plan for x in a) == list(range(n)),
            "Plan must partition the vertex labels")
    answer = []

    def build(a):
        if len(a) < 2:
            return
        cut = len(a) // 2
        left, right = a[:cut], a[cut:]
        build(left)
        build(right)
        answer.append((left, right, sorted(set(range(n)) - set(a))))

    for block in plan:
        build(block)
    answer.append(plan)
    require(len(answer) == n - 2, "Incorrect operation count")
    return answer


def supports(n, plan, backend):
    d, a, b = (backend[k] for k in ("denominator", "middle", "small"))
    forms = sorted(set(permutations((d, d, 0))))
    forms += sorted(set(permutations((d, a, b))))
    rows = []
    pair_class = {(0, 1): 0, (0, 2): 1, (1, 2): 2}
    for op in operations(n, plan):
        color = {v: j for j, part in enumerate(op) for v in part}
        for form in forms:
            row = []
            for x, y in combinations(range(n), 2):
                i, j = sorted((color[x], color[y]))
                row.append(0 if i == j else form[pair_class[i, j]])
            rows.append(tuple(row))
    require(len(rows) == 9 * (n - 2), "Incorrect support count")
    return rows


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def solve(matrix, rhs):
    """Exact Gaussian elimination; None denotes a singular system."""
    n = len(rhs)
    a = [[F(x) for x in row] + [F(y)] for row, y in zip(matrix, rhs)]
    for i in range(n):
        pivot = next((j for j in range(i, n) if a[j][i]), None)
        if pivot is None:
            return None
        a[i], a[pivot] = a[pivot], a[i]
        factor = a[i][i]
        a[i] = [x / factor for x in a[i]]
        for j in range(n):
            if j != i and a[j][i]:
                factor = a[j][i]
                a[j] = [x - factor*y for x, y in zip(a[j], a[i])]
    return [row[-1] for row in a]


def closest_gram(gram):
    """Closest-point squared norm and convex weights, with exact KKT check.

    For a singular active face, a minimum can be represented on a smaller
    face, which is also enumerated. All vectors here are nonnegative and
    nonzero, so the closest point cannot be zero.
    """
    n = len(gram)
    best = None
    best_weights = None
    for size in range(1, n + 1):
        for active in combinations(range(n), size):
            values = solve([[gram[i][j] for j in active] for i in active],
                           [1] * size)
            if values is None:
                continue
            total = sum(values)
            if total <= 0:
                continue
            weights = [x / total for x in values]
            if min(weights) < 0:
                continue
            value = 1 / total
            if best is None or value < best:
                best = value
                best_weights = [F(0)] * n
                for i, x in zip(active, weights):
                    best_weights[i] = x
    require(best is not None, "No closest point found")
    require(sum(best_weights) == 1 and min(best_weights) >= 0,
            "Invalid convex weights")
    for j, row in enumerate(gram):
        inner = sum(x*y for x, y in zip(row, best_weights))
        require(inner >= best, "Projection inequality failed")
        if best_weights[j]:
            require(inner == best, "Active-face equality failed")
    return best, best_weights


def certify(entry, payload=None):
    """Cover every support tuple, using rigorous integer upper-bound pruning.

    The sum of squared norms over pruned tuples is evaluated by distributivity,
    not estimated. The final checksum and tuple count therefore also check the
    complete Cartesian product. Only tuples exceeding the uniform-average
    threshold need a rational convex-hull calculation.
    """
    payload = data() if payload is None else payload
    n = entry["r"]
    backend = payload["backends"][entry["backend"]]
    menus = [supports(n, p, backend) for p in payload["menus"][str(n)]]
    require(len(menus) == 4, "This exhaustive driver expects four plans")
    norms = [[dot(v, v) for v in menu] for menu in menus]
    twice = {(i, j): [[2*dot(v, w) for w in menus[j]] for v in menus[i]]
             for i in range(4) for j in range(i + 1, 4)}

    def gram(ids):
        return [[norms[i][ids[i]] if i == j else
                 twice[min(i, j), max(i, j)][ids[min(i, j)]][ids[max(i, j)]] // 2
                 for j in range(4)] for i in range(4)]

    target = F(entry["R"])
    witness = entry["witness"]
    witness_gram = gram(witness)
    witness_value, witness_weights = closest_gram(witness_gram)
    require(witness_value <= target, "Invalid lower witness")
    if entry["sharp"]:
        require(witness_value == target, "Sharpness witness failed")
    largest = sum(sum(row) for row in witness_gram)
    threshold = (16 * target.numerator) // target.denominator
    require(largest >= threshold, "Witness insufficient for max-norm pruning")
    total = count = hull_count = direct_count = pair_skips = row_skips = 0
    n2, n3 = len(menus[2]), len(menus[3])
    d23 = twice[2, 3]
    row_max = [max(row) for row in d23]
    row_sum = [sum(row) for row in d23]
    d23_max, d23_sum = max(row_max), sum(row_sum)
    n0, n1 = norms[0], norms[1]
    for i in range(len(menus[0])):
        for j in range(len(menus[1])):
            base = n0[i] + n1[j] + twice[0, 1][i][j]
            c = [norms[2][k] + twice[0, 2][i][k] + twice[1, 2][j][k]
                 for k in range(n2)]
            e = [norms[3][l] + twice[0, 3][i][l] + twice[1, 3][j][l]
                 for l in range(n3)]
            emax, esum = max(e), sum(e)
            if base + max(c) + emax + d23_max <= threshold:
                count += n2 * n3
                total += n2*n3*base + n3*sum(c) + n2*esum + d23_sum
                pair_skips += 1
                continue
            for k in range(n2):
                start = base + c[k]
                if start + emax + row_max[k] <= threshold:
                    count += n3
                    total += n3*start + esum + row_sum[k]
                    row_skips += 1
                    continue
                for l, cross in enumerate(d23[k]):
                    value = start + e[l] + cross
                    total += value
                    count += 1
                    direct_count += 1
                    largest = max(largest, value)
                    if value > threshold:
                        closest, _ = closest_gram(gram((i, j, k, l)))
                        require(closest <= target, "Convex-hull upper bound failed")
                        hull_count += 1
    require(count == entry["expected_tuples"], "Tuple count mismatch")
    require(total == entry["expected_norm_sum"], "Norm checksum mismatch")
    require(largest == entry["expected_Q"], "Maximum norm mismatch")
    beta2 = 2 * target / (backend["denominator"]**2 * n*n)
    require(beta2 == F(entry["beta_squared"]), "Beta normalization failed")
    return {
        "backend": entry["backend"], "r": n, "plans": 4,
        "supports_per_plan": 9*(n-2), "tuples_covered": count,
        "direct_norm_evaluations": direct_count, "pruned_pairs": pair_skips,
        "pruned_rows": row_skips, "exact_hull_evaluations": hull_count,
        "maximum_uniform_sum_norm_squared": largest,
        "sum_of_all_tuple_norms_squared": total,
        "certified_hull_norm_squared": str(target),
        "sharp_for_menu": entry["sharp"], "beta_squared": str(beta2),
        "witness_gram": witness_gram,
        "witness_closest_norm_squared": str(witness_value),
        "witness_weights": [str(x) for x in witness_weights],
    }


def select_plan(n, dimensions, backend_name="classical"):
    """Choose the least expensive plan using exact integer powers.

    dimensions maps every (g,h), g != h, to a positive exact pair-list size.
    An allocation with an empty list has zero contribution and is skipped.
    """
    payload = data()
    require(str(n) in payload["menus"], "Unsupported group count")
    backend = payload["backends"][backend_name]
    for g in range(n):
        for h in range(n):
            if g != h:
                require(isinstance(dimensions.get((g, h)), int) and
                        not isinstance(dimensions[g, h], bool) and
                        dimensions[g, h] > 0, "Positive integer list sizes required")
    dims = [dimensions[g, h] * dimensions[h, g]
            for g, h in combinations(range(n), 2)]
    scores = []
    plans = payload["menus"][str(n)]
    for plan in plans:
        scores.append(max(prod(d**v for d, v in zip(dims, row))
                          for row in supports(n, plan, backend)))
    winner = min(range(len(plans)), key=lambda j: (scores[j], j))
    return {"plan": winner, "blocks": plans[winner],
            "integer_score": scores[winner],
            "score_power": backend["denominator"], "all_scores": scores}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", choices=("classical", "nine_fourths", "all"),
                        default="all")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = data()
    selected = [e for e in payload["certificates"]
                if args.backend == "all" or e["backend"] == args.backend]
    result = {"status": "PASS", "certificates": [certify(e, payload) for e in selected]}
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
