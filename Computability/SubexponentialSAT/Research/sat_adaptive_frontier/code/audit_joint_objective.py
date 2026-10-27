#!/usr/bin/env python3
"""Exact independent covariance enumeration for the six-cost objective."""
from fractions import Fraction as F
from itertools import combinations
import json
import math
from pathlib import Path
import random


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def partitions(k):
    r = 3 * k
    allv = set(range(r))
    for a in combinations(range(r), k):
        rest = allv - set(a)
        for b in combinations(sorted(rest), k):
            label = [2] * r
            for v in a:
                label[v] = 0
            for v in b:
                label[v] = 1
            yield label


def coefficient_numerator(labels, edge):
    a, b = sorted(labels[v] for v in edge)
    v = [0] * 6
    v[a] = 5
    v[b] = 5
    if a != b:
        v[3:] = [5, 5, 5]
        typ = {(0, 1): 0, (0, 2): 1, (1, 2): 2}[(a, b)]
        v[3 + typ] = 2
    total = sum(v)
    return [6 * a - total for a in v]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def main():
    rng = random.Random(98746)
    output = {"status": "PASS", "results": []}
    for k in [2, 3, 4, 5]:
        r = 3 * k
        totals = [0, 0, 0]
        count = 0
        ps = []
        # k=5 has 756,756 labelled partitions; use endpoint-color counting instead.
        if k == 5:
            from itertools import product
            for colors in product(range(3), repeat=4):
                used = [0, 0, 0]
                ways = 1
                for c in colors:
                    ways *= k - used[c]
                    used[c] += 1
                u = coefficient_numerator(colors, (0, 1))
                totals[0] += ways * dot(u, u)
                totals[1] += ways * dot(u, coefficient_numerator(colors, (0, 2)))
                totals[2] += ways * dot(u, coefficient_numerator(colors, (2, 3)))
                count += ways
        else:
            for p in partitions(k):
                ps.append(p)
                u = coefficient_numerator(p, (0, 1))
                totals[0] += dot(u, u)
                totals[1] += dot(u, coefficient_numerator(p, (0, 2)))
                totals[2] += dot(u, coefficient_numerator(p, (2, 3)))
                count += 1
        d, e, f = [F(x, 900 * count) for x in totals]
        eigen = [d + 2 * (r - 2) * e + F((r - 2) * (r - 3), 2) * f,
                 d + (r - 4) * e - (r - 3) * f,
                 d - 2 * e + f]
        l0, l1, l2 = eigen
        require(l1 > l0 and l1 >= l2 >= 0, "Eigenvalue ordering")
        a = (1 + F(17, 5) * F(2 * k, r - 1)) / 6
        c = 1 - l0 / l1
        norm2 = a * a * r * (r - 1) / c + F(5, 3) * l1
        beta2 = norm2 / (r * r)
        if k == 3:
            require([d, e, f] == [F(109, 120), F(869, 4200), F(-379, 2100)], "r9 entries")
            require(eigen == [F(3, 200), F(1059, 350), F(1319, 4200)], "r9 eigs")
        checked = 0
        if k <= 4:
            for _ in range(12):
                h = {(i, j): rng.randint(0, 9) for i in range(r) for j in range(r) if i != j}
                best = None
                for p in ps:
                    inc = [0, 0, 0]
                    cross = [0, 0, 0]
                    for (i, j), v in h.items():
                        aa, bb = sorted((p[i], p[j]))
                        inc[aa] += v
                        if aa != bb:
                            inc[bb] += v
                            cross[{(0, 1): 0, (0, 2): 1, (1, 2): 2}[(aa, bb)]] += v
                    costs = [F(a) for a in inc] + [sum(cross) - F(3, 5) * z for z in cross]
                    cost = max(costs)
                    best = cost if best is None else min(best, cost)
                require(best * best <= norm2 * sum(x * x for x in h.values()), "Joint max norm bound")
                checked += 1
        output["results"].append({"k": k, "r": r, "count": count,
                                   "covariance": list(map(str, [d, e, f])),
                                   "eigenvalues": list(map(str, eigen)),
                                   "mean_coefficient": str(a),
                                   "norm_squared": str(norm2),
                                   "beta_squared": str(beta2),
                                   "beta": math.sqrt(float(beta2)),
                                   "exact_inequality_examples": checked})
    (Path(__file__).resolve().parents[1] / "results" / "joint_objective_audit.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
