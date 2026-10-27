#!/usr/bin/env python3
"""Independent exact checks for the two adaptive entropy norm arguments."""
from fractions import Fraction as F
from itertools import combinations
import json
import random
from pathlib import Path


def require(value, message):
    if not value:
        raise RuntimeError(message)


def partitions(k):
    vertices = set(range(3 * k))
    for a in combinations(range(3 * k), k):
        rest = sorted(vertices - set(a))
        for b in combinations(rest, k):
            c = vertices - set(a) - set(b)
            labels = [2] * (3 * k)
            for v in a:
                labels[v] = 0
            for v in b:
                labels[v] = 1
            yield labels


def z(labels, edge):
    a, b = sorted(labels[v] for v in edge)
    values = [0, 0, 0]
    if a != b:
        typ = {(0, 1): 0, (0, 2): 1, (1, 2): 2}[(a, b)]
        values = [-1, -1, -1]
        values[typ] = 2
    return values


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def covariance_check():
    rows = []
    for k in (2, 3, 4):
        r = 3 * k
        total = [0, 0, 0]
        count = 0
        for p in partitions(k):
            u = z(p, (0, 1))
            total[0] += dot(u, u)
            total[1] += dot(u, z(p, (0, 2)))
            total[2] += dot(u, z(p, (2, 3)))
            count += 1
        actual = [F(a, 9 * count) for a in total]
        expected = [F(4 * k, 3 * (r - 1)),
                    F(2 * k * (k - 2), 3 * (r - 1) * (r - 2)),
                    F(-8 * k * (k - 1), 3 * (r - 1) * (r - 2) * (r - 3))]
        require(actual == expected, "Covariance combinatorial enumeration")
        d, e, f = expected
        eigenvalues = [d + 2 * (r - 2) * e + F((r - 2) * (r - 3), 2) * f,
                       d + (r - 4) * e - (r - 3) * f,
                       d - 2 * e + f]
        formulas = [F(0), F(2 * k ** 3, (r - 1) * (r - 2)),
                    F(8 * k * (k - 1), 3 * (r - 2) * (r - 3))]
        require(eigenvalues == formulas, "Johnson eigenvalue formula")
        rows.append({"k": k, "partitions": count,
                     "covariance_entries": list(map(str, actual)),
                     "eigenvalues": list(map(str, eigenvalues))})
    for k in range(2, 1001):
        require(9 * k * k >= 4 * (3 * k - 1), "Eigenvalue ordering")
    return rows


def triangle_check(rng):
    tests = 0
    delta = F(3, 5)
    for k in (1, 2, 3):
        r = 3 * k
        ps = list(partitions(k))
        lam = F(2 * k ** 3, (r - 1) * (r - 2))
        a = (1 - delta / 3) * F(2 * k, r - 1)
        c2 = a * a * r * (r - 1) + F(4, 3) * delta * delta * lam
        for _ in range(24):
            h = {(i, j): rng.randint(0, 10) for i in range(r) for j in range(r) if i != j}
            norm2 = sum(v * v for v in h.values())
            best = None
            for p in ps:
                hs = [0, 0, 0]
                for (i, j), v in h.items():
                    q = tuple(sorted((p[i], p[j])))
                    if q[0] != q[1]:
                        hs[{(0, 1): 0, (0, 2): 1, (1, 2): 2}[q]] += v
                cost = sum(hs) - delta * min(hs)
                best = cost if best is None else min(best, cost)
            require(best * best <= c2 * norm2, "Adaptive triangle norm bound")
            tests += 1
    return {"exact_nonnegative_entropy_examples": tests,
            "delta": "3/5"}


MATCHINGS = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]


def quartet_tree(h, vertices):
    if len(vertices) == 1:
        return 0
    k = len(vertices) // 4
    blocks = [vertices[j * k:(j + 1) * k] for j in range(4)]
    inner = [quartet_tree(h, block) for block in blocks]
    hs = {(a, b): sum(h[i, j] + h[j, i] for i in blocks[a] for j in blocks[b])
          for a in range(4) for b in range(a + 1, 4)}
    total = sum(hs.values())
    costs = []
    for (a, b), (c, d) in MATCHINGS:
        costs.append(total - hs[a, b] - hs[c, d] +
                     max(hs[a, b] + max(inner[a], inner[b]),
                         hs[c, d] + max(inner[c], inner[d])))
    return min(costs)


def quartet_check(rng):
    tests = 0
    for r, c2 in [(4, F(26, 3)), (16, F(442, 3))]:
        for _ in range(100):
            h = {(i, j): rng.randint(0, 20) for i in range(r) for j in range(r) if i != j}
            cost = quartet_tree(h, list(range(r)))
            require(cost * cost <= c2 * sum(v * v for v in h.values()),
                    "Recursive quartet bound")
            tests += 1
    require(F(442, 3) / 170 == F(13, 15), "r=16 comparison")
    return {"examples": tests, "c4_squared": "26/3", "c16_squared": "442/3",
            "c16_squared_ratio_to_fixed_tree_170": "13/15"}


def main():
    rng = random.Random(77899)
    data = {"status": "PASS", "covariance": covariance_check(),
            "triangle": triangle_check(rng), "quartet": quartet_check(rng),
            "scope": "Exact finite checks complement the algebraic proofs; no SAT timings."}
    Path(__file__).with_name("adaptive_coefficient_audit.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
