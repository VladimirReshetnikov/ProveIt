#!/usr/bin/env python3
"""Exact-rational reference implementation for finite-cloud projection.

No floating point, numerical optimizer, or real-equality oracle is used.
The tests validate these finite examples, not universal iPRA derivability.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import json


def linf(x, y):
    return max((abs(a - b) for a, b in zip(x, y)), default=Q(0))


def sqdist(x, y):
    return sum(((a - b) ** 2 for a, b in zip(x, y)), Q(0))


def midpoint(x, y):
    return tuple((a + b) / 2 for a, b in zip(x, y))


def pick(cloud, anchor):
    assert cloud
    # Python min returns the first minimizing index, as specified in the paper.
    return cloud[min(range(len(cloud)), key=lambda i: sqdist(cloud[i], anchor))]


def hausdorff(s, t):
    assert s and t
    return max(max(min(linf(x, y) for y in t) for x in s),
               max(min(linf(x, y) for x in s) for y in t))


def midpoint_defect(s):
    assert s
    return max(min(linf(w, midpoint(x, y)) for w in s) for x in s for y in s)


def compositions(total, slots):
    """All weak compositions; its bounded cube enumeration is PR as well."""
    assert slots >= 1 and total >= 0
    if slots == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, slots - 1):
                yield (first,) + rest


def round_simplex(weights, denominator):
    assert denominator >= 1 and weights and sum(weights) == 1
    assert all(a >= 0 for a in weights)
    nums = [int((denominator * a).__floor__()) for a in weights[:-1]]
    nums.append(denominator - sum(nums))
    assert min(nums) >= 0 and sum(nums) == denominator
    return tuple(nums)


def weighted_point(vertices, nums, denominator):
    assert sum(nums) == denominator
    return tuple(sum((Q(a, denominator) * v[i] for a, v in zip(nums, vertices)), Q(0))
                 for i in range(len(vertices[0])))


def hull_cloud(vertices, denominator):
    return tuple(weighted_point(vertices, a, denominator)
                 for a in compositions(denominator, len(vertices)))


def finite_pair_check(s, t, z, w, bound=1):
    d = len(z)
    ell = 4 * d * bound
    h, es, et = hausdorff(s, t), midpoint_defect(s), midpoint_defect(t)
    x, y = pick(s, z), pick(t, z)
    assert sqdist(x, y) <= 2 * ell * (es + et + h)
    yw = pick(t, w)
    assert sqdist(x, yw) <= 4 * ell * (es + et + h) + 4 * sqdist(z, w)


def segment_project(z, a, b):
    direction = tuple(y - x for x, y in zip(a, b))
    den = sqdist(a, b)
    if den == 0:
        return a
    t = sum(((zi - ai) * vi for zi, ai, vi in zip(z, a, direction)), Q(0)) / den
    t = min(Q(1), max(Q(0), t))
    return tuple(ai + t * vi for ai, vi in zip(a, direction))


def run_validation():
    counts = {"finite_pair_cases": 0, "rounding_cases": 0,
              "midpoint_certificate_cases": 0, "transfer_certificate_cases": 0}
    base = tuple((Q(i),) for i in [-1, 0, 1])
    clouds = [c for k in range(1, 4) for c in combinations(base, k)]
    anchors = [(Q(i, 2),) for i in range(-2, 3)]
    for s, t, z, w in product(clouds, clouds, anchors, anchors):
        finite_pair_check(s, t, z, w)
        counts["finite_pair_cases"] += 1

    base2 = tuple((Q(i), Q(j)) for i, j in product([-1, 0, 1], repeat=2))
    clouds2 = list(combinations(base2, 2))[::4] + list(combinations(base2, 3))[::9]
    anchors2 = [(Q(0), Q(0)), (Q(1, 2), Q(-1, 2)), (Q(-1), Q(1))]
    for s, t, z, w in product(clouds2, clouds2, anchors2, anchors2):
        finite_pair_check(s, t, z, w)
        counts["finite_pair_cases"] += 1

    vertex_sets = [((Q(0), Q(0)),),
                   ((Q(-1), Q(0)), (Q(1), Q(0))),
                   ((Q(-1), Q(0)), (Q(1), Q(0)), (Q(0), Q(1, 3)))]
    for vertices in vertex_sets:
        m = len(vertices)
        for den in range(1, 8):
            all_nums = tuple(compositions(den, m))
            for a, b in product(all_nums, repeat=2):
                weights = tuple(Q(ai + bi, 2 * den) for ai, bi in zip(a, b))
                rounded = round_simplex(weights, den)
                err = sum((abs(t - Q(r, den)) for t, r in zip(weights, rounded)), Q(0))
                assert err <= Q(2 * (m - 1), den)
                counts["rounding_cases"] += 1
                x, y = weighted_point(vertices, a, den), weighted_point(vertices, b, den)
                point = weighted_point(vertices, rounded, den)
                assert linf(point, midpoint(x, y)) <= Q(2 * (m - 1), den)
                counts["midpoint_certificate_cases"] += 1
            for target_den in range(1, 8):
                for a in all_nums:
                    rounded = round_simplex(tuple(Q(ai, den) for ai in a), target_den)
                    x = weighted_point(vertices, a, den)
                    y = weighted_point(vertices, rounded, target_den)
                    assert linf(x, y) <= Q(2 * (m - 1), target_den)
                    counts["transfer_certificate_cases"] += 1

    # Nonconvex Hausdorff coherence does not suffice: the nearest points alternate.
    unstable = []
    for n in range(1, 9):
        s = ((Q(-1),), (Q(1) + Q((-1) ** n, 2 ** n),))
        selected = pick(s, (Q(0),))
        unstable.append({"stage": n, "selected": str(selected[0])})
        assert selected[0] == (Q(-1) if n % 2 == 0 else Q(1) - Q(1, 2 ** n))

    # Degenerate and nearly degenerate convex hulls use the same algorithm.
    projection_examples = []
    z = (Q(1, 3), Q(1))
    for height in [Q(0), Q(1, 32), Q(1, 4)]:
        vertices = ((Q(-1), Q(0)), (Q(1), Q(0)), (Q(0), height))
        exact_candidates = [segment_project(z, a, b) for a, b in combinations(vertices, 2)]
        exact = pick(exact_candidates, z)  # z lies above the whole triangle.
        for den in [4, 8, 16, 32]:
            cloud = hull_cloud(vertices, den)
            approx = pick(cloud, z)
            # A finite point cannot beat the exact segment/triangle projection.
            assert sqdist(approx, z) >= sqdist(exact, z)
            projection_examples.append({
                "height": str(height), "denominator": den,
                "cloud_size": len(cloud),
                "selected": [str(x) for x in approx],
                "exact_projection": [str(x) for x in exact],
                "squared_point_error": str(sqdist(approx, exact)),
                "squared_objective": str(sqdist(approx, z))})
    return {"status": "passed", "arithmetic": "fractions.Fraction; no floating point",
            "counts": counts,
            "nonconvex_counterexample": unstable,
            "convex_hull_examples": projection_examples,
            "proof_status": "Finite execution checks only; universal theorems have human proofs and Lean outlines."}


if __name__ == "__main__":
    result = run_validation()
    destination = Path(__file__).resolve().parents[1] / "validation" / "convex_clouds_validation.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "counts": result["counts"],
                      "report": str(destination)}, indent=2))
