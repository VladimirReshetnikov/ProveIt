#!/usr/bin/env python3
"""Small exact mode-graph tests over (Z/64Z)[V]/(V^2).

This independently checks support-score selection, finite distributivity,
and paid child-cache entry counts. All matrix-shaped operations here use
ordinary scalar sums/products; this is not a fast-backend implementation.
"""
from itertools import combinations, product
from math import prod
from pathlib import Path
import argparse
import json
import random

from adaptive_rectangular import data, operations, require, select_plan


ZERO, ONE = (0, 0), (1, 0)


def add(a, b):
    return ((a[0]+b[0]) % 64, (a[1]+b[1]) % 64)


def mul(a, b):
    return (a[0]*b[0] % 64, (a[0]*b[1] + a[1]*b[0]) % 64)


def independent_score(n, plan, dims, backend):
    denominator, middle, small = (backend[k] for k in ("denominator", "middle", "small"))
    worst = 0
    for op in operations(n, plan):
        sizes = []
        for i, j in combinations(range(3), 2):
            sizes.append(prod(dims[g, h]*dims[h, g] for g in op[i] for h in op[j]))
        x, y, z = sorted(sizes, reverse=True)
        worst = max(worst, (x*y)**denominator,
                    x**denominator * y**middle * z**small)
    return worst


def fixture(n, rng, backend_name):
    payload = data()
    plans = payload["menus"][str(n)]
    backend = payload["backends"][backend_name]
    edges = sorted(rng.sample(list(combinations(range(n), 2)), 6))
    dims = {(g, h): 1 for g in range(n) for h in range(n) if g != h}
    for g, h in edges:
        dims[g, h] = 2
    selected = select_plan(n, dims, backend_name)
    scores = [independent_score(n, p, dims, backend) for p in plans]
    require(scores == selected["all_scores"], "Support and direct dimension costs disagree")
    require(selected["plan"] == min(range(len(plans)), key=lambda j: (scores[j], j)),
            "Incorrect selected plan")

    cache = {}
    calls = 0
    expected_calls = 0
    for v in range(n):
        axes = tuple(i for i, e in enumerate(edges) if v in e)
        entries = {}
        expected_calls += 2**len(axes)
        for key in product(range(2), repeat=len(axes)):
            # The synthetic oracle is evaluated exactly once per cache entry.
            entries[key] = (rng.randrange(64), rng.randrange(64))
            calls += 1
        cache[v] = (axes, entries)
    require(calls == expected_calls, "Unpaid or duplicated child-cache calls")

    literal = ZERO
    for assignment in product(range(2), repeat=len(edges)):
        value = ONE
        for v in range(n):
            axes, table = cache[v]
            value = mul(value, table[tuple(assignment[i] for i in axes)])
        literal = add(literal, value)

    def merge(a, b):
        aset, aaxes, atable = a
        bset, baxes, btable = b
        union = aset | bset
        axes = tuple(sorted(set(aaxes) | set(baxes)))
        output_axes = tuple(i for i in axes if (edges[i][0] in union) != (edges[i][1] in union))
        position = {axis: j for j, axis in enumerate(axes)}
        output = {}
        for key in product(range(2), repeat=len(axes)):
            av = atable[tuple(key[position[i]] for i in aaxes)]
            bv = btable[tuple(key[position[i]] for i in baxes)]
            outkey = tuple(key[position[i]] for i in output_axes)
            output[outkey] = add(output.get(outkey, ZERO), mul(av, bv))
        return union, output_axes, output

    def build(vertices):
        if len(vertices) == 1:
            v = vertices[0]
            axes, table = cache[v]
            return {v}, axes, table
        cut = len(vertices) // 2
        return merge(build(vertices[:cut]), build(vertices[cut:]))

    checks = 0
    for plan in plans:
        a, b, c = (build(block) for block in plan)
        vertices, axes, result = merge(merge(a, b), c)
        require(vertices == set(range(n)) and axes == (), "Wrong final table domain")
        require(result[()] == literal, "Tree contraction differs from literal finite sum")
        checks += 1
    return {"plans_checked": checks, "oracle_calls": calls, "assignments": 2**len(edges),
            "selected_plan": selected["plan"], "result": literal}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rng = random.Random(20261026)
    require(mul((0, 1), (0, 1)) == ZERO and (0, 1) != ZERO,
            "Fixture ring is not the intended nonfield ring")
    records = []
    for backend, groups in (("classical", (9, 12)), ("nine_fourths", (10, 12))):
        for n in groups:
            for _ in range(4):
                rec = fixture(n, rng, backend)
                rec.update({"backend": backend, "r": n})
                records.append(rec)
    rejected = 0
    for bad in ({}, {(g, h): 0 for g in range(9) for h in range(9) if g != h}):
        try:
            select_plan(9, bad)
        except ValueError:
            rejected += 1
    require(rejected == 2, "Invalid-list controls failed")
    result = {"status": "PASS", "ring": "(Z/64Z)[V]/(V^2)",
              "fixtures": len(records), "plan_contractions": sum(x["plans_checked"] for x in records),
              "literal_assignments": sum(x["assignments"] for x in records),
              "oracle_calls": sum(x["oracle_calls"] for x in records),
              "invalid_input_rejections": rejected, "records": records}
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
