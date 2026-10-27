#!/usr/bin/env python3
"""Independent finite-sum tests for the four affine contraction plans.

This checks r=9,15,18 algebra over Z/256Z[V]/(V^2).
The r15 and r18 fixtures use the actual rounded joint integer selectors.  It uses ordinary exact summation,
not the asymptotic fast-matrix backend.  All conditions survive python -O.
"""
from itertools import product, combinations
from pathlib import Path
import json
import random
import check_partial_affine_joint as joint15
import check_rectangular_joint as joint18
from geometry18_independent import affine_plan, NORMALS

MOD = 256


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def add(x, y):
    return ((x[0] + y[0]) % MOD, (x[1] + y[1]) % MOD)


def mul(x, y):
    return ((x[0] * y[0]) % MOD,
            (x[0] * y[1] + x[1] * y[0]) % MOD)


def affine_plans(duplicate=True):
    classes = []
    classes.append([[3*x + y for y in range(3)] for x in range(3)])
    for slope in range(3):
        classes.append([[3*x + (slope*x + intercept) % 3
                         for x in range(3)] for intercept in range(3)])
    if duplicate:
        classes = [[block + [v+9 for v in block] for block in p]
                   for p in classes]
    return classes


def assignments(scope, dims):
    return product(*(range(dims[e]) for e in scope))


def factor(scopes, dims, rng):
    return (tuple(scopes), {a: (rng.randrange(MOD), rng.randrange(MOD))
                           for a in assignments(scopes, dims)})


def merge(f, g, dims):
    fs, ft = f
    gs, gt = g
    common = set(fs) & set(gs)
    union = tuple(sorted(set(fs) | set(gs)))
    out = tuple(e for e in union if e not in common)
    positions = {e: i for i, e in enumerate(union)}
    fi = [positions[e] for e in fs]
    gi = [positions[e] for e in gs]
    oi = [positions[e] for e in out]
    table = {a: (0, 0) for a in assignments(out, dims)}
    for a in assignments(union, dims):
        fa = tuple(a[i] for i in fi)
        ga = tuple(a[i] for i in gi)
        oa = tuple(a[i] for i in oi)
        table[oa] = add(table[oa], mul(ft[fa], gt[ga]))
    return out, table


def plan_contract(plan, vertices, dims):
    def build(block):
        if len(block) == 1:
            return vertices[block[0]]
        k = len(block) // 2
        return merge(build(block[:k]), build(block[k:]), dims)
    blocks = [build(block) for block in plan]
    result = merge(merge(blocks[0], blocks[1], dims), blocks[2], dims)
    require(result[0] == (), "final scope is nonempty")
    return result[1][()]


def literal_contract(vertices, dims):
    edges = tuple(sorted(dims))
    positions = {e: i for i, e in enumerate(edges)}
    indices = [[positions[e] for e in scope] for scope, _ in vertices]
    total = (0, 0)
    count = 0
    for a in assignments(edges, dims):
        value = (1, 0)
        for (_, table), ind in zip(vertices, indices):
            value = mul(value, table[tuple(a[i] for i in ind)])
        total = add(total, value)
        count += 1
    return total, count


def selected_plan(plans, dims):
    r = sum(map(len, plans[0]))
    undirected = list(combinations(range(r), 2))
    # Each d is the PRODUCT of the two independently indexed directions.
    d = {e: dims.get(e, 1) * dims.get((e[1], e[0]), 1)
         for e in undirected}
    if r in (15, 18):
        products = [d[e] for e in undirected]
        record = (joint15 if r == 15 else joint18).select_joint(products)
        scores = [item["score"] for item in record["plans"]]
        selected = record["selected_plan"]
        require(scores[selected] == min(scores), "joint selector score mismatch")
        return selected, scores
    universe = set(range(r))
    def score(plan):
        scores = []
        def operation(A, B, C):
            classes = [set(A), set(B), set(C)]
            lengths = []
            for i, j in [(0, 1), (0, 2), (1, 2)]:
                length = 1
                for x, y in undirected:
                    if ((x in classes[i] and y in classes[j]) or
                        (x in classes[j] and y in classes[i])):
                        length *= d[(x, y)]
                lengths.append(length)
            whole = lengths[0] * lengths[1] * lengths[2]
            # (d1 d2 d3 / min(d1,d2,d3)^(5/8))^8
            scores.append(whole**8 // min(lengths)**5)
        def build(block):
            if len(block) == 1:
                return
            k = len(block) // 2
            A, B = block[:k], block[k:]
            build(A)
            build(B)
            operation(A, B, universe-set(block))
        for block in plan:
            build(block)
        operation(*plan)
        return max(scores)
    scores = [score(p) for p in plans]
    return min(range(len(plans)), key=lambda i: (scores[i], i)), scores


def run():
    results = []
    assignments_total = 0
    checked_plans = 0
    nonzero = 0
    for r in [9, 15, 18]:
        if r == 9:
            plans = affine_plans(duplicate=False)
        elif r == 15:
            plans = joint15.plans()
        else:
            plans = [affine_plan(normal) for normal in NORMALS]
        all_edges = [(i, j) for i in range(r) for j in range(r) if i != j]
        for seed in range(12):
            rng = random.Random(1000*r + seed)
            # Both directed indices occur independently.  Small active
            # subsets allow a literal sum to serve as an independent oracle.
            active = rng.sample(all_edges, 8 + seed % 3)
            if seed % 3 == 0:
                active[0:2] = [(0, 1), (1, 0)]
            active = sorted(set(active))
            dims = {e: (3 if i == 0 and seed % 4 == 1 else 2)
                    for i, e in enumerate(active)}
            vertices = []
            for v in range(r):
                scope = tuple(e for e in active if v in e)
                vertices.append(factor(scope, dims, rng))
            kind = "random"
            if seed == 10:
                scope, table = vertices[0]
                vertices[0] = (scope, {a: (0, 0) for a in table})
                kind = "zero"
            if seed == 11:
                for v in [0, 1]:
                    scope, table = vertices[v]
                    vertices[v] = (scope, {a: (0, 1+rng.randrange(255))
                                          for a in table})
                kind = "double_nilpotent"
            direct, count = literal_contract(vertices, dims)
            assignments_total += count
            if direct != (0, 0):
                nonzero += 1
            answers = [plan_contract(p, vertices, dims) for p in plans]
            for answer in answers:
                require(answer == direct,
                        "regrouping mismatch r=%d seed=%d" % (r, seed))
                checked_plans += 1
            choice, scores = selected_plan(plans, dims)
            require(answers[choice] == direct, "dispatch mismatch")
            if kind != "random":
                require(direct == (0, 0), "special zero fixture failed")
            results.append({"groups": r, "seed": seed, "fixture": kind,
                            "active_directed_indices": len(active),
                            "literal_assignments": count,
                            "selected_plan": choice, "joint_selector": r in (15, 18), "result": direct})
    require(nonzero >= 8, "too few nonzero fixtures")
    return {"status": "PASS", "ring": "Z/256Z[V]/(V^2)",
            "fixtures": len(results), "plan_contractions": checked_plans,
            "literal_assignments": assignments_total,
            "nonzero_fixtures": nonzero, "details": results}


if __name__ == "__main__":
    result = run()
    destination = Path(__file__).resolve().parents[1] / "results"
    destination.mkdir(exist_ok=True)
    (destination / "tensor_regrouping.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "details"}))

