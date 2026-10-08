"""Independent referee checks: categorical associativity and transfer equivariance.

Run directly; implementation/fast and baseline/fast are resolved from
this file inside the extracted bundle.  Use --help for output options.

These checks exercise relationships between several operations, rather than
reimplementing the ranked-convolution or coefficient-reconstruction loops.
"""
from __future__ import annotations

import argparse
import json
import random
from pathlib import Path

from bundle_paths import HERE, baseline_module
from fastunknot.dense_compose import AdaptivePlanar

Diagram = baseline_module("diagram").Diagram
Planar = baseline_module("planar").Planar


def matchings(points):
    if not points:
        return [()]
    result = []
    for cut in range(1, len(points), 2):
        for inner in matchings(points[1:cut]):
            for outer in matchings(points[cut + 1:]):
                result.append(tuple(sorted(((points[0], points[cut]),) + inner + outer)))
    return result


def associativity(rng):
    checks = 0
    zero_genus_plans = 0
    for size in range(0, 13, 2):
        alg = AdaptivePlanar(force_dense=True, shape_cache=False)
        ids = [alg.intern(pairs) for pairs in matchings(tuple(range(size)))]
        for _ in range(300):
            a, b, c, d = [rng.choice(ids) for _ in range(4)]
            f = rng.getrandbits(1 << alg.basis(a, b)[1])
            g = rng.getrandbits(1 << alg.basis(b, c)[1])
            h = rng.getrandbits(1 << alg.basis(c, d)[1])
            fg = alg.compose(a, b, c, f, g)
            gh = alg.compose(b, c, d, g, h)
            assert alg.compose(a, c, d, fg, h) == alg.compose(a, b, d, f, gh)
            checks += 1
            zero_genus_plans += alg.compose_plan(a, b, c) is None
            zero_genus_plans += alg.compose_plan(b, c, d) is None
    return {"associativity_checks": checks,
            "positive_genus_intermediate_plans": zero_genus_plans}


def transfer_equivariance(rng):
    reference = Planar(shape_cache=False)
    dense = AdaptivePlanar(shape_cache=True, force_dense=True)
    adaptive = AdaptivePlanar(shape_cache=True)
    engines = [reference, dense, adaptive]
    checks = 0
    max_frontier = 0
    high_support_thresholds = set()
    closed_counts = set()
    fixtures = [(2, [1] * 7), (3, [1, -2] * 5),
                (4, [1, -2, 3] * 3), (5, [1, -2, 3, -4] * 4)]
    for strands, word in fixtures:
        diagram = Diagram.from_braid(strands, word)
        order = list(range(len(diagram.pd)))
        rng.shuffle(order)
        points = frozenset()
        pool = [()]
        for crossing in order:
            slots = tuple(diagram.pd[crossing])
            max_frontier = max(max_frontier, len(points))
            for alg in engines:
                alg.stage(points, slots)
            pairs = [(rng.choice(pool), rng.choice(pool)) for _ in range(3)]
            pairs.append((pool[0], pool[0]))
            cases = []
            for left, right in pairs:
                a, b = reference.intern(left), reference.intern(right)
                variables = reference.basis(a, b)[1]
                count = 1 << variables
                inputs = [1, 1 << (count - 1), rng.getrandbits(count)]
                if count >= 64:
                    inputs.extend(sum(1 << mask for mask in rng.sample(range(count), support))
                                  for support in (32, 33))
                    high_support_thresholds.update((32, 33))
                for f in inputs:
                    for i in (0, 1):
                        for j in (0, 1):
                            expected = reference.transfer(a, b, f, i, j)
                            for alg in (dense, adaptive):
                                actual = alg.transfer(alg.intern(left), alg.intern(right), f, i, j)
                                assert actual == expected, (strands, slots, left, right, i, j, f)
                            cases.append((left, right, f, i, j, expected))
                            checks += 2
                for smoothing in (0, 1):
                    closed_counts.add(reference.glue(a, smoothing)[1])
            new_pool = set()
            for matching in pool:
                a = reference.intern(matching)
                for smoothing in (0, 1):
                    new_pool.add(reference.pairs[reference.glue(a, smoothing)[0]])
            new_pool = sorted(new_pool)
            if len(new_pool) > 24:
                new_pool = rng.sample(new_pool, 24)
            new_points = reference.new_points()

            # Relabeling preserves shape and circle numbering, while changing
            # matching identifiers and forcing fresh stage-local mask caches.
            def relabel(label):
                return 1_000_003 + 17 * label

            def relabel_matching(matching):
                return tuple((relabel(p), relabel(q)) for p, q in matching)

            for alg in (dense, adaptive):
                alg.stage(frozenset(map(relabel, points)), tuple(map(relabel, slots)))
                for left, right, f, i, j, expected in cases:
                    a = alg.intern(relabel_matching(left))
                    b = alg.intern(relabel_matching(right))
                    assert alg.transfer(a, b, f, i, j) == expected
                    checks += 1
            pool, points = new_pool, new_points
    assert high_support_thresholds == {32, 33}
    assert closed_counts == {0, 1, 2}
    assert dense.stats["shape_hits"] > 0 and adaptive.stats["shape_hits"] > 0
    return {"transfer_comparisons": checks,
            "max_input_frontier": max_frontier,
            "closed_smoothing_circle_counts": sorted(closed_counts),
            "explicit_support_thresholds": sorted(high_support_thresholds),
            "dense_shape_cache_hits": dense.stats["shape_hits"],
            "adaptive_shape_cache_hits": adaptive.stats["shape_hits"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE/"referee_results_reproduced.json")
    args = parser.parse_args()
    rng = random.Random(202610070123)
    result = associativity(rng)
    result.update(transfer_equivariance(rng))
    result["seed"] = 202610070123
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
