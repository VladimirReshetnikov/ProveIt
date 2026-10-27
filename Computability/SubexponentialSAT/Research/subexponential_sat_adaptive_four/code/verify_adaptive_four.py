#!/usr/bin/env python3
"""Exact finite checks of adaptive_four.py, with independent brute force."""
import json
import random
from math import prod

from adaptive_four import (
    DualRing, ModRing, Network, brute_force, cached_adaptive_four,
    fast_cost_fifth_power,
)


def demand(condition, message):
    if not condition:
        raise AssertionError(message)


def fixture(order, domains, ring, seed, name):
    network = Network(order, domains)
    rng = random.Random(seed)
    factors = []
    for vertex in range(order):
        values = {}
        for assignment in network.assignments(network.incident(vertex)):
            if isinstance(ring, DualRing):
                value = (rng.randrange(ring.modulus), rng.randrange(ring.modulus))
            else:
                value = rng.randrange(ring.modulus)
            values[assignment] = value
        factors.append(values)
    expected = brute_force(network, ring, lambda g, key: factors[g][key])
    call_keys = [set() for _ in range(order)]

    def counted_oracle(g, key):
        demand(key not in call_keys[g], "a cached oracle entry was recomputed")
        call_keys[g].add(key)
        return factors[g][key]

    actual, ledger = cached_adaptive_four(network, ring, counted_oracle)
    demand(actual == expected, "adaptive contraction disagrees with direct summation")
    expected_calls = [prod(network.sizes[e] for e in network.incident(g))
                      for g in range(order)]
    demand(ledger.oracle_calls == expected_calls, "oracle count mismatch")
    demand([len(keys) for keys in call_keys] == expected_calls, "oracle key coverage mismatch")
    demand(len(ledger.matrix_shapes) == order - 1, "wrong binary merge count")
    chosen = next(row for row in ledger.matching_candidates
                  if row["matching"] == ledger.selected_matching)
    demand(chosen["max_cost_fifth_power"] ==
           min(row["max_cost_fifth_power"] for row in ledger.matching_candidates),
           "matching selection was not model-optimal")
    for row in ledger.matching_candidates:
        demand(row["max_cost_fifth_power"] ==
               max(fast_cost_fifth_power(shape) for shape in row["merge_shapes"]),
               "recorded cost does not match matrix shapes")
    return {
        "name": name, "order": order,
        "ring": ("dual" if isinstance(ring, DualRing) else "modular"),
        "modulus": ring.modulus,
        "global_assignments": network.cardinality(network.edges),
        "result": actual, "expected": expected,
        **ledger.summary(),
    }


def run():
    cases = []
    seed = 481516
    for order in (4, 8, 12):
        edges = [(g, h) for g in range(order) for h in range(order) if g != h]
        for ring in (ModRing(64), DualRing(64)):
            cases.append(fixture(order, {}, ring, seed, f"constant_domains_r{order}"))
            seed += 1
            for trial in range(5):
                rng = random.Random(seed)
                selected = rng.sample(edges, min(7 + trial % 3, len(edges)))
                domains = {edge: (3 if j == 0 and trial % 2 else 2)
                           for j, edge in enumerate(selected)}
                cases.append(fixture(order, domains, ring, seed,
                                     f"random_r{order}_{trial}"))
                seed += 1

    # All 12 directed pair axes are active in this separate complete-K4 case.
    full4 = {(g, h): 2 for g in range(4) for h in range(4) if g != h}
    for ring in (ModRing(64), DualRing(64)):
        cases.append(fixture(4, full4, ring, seed, "complete_directed_K4"))
        seed += 1

    # Make each possible matching uniquely best in turn, at each supported r.
    intended = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
    for order in (4, 8, 12):
        step = order // 4
        for matching in intended:
            domains = {(a * step, b * step): 4 for a, b in matching}
            row = fixture(order, domains, DualRing(64), seed,
                          f"matching_selection_r{order}_{matching}")
            demand(row["selected_matching"] == matching,
                   "matching-specific fixture chose the wrong tree")
            cases.append(row)
            seed += 1

    # Value arithmetic has actual zero divisors and a nonzero nilpotent.
    ring = DualRing(64)
    demand(ring.mul((0, 1), (0, 1)) == (0, 0), "nilpotent multiplication failed")
    demand(ring.mul((2, 0), (32, 0)) == (0, 0), "zero-divisor multiplication failed")
    demand(ring.mul((3, 5), (7, 11)) == (21, 4), "dual-ring cross term failed")

    # The exact integer cost compares fractional model exponents without logs.
    demand(fast_cost_fifth_power((2, 2, 2)) == 4096, "square model-cost check failed")
    demand(fast_cost_fifth_power((1, 3, 5)) == 15 ** 5, "rectangular model-cost check failed")
    return {
        "status": "passed", "case_count": len(cases),
        "case_orders": [4, 8, 12],
        "rings": ["Z/64Z", "(Z/64Z)[epsilon]/(epsilon^2)"],
        "tests": ["independent direct sums", "every child oracle entry exactly once",
                  "exact matching selection", "all three matching choices exercised",
                  "all binary merges counted", "zero-divisor and nilpotent arithmetic"],
        "runtime_scope": "finite regrouping demonstration; cubic backend, not the asymptotic fast backend",
        "total_brute_force_assignments": sum(row["global_assignments"] for row in cases),
        "cases": cases,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
