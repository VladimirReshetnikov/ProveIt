#!/usr/bin/env python3
"""Independent exact finite tests. Run with --suite all (default), or a name.

The universal theorems are proved in the article; these finite checks test the
reference implementation and algebraic identities, not their infinite scope.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path
import random
import time
from energy_inventory import (FiniteAbelianGroup as Group, build_inventory,
    deterministic_round, fixed_size_round, cyclic_graph_models, SupportInventory,
    response_coefficients, _jsonable)
from fejer_search import rational_fejer_table, search_family
from system_inventory import SystemInventory, system_round

SEED = 20261006


def deterministic_energy(G, labels, selected, order):
    counts = Counter({G.zero: 1})
    for _ in range(order):
        nxt = Counter()
        for x, value in counts.items():
            for i in selected:
                nxt[G.add(x, labels[i])] += value
        counts = nxt
    return sum(v * v for v in counts.values())


def expected_brute(G, labels, probabilities, order):
    n = len(labels)
    answer = F(0)
    for mask in range(1 << n):
        prob = math.prod(probabilities[i] if mask >> i & 1 else 1 - probabilities[i]
                         for i in range(n))
        if prob:
            answer += prob * deterministic_energy(G, labels, [i for i in range(n) if mask >> i & 1], order)
    return answer


def coefficient_brute(G, labels, probabilities, a, b):
    """Independently enumerate ordered tuples, not the inventory recurrence."""
    out = [F(0)] * G.size
    n = len(labels)
    for indices in itertools.product(range(n), repeat=a + b):
        z = G.zero
        for j, i in enumerate(indices):
            z = G.add(z, G.scale(1 if j < a else -1, labels[i]))
        prob = math.prod(probabilities[i] for i in set(indices))
        out[G.index(z)] += prob
    return out


def suite_inventory():
    rng = random.Random(SEED)
    cases = replacements = full_coefficients = 0
    for moduli in [(2,), (3,), (4,), (5,), (2, 2), (2, 3)]:
        G = Group(moduli)
        for trial in range(8):
            n = rng.randint(1, 5)
            labels = [rng.choice(G.elements()) for _ in range(n)]
            p = [rng.choice([F(0), F(1, 3), F(1, 2), F(2, 3), F(1)]) for _ in range(n)]
            order = 1 + trial % 3
            inv = build_inventory(G, labels, p, order)
            assert inv.energy() == expected_brute(G, labels, p, order)
            if n <= 3 or order <= 2:
                for a in range(order + 1):
                    for b in range(order + 1):
                        assert inv.A[a, b] == coefficient_brute(G, labels, p, a, b)
                        full_coefficients += G.size
            for _ in range(3):
                j = rng.randrange(n)
                p0, p1 = p[:], p[:]
                p0[j], p1[j] = F(0), F(1)
                deriv = expected_brute(G, labels, p1, order) - expected_brute(G, labels, p0, order)
                assert inv.derivative(labels[j], p[j]) == deriv
                new = rng.choice([F(0), F(1, 4), F(1)])
                inv.replace_probability(labels[j], p[j], new)
                p[j] = new
                assert inv.energy() == expected_brute(G, labels, p, order)
                replacements += 1
            cases += 1
    return {"cases": cases, "exact_group_coefficients_checked": full_coefficients,
            "exact_derivatives_and_replacements": replacements,
            "moduli": [[2], [3], [4], [5], [2, 2], [2, 3]], "orders": [1, 2, 3]}


def suite_rounding():
    cases = decisions = 0
    for p in (2, 3, 4):
        domain = list(range(p))
        maps = itertools.product(range(p), repeat=p)
        if p == 4:
            maps = itertools.islice(maps, 0, 256, 11)
        for values in maps:
            models = cyclic_graph_models(p, domain, values, F(1, 3))
            probabilities = [F((i % 3) + 1, 4) for i in range(p)]
            result = deterministic_round(models, probabilities, 2)
            initial = sum(F(w) * expected_brute(G, labels, probabilities, 2)
                          for G, labels, w in models)
            final = sum(F(w) * deterministic_energy(G, labels, result["selected_indices"], 2)
                        for G, labels, w in models)
            assert initial == result["initial_objective"] and final == result["final_objective"]
            assert final >= initial
            C = math.comb(4, 2) ** 2
            assert result["weighted_shift_additions"] <= 2 * C * p * (p + p * p)
            cases += 1
            decisions += len(result["trace"])
    return {"exact_graph_cases": cases, "decisions": decisions,
            "orders": [2], "cyclic_moduli": [2, 3, 4], "operation_bound_checked": True}


def suite_fixed():
    rng = random.Random(SEED + 1)
    cases = profiles = conditional_cases = 0
    for p in (2, 3, 4, 5, 7):
        for trial in range(5):
            n = min(p, 4)
            domain = list(range(n))
            values = [rng.randrange(p) for _ in domain]
            s = 2 + (trial == 0)
            models = cyclic_graph_models(p, domain, values, F(1, 4))
            G, labels, _ = models[1]
            inventory = SupportInventory(G, s)
            for g in labels:
                inventory.add_undecided(g)
            # Distinct-support coefficients checked by tuple enumeration.
            expected = [0] * (2 * s + 1)
            for indices in itertools.product(range(n), repeat=2 * s):
                z = G.zero
                for j, i in enumerate(indices):
                    z = G.add(z, G.scale(1 if j < s else -1, labels[i]))
                if z == G.zero:
                    expected[len(set(indices))] += 1
            actual = [inventory.A[s, s][j][0] for j in range(2 * s + 1)]
            assert actual == expected
            profiles += 1
            for size in range(n + 1):
                result = fixed_size_round(models, s, size)
                avg = sum(sum(F(w) * deterministic_energy(H, data, subset, s)
                              for H, data, w in models)
                          for subset in itertools.combinations(range(n), size)) / math.comb(n, size)
                final = sum(F(w) * deterministic_energy(H, data, result["selected_indices"], s)
                            for H, data, w in models)
                assert avg == result["initial_objective"] and final == result["final_objective"]
                assert len(result["selected_indices"]) == size and final >= avg
                conditional_cases += len(result["trace"])
                cases += 1
    return {"support_profiles": profiles, "prescribed_size_runs": cases,
            "conditional_steps": conditional_cases, "all_cardinalities_tested": True,
            "cyclic_moduli": [2, 3, 4, 5, 7], "orders": [2, 3]}


def suite_systems():
    rng = random.Random(SEED + 2)
    cases = replacements = 0
    for moduli in [(2,), (4,), (5,), (3, 3)]:
        G = Group(moduli)
        for trial in range(10):
            n, t = rng.randint(1, 4), rng.randint(2, 5)
            # No genericity: zero coefficients, nonunits and repeated images occur.
            steps = [[rng.choice(G.elements()) for _ in range(t)] for _ in range(n)]
            probabilities = [rng.choice([F(0), F(1, 3), F(1, 2), F(1)]) for _ in range(n)]
            def brute(pr):
                ans = F(0)
                for indices in itertools.product(range(n), repeat=t):
                    z = G.zero
                    for j, i in enumerate(indices):
                        z = G.add(z, steps[i][j])
                    if z == G.zero:
                        ans += math.prod(pr[i] for i in set(indices))
                return ans
            inv = SystemInventory(G, t)
            for step, prob in zip(steps, probabilities):
                inv.add_label(step, prob)
            assert inv.count() == brute(probabilities)
            for i in range(n):
                p0, p1 = probabilities[:], probabilities[:]
                p0[i], p1[i] = F(0), F(1)
                delta = brute(p1) - brute(p0)
                assert inv.derivative(steps[i], probabilities[i]) == delta
                new = F(int(delta >= 0))
                inv.replace_probability(steps[i], probabilities[i], new)
                probabilities[i] = new
                assert inv.count() == brute(probabilities)
                replacements += 1
            cases += 1
    return {"systems": cases, "derivatives_and_replacements": replacements,
            "positions_range": [2, 5], "includes_composite_moduli": True}


def suite_kernel():
    cases = entries = 0
    largest_float_discrepancy = 0.0
    for p in (3, 5, 7, 11):
        for L in (2, 3, 4):
            data = rational_fejer_table(p, L, 256)
            for t, (lo, hi) in enumerate(data["intervals"]):
                # Independent numerical smoke test, not the interval certificate proof.
                true = (L + 2 * sum((L - j) * math.cos(2 * math.pi * j * t / p)
                                     for j in range(1, L))) / L ** 2
                q = float(data["table"][t])
                assert float(lo) - 1e-13 <= true <= float(hi) + 1e-13
                assert 0 <= data["table"][t] <= lo <= hi <= 1
                assert hi - data["table"][t] < F(2, 256)
                largest_float_discrepancy = max(largest_float_discrepancy, abs(q - true))
                entries += 1
            cases += 1
    return {"certified_rational_tables": cases, "table_entries": entries,
            "floating_smoke_test_max_error": largest_float_discrepancy,
            "note": "Rational interval validity follows from the proved series bounds; float comparison is supplementary."}


def suite_lipschitz():
    rng = random.Random(SEED + 3)
    cases = 0
    for p in (3, 4, 5):
        for trial in range(10):
            n = p
            values = [rng.randrange(p) for _ in range(n)]
            models = cyclic_graph_models(p, list(range(n)), values, F(1, 5))
            probs = [F(rng.randrange(11), 10) for _ in range(n)]
            other = [min(F(1), x + F(rng.randrange(3), 20)) for x in probs]
            v = sum(F(w) * expected_brute(G, labels, probs, 2) for G, labels, w in models)
            u = sum(F(w) * expected_brute(G, labels, other, 2) for G, labels, w in models)
            epsilon = max(abs(a - b) for a, b in zip(probs, other))
            assert abs(u - v) <= 4 * n ** 3 * epsilon
            cases += 1
    return {"exact_lipschitz_cases": cases}


def suite_high_order():
    rng = random.Random(SEED + 4)
    cases = 0
    for modulus in (3, 5, 7):
        for order in (4, 6, 8):
            n = min(modulus, 5)
            domain = list(range(n))
            values = [rng.randrange(modulus) for _ in domain]
            probabilities = [F((i % 3) + 1, 4) for i in domain]
            models = cyclic_graph_models(modulus, domain, values, F(1, 3))
            result = deterministic_round(models, probabilities, order)
            initial = sum(F(w) * expected_brute(G, labels, probabilities, order)
                          for G, labels, w in models)
            final = sum(F(w) * deterministic_energy(G, labels, result["selected_indices"], order)
                        for G, labels, w in models)
            assert initial == result["initial_objective"] and final == result["final_objective"]
            assert final >= initial
            cases += 1
    models = cyclic_graph_models(3, [0, 1, 2], [0, 0, 1], F(1, 4))
    for size in range(4):
        result = fixed_size_round(models, 8, size)
        avg = sum(sum(F(w) * deterministic_energy(G, labels, sub, 8) for G, labels, w in models)
                  for sub in itertools.combinations(range(3), size)) / math.comb(3, size)
        assert avg == result["initial_objective"] and len(result["selected_indices"]) == size
    return {"bernoulli_high_order_cases": cases, "orders": [4, 6, 8],
            "fixed_size_order_eight_cases": 4}


def suite_edge_and_system_rounding():
    """Explicit empty, trivial-group, and signed system-rounding regressions."""
    G = Group((1,))
    assert deterministic_round([(G, [], 1)], [], 3)["final_objective"] == 0
    assert fixed_size_round([(G, [], 1)], 3, 0)["selected_indices"] == []
    for size in range(6):
        labels = [(0,)] * 5
        result = fixed_size_round([(G, labels, 1)], 4, size)
        assert result["initial_objective"] == size ** 8
        assert result["final_objective"] == size ** 8
    rng = random.Random(SEED + 5)
    cases = 0
    for modulus in (2, 3, 4, 5):
        G = Group((modulus,))
        for t in (2, 3, 4, 5):
            n = 4
            models = [(G, [[rng.choice(G.elements()) for _ in range(t)]
                            for _ in range(n)], w) for w in (F(1), -F(3, 4))]
            probs = [F(0), F(1, 3), F(2, 3), F(1)]
            def objective(selected):
                ans = F(0)
                for group, steps, weight in models:
                    total = 0
                    for indices in itertools.product(selected, repeat=t):
                        z = group.zero
                        for j, i in enumerate(indices):
                            z = group.add(z, steps[i][j])
                        total += z == group.zero
                    ans += weight * total
                return ans
            avg = F(0)
            for mask in range(1 << n):
                probability = math.prod(probs[i] if mask >> i & 1 else 1-probs[i]
                                        for i in range(n))
                avg += probability * objective([i for i in range(n) if mask >> i & 1])
            result = system_round(models, probs, t)
            assert result["initial_objective"] == avg
            assert result["final_objective"] == objective(result["selected_indices"])
            assert result["final_objective"] >= avg
            cases += 1
    return {"empty_or_trivial_group_cases": 8, "signed_system_rounding_cases": cases}


SUITES = {"inventory": suite_inventory, "rounding": suite_rounding,
          "fixed": suite_fixed, "systems": suite_systems,
          "kernel": suite_kernel, "lipschitz": suite_lipschitz,
          "high_order": suite_high_order, "edge_and_system_rounding": suite_edge_and_system_rounding}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--suite", choices=["all"] + list(SUITES), default="all")
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    start = time.perf_counter()
    selected = SUITES if args.suite == "all" else {args.suite: SUITES[args.suite]}
    results = {name: fn() for name, fn in selected.items()}
    report = {"status": "passed", "seed": SEED, "suites": results,
              "elapsed_seconds": round(time.perf_counter() - start, 4),
              "scope": "Finite exact-arithmetic tests; not a formal verification or exhaustive priority search."}
    text = json.dumps(_jsonable(report), indent=2)
    if args.output:
        args.output.write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
