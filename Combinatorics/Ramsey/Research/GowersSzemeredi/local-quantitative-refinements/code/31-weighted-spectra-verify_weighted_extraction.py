#!/usr/bin/env python3
"""Exact finite diagnostics for weighted BSG and Freiman restriction.

Only Python's standard library is used. All inequalities are checked with
integers or Fraction; square roots in the precise BSG constants are removed
by squaring nonnegative quantities. This is a finite diagnostic, not a proof
of the general theorems and not Lean verification.

Run from any directory. By default, the recorded JSON is written in the
package data directory. Pass --output PATH to select a different destination.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import random


SEED = 20261006


def add(x, y, p):
    return tuple((a + b) % p for a, b in zip(x, y))


def sub(x, y, p):
    return tuple((a - b) % p for a, b in zip(x, y))


def sumset(a, b, p):
    return {add(x, y, p) for x in a for y in b}


def difference(a, b, p):
    return {sub(x, y, p) for x in a for y in b}


def iterated_sum(a, k, p):
    dim = len(next(iter(a)))
    ans = {(0,) * dim}
    for _ in range(k):
        ans = sumset(ans, a, p)
    return ans


def direct_freiman(graph, k, p):
    """Test the defining equal-k-sums property by its full finite sumset."""
    seen = {}
    for x, y in iterated_sum(graph, k, p):
        if x in seen and seen[x] != y:
            return False
        seen[x] = y
    return True


def defect_set(graph, k, p):
    sums = iterated_sum(graph, k, p)
    fibers = defaultdict(set)
    for x, y in sums:
        fibers[x].add(y)
    return {(a - b) % p for values in fibers.values()
            for a in values for b in values}


def restrict_graph(graph, weights, k, p):
    """Construct the theorem's actual dilation and best weighted translate."""
    defects = defect_set(graph, k, p)
    q = len(defects)
    length = p // (k * q)
    good = []
    for d in range(1, p):
        if all(j * d % p not in defects - {0}
               for j in range(1, k * length + 1)):
            good.append(d)
    assert good, (p, k, defects, length)
    d = good[0]
    progression = {j * d % p for j in range(length + 1)}
    assert len(progression) == length + 1
    candidates = []
    for t in range(p):
        candidate = {z for z in graph if (z[1] - t) % p in progression}
        candidates.append((sum((weights[z] for z in candidate), F(0)), t,
                           candidate))
    mass, translate, chosen = max(candidates, key=lambda item: (item[0], -item[1]))
    total = sum((weights[z] for z in graph), F(0))
    assert mass * p >= (length + 1) * total
    assert mass * k * q >= total
    assert chosen and direct_freiman(chosen, k, p)
    return chosen, {
        "q": q,
        "length_minus_one": length,
        "dilation": d,
        "translate": translate,
        "selected_mass": mass,
        "total_mass": total,
    }


def exhaustive_graph_checks():
    graphs = 0
    restrictions = 0
    injections = 0
    identity_fibers = 0
    nontrivial_defects = 0
    cases_by_prime = {}
    for p in (2, 3, 5):
        prime_count = 0
        # -1 means that the point does not belong to the domain.
        for values in product(range(-1, p), repeat=p):
            graph = {(x, y) for x, y in enumerate(values) if y != -1}
            if not graph:
                continue
            graphs += 1
            prime_count += 1
            n = len(graph)
            doubling = F(len(difference(graph, graph, p)), n)
            profiles = (
                {z: F(1) for z in graph},
                {z: F(1 + (3 * z[0] + z[1]) % 7, 7) for z in graph},
            )
            for k in (2, 3):
                defects = defect_set(graph, k, p)
                q = len(defects)
                assert 0 in defects
                assert defects == {(-x) % p for x in defects}
                sums = iterated_sum(graph, k, p)
                mixed = difference(sumset(sums, graph, p), sums, p)
                image = {(x, (y + v) % p) for v in defects for x, y in graph}
                assert len(image) == q * n
                assert image <= mixed
                assert q * n <= len(mixed)
                assert len(mixed) <= doubling ** (2 * k + 1) * n
                assert q <= doubling ** (2 * k + 1)
                injections += 1
                identity_fibers += int(q == 1)
                nontrivial_defects += int(q > 1)
                for weights in profiles:
                    chosen, result = restrict_graph(graph, weights, k, p)
                    assert result["selected_mass"] * k * doubling ** (2 * k + 1) \
                        >= result["total_mass"]
                    restrictions += 1
        cases_by_prime[str(p)] = prime_count
    return {
        "primes": [2, 3, 5],
        "orders": [2, 3],
        "nonempty_partial_graphs": graphs,
        "graphs_by_prime": cases_by_prime,
        "weighted_and_unweighted_restrictions": restrictions,
        "vertical_fiber_injections": injections,
        "trivial_defect_sets": identity_fibers,
        "nontrivial_defect_sets": nontrivial_defects,
    }


def exhaustive_dilation_checks():
    cases = 0
    positive_length_cases = 0
    primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
    for p in primes:
        if p == 2:
            blocks = [{1}]
        else:
            blocks = [{j, p - j} for j in range(1, (p + 1) // 2)]
        for mask in range(1 << len(blocks)):
            defects = {0}
            for bit, block in enumerate(blocks):
                if mask >> bit & 1:
                    defects.update(block)
            q = len(defects)
            for k in range(2, 9):
                length = p // (k * q)
                bad = {d for d in range(1, p)
                       if any(j * d % p in defects - {0}
                              for j in range(1, k * length + 1))}
                assert len(bad) <= k * length * (q - 1)
                assert len(bad) < p - 1
                assert length < p
                assert F(length + 1, p) >= F(1, k * q)
                positive_length_cases += int(length > 0)
                cases += 1
    return {
        "primes": list(primes),
        "orders": list(range(2, 9)),
        "all_symmetric_defect_sets_tested": True,
        "defect_set_order_cases": cases,
        "positive_length_cases": positive_length_cases,
    }


def energy(weights, p):
    r = defaultdict(F)
    for x, wx in weights.items():
        for y, wy in weights.items():
            r[sub(x, y, p)] += wx * wy
    answer = sum((value * value for value in r.values()), F(0))
    # Independent direct additive-quadruple evaluation.
    check = F(0)
    for a, wa in weights.items():
        for b, wb in weights.items():
            for c, wc in weights.items():
                fourth = sub(add(a, b, p), c, p)
                check += wa * wb * wc * weights.get(fourth, F(0))
    assert answer == check
    return answer, dict(r)


def weighted_bsg(weights, p, check_paths=True):
    assert weights and all(0 < w <= 1 for w in weights.values())
    support = set(weights)
    mass = sum(weights.values(), F(0))
    en, correlations = energy(weights, p)
    c = en / mass ** 3
    assert 0 < c <= 1
    rho = c / (2 - c)
    popular = {d for d, value in correlations.items() if value >= c * mass / 2}
    assert popular == {tuple(-x % p for x in d) for d in popular}
    assert len(popular) <= 2 * mass / c
    popular_mass = sum((correlations[d] for d in popular), F(0))
    assert popular_mass >= rho * mass ** 2

    neighborhoods = {x: {y for y in support if sub(x, y, p) in popular}
                     for x in support}
    common = {(a, b): sum((weights[z] for z in neighborhoods[a] & neighborhoods[b]),
                          F(0))
              for a in support for b in support}
    bad = {(a, b) for a in support for b in support
           if common[a, b] < rho ** 2 * mass / 12}

    choices = []
    expected_certificate = F(0)
    for y in sorted(support):
        u_set = neighborhoods[y]
        u = sum((weights[x] for x in u_set), F(0)) / mass
        bad_weight = sum((weights[a] * weights[b]
                          for a in u_set for b in u_set if (a, b) in bad),
                         F(0)) / mass ** 2
        certificate = u ** 2 - 6 * bad_weight
        expected_certificate += weights[y] / mass * certificate
        choices.append((certificate, y, u_set, u, bad_weight))
    assert expected_certificate >= rho ** 2 / 2
    certificate, witness, u_set, u, bad_weight = max(choices, key=lambda item: item[0])
    assert certificate >= rho ** 2 / 2
    assert 2 * u ** 2 >= rho ** 2
    assert 6 * bad_weight <= u ** 2
    chosen = {
        a for a in u_set
        if sum((weights[b] for b in u_set if (a, b) in bad), F(0))
        <= u * mass / 3
    }
    selected_mass = sum((weights[x] for x in chosen), F(0))
    assert chosen
    assert 8 * selected_mass ** 2 >= rho ** 2 * mass ** 2
    assert selected_mass >= c * mass / 8
    differences = difference(chosen, chosen, p)
    assert F(len(differences)) ** 2 * rho ** 10 * c ** 8 \
        <= 2 * 6912 ** 2 * mass ** 2
    assert len(differences) <= 2 ** 19 * c ** -9 * mass

    endpoint_checks = 0
    path_checks = 0
    if check_paths:
        labels_by_difference = {}
        for a in sorted(chosen):
            for b in sorted(chosen):
                partners = {z for z in u_set if (a, z) not in bad and (b, z) not in bad}
                weighted_paths = F(0)
                labels = set()
                paths = 0
                for z in partners:
                    for x in neighborhoods[a] & neighborhoods[z]:
                        for y in neighborhoods[b] & neighborhoods[z]:
                            label = (sub(a, x, p), sub(z, x, p),
                                     sub(z, y, p), sub(b, y, p))
                            assert all(d in popular for d in label)
                            assert sub(add(sub(label[0], label[1], p), label[2], p),
                                       label[3], p) == sub(a, b, p)
                            assert label not in labels
                            labels.add(label)
                            weighted_paths += weights[z] * weights[x] * weights[y]
                            paths += 1
                assert weighted_paths <= paths
                assert 2 * 432 ** 2 * weighted_paths ** 2 >= rho ** 10 * mass ** 6
                difference_value = sub(a, b, p)
                if difference_value not in labels_by_difference:
                    labels_by_difference[difference_value] = labels
                endpoint_checks += 1
                path_checks += paths
        all_labels = set()
        for labels in labels_by_difference.values():
            assert all_labels.isdisjoint(labels)
            all_labels.update(labels)
        assert len(all_labels) <= len(popular) ** 4

    return chosen, {
        "energy": en,
        "mass": mass,
        "c": c,
        "rho": rho,
        "selected_mass": selected_mass,
        "selected_cardinality": len(chosen),
        "difference_cardinality": len(differences),
        "witness": witness,
        "bad_ordered_pairs": len(bad),
        "endpoint_checks": endpoint_checks,
        "path_checks": path_checks,
    }


def randomized_weighted_checks():
    rng = random.Random(SEED)
    cases = []
    # Singletons, complete groups, nonconstant weights, and support on a line.
    cases.append((2, {(0, 0): F(1, 4)}))
    cases.append((2, {x: F(1) for x in product(range(2), repeat=2)}))
    cases.append((3, {(x, 0): F(x + 1, 3) for x in range(3)}))
    cases.append((5, {(x, x): F(1) for x in range(5)}))
    # A horizontal subgroup with six exceptional points: the popular graph
    # has 160 bad ordered pairs, so this exercises the nontrivial cleanup.
    subgroup_with_exceptions = {(x, 0): F(1) for x in range(11)}
    subgroup_with_exceptions.update({(x, x * x % 11): F(1) for x in range(1, 7)})
    cases.append((11, subgroup_with_exceptions))
    for _ in range(80):
        p = rng.choice((2, 3, 5, 7))
        universe = list(product(range(p), repeat=2))
        size = rng.randint(1, min(8, len(universe)))
        support = rng.sample(universe, size)
        cases.append((p, {x: F(rng.randint(1, 8), 8) for x in support}))

    endpoint_checks = 0
    path_checks = 0
    combined_checks = 0
    cases_with_bad_pairs = 0
    bad_pair_checks = 0
    minimum_capture = F(1)
    maximum_c = F(0)
    minimum_c = F(1)
    for p, weights in cases:
        selected, result = weighted_bsg(weights, p)
        c, rho, mass = result["c"], result["rho"], result["mass"]
        minimum_c = min(minimum_c, c)
        maximum_c = max(maximum_c, c)
        endpoint_checks += result["endpoint_checks"]
        path_checks += result["path_checks"]
        cases_with_bad_pairs += int(result["bad_ordered_pairs"] > 0)
        bad_pair_checks += result["bad_ordered_pairs"]
        fibers = defaultdict(list)
        for x in weights:
            fibers[x[0]].append(x)
        cap = max(map(len, fibers.values()))
        selected_fibers = defaultdict(list)
        for x in selected:
            selected_fibers[x[0]].append(x)
        graph = {max(points, key=lambda z: (weights[z], z))
                 for points in selected_fibers.values()}
        graph_mass = sum((weights[x] for x in graph), F(0))
        assert cap * graph_mass >= result["selected_mass"]
        graph_doubling = F(len(difference(graph, graph, p)), len(graph))
        assert graph_doubling <= 27648 * cap * rho ** -6 * c ** -4
        assert graph_doubling < 2 ** 21 * cap * c ** -10
        for k in (2, 3, 8):
            restricted, info = restrict_graph(graph, weights, k, p)
            factor = c ** (20 * k + 11) / (k * 2 ** (42 * k + 24) * cap ** (2 * k + 2))
            assert info["selected_mass"] >= factor * mass
            assert restricted <= set(weights)
            minimum_capture = min(minimum_capture, info["selected_mass"] / mass)
            combined_checks += 1
    return {
        "seed": SEED,
        "fixed_cases": 5,
        "random_cases": 80,
        "weighted_bsg_cases": len(cases),
        "direct_energy_identity_checks": len(cases),
        "weighted_path_endpoint_checks": endpoint_checks,
        "individual_injective_path_checks": path_checks,
        "cases_with_nonempty_bad_pair_relation": cases_with_bad_pairs,
        "bad_ordered_pairs_in_inputs": bad_pair_checks,
        "combined_order_k_restrictions": combined_checks,
        "combined_orders": [2, 3, 8],
        "minimum_observed_energy_parameter": str(minimum_c),
        "maximum_observed_energy_parameter": str(maximum_c),
        "minimum_actual_combined_mass_fraction": str(minimum_capture),
    }


def constant_checks():
    assert 27648 * 2 ** 6 == 1769472 < 2 ** 21
    assert 2 * 221184 ** 2 < 2 ** 38  # 221184 sqrt(2) < 2^19.
    assert 42 * 8 + 24 + 3 == 363
    assert 20 * 8 + 11 == 171
    assert 2 * 8 + 2 == 18
    # Reiher--Schoen eta=1/4: |A'| >= (3/4)sqrt(c)|A|,
    # and relative difference-set constant 2^(33+18)c^(-4).
    assert 33 + 2 * 9 == 51
    assert 2 + 3 + 51 * 17 == 872
    assert F(1, 2) + 4 * 17 == F(137, 2)
    for j in range(1, 17):
        root_c = F(j, 16)
        c = root_c ** 2
        old = F(1, 2 ** 1882) * c ** 1164
        elementary = F(1, 2 ** 363) * c ** 171
        modern_composition = F(3, 2 ** 872) * root_c ** 137
        factored = F(3, 4) * root_c / (8 * (2 ** 51 * c ** -4) ** 17)
        assert modern_composition == factored
        assert elementary >= old
        assert modern_composition >= old
    return {
        "elementary_order_eight": "2^-363 c^171 K^-18",
        "historical_order_eight": "2^-1882 c^1164",
        "reiher_schoen_composition_order_eight": "3 * 2^-872 c^(137/2)",
        "reiher_schoen_eta": "1/4",
        "square_rational_comparison_points": 16,
        "constants_checked_exactly": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent.parent / "data" / "weighted_extraction_results.json")
    args = parser.parse_args()
    results = {
        "status": "all exact finite checks passed",
        "arithmetic": "Python integers and fractions.Fraction only",
        "verification_scope": "finite diagnostics; no general theorem or Lean proof claimed",
        "exhaustive_partial_graphs": exhaustive_graph_checks(),
        "exhaustive_dilation_avoidance": exhaustive_dilation_checks(),
        "weighted_bsg_and_combined_restriction": randomized_weighted_checks(),
        "constant_ledger": constant_checks(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
