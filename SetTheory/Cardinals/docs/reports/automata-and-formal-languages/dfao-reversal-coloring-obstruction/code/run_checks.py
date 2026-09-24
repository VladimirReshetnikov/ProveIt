#!/usr/bin/env python3
"""Reproduce the exact verification record and finite-bound tables.

Default run is self-contained and needs Python 3.9+. Optional C++ BFS checks
are run separately with orbit_count.cpp; see README.md.
"""
import argparse
import csv
import json
from math import gcd, factorial
import random
import time
from itertools import permutations, product
from pathlib import Path
from reversal import (act, accessible, bipartite_colorings, collision_graph,
                      cyclic_membership, cycles, davies_lower_bound, first_collision,
                      is_permutation, landau, minimal_state_count, missing_coloring,
                      orbit, permutation_order, permutation_orders, proper, structural_bound,
                      surjective_proper_coloring, u_witness)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=30)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    if args.max_n < 7:
        parser.error("--max-n must be at least 7.")
    args.output.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    record = {"seed": 20260920, "max_n": args.max_n, "checks": {}}

    # Exhaustive n=3,k=3, all ordered pairs of transformations and all tau.
    transformations = list(product(range(3), repeat=3))
    colorings = list(product(range(3), repeat=3))
    total, maximum = 0, 0
    for a in transformations:
        for b in transformations:
            for tau in colorings:
                reached = orbit(tau, (a, b))
                certificate = missing_coloring(a, b, tau, 3)
                assert tuple(certificate["target"]) not in reached
                assert len(reached) <= 3 ** 3 - 6 + landau(3)
                total += 1
                maximum = max(maximum, len(reached))
    record["checks"]["exhaustive_n3_k3"] = {"instances": total, "maximum": maximum}
    print("Exhaustive n=3,k=3:", total, "instances; max", maximum, flush=True)

    # Independent brute-force comparison for every permutation, tau, target
    # at n=3,k=3, and n=4,k=3 (surjectivity is not assumed).
    crt_total = 0
    for n, k in ((3, 3), (4, 3)):
        colors = list(product(range(k), repeat=n))
        for p in permutations(range(n)):
            for tau in colors:
                cyc = orbit(tau, (p,))
                for target in colors:
                    result = cyclic_membership(tau, p, target)
                    assert result["member"] == (target in cyc)
                    crt_total += 1
    record["checks"]["cyclic_CRT_vs_BFS"] = {"instances": crt_total}
    print("Cyclic membership:", crt_total, "instances", flush=True)

    # Targeted and random mixed cases, plus random transformations.
    rng = random.Random(record["seed"])
    random_total = 0
    for n, k, count in ((4, 3, 600), (4, 4, 400), (5, 3, 500), (5, 4, 300),
                        (5, 5, 200), (6, 3, 300), (6, 4, 150), (6, 5, 100)):
        for i in range(count):
            tau = tuple(rng.randrange(k) for _ in range(n))
            if i % 2 == 0:
                p = list(range(n))
                rng.shuffle(p)
                a = tuple(p)
                b = tuple(rng.randrange(n) for _ in range(n))
            else:
                a = tuple(rng.randrange(n) for _ in range(n))
                b = tuple(rng.randrange(n) for _ in range(n))
            reached = orbit(tau, (a, b))
            certificate = missing_coloring(a, b, tau, k)
            assert tuple(certificate["target"]) not in reached
            assert len(reached) <= k ** n - factorial(k) + landau(k)
            assert len(reached) <= structural_bound(n, k)["upper_bound"]
            random_total += 1
    record["checks"]["random_orbits_and_certificates"] = {"instances": random_total}
    print("Random orbit and certificate checks:", random_total, flush=True)

    # Check graph proper-coloring counts by direct enumeration of small graphs.
    graph_total = 0
    for n in range(3, 6):
        for p in permutations(range(n)):
            for x in range(n):
                for y in range(x + 1, n):
                    edges = collision_graph(p, (x, y))
                    c = surjective_proper_coloring(n, 3, edges)
                    assert proper(c, edges) and set(c) == {0, 1, 2}
                    # Independent inclusion-exclusion over graph edges.
                    es = list(edges)
                    expected = 0
                    for mask in range(1 << len(es)):
                        parent = list(range(n))
                        def root(q):
                            while parent[q] != q:
                                q = parent[q]
                            return q
                        for i, (u, v) in enumerate(es):
                            if mask >> i & 1:
                                parent[root(u)] = root(v)
                        components = len({root(q) for q in range(n)})
                        expected += (-1) ** bin(mask).count("1") * 3 ** components
                    observed = sum(proper(c, edges) for c in product(range(3), repeat=n))
                    cs = cycles(p)
                    cx = next(z for z in cs if x in z)
                    cy = next(z for z in cs if y in z)
                    if cx == cy:
                        m = len(cx)
                        d = gcd(m, cx.index(y) - cx.index(x))
                        length = m // d
                        formula = (2 ** length + (-1) ** length * 2) ** d * 3 ** (n - m)
                    else:
                        a, b = len(cx), len(cy)
                        d = gcd(a, b)
                        formula = bipartite_colorings(a // d, b // d, 3) ** d * 3 ** (n - a - b)
                    assert observed == expected == formula
                    graph_total += 1
    record["checks"]["graph_counts_and_colorings"] = {"instances": graph_total}
    print("Graph checks:", graph_total, flush=True)

    order_total = 0
    for n in range(0, 9):
        actual = {permutation_order(tuple(p)) for p in permutations(range(n))}
        assert actual == set(permutation_orders(n))
        order_total += factorial(n)
    record["checks"]["partition_orders_vs_permutations"] = {"permutations": order_total}

    # Match upper and published lower bounds, using exact integer arithmetic.
    rows, mismatches = [], []
    for n in range(7, args.max_n + 1):
        for k in range(3, n):
            upper = structural_bound(n, k)
            lower = davies_lower_bound(n, k)
            assert lower is not None
            row = {"n": n, "k": k, "upper": upper["upper_bound"],
                   "lower": lower["lower_bound"],
                   "match": int(upper["upper_bound"] == lower["lower_bound"]),
                   "ell": lower["ell"], "m": lower["m"],
                   "minimizer": json.dumps(upper["minimizer"], sort_keys=True),
                   "candidates": upper["candidates_examined"]}
            rows.append(row)
            if not row["match"]:
                mismatches.append(row)
    with (args.output / "finite_range_bounds.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    record["checks"]["finite_range_comparison"] = {
        "parameter_pairs": len(rows), "matches": len(rows) - len(mismatches),
        "mismatches": mismatches,
        "note": "Upper bound proved in article; lower bound uses Davies Corollary 3."
    }
    print("Finite range:", len(rows), "pairs; mismatches", len(mismatches), flush=True)

    # Small witness search, restricted to the explicit V-style generator pairs.
    v_singular = {3: (0, 0, 2), 4: (0, 0, 3, 2),
                  5: (0, 0, 3, 4, 2), 6: (0, 3, 0, 4, 5, 1)}
    witnesses = []
    for n in range(3, 7):
        p = tuple(list(range(1, n)) + [0])
        s = v_singular[n]
        for k in range(3, n + 1):
            wanted = structural_bound(n, k)["upper_bound"]
            best_count, best_tau = -1, None
            # Restricted-growth strings enumerate output maps modulo label permutations.
            for tau in product(range(k), repeat=n):
                if tau[0] != 0 or len(set(tau)) != k:
                    continue
                if any(tau[j] > 1 + max(tau[:j]) for j in range(1, n)):
                    continue
                count = len(orbit(tau, (p, s)))
                if count > best_count:
                    best_count, best_tau = count, tau
                if count == wanted:
                    break
            # U construction may beat V at n=5,k=4.
            if n == 5 and k < n:
                up, us, ut = u_witness(2, 3, k)
                uc = len(orbit(ut, (up, us)))
                if uc > best_count:
                    p_used, s_used, best_tau, best_count = up, us, ut, uc
                else:
                    p_used, s_used = p, s
            else:
                p_used, s_used = p, s
            assert accessible(n, (p_used, s_used))
            assert minimal_state_count(best_tau, (p_used, s_used)) == n
            item = {"n": n, "k": k, "p": p_used, "s": s_used, "tau": best_tau,
                    "orbit": best_count, "upper": wanted, "meets_upper": best_count == wanted}
            witnesses.append(item)
    (args.output / "small_witnesses.json").write_text(json.dumps(witnesses, indent=2) + "\n")
    record["checks"]["small_witnesses"] = {"instances": len(witnesses),
        "upper_met": sum(w["meets_upper"] for w in witnesses)}

    p, s, tau = u_witness(3, 5, 5)
    certificate = {"n": 8, "k": 5, "a": p, "b": s, "tau": tau,
                   "unreachable": missing_coloring(p, s, tau, 5)}
    (args.output / "example_certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")
    record["checks"]["published_table_arithmetic"] = {
        "n": 8, "k": 5, "ell": 3, "m": 5,
        "B": bipartite_colorings(3, 5, 5),
        "formula_value": 5 ** 8 - bipartite_colorings(3, 5, 5) + 15,
        "v2_printed_table_value": 368020}
    record["elapsed_seconds"] = round(time.perf_counter() - start, 3)
    (args.output / "verification_summary.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2), flush=True)


if __name__ == "__main__":
    main()
