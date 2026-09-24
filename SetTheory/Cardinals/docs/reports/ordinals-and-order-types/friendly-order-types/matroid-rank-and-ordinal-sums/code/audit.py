#!/usr/bin/env python3
"""Reproduce all finite checks stated in the article (standard library only)."""
from __future__ import annotations
import argparse
import csv
import json
import platform
import random
import time
from itertools import product
from pathlib import Path
from friendly_order import (Poset, antichain, chain, cartesian, cartesian_formula,
                            disjoint_sum, naturally_labelled_posets, ordinal_sum,
                            substitute, substitution_formula)


def require(test: bool, message: str) -> None:
    if not test:
        raise AssertionError(message)


def audit(max_n: int, output: Path) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    rng = random.Random(20260919)
    report = {"python": platform.python_version(), "max_n": max_n,
              "enumeration": "naturally labelled posets, not isomorphism classes",
              "finite_posets": [], "relabelled_cases": 0}
    for n in range(max_n + 1):
        count, hist, t0 = 0, [0] * max(1, n), time.perf_counter()
        for p in naturally_labelled_posets(n):
            count += 1
            exact, predicted = p.exact_friendly_rank(), p.friendly_formula()
            require(exact == predicted, f"Finite formula failed: {p.up}")
            require(p.incidence_rank_f2() == exact, f"F2 rank failed: {p.up}")
            witness = p.optimal_witness()
            require(len(witness["selected"]) == exact, "Witness length failed")
            if count <= 100:
                permutation = list(range(n))
                rng.shuffle(permutation)
                q = p.relabel(permutation)
                require(q.exact_friendly_rank() == exact, "Relabelling changed rank")
                q.optimal_witness()
                report["relabelled_cases"] += 1
            hist[exact] += 1
        row = {"n": n, "count": count, "rank_histogram": hist,
               "seconds": round(time.perf_counter() - t0, 4), "status": "PASS"}
        report["finite_posets"].append(row)
        print(f"finite n={n}: {count} PASS", flush=True)
    report["total_finite_posets"] = sum(r["count"] for r in report["finite_posets"])

    factors = [p for n in range(2, 6) for p in naturally_labelled_posets(n)]
    product_count, product_exact, t0 = 0, 0, time.perf_counter()
    for a, b in product(factors, repeat=2):
        p = cartesian(a, b)
        predicted = cartesian_formula(a, b)
        require(p.friendly_formula() == predicted, f"Product graph failed: {a.up}, {b.up}")
        if p.n <= 9:
            require(p.exact_friendly_rank() == predicted, "Exact product rank failed")
            product_exact += 1
        product_count += 1
    report["cartesian_products"] = {"graph_checks": product_count,
        "exact_rank_checks_size_at_most_9": product_exact,
        "factor_sizes": [2, 3, 4, 5], "seconds": round(time.perf_counter()-t0, 4),
        "status": "PASS"}
    print(f"products: {product_count} graph, {product_exact} exact PASS", flush=True)

    small = [p for n in range(1, 4) for p in naturally_labelled_posets(n)]
    subst_count, t0 = 0, time.perf_counter()
    for index in [Poset(())] + small:
        for fibers in product(small, repeat=index.n):
            p = substitute(index, fibers)
            expected = substitution_formula(index, fibers)
            require(p.exact_friendly_rank() == expected, "Substitution formula failed")
            require(p.friendly_formula() == expected, "Substitution graph failed")
            subst_count += 1
    report["substitutions"] = {"exact_rank_checks": subst_count,
        "index_sizes": [0, 1, 2, 3], "fiber_sizes": [1, 2, 3],
        "seconds": round(time.perf_counter()-t0, 4), "status": "PASS"}
    print(f"substitutions: {subst_count} exact PASS", flush=True)

    examples = {"chain_4": chain(4), "antichain_4": antichain(4),
                "two_antichains_ordinal_sum": ordinal_sum(antichain(2), antichain(2)),
                "two_chains_disjoint_sum": disjoint_sum(chain(2), chain(2)),
                "grid_2_by_3": cartesian(chain(2), chain(3)),
                "boolean_3": cartesian(cartesian(chain(2), chain(2)), chain(2)),
                "empty": Poset(())}
    example_data = {name: {"up_masks": list(p.up), "friendly_rank": p.friendly_formula(),
                           **p.optimal_witness()} for name, p in examples.items()}
    (output / "examples.json").write_text(json.dumps(example_data, indent=2) + "\n")
    report["total_seconds"] = round(time.perf_counter() - started, 4)
    report["status"] = "PASS"
    (output / "audit_results.json").write_text(json.dumps(report, indent=2) + "\n")
    with (output / "rank_distributions.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "naturally_labelled_posets", "friendly_rank", "count"])
        for row in report["finite_posets"]:
            for rank, count in enumerate(row["rank_histogram"]):
                writer.writerow([row["n"], row["count"], rank, count])
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=7)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    if not 0 <= args.max_n <= 8:
        parser.error("Use 0 <= --max-n <= 8; n=8 is substantially slower")
    result = audit(args.max_n, args.output)
    print(json.dumps({k: result[k] for k in ("status", "total_finite_posets", "total_seconds")}, indent=2))
