#!/usr/bin/env python3
"""Reproduce exhaustive checks; no third-party dependencies or random inputs."""
from __future__ import annotations
import argparse
import csv
import itertools
from functools import lru_cache
import json
import platform
import time
from collections import Counter
from pathlib import Path
from friendly import Poset, bits, naturally_labelled_posets


def demand(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def check_invalid_inputs() -> int:
    rejected = 0
    cases = [lambda: Poset.from_relations(2, [(0,1),(1,0)]),
             lambda: Poset.from_relations(2, [(0,2)]),
             lambda: Poset.from_relations(2, [(0,0)]),
             lambda: Poset.from_relations(-1, []),
             lambda: Poset([3,6,4]),
             lambda: Poset([0]),
             lambda: Poset.from_relations(2, [(True,1)])]
    for make in cases:
        try:
            make()
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("An invalid poset was accepted")
    chain = Poset.from_relations(2, [(0,1)])
    try:
        chain.check_certificate({"rank":1,"steps":[{"choice":0,"friend":1}]}, require_optimal=False)
    except ValueError:
        rejected += 1
    else:
        raise AssertionError("A comparable friend was accepted")
    return rejected


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=7)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    if not 0 <= args.max_n <= 9:
        parser.error("--max-n must lie in 0,...,9 (8 and 9 can be expensive)")
    args.out.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    rows: list[dict] = []
    connected_lemma_checks = 0
    for n in range(args.max_n+1):
        count = 0
        hist: Counter[int] = Counter()
        for lower in naturally_labelled_posets(n):
            p = Poset._from_natural_lower(lower)
            direct = p.friendly_dp()
            formula = p.friendly()
            demand(direct == formula, f"Rank mismatch n={n}, lower={lower}")
            demand(p.dual().friendly_dp() == direct, f"Dual rank mismatch {lower}")
            p.check_certificate(p.optimal_certificate())
            if n >= 2 and len(p.components()) == 1:
                x = p.maximal_noncut(p.full)
                demand(p.upper[x] == 1 << x, "Noncut choice was not maximal")
                demand(len(p.components(p.full & ~(1 << x))) == 1, "Noncut deletion disconnected graph")
                connected_lemma_checks += 1
            count += 1
            hist[direct] += 1
        rows.append({"n":n,"naturally_labelled_posets":count,
                     "rank_histogram":{str(k):hist[k] for k in sorted(hist)}})
        print(f"n={n}: {count} cases, ranks={dict(sorted(hist.items()))}", flush=True)
    base_orders = [Poset._from_natural_lower(lo)
                   for n in range(5) for lo in naturally_labelled_posets(n)]
    product_cases = 0
    for a, b in itertools.product(base_orders, repeat=2):
        product = a.cartesian(b)
        if a.n == 0 or b.n == 0:
            expected = 0
        elif a.n == 1:
            expected = b.friendly()
        elif b.n == 1:
            expected = a.friendly()
        else:
            expected = (a.n*b.n - 1 - int(a.has_least() and b.has_least())
                        - int(a.has_greatest() and b.has_greatest()))
        demand(product.friendly() == expected, "Cartesian component formula failed")
        demand(product.friendly_dp() == expected, "Cartesian independent DP failed")
        product_cases += 1
    print(f"Cartesian products: {product_cases} cases, independent DP included", flush=True)
    fibers = [Poset.from_relations(1, []), Poset.from_relations(2, [(0,1)]),
              Poset.from_relations(2, []), Poset.from_relations(3, [(0,1),(1,2)])]
    substitution_cases = 0
    for base in base_orders:
        for assignment in itertools.product(fibers, repeat=base.n):
            expected = 0
            for comp in base.components():
                labels = list(bits(comp))
                expected += (assignment[labels[0]].friendly() if len(labels) == 1
                             else sum(assignment[i].n for i in labels)-1)
            lex = base.substitute(assignment)
            demand(lex.friendly() == expected, "Substitution component formula failed")
            demand(lex.friendly_dp() == expected, "Substitution independent DP failed")
            substitution_cases += 1
    print(f"Heterogeneous substitutions: {substitution_cases} cases, independent DP included", flush=True)
    # Independently classify maximum friendly subsets through five elements.
    subset_cases = 0
    root_certificate_cases = 0
    for n in range(6):
        for lower in naturally_labelled_posets(n):
            p = Poset._from_natural_lower(lower)
            target = p.friendly()
            comps = p.components()
            for selected in range(1 << n):
                if selected.bit_count() != target:
                    continue
                @lru_cache(None)
                def restricted_rank(mask: int) -> int:
                    return max((1 + restricted_rank(mask & ~p.upper[x])
                                for x in bits(mask & selected) if p.inc[x] & mask), default=0)
                actual = restricted_rank(p.full) == target
                expected = all((c & ~selected).bit_count() == 1 and
                               p.lower[next(bits(c & ~selected))] & c == (c & ~selected)
                               for c in comps)
                demand(actual == expected, "Maximum-friendly-subset classification failed")
                if expected:
                    roots = list(bits(p.full & ~selected))
                    certificate = p.optimal_certificate(roots)
                    p.check_certificate(certificate)
                    choices = sum(1 << step["choice"] for step in certificate["steps"])
                    demand(choices == selected, "Protected-root certificate used wrong subset")
                    root_certificate_cases += 1
                subset_cases += 1
    print(f"Maximum friendly subsets: {subset_cases} candidates, "
          f"{root_certificate_cases} protected-root certificates", flush=True)
    invalid_count = check_invalid_inputs()
    elapsed = time.perf_counter() - start
    result = {"status":"PASS", "python":platform.python_version(),
              "enumeration":"naturally labelled posets, not isomorphism classes or all labelings",
              "maximum_n":args.max_n,
              "total_finite_posets":sum(r["naturally_labelled_posets"] for r in rows),
              "exhaustive":rows,
              "checks_per_poset":["graph formula vs residual DP", "dual residual DP",
                                  "optimal-sequence simulation and spanning-forest verification"],
              "connected_maximal_noncut_checks":connected_lemma_checks,
              "cartesian_pairs":product_cases,
              "cartesian_factor_sizes":"0 through 4; product support at most 16",
              "heterogeneous_substitutions":substitution_cases,
              "substitution_fibers":"singleton, 2-chain, 2-antichain, 3-chain; base size <=4",
              "maximum_subset_candidates":subset_cases,
              "protected_root_certificates":root_certificate_cases,
              "maximum_subset_support_bound":5,
              "invalid_inputs_rejected":invalid_count,
              "elapsed_seconds":round(elapsed,3),
              "limitations":"Finite computation is not a proof for all finite or infinite posets; no Lean formalization."}
    (args.out / "verification.json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    with (args.out / "rank_distribution.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["n","friendly_order_type","naturally_labelled_posets"])
        for row in rows:
            for rank, count in row["rank_histogram"].items():
                writer.writerow([row["n"], rank, count])
    print(json.dumps({k:v for k,v in result.items() if k != "exhaustive"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
