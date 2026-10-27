"""Reproduce exact finite algebra and integer-selector checks; standard library only."""

import argparse
from copy import deepcopy
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
import random

from affine_kernel import EDGES, PLANS, assignments, brute_force, contract, incident, plan_scores, select_plan


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def independent_scores(domains):
    if 0 in domains:
        return None
    result = []
    for plan in PLANS:
        operations = []
        for line in plan:
            pair = frozenset(line[1:])
            whole = frozenset(line)
            operations.extend(((frozenset((line[1],)), frozenset((line[2],)), frozenset(range(9)) - pair),
                               (frozenset((line[0],)), pair, frozenset(range(9)) - whole)))
        operations.append(tuple(frozenset(line) for line in plan))
        score = 0
        for triple in operations:
            dimensions = []
            for i, j in combinations(range(3), 2):
                dimensions.append(prod(domains[e] for e, (a, b) in enumerate(EDGES)
                                       if (a in triple[i] and b in triple[j]) or
                                          (a in triple[j] and b in triple[i])))
            score = max(score, *(prod(dimensions) ** 5 // d ** 3 for d in dimensions))
        result.append(score)
    return tuple(result)


def make_factors(domains, precision, seed, kind="random"):
    rng = random.Random(seed)
    result = []
    for v in range(9):
        values = {}
        for key in assignments(incident(v), domains):
            if kind == "one":
                value = 1
            elif kind == "zero" and v == 4:
                value = 0
            else:
                value = rng.randrange(-(1 << precision), 2 << precision)
            values[key] = value
        result.append(values)
    return result


def main(output):
    rng = random.Random(20261026)
    fixtures = []
    fixtures.append(("all_singleton_domains", [1] * 36, 7, "random"))
    fixtures.append(("all_one_factors", [2 if i < 10 else 1 for i in range(36)], 13, "one"))
    fixtures.append(("zero_factor", [2 if i < 8 else 1 for i in range(36)], 7, "zero"))
    zero_domains = [1] * 36
    zero_domains[8] = 0
    fixtures.append(("empty_edge_domain", zero_domains, 5, "random"))
    for case in range(20):
        edges = list(range(36))
        rng.shuffle(edges)
        active = (1, 3, 6, 8, 10, 12)[case % 6]
        domains = [1] * 36
        for e in edges[:active]:
            domains[e] = 2
        if case % 3 == 0:
            domains[edges[0]] = 3
        fixtures.append(("seeded_%02d" % case, domains, (1, 2, 4, 7, 11)[case % 5], "random"))

    records = []
    total_assignments = 0
    for number, (name, domains, precision, kind) in enumerate(fixtures):
        factors = make_factors(domains, precision, 7000 + number, kind)
        direct = brute_force(domains, factors, precision)
        scores = plan_scores(domains)
        require(scores == independent_scores(domains), "Selector score mismatch: " + name)
        if scores is not None:
            require(select_plan(domains) == min(range(4), key=lambda j: (scores[j], j)),
                    "Selector decision mismatch: " + name)
        each = [contract(domains, factors, precision, j) for j in range(4)]
        selected = contract(domains, factors, precision)
        require(all(r["value"] == direct for r in each), "Plan value mismatch: " + name)
        require(selected["value"] == direct, "Selected contraction mismatch: " + name)
        require(selected["plan"] == select_plan(domains), "Wrong selected plan: " + name)
        if kind == "one":
            require(direct == prod(domains) % (1 << precision), "Constant-one sum mismatch")
        if kind == "zero" or 0 in domains:
            require(direct == 0, "Expected zero contraction")
        if 0 not in domains:
            calls = sum(prod(domains[e] for e in incident(v)) for v in range(9))
            require(all(r["cached_entries"] == calls for r in each), "Unpaid/repeated singleton entry")
        total_assignments += prod(domains)
        records.append({"name": name, "precision": precision, "active_edges": sum(d > 1 for d in domains),
                        "domain_product": prod(domains), "value": direct,
                        "selected_plan": selected["plan"], "scores": scores,
                        "cached_entries": selected["cached_entries"],
                        "binary_products": [r["binary_products"] for r in each],
                        "triangle_terms": [r["triangle_terms"] for r in each]})

    rejected = []
    valid_domains = [1] * 36
    valid_factors = make_factors(valid_domains, 4, 100)
    bad_factors = deepcopy(valid_factors)
    bad_factors[0].clear()
    bad_entries = deepcopy(valid_factors)
    bad_entries[0][(0,) * 8] = "not an integer"
    tests = (
        ("negative_domain", lambda: select_plan([-1] + [1] * 35)),
        ("wrong_domain_count", lambda: select_plan([1] * 35)),
        ("boolean_domain", lambda: select_plan([True] + [1] * 35)),
        ("invalid_precision", lambda: contract(valid_domains, valid_factors, 0)),
        ("invalid_plan", lambda: contract(valid_domains, valid_factors, 4, 4)),
        ("incomplete_factor", lambda: contract(valid_domains, bad_factors, 4)),
        ("noninteger_factor", lambda: contract(valid_domains, bad_entries, 4)),
    )
    for label, test in tests:
        try:
            test()
        except ValueError:
            rejected.append(label)
        else:
            raise RuntimeError("Negative control accepted: " + label)

    result = {"status": "passed", "seed": 20261026, "fixtures": len(records),
              "plan_contractions_checked": 4 * len(records),
              "selected_contractions_checked": len(records),
              "direct_assignments_enumerated": total_assignments,
              "negative_controls_rejected": rejected, "records": records,
              "scope": "Exact finite Z/(2^p) graph contractions and integer selection; naive arithmetic backend; not a SAT solver or asymptotic matrix implementation."}
    Path(output).parent.mkdir(parents=True, exist_ok=True)
    Path(output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in ("status", "fixtures", "plan_contractions_checked", "selected_contractions_checked", "direct_assignments_enumerated")}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=str(Path(__file__).with_name("results.json")))
    main(parser.parse_args().output)
