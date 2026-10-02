#!/usr/bin/env python3
"""Reproduce finite checks and the coefficient-level example.

Run: python verify.py --output verification.json
Optional: --export-dir example (requires SymPy).
The finite checks supplement, and do not replace, the manuscript's proofs.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import random
from typing import Any

from sandpile_cubic import (Graph, burning_ranks, box_graph, certificate,
    collar_heights, comparison_data, comparison_terms, evaluate, local_rank_test,
    names, polynomial_terms, stabilize, stabilize_parallel, symbolic_polynomial)


def digest(obj: Any) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def run_checks(export_dir: Path | None) -> dict[str, Any]:
    if not __debug__:
        raise RuntimeError("verification requires assertions; do not use python -O")
    receipt: dict[str, Any] = {"schema": 1, "seed": 20261002,
        "scope": "Exact finite checks only; semantic proofs are in article.tex.",
        "witness_domain": "nonnegative integers, including zero"}
    graphs = {
        "two_sites": Graph(((0, 1), (1, 0)), (2, 2)),
        "three_site_path": Graph(((0, 1, 0), (1, 0, 1), (0, 1, 0)), (2, 2, 2)),
        "triangle_with_sink_edges": Graph(((0, 1, 1), (1, 0, 1), (1, 1, 0)), (3, 3, 3)),
    }
    # A complete bounded search over proposed odometers, not merely successful runs.
    exhaustive = {}
    for label, graph in graphs.items():
        checked = stable_candidates = accepted = 0
        for eta in itertools.product(range(5), repeat=graph.n):
            actual, final = stabilize(graph, eta)
            assert (actual, final) == stabilize_parallel(graph, eta)
            assert (actual, final) == stabilize(graph, eta, bulk=False, reverse=True)
            assert evaluate(graph, eta, certificate(graph, eta, actual)) == 0
            for candidate in itertools.product(range(7), repeat=graph.n):
                checked += 1
                lu = graph.laplacian(candidate)
                z = tuple(eta[v]-lu[v] for v in range(graph.n))
                passes = False
                if all(0 <= z[v] < graph.d[v] for v in range(graph.n)):
                    stable_candidates += 1
                    passes = burning_ranks(graph, candidate, z) is not None
                assert passes == (candidate == actual), (label, eta, candidate, z)
                accepted += int(passes)
        exhaustive[label] = {"candidate_checks": checked,
            "stable_candidates": stable_candidates, "accepted_candidates": accepted}
    receipt["exhaustive_odometer_checks"] = exhaustive

    rank_checks = 0
    for graph in graphs.values():
        for z in itertools.product(*(range(deg) for deg in graph.d)):
            for support in itertools.product((0, 1), repeat=graph.n):
                canonical = burning_ranks(graph, support, z)
                matches = []
                options = [range(1, graph.n+3) if b else (0,) for b in support]
                for ranks in itertools.product(*options):
                    rank_checks += 1
                    if local_rank_test(graph, support, z, ranks):
                        matches.append(ranks)
                assert matches == ([] if canonical is None else [canonical])
    receipt["canonical_rank_assignments_checked"] = rank_checks

    comparator_checks = 0
    for x, y in itertools.product(range(-3, 7), repeat=2):
        roots = []
        for b, c, s in itertools.product(range(4), range(4), range(13)):
            terms = comparison_terms(x, y, b, c, s)
            assert all(t >= 0 for t in terms)
            comparator_checks += 1
            if sum(terms) == 0:
                roots.append((b, c, s))
        assert roots == [comparison_data(x, y)]
    receipt["comparator_tuples_checked"] = comparator_checks

    rng = random.Random(receipt["seed"])
    weighted_checks = 0
    for _ in range(120):
        n = rng.randrange(1, 7)
        a = [[0]*n for _ in range(n)]
        for v in range(n):
            for j in range(v):
                a[v][j] = a[j][v] = rng.randrange(4)
        # A sink edge at each vertex guarantees dissipativity, even if disconnected.
        d = tuple(sum(a[v])+rng.randrange(1, 4) for v in range(n))
        graph = Graph(tuple(map(tuple, a)), d)
        eta = tuple(rng.randrange(41) for _ in range(n))
        actual = stabilize(graph, eta)
        assert actual == stabilize_parallel(graph, eta)
        assert actual == stabilize(graph, eta, bulk=False, reverse=True)
        assert evaluate(graph, eta, certificate(graph, eta)) == 0
        weighted_checks += 1
    receipt["weighted_multigraph_inputs"] = weighted_checks

    graph = graphs["two_sites"]
    mutation_checks = 0
    for eta in ((0, 0), (1, 0), (2, 0), (4, 0), (19, 17)):
        w = certificate(graph, eta)
        for name in names(graph):
            for delta in (-1, 1):
                if w[name]+delta >= 0:
                    changed = dict(w)
                    changed[name] += delta
                    assert evaluate(graph, eta, changed) > 0
                    mutation_checks += 1
    receipt["single_coordinate_mutations_rejected"] = mutation_checks

    invalid = 0
    bad_graphs = [(((0, 2), (1, 0)), (1, 3)),  # directed counterexample excluded
                  (((0, 1), (1, 0)), (1, 1)),  # no sink
                  (((1,),), (2,)),             # loop
                  (((0,),), (0,))]
    for a, d in bad_graphs:
        try:
            Graph(a, d)
        except ValueError:
            invalid += 1
        else:
            raise AssertionError("invalid graph accepted")
    for bad in (-1, True, 1.0):
        w = certificate(graph, (1, 0))
        w["u_0"] = bad
        try:
            evaluate(graph, (1, 0), w)
        except ValueError:
            invalid += 1
        else:
            raise AssertionError("invalid natural witness accepted")
    receipt["malformed_inputs_rejected"] = invalid

    # Direct verification of why the theorem must not be used on arbitrary digraphs.
    directed_L = ((1, -2), (-1, 3))
    eta = (0, 2)
    fake = (2, 1)
    z = tuple(eta[v]-sum(directed_L[v][j]*fake[j] for j in range(2)) for v in range(2))
    assert z == (0, 1) and eta[0] < 1 and eta[1] < 3
    assert z[1] >= 1 and z[0] >= 0  # ranks (2,1) pass the naive incoming test
    assert z[0] < 2                # rank-2 failure also passes
    receipt["directed_counterexample"] = {"L": directed_L, "eta": eta,
        "actual_u": [0, 0], "spurious_u": fake, "spurious_z": z, "ranks": [2, 1]}

    # Canonical radius and collar conditions on an infinite line, zero background.
    box_checks = 0
    radius_records = []
    for chips in range(13):
        eta_fn = lambda x, chips=chips: chips if x == (0,) else 0
        big, sites = box_graph(1, 7)
        big_u, _ = stabilize(big, tuple(eta_fn(x) for x in sites))
        assert all(h < 2 for h in collar_heights(sites, big_u, eta_fn).values())
        support = [abs(x[0]) for x, count in zip(sites, big_u) if count]
        minimum = max(support, default=0)
        accepted_radii = []
        for radius in range(7):
            small, ss = box_graph(1, radius)
            w = certificate(small, tuple(eta_fn(x) for x in ss))
            u = tuple(w[f"u_{v}"] for v in range(small.n))
            closed = all(h < 2 for h in collar_heights(ss, u, eta_fn).values())
            outer_active = sum(w[f"e_{v}"] for v, x in enumerate(ss) if abs(x[0]) == radius)
            canonical = closed and (radius == 0 or outer_active >= 1)
            if canonical:
                accepted_radii.append(radius)
            assert closed == (radius >= minimum)
            box_checks += 1
        assert accepted_radii == [minimum]
        radius_records.append({"chips": chips, "radius": minimum})
    receipt["finite_support_box_checks"] = box_checks
    receipt["line_minimal_radii"] = radius_records

    # Maximal stable background plus one extra grain: collar must not be dropped.
    exploding_checks = 0
    for dim in (1, 2):
        for radius in range(4):
            box, sites = box_graph(dim, radius)
            zero = (0,)*dim
            eta_fn = lambda x, dim=dim, zero=zero: 2*dim-1+int(x == zero)
            u, _ = stabilize(box, tuple(eta_fn(x) for x in sites))
            assert any(h >= 2*dim for h in collar_heights(sites, u, eta_fn).values())
            exploding_checks += 1
    receipt["unstable_collar_rejections"] = exploding_checks

    bound_checks = 0
    for dim in (1, 2, 3):
        for radius in (0, 1, 2):
            box, sites = box_graph(dim, radius)
            eta = tuple(rng.randrange(2*dim+5) for _ in sites)
            u, _ = stabilize(box, eta)
            M = max(eta)
            assert all(2*count <= M*((radius+1)**2-x[0]**2)
                       for x, count in zip(sites, u))
            bound_checks += 1
    receipt["quadratic_spatial_bounds_checked"] = bound_checks

    period_checks = 0
    for t in range(301):
        u, z = stabilize(graph, (t, 0))
        expected = (0, 0) if t == 0 else ((2*t-1)//3, (t-1)//3)
        assert u == expected
        if t >= 1:
            expected_z = {0: (1, 1), 1: (1, 0), 2: (0, 1)}[t % 3]
            assert z == expected_z
        if t >= 4:
            newer, newer_z = stabilize(graph, (t+3, 0))
            assert newer == (u[0]+2, u[1]+1) and newer_z == z
            assert burning_ranks(graph, newer, z) == burning_ranks(graph, u, z)
        period_checks += 1
    receipt["two_site_period_inputs"] = period_checks
    huge = 10**100+7
    huge_u = ((2*huge-1)//3, (huge-1)//3)
    w = certificate(graph, (huge, 0), huge_u)
    receipt["huge_input"] = {"eta": [huge, 0], "u": huge_u,
        "topplings": sum(huge_u), "coordinates": len(w),
        "summands": len(polynomial_terms(graph, (huge, 0), w)),
        "polynomial_value": evaluate(graph, (huge, 0), w), "certificate_sha256": digest(w)}

    # Exact rational-period computation, separate from floating-point numerics.
    import sympy as sp
    period_graphs = 0
    for label, g in graphs.items():
        L = sp.Matrix([[g.d[v]*int(v == j)-g.a[v][j] for j in range(g.n)] for v in range(g.n)])
        h = sp.Matrix([1]+[0]*(g.n-1))
        c = L.inv()*h
        b = L.inv()*sp.Matrix([x-1 for x in g.d])
        q = int(sp.ilcm(*[x.q for x in c])) if g.n > 1 else int(c[0].q)
        T = 1+max(int(sp.floor(b[v]/c[v])) for v in range(g.n))
        nu = tuple(int(q*x) for x in c)
        assert int(L.det()) % q == 0
        observed = []
        for t in range(T, T+2*q+2):
            u, z = stabilize(g, (t,)+(0,)*(g.n-1))
            newer, zz = stabilize(g, (t+q,)+(0,)*(g.n-1))
            assert newer == tuple(u[v]+nu[v] for v in range(g.n)) and z == zz
            observed.append(z)
        for p in range(1, q):
            assert any(observed[i] != observed[i+p] for i in range(q))
        period_graphs += 1
    receipt["exact_period_graphs"] = period_graphs

    if export_dir is not None:
        export_dir.mkdir(parents=True, exist_ok=True)
        poly, free, aux = symbolic_polynomial(graph)
        assert len(aux) == 38 and poly.total_degree() == 3
        assert len(polynomial_terms(graph, free, dict(zip(names(graph), aux)))) == 40
        gens = tuple(free)+tuple(aux)
        data = {"graph": {"a": graph.a, "d": graph.d},
            "variable_order": [str(v) for v in gens], "input_count": len(free),
            "certificate_count": len(aux), "degree": int(poly.total_degree()),
            "terms": [{"coefficient": int(coef), "exponents": list(mon)}
                      for mon, coef in poly.terms()]}
        (export_dir/"two_site_polynomial.json").write_text(json.dumps(data, indent=2)+"\n")
        (export_dir/"two_site_polynomial.txt").write_text(str(poly.as_expr())+"\n")
        substitutions = dict(zip(free, (huge, 0))) | {symbol: w[str(symbol)] for symbol in aux}
        assert poly.as_expr().subs(substitutions) == 0
        (export_dir/"huge_input_certificate.json").write_text(json.dumps(
            {"eta": [huge, 0], "certificate": w}, indent=2)+"\n")
        receipt["symbolic_export"] = {"degree": int(poly.total_degree()),
            "input_variables": len(free), "certificate_variables": len(aux),
            "expanded_monomials": len(poly.terms()), "coefficient_table_sha256": digest(data)}
    receipt["all_checks_passed"] = True
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    parser.add_argument("--export-dir", type=Path, default=Path("example"))
    args = parser.parse_args()
    receipt = run_checks(args.export_dir)
    args.output.write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
