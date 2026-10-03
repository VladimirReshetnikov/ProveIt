#!/usr/bin/env python3
"""Verify compact compiler, explicit inverse zero-set maps, and expansion."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import random
from sandpile_cubic import Graph, certificate as baseline_certificate
import sandpile_compact as compact
from verify import digest


def run_checks() -> dict:
    if not __debug__:
        raise RuntimeError("verification requires assertions; do not use python -O")
    graphs = [Graph(((0, 1), (1, 0)), (2, 2)),
              Graph(((0, 1, 0), (1, 0, 1), (0, 1, 0)), (2, 2, 2)),
              Graph(((0, 1, 1), (1, 0, 1), (1, 1, 0)), (3, 3, 3))]
    roundtrips = mutations = 0
    for g in graphs:
        for eta in itertools.product(range(5), repeat=g.n):
            old = baseline_certificate(g, eta)
            new = compact.certificate(g, eta)
            assert new == compact.from_baseline(g, eta, old)
            assert old == compact.to_baseline(g, eta, new)
            assert len(new) == 10*g.n+3*len(g.edges)
            assert len(compact.polynomial_terms(g, eta, new)) == 10*g.n+7*len(compact.edges(g))
            roundtrips += 1
            for name in new:
                for delta in (-1, 1):
                    if new[name]+delta >= 0:
                        changed = dict(new)
                        changed[name] += delta
                        assert compact.evaluate(g, eta, changed) > 0
                        mutations += 1
    five_checks = 0
    for delta in range(-8, 9):
        roots = []
        for selectors in itertools.product(range(3), repeat=5):
            for gap in range(9):
                values = (*selectors, gap)
                terms = compact.five_terms(delta, *values)
                assert all(term >= 0 for term in terms)
                if sum(terms) == 0:
                    roots.append(values)
                five_checks += 1
        assert roots == [compact.five_data(delta)]
    rng = random.Random(20261003)
    random_checks = 0
    for _ in range(120):
        n = rng.randrange(1, 7)
        a = [[0]*n for _ in range(n)]
        for v in range(n):
            for j in range(v):
                a[v][j] = a[j][v] = rng.randrange(4)
        g = Graph(tuple(map(tuple, a)), tuple(sum(row)+rng.randrange(1, 4) for row in a))
        eta = tuple(rng.randrange(50) for _ in range(n))
        new = compact.certificate(g, eta)
        old = baseline_certificate(g, eta)
        assert compact.to_baseline(g, eta, new) == old
        assert compact.from_baseline(g, eta, old) == new
        random_checks += 1
    g = graphs[0]
    t = 10**100+7
    new = compact.certificate(g, (t, 0), ((2*t-1)//3, (t-1)//3))
    poly, free, ws = compact.symbolic_polynomial(g)
    assert poly.total_degree() == 3 and len(ws) == 26
    values = dict(zip(free, (t, 0))) | {s: new[str(s)] for s in ws}
    assert poly.as_expr().subs(values) == 0
    data = {"graph": {"a": g.a, "d": g.d}, "degree": int(poly.total_degree()),
        "variable_order": list(map(str, free+ws)), "input_count": len(free),
        "certificate_count": len(ws), "terms": [
            {"coefficient": int(c), "exponents": list(mon)} for mon, c in poly.terms()]}
    example = Path("example")
    example.mkdir(exist_ok=True)
    (example/"compact_two_site_polynomial.json").write_text(json.dumps(data, indent=2)+"\n")
    (example/"compact_two_site_polynomial.txt").write_text(str(poly.as_expr())+"\n")
    (example/"compact_huge_input_certificate.json").write_text(json.dumps(
        {"eta": [t, 0], "certificate": new}, indent=2)+"\n")
    return {"schema": 1, "random_seed": 20261003, "small_input_roundtrips": roundtrips,
        "mutations_rejected": mutations, "five_way_tuples_checked": five_checks,
        "weighted_graph_roundtrips": random_checks, "two_site": {
            "certificate_variables": len(ws), "summands": 27,
            "expanded_degree": int(poly.total_degree()), "monomials": len(poly.terms()),
            "coefficient_table_sha256": digest(data), "huge_input_value": 0,
            "huge_certificate_sha256": digest(new)}, "all_checks_passed": True}


if __name__ == "__main__":
    receipt = run_checks()
    Path("verification_compact.json").write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps(receipt, indent=2))
