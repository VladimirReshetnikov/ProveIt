#!/usr/bin/env python3
"""Recompute the certificate and run independent exact tests; no dependencies."""
from __future__ import annotations
import csv
import json
import random
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from time import perf_counter
from domination import (adjacency, components, brute_polynomial, core_polynomial,
                        leaf_polynomial, leaf_terms, evaluate, derivative,
                        divide_linear, mul, construction_shapes, rooted_polynomials,
                        four_cycle_certificate)

ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> None:
    start = perf_counter()
    graph = json.loads((ROOT / 'data/graph30.json').read_text())
    n, edges = graph['order'], [tuple(e) for e in graph['edges']]
    adj = adjacency(n, edges)
    require(n == 30 and len(edges) == 31, 'Wrong graph size')
    require(len(components(adj)) == 1, 'Graph is disconnected')
    p1, core = core_polynomial(n, edges)
    p2 = leaf_polynomial(n, edges)
    p3 = four_cycle_certificate()
    require(p1 == p2 == p3 == tuple(graph['coefficients']), 'Polynomial mismatch')
    require(evaluate(p1, -4) == 0, 'The proposed root is not exact')
    gamma = next(i for i, v in enumerate(p1) if v)
    require(gamma == 10, 'Incorrect domination number')
    q, remainder = divide_linear(p1[gamma:], -4)
    require(remainder == 0, 'Synthetic division failed')
    require(mul((0,) * gamma + (4, 1), q) == p1, 'Factorization failed')
    slope = evaluate(derivative(p1), -4)
    require(slope == -40179620380672, 'Incorrect derivative certificate')
    require(evaluate(q, -4) == -38318272, 'Incorrect quotient certificate')
    states = {name: tuple(evaluate(p, -4) for p in rooted_polynomials(shape))
              for name, shape in construction_shapes().items()}
    ratios = {name: Fraction(b, a + b) for name, (a, b, c) in states.items()
              if c == 0 and a + b != 0}
    a, b, c, r = (ratios[name] for name in ('E', 'T', 'K', 'S5'))
    require(21 + c + r * (a + b) == 0, 'Rational cancellation failed')
    # All labelled simple graphs on at most five vertices, including n=0.
    exhaustive = 0
    for k in range(6):
        possible = list(combinations(range(k), 2))
        for mask in range(1 << len(possible)):
            es = [e for i, e in enumerate(possible) if mask & (1 << i)]
            brute = brute_polynomial(k, es)
            require(core_polynomial(k, es)[0] == brute, f'Core test failed n={k}')
            require(leaf_polynomial(k, es) == brute, f'Leaf test failed n={k}')
            exhaustive += 1
    # Deterministic larger random tests.
    rng = random.Random(20260918)
    for _ in range(120):
        k = rng.randrange(6, 10)
        es = [e for e in combinations(range(k), 2) if rng.randrange(4) == 0]
        brute = brute_polynomial(k, es)
        require(core_polynomial(k, es)[0] == brute, 'Random core test failed')
        require(leaf_polynomial(k, es) == brute, 'Random leaf test failed')
    # Test the connected root-preserving path-of-supports construction.
    family_edges = list(edges)
    last = 10
    for t in range(1, 6):
        u, v = 30 + 2 * (t - 1), 31 + 2 * (t - 1)
        family_edges += [(last, u), (u, v)]
        last = u
        expected = p1
        for _ in range(t):
            expected = mul(expected, (0, 2, 1))
        require(core_polynomial(30 + 2 * t, family_edges)[0] == expected,
                f'Connected-family test failed t={t}')
    terms = leaf_terms(n, edges)
    (ROOT / 'results').mkdir(exist_ok=True)
    with (ROOT / 'data/coefficients.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['degree', 'coefficient'])
        writer.writerows(enumerate(p1))
    with (ROOT / 'data/leaf_certificate.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['a', 'b', 'multiplicity_of_x^a_(1+x)^b'])
        writer.writerows((a, b, m) for (a, b), m in sorted(terms.items()))
    report = {'passed': True, 'order': n, 'edges': len(edges),
              'cyclomatic_number': len(edges) - n + 1,
              'maximum_degree': max(map(len, adj)),
              'leaves': sum(len(nb) == 1 for nb in adj), 'two_core': core,
              'gamma': gamma, 'D_minus4': evaluate(p1, -4),
              'D_derivative_minus4': slope, 'Q_minus4': evaluate(q, -4),
              'quotient_coefficients_ascending': q,
              'rooted_states_at_minus4': states,
              'rooted_ratios': {name: str(value) for name, value in ratios.items()},
              'three_polynomial_certificates_agree': True,
              'exhaustive_small_graph_tests': exhaustive,
              'random_graph_tests': 120, 'connected_family_tests': 5,
              'leaf_certificate_terms': len(terms),
              'admissible_nonleaf_subsets': sum(terms.values()),
              'elapsed_seconds': round(perf_counter() - start, 3)}
    (ROOT / 'results/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
