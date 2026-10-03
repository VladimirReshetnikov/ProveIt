#!/usr/bin/env python3
"""Exact finite verification. These checks support, but do not replace, proofs.

Run: python code/verify.py --max-n 8 --output results/verification.json
All random choices use a fixed seed and integer/rational arithmetic.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
from math import comb
from pathlib import Path
import platform
import random
import time

import networkx as nx
import sympy as sp
from marked_trees import (hull, recognize, terminal_skeleton, stable_polynomial,
                          maximum_weight_stable, nearest_stable, product)


def powerset(vertices):
    vertices = list(vertices)
    for bits in range(1 << len(vertices)):
        yield {v for i, v in enumerate(vertices) if bits >> i & 1}


def trees(n):
    if n == 1:
        yield nx.empty_graph(1)
    else:
        for t in nx.nonisomorphic_trees(n):
            yield nx.convert_node_labels_to_integers(t)


def exact_psd(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    while a:
        if any(a[i][i] < 0 for i in range(len(a))):
            return False
        zero = next((i for i in range(len(a)) if a[i][i] == 0), None)
        if zero is not None:
            if any(a[zero]):
                return False
            keep = [i for i in range(len(a)) if i != zero]
            a = [[a[i][j] for j in keep] for i in keep]
        else:
            pivot = a[0][0]
            a = [[a[i][j] - a[i][0] * a[0][j] / pivot
                  for j in range(1, len(a))] for i in range(1, len(a))]
    return True


def forced_covariance(tree, marks, paths):
    """Candidate forced by marked singletons and terminal-to-terminal paths."""
    c = [[Fraction(0) for _ in tree] for _ in tree]
    for a in marks:
        c[a][a] = 1
    for a, b in combinations(marks, 2):
        if not (set(paths[a][b][1:-1]) & marks):
            c[a][b] = c[b][a] = Fraction(-1, 2)
    return c


def matching_supports(tree, marks):
    n = len(tree)
    edges = list(tree.edges())
    adj = [0] * n
    for j, (a, b) in enumerate(edges):
        adj[a] |= 1 << j
        adj[b] |= 1 << j
    for a in marks:
        adj[a] |= 1 << (n - 1)
    dp = [set() for _ in range(1 << n)]
    dp[0].add(0)
    out = {(0, 0)}
    for rows in range(1, 1 << n):
        bit = rows & -rows
        i = bit.bit_length() - 1
        for columns in dp[rows ^ bit]:
            available = adj[i] & ~columns
            while available:
                new = available & -available
                available ^= new
                dp[rows].add(columns | new)
        out.update((rows, columns) for columns in dp[rows])
    return out, edges


def cofactor_checks(tree, marks, c):
    """Full coefficient check, not sampled evaluations; orders <= 5 in main()."""
    n = len(tree)
    supports, edges = matching_supports(tree, marks)
    b = sp.zeros(n, n - 1)
    for j, (a, v) in enumerate(edges):
        b[a, j], b[v, j] = 1, -1
    c = sp.Matrix(c)
    checks = 0
    for k in range(n + 1):
        for rows in combinations(range(n), k):
            mask = sum(1 << i for i in rows)
            for cols in combinations(range(n - 1), k):
                value = b.extract(rows, cols).det()**2
                cmask = sum(1 << j for j in cols)
                assert value == int((mask, cmask) in supports)
                checks += 1
            if not k:
                continue
            for cols in combinations(range(n - 1), k - 1):
                m = b.extract(rows, cols)
                q = sp.zeros(n, 1)
                for j, v in enumerate(rows):
                    minor = m.extract([i for i in range(k) if i != j], range(k - 1))
                    q[v] = (-1)**(j + k - 1) * minor.det()
                value = (q.T * c * q)[0]
                cmask = sum(1 << j for j in cols) | (1 << (n - 1))
                assert value == int((mask, cmask) in supports), (tree.edges(), marks, rows, cols, value)
                checks += 1
    return checks


def unmarked_branch_witness(tree, marks, branch):
    """Find three induced odd paths to the apex, checking the stated obstruction."""
    paths = []
    for neighbor in tree[branch]:
        queue = [(neighbor, branch, [branch, neighbor])]
        while queue:
            node, previous, path = queue.pop(0)
            if node in marks:
                paths.append(path)
                break
            queue.extend((v, node, path + [v]) for v in tree[node] if v != previous)
        if len(paths) == 3:
            break
    assert len(paths) == 3
    assert all(set(path[:-1]).isdisjoint(marks) and path[-1] in marks for path in paths)
    assert all(set(a[1:]).isdisjoint(b[1:]) for a, b in combinations(paths, 2))
    vertices = set().union(*(set(p) for p in paths))
    assert len(tree.subgraph(vertices).edges()) == sum(len(p) - 1 for p in paths)
    return [2 * (len(p) - 1) + 1 for p in paths]


def rayleigh_certificate(tree, marks, v):
    n = len(tree)
    c = sp.Matrix(forced_covariance(tree, marks, dict(nx.all_pairs_shortest_path(tree))))
    v = sp.Matrix(v)
    energy = (v.T * c * v)[0]
    assert energy < 0 and all(a > 0 for a in v)
    y = [1 / (v[a] * v[b]) for a, b in tree.edges()]
    x = [sp.Rational(tree.degree(i), 1) / v[i]**2 -
         sum(1 / (v[i] * v[j]) for j in tree[i]) for i in tree]
    L = sp.diag(*x)
    for (a, b), w in zip(tree.edges(), y):
        L[a, a] += w; L[b, b] += w
        L[a, b] -= w; L[b, a] -= w
    scale = product(1 / a**2 for a in v)
    assert L.det() == 0 and L.adjugate() == scale * v * v.T
    return {"n": n, "edges": list(tree.edges()), "marks": sorted(marks),
            "v": list(map(str, v)), "energy": str(energy),
            "x": list(map(str, x)), "y": list(map(str, y)),
            "rayleigh_differences": [str(scale**2 * a**2 * energy) for a in v]}


def main(max_n, output):
    start = time.monotonic()
    rng = random.Random(20260930)
    rows = []
    totals = Counter()
    for n in range(1, max_n + 1):
        row = Counter(n=n)
        for tree in trees(n):
            row["trees"] += 1
            paths = dict(nx.all_pairs_shortest_path(tree))
            connected = [w for w in powerset(tree) if w and nx.is_connected(tree.subgraph(w))] if n <= 6 else []
            stable_sets = []
            for marks in powerset(tree):
                result = recognize(tree, marks, validate=False)
                row["marked_instances"] += 1
                row[result.kind.split('_')[0] if result.stable else result.kind] += 1
                if result.stable:
                    stable_sets.append(marks)
                    row["stable_instances"] += 1
                c = forced_covariance(tree, marks, paths)
                if result.kind != "unmarked_branch":
                    assert exact_psd(c) == result.stable
                    totals["exact_psd_comparisons"] += 1
                else:
                    lengths = unmarked_branch_witness(tree, marks, result.unmarked_branch)
                    assert len(lengths) == 3 and all(k >= 3 and k % 2 for k in lengths)
                    totals["unmarked_branch_witnesses"] += 1
                if connected:
                    holds = all(sum(c[a][b] for a in w for b in w) == int(bool(w & marks)) for w in connected)
                    assert holds == (result.kind != "unmarked_branch")
                    totals["connected_energy_instances"] += 1
                if n <= 5 and result.kind != "unmarked_branch":
                    totals["exact_minor_coefficients"] += cofactor_checks(tree, marks, c)
                    totals["full_polynomial_identity_instances"] += 1
            maximum_size = max(map(len, stable_sets))
            diameter = nx.diameter(tree)
            assert diameter + 1 <= maximum_size <= min(n, diameter + 3)
            totals["diameter_window_checks"] += 1
            for weights in ({v: 1 for v in tree}, {v: rng.randint(1, 5) for v in tree}):
                expected = [0] * (n + 1)
                for marks in stable_sets:
                    expected[len(marks)] += product(weights[v] for v in marks)
                actual = stable_polynomial(tree, weights)
                assert actual == expected, (tree.edges(), weights, actual, expected)
                totals["enumerator_comparisons"] += 1
            for trial in range(3):
                scores = {v: rng.randint(-5, 5) for v in tree}
                value, chosen = maximum_weight_stable(tree, scores)
                assert recognize(tree, chosen).stable
                assert value == max(sum(scores[v] for v in marks) for marks in stable_sets)
                totals["optimization_comparisons"] += 1
            original = {v for v in tree if rng.randrange(2)}
            distance, chosen = nearest_stable(tree, original)
            assert distance == min(len(original ^ marks) for marks in stable_sets)
            totals["repair_comparisons"] += 1
        rows.append(dict(row))
        print(json.dumps(dict(row)), flush=True)
    theta = nx.star_graph(3)
    supports, _ = matching_supports(theta, {1, 2, 3})
    p = [0] * 5
    for i, j in supports:
        p[i.bit_count()] += 1
    t = sp.symbols('t')
    polynomial = sum(c * t**k for k, c in enumerate(p))
    discriminant = sp.discriminant(polynomial, t)
    assert p == [1, 9, 24, 16, 1] and discriminant == -5243
    for n in (1, 2, 4, 9, 15):
        assert stable_polynomial(nx.path_graph(n)) == [comb(n, k) for k in range(n + 1)]
    for m in range(11):
        expected = [0] * (m + 2)
        for k in range(min(m, 2) + 1):
            expected[k] += comb(m, k)
        for k in range(min(m, 4) + 1):
            expected[k + 1] += comb(m, k)
        assert stable_polynomial(nx.star_graph(m)) == expected
    shape_counterexamples = {str(m): stable_polynomial(nx.star_graph(m)) for m in (3, 4, 6)}
    assert shape_counterexamples["3"] == [1, 4, 6, 3, 1]
    assert shape_counterexamples["4"][3]**2 < shape_counterexamples["4"][2] * shape_counterexamples["4"][4]
    assert shape_counterexamples["6"][2] > shape_counterexamples["6"][3] < shape_counterexamples["6"][4]
    star = nx.star_graph(5)
    extended = star.copy()
    extended.remove_edge(0, 1)
    extended.add_edges_from([(0, 6), (6, 1), (6, 7), (7, 8)])
    certificates = [rayleigh_certificate(star, set(star), [2, 1, 1, 1, 1, 1]),
                    rayleigh_certificate(extended, set(range(6)), [2, 1, 1, 1, 1, 1, 1, 1, 1])]
    result = {"status": "All listed exact finite checks passed; these are not formal proofs.",
              "max_tree_size": max_n, "seed": 20260930,
              "versions": {"python": platform.python_version(), "networkx": nx.__version__, "sympy": sp.__version__},
              "table": rows, "checks": dict(totals),
              "theta_three": {"polynomial_coefficients": p, "discriminant": int(discriminant)},
              "rayleigh_certificates": certificates,
              "neighborhood_polynomial_counterexamples": shape_counterexamples,
              "path_formula_instances": 5, "star_formula_instances": 11,
              "elapsed_seconds": round(time.monotonic() - start, 3)}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result["checks"], indent=2), flush=True)
    print(f"Saved {output}", flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=8)
    parser.add_argument('--output', type=Path, default=Path('results/verification.json'))
    args = parser.parse_args()
    if not 1 <= args.max_n <= 10:
        parser.error('--max-n must lie between 1 and 10')
    main(args.max_n, args.output)
