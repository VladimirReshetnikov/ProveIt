#!/usr/bin/env python3
"""Exact, reproducible finite checks for the accompanying research manuscript.

These tests corroborate, but do not replace, the all-size proofs.  In particular,
weighted evaluation of a proposed polynomial identity is not an identity proof.
Dependencies: Python >=3.11, SymPy, NetworkX.  No network access is used.
Run from any directory: python code/verify.py
"""
from __future__ import annotations

import argparse
import json
import platform
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
from typing import Iterable, Sequence

import networkx as nx
import sympy as sp


def masks_weights(values: Sequence[int]) -> list[int]:
    result = [1] * (1 << len(values))
    for mask in range(1, len(result)):
        bit = mask & -mask
        result[mask] = result[mask ^ bit] * values[bit.bit_length() - 1]
    return result


def matching_supports(adjacency: Sequence[int], right_size: int) -> list[tuple[int, int]]:
    """Enumerate endpoint pairs once, not once per perfect matching.

    dp[I] is the set of right endpoint masks attainable by matching every row
    of I.  The use of a set removes all multiplicities of matchings.
    """
    if any(a < 0 or a >= 1 << right_size for a in adjacency):
        raise ValueError("An adjacency mask is outside the right vertex set")
    dp: list[set[int]] = [set() for _ in range(1 << len(adjacency))]
    dp[0].add(0)
    result: list[tuple[int, int]] = [(0, 0)]
    for rows in range(1, len(dp)):
        bit = rows & -rows
        i = bit.bit_length() - 1
        for cols in dp[rows ^ bit]:
            available = adjacency[i] & ~cols
            while available:
                new_bit = available & -available
                available ^= new_bit
                dp[rows].add(cols | new_bit)
        result.extend((rows, cols) for cols in sorted(dp[rows]))
    return result


def basis_masks(supports: Iterable[tuple[int, int]], rank: int) -> list[int]:
    full = (1 << rank) - 1
    return [(full ^ rows) | (cols << rank) for rows, cols in supports]


def support_polynomial(supports: Iterable[tuple[int, int]], u: sp.Symbol) -> sp.Expr:
    counts = Counter(rows.bit_count() for rows, _ in supports)
    return sum(value * u**degree for degree, value in counts.items())


def evaluate_basis(supports: Iterable[tuple[int, int]],
                   x: Sequence[int], y: Sequence[int]) -> int:
    xw, yw = masks_weights(x), masks_weights(y)
    full = (1 << len(x)) - 1
    return sum(xw[full ^ rows] * yw[cols] for rows, cols in supports)


def tree_apex(tree: nx.Graph) -> tuple[list[int], list[tuple[int, int]]]:
    r = len(tree)
    assert set(tree) == set(range(r)) and nx.is_tree(tree)
    edges = sorted(tuple(sorted(e)) for e in tree.edges())
    adj = [1 << len(edges) for _ in range(r)]
    for j, (a, b) in enumerate(edges):
        adj[a] |= 1 << j
        adj[b] |= 1 << j
    return adj, edges


def covariance(tree: nx.Graph) -> sp.Matrix:
    r = len(tree)
    C = sp.eye(r)
    for a, b in tree.edges():
        C[a, b] = C[b, a] = -sp.Rational(1, 2)
    return C


def weighted_laplacian(edges: Sequence[tuple[int, int]], x: Sequence[int],
                       y: Sequence[int]) -> sp.Matrix:
    L = sp.diag(*x)
    for (a, b), weight in zip(edges, y):
        L[a, a] += weight
        L[b, b] += weight
        L[a, b] -= weight
        L[b, a] -= weight
    return L


def determinant_formula(L: sp.Matrix, C: sp.Matrix, s: int) -> sp.Expr:
    det = L.det()
    if det:
        return sp.cancel(det * (1 + s * sp.trace(L.inv() * C)))
    return s * sp.trace(L.adjugate() * C)


def exact_psd(A: sp.Matrix) -> bool:
    """Exact symmetric Schur test.  A zero diagonal in a PSD matrix has a zero row."""
    A = sp.Matrix(A)
    assert A == A.T
    while A.rows:
        if any(A[i, i] < 0 for i in range(A.rows)):
            return False
        zero = next((i for i in range(A.rows) if A[i, i] == 0), None)
        if zero is not None:
            if any(A[zero, j] != 0 for j in range(A.rows)):
                return False
            keep = [i for i in range(A.rows) if i != zero]
            A = A.extract(keep, keep)
            continue
        a, v = A[0, 0], A[1:, 0]
        A = A[1:, 1:] - v * v.T / a
    return True


def ade_shape(tree: nx.Graph) -> str | None:
    """Independent combinatorial implementation of the list in the article."""
    r = len(tree)
    degrees = dict(tree.degree())
    if max(degrees.values()) <= 2:
        return f"A_{r}"
    branches = [v for v in tree if degrees[v] >= 3]
    if max(degrees.values()) >= 5:
        return None
    if any(degrees[v] == 4 for v in tree):
        return "affine_D_4" if r == 5 and sorted(degrees.values()) == [1, 1, 1, 1, 4] else None
    if len(branches) == 2:
        path = nx.shortest_path(tree, *branches)
        if r != len(path) + 4:
            return None
        for v in branches:
            outside = [w for w in tree[v] if w not in path]
            if len(outside) != 2 or any(degrees[w] != 1 for w in outside):
                return None
        return f"affine_D_{r - 1}"
    if len(branches) != 1:
        return None
    center = branches[0]
    arms = []
    for neighbor in tree[center]:
        length, previous, current = 1, center, neighbor
        while degrees[current] == 2:
            nxt = next(v for v in tree[current] if v != previous)
            previous, current = current, nxt
            length += 1
        arms.append(length)
    a, b, c = sorted(arms)
    if a == b == 1:
        return f"D_{r}"
    names = {(1, 2, 2): "E_6", (1, 2, 3): "E_7", (1, 2, 4): "E_8",
             (2, 2, 2): "affine_E_6", (1, 3, 3): "affine_E_7", (1, 2, 5): "affine_E_8"}
    return names.get((a, b, c))


def unlabeled_trees(r: int) -> Iterable[nx.Graph]:
    if r == 1:
        yield nx.empty_graph(1)
    else:
        for tree in nx.nonisomorphic_trees(r):
            yield nx.convert_node_labels_to_integers(tree)


def cofactor_coefficient_checks(tree: nx.Graph) -> int:
    """Check every apex-containing coefficient using integer incidence minors."""
    r = len(tree)
    adjacency, edges = tree_apex(tree)
    feasible = set(matching_supports(adjacency, r))
    incidence = sp.zeros(r, len(edges))
    for j, (a, b) in enumerate(edges):
        incidence[a, j], incidence[b, j] = 1, -1
    C = covariance(tree)
    checks = 0
    for k in range(1, r + 1):
        for rows in combinations(range(r), k):
            for cols in combinations(range(r - 1), k - 1):
                B = incidence.extract(rows, cols)
                q = sp.zeros(r, 1)
                for i, vertex in enumerate(rows):
                    # Cofactor of the last column of [B,w].
                    minor_rows = [j for j in range(k) if j != i]
                    q[vertex] = (-1)**(i + k - 1) * B.extract(minor_rows, range(k - 1)).det()
                lhs = (q.T * C * q)[0]
                rowmask = sum(1 << i for i in rows)
                colmask = sum(1 << j for j in cols) | (1 << (r - 1))
                assert lhs == int((rowmask, colmask) in feasible), (tree.edges(), rows, cols, lhs)
                checks += 1
    return checks


def multi_theta(lengths: Sequence[int]) -> tuple[list[int], list[int], list[int], list[list[int]]]:
    if not lengths or any(n < 1 for n in lengths):
        raise ValueError("Path lengths must be positive")
    if len({n % 2 for n in lengths}) != 1 or sum(n == 1 for n in lengths) > 1:
        raise ValueError("Require a simple bipartite multi-theta")
    graph, nxt, paths = nx.Graph(), 2, []
    for length in lengths:
        path = [0] + list(range(nxt, nxt + length - 1)) + [1]
        nxt += length - 1
        graph.add_edges_from(zip(path, path[1:]))
        paths.append(path)
    colors = nx.bipartite.color(graph)
    left = sorted(v for v in graph if colors[v] == colors[0])
    right = sorted(set(graph) - set(left))
    adjacency = [sum(1 << j for j, v in enumerate(right) if graph.has_edge(u, v)) for u in left]
    return left, right, adjacency, paths


def even_theta_minor_check(lengths: Sequence[int]) -> int:
    """Exact expected squared determinants, with sqrt(2) retained symbolically.

    The two alternating terms give the same expectation independently of the
    biases of signs not present on their alternating cycle.  Enumerating signs
    here is deliberately an independent, small-instance verification.
    """
    left, right, adjacency, paths = multi_theta(lengths)
    r, c = len(left), len(right)
    supported = set(matching_supports(adjacency, c))
    matrices = []
    root2 = sp.sqrt(2)
    for signs in product((-1, 1), repeat=len(paths)):
        K = sp.zeros(r, c)
        probability = sp.Integer(1)
        for path, sign in zip(paths, signs):
            # E sign = -1/sqrt(2).
            probability *= (1 - sign / root2) / 2
            for step in range(0, len(path) - 2, 2):
                a, b, d = path[step:step + 3]
                K[left.index(a), right.index(b)] = 1
                K[left.index(d), right.index(b)] = sign if step == 0 else -1
        matrices.append((K, probability))
    checks = 0
    for size in range(min(r, c) + 1):
        for rows in combinations(range(r), size):
            for cols in combinations(range(c), size):
                value = sp.expand(sum(prob * K.extract(rows, cols).det()**2
                                      for K, prob in matrices))
                value = sp.simplify(value)
                rowmask = sum(1 << i for i in rows)
                colmask = sum(1 << j for j in cols)
                assert value == int((rowmask, colmask) in supported), (lengths, rows, cols, value)
                checks += 1
    return checks



def path_shortening_check(lengths: Sequence[int], selected: int = 0) -> int:
    """Compare the exact basis sets of the stated contraction/deletion minor."""
    left, right, adjacency, paths = multi_theta(lengths)
    path = paths[selected]
    if len(path) < 5:
        raise ValueError("The selected path must have at least four edges")
    c, b = path[1], path[2]
    old_ground = left + right
    cpos, bpos = old_ground.index(c), old_ground.index(b)
    old_bases = basis_masks(matching_supports(adjacency, len(right)), len(left))
    new_left = [v for v in left if v != b]
    new_right = [v for v in right if v != c]
    new_ground = new_left + new_right
    minor = set()
    for mask in old_bases:
        if (mask & (1 << cpos)) and not (mask & (1 << bpos)):
            minor.add(sum(1 << new_ground.index(vertex)
                          for pos, vertex in enumerate(old_ground)
                          if vertex not in (b, c) and mask & (1 << pos)))
    new_paths = [p[:] for p in paths]
    new_paths[selected] = [path[0]] + path[3:]
    graph = nx.Graph()
    for new_path in new_paths:
        graph.add_edges_from(zip(new_path, new_path[1:]))
    new_adj = [sum(1 << j for j, v in enumerate(new_right) if graph.has_edge(u, v))
               for u in new_left]
    expected = set(basis_masks(matching_supports(new_adj, len(new_right)), len(new_left)))
    assert minor == expected, (lengths, len(minor), len(expected))
    return len(minor)


def subdivided_star_check(pages: int, arm_lengths: Sequence[int]) -> int:
    """Check the terminal-only covariance identity on a subdivided star."""
    assert len(arm_lengths) == pages and all(a >= 1 for a in arm_lengths)
    skeleton = nx.star_graph(pages)
    tree = nx.Graph()
    tree.add_nodes_from(range(pages + 1))
    nxt = pages + 1
    for leaf, length in enumerate(arm_lengths, 1):
        path = [0] + list(range(nxt, nxt + length - 1)) + [leaf]
        nxt += length - 1
        tree.add_edges_from(zip(path, path[1:]))
    r = len(tree)
    edges = sorted(tuple(sorted(e)) for e in tree.edges())
    adjacency = [0] * r
    for j, (a, b) in enumerate(edges):
        adjacency[a] |= 1 << j
        adjacency[b] |= 1 << j
    for terminal in range(pages + 1):
        adjacency[terminal] |= 1 << (r - 1)
    C = sp.zeros(r)
    C[:pages + 1, :pages + 1] = covariance(skeleton)
    supports = matching_supports(adjacency, r)
    for trial in range(2):
        x = [1 + (i + trial) % 4 for i in range(r)]
        y = [1 + (3*i + trial) % 5 for i in range(r - 1)]
        s = trial + 2
        lhs = evaluate_basis(supports, x, y + [s])
        rhs = determinant_formula(weighted_laplacian(edges, x, y), C, s)
        assert lhs == rhs, (pages, arm_lengths, lhs, rhs)
    return len(supports)


def main(output: Path, max_tree_size: int) -> None:
    if not 1 <= max_tree_size <= 12:
        raise ValueError("Choose a tree size between 1 and 12 (default 9)")
    u, m = sp.symbols("u m")
    results: dict[str, object] = {
        "status": "All listed finite exact checks passed; not a formal proof of the theorems.",
        "python": platform.python_version(), "sympy": sp.__version__, "networkx": nx.__version__,
        "tree_checks": [],
    }
    trees_tested = weighted_checks = coefficient_checks = 0
    for r in range(1, max_tree_size + 1):
        total = stable = 0
        kinds = Counter()
        for tree in unlabeled_trees(r):
            total += 1
            trees_tested += 1
            adjacency, edges = tree_apex(tree)
            supports = matching_supports(adjacency, r)
            C = covariance(tree)
            is_psd = exact_psd(C)
            name = ade_shape(tree)
            assert is_psd == (name is not None), list(tree.edges())
            stable += int(is_psd)
            if name:
                kinds[name] += 1
            for trial in range(2):
                # Distinct deterministic positive integral assignments.
                x = [1 + ((3 * i + 2 * trial) % 5) for i in range(r)]
                y = [1 + ((2 * i + trial) % 4) for i in range(r - 1)]
                s = trial + 2
                L = weighted_laplacian(edges, x, y)
                lhs = evaluate_basis(supports, x, y + [s])
                rhs = determinant_formula(L, C, s)
                assert lhs == rhs, (list(tree.edges()), trial, lhs, rhs)
                weighted_checks += 1
            if r <= 5:
                coefficient_checks += cofactor_coefficient_checks(tree)
        results["tree_checks"].append({"vertices": r, "trees": total, "psd_and_ADE": stable,
                                        "types": dict(sorted(kinds.items()))})
        print(f"trees r={r}: {total}, stable types={stable}", flush=True)
    results.update(trees_tested=trees_tested, determinant_evaluation_checks=weighted_checks,
                   apex_coefficient_checks=coefficient_checks)

    Q = 1 + (2*m + 3)*u + (m*m + m + 3)*u*u + u**3
    assert sp.factor(sp.discriminant(Q, u)) == m*m*(8*m**3 + 13*m*m + 54*m - 27)
    results["book_checks"] = []
    for pages in range(9):
        tree = nx.star_graph(pages)
        adjacency, _ = tree_apex(tree)
        supports = matching_supports(adjacency, pages + 1)
        p = sp.expand(support_polynomial(supports, u))
        expected = sp.cancel((1 + u)**(pages - 2) * Q.subs(m, pages))
        assert sp.expand(p - expected) == 0
        masks = basis_masks(supports, pages + 1)
        rank = pages + 1
        a, b = 0, 2 * rank - 1  # Center identity and the apex column.
        Z = len(masks)
        na = sum(bool(mask & (1 << a)) for mask in masks)
        nb = sum(bool(mask & (1 << b)) for mask in masks)
        nab = sum(bool(mask & (1 << a)) and bool(mask & (1 << b)) for mask in masks)
        delta = na * nb - Z * nab
        assert Fraction(delta) == Fraction(4)**(pages - 1) * (4 - pages)
        results["book_checks"].append({"pages": pages,
            "coefficients": [int(p.coeff(u, j)) for j in range(pages + 2)],
            "basis_count": Z, "center_count": na, "apex_count": nb,
            "both_count": nab, "Rayleigh_at_one": delta,
            "covariance": str(Fraction(-delta, Z*Z))})
    print("books m=0,...,8: polynomial and Rayleigh checks passed", flush=True)

    # The negative rational Rayleigh certificate for K_{1,5}.
    tree = nx.star_graph(5)
    v = sp.Matrix([2, 1, 1, 1, 1, 1])
    C = covariance(tree)
    assert (v.T * C * v)[0] == -1
    edges = sorted(tuple(sorted(e)) for e in tree.edges())
    ys = [1 / (v[a] * v[b]) for a, b in edges]
    xs = [sp.Rational(tree.degree(i), 1) / v[i]**2
          - sum(1 / (v[i] * v[j]) for j in tree[i]) for i in tree]
    L = weighted_laplacian(edges, xs, ys)
    c = sp.prod(t**(-2) for t in v)
    assert L * v == sp.zeros(6, 1) and L.adjugate() == c * v * v.T
    results["rational_certificate"] = {
        "tree": "K_1,5", "v": list(map(str, v)), "x": list(map(str, xs)),
        "y": list(map(str, ys)), "s": "0", "vTCv": "-1",
        "Rayleigh_s_center": str(c*c*v[0]**2*(-1)),
    }

    theta_paths = [(2, 2, 2), (2, 2, 4), (2, 4, 4), (4, 4, 4),
                   (3, 3, 3), (3, 3, 5), (1, 3, 5), (1, 3, 3, 3, 3)]
    results["theta_checks"] = []
    for lengths in theta_paths:
        left, right, adjacency, _ = multi_theta(lengths)
        supports = matching_supports(adjacency, len(right))
        p = sp.Poly(support_polynomial(supports, u), u)
        results["theta_checks"].append({"path_lengths": list(lengths),
            "coefficients": list(reversed([int(a) for a in p.all_coeffs()]))})
        if lengths == (3, 3, 3):
            assert p.as_expr() == 1 + 9*u + 24*u*u + 16*u**3 + u**4
            assert sp.discriminant(p.as_expr(), u) == -5243
        if lengths == (3, 3, 5):
            assert p.count_roots(-sp.oo, 0) == p.degree()  # Exact Sturm count.
    even_checks = 0
    for lengths in [(2, 2, 2), (2, 2, 4), (4, 4, 4)]:
        count = even_theta_minor_check(lengths)
        even_checks += count
        print(f"even theta {lengths}: {count} expected-minor checks passed", flush=True)
    results["expected_even_theta_minor_checks"] = even_checks

    results["path_minor_checks"] = [
        {"lengths": list(lengths), "minor_basis_count": path_shortening_check(lengths)}
        for lengths in [(5, 3, 3), (5, 3, 1), (7, 5, 3), (4, 2, 2)]]
    results["subdivided_star_checks"] = [
        {"pages": pages, "skeleton_arm_lengths": list(lengths),
         "basis_count": subdivided_star_check(pages, lengths)}
        for pages, lengths in [(3, (1, 2, 3)), (4, (1, 1, 2, 2)), (5, (1, 1, 1, 1, 2))]]
    print("four exact path-minor comparisons and six subdivision evaluations passed", flush=True)

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"All exact checks passed. Results: {output}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-tree-size", type=int, default=9)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "verification_results.json")
    args = parser.parse_args()
    main(args.output, args.max_tree_size)
