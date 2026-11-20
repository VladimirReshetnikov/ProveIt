#!/usr/bin/env python3
"""Exact finite regression checks for Section 5.

No numerical tolerance, symbolic theorem prover, or external dependency is used.
These checks validate implementations and small instances; they are not iPRA
proofs.  Run from any directory: python3 algebraic_checks.py --output FILE.
"""
from __future__ import annotations

import argparse
import itertools
import json
from collections import deque
from fractions import Fraction
from pathlib import Path


def add(*chains):
    ans = {}
    for chain in chains:
        for simplex, coefficient in chain.items():
            ans[simplex] = ans.get(simplex, 0) + coefficient
    return {s: c for s, c in ans.items() if c}


def scale(a, chain):
    return {s: a * c for s, c in chain.items() if a * c}


def oriented(vertices):
    if len(set(vertices)) != len(vertices):
        return {}
    inversions = sum(vertices[i] > vertices[j]
                     for i in range(len(vertices))
                     for j in range(i + 1, len(vertices)))
    return {tuple(sorted(vertices)): (-1) ** inversions}


def boundary(chain):
    ans = {}
    for simplex, coefficient in chain.items():
        if len(simplex) == 1:
            continue
        for i in range(len(simplex)):
            ans = add(ans, {simplex[:i] + simplex[i + 1:]:
                            coefficient * (-1) ** i})
    return ans


def push(chain, vertex_map):
    return add(*(scale(c, oriented(tuple(vertex_map[v] for v in s)))
                 for s, c in chain.items()))


def prism(chain, f, g):
    ans = {}
    for s, c in chain.items():
        for i in range(len(s)):
            vertices = tuple(f[v] for v in s[:i + 1]) + \
                       tuple(g[v] for v in s[i:])
            ans = add(ans, scale(c * (-1) ** i, oriented(vertices)))
    return ans


def matrix_rank(rows, ncols):
    a = [list(map(Fraction, row)) for row in rows]
    r = 0
    for j in range(ncols):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        p = a[r][j]
        a[r] = [x / p for x in a[r]]
        for i in range(len(a)):
            if i != r:
                p = a[i][j]
                a[i] = [x - p * y for x, y in zip(a[i], a[r])]
        r += 1
    return r


def homology(complex_):
    dimension = max((len(s) for s in complex_), default=0)
    basis = [[s for s in sorted(complex_) if len(s) == k + 1]
             for k in range(dimension)]
    dims = list(map(len, basis))
    ranks = [0]
    for k in range(1, dimension):
        rows = [[boundary({s: 1}).get(t, 0) for s in basis[k]]
                for t in basis[k - 1]]
        ranks.append(matrix_rank(rows, len(basis[k])))
    ranks.append(0)
    betti = [dims[k] - ranks[k] - ranks[k + 1]
             for k in range(dimension)]
    assert all(b >= 0 for b in betti)
    assert sum((-1) ** k * c for k, c in enumerate(dims)) == \
           sum((-1) ** k * b for k, b in enumerate(betti))
    return betti


def all_complexes(n):
    simplices = [s for k in range(1, n + 1)
                 for s in itertools.combinations(range(n), k)]
    for mask in range(1 << len(simplices)):
        complex_ = {s for i, s in enumerate(simplices) if mask >> i & 1}
        if all(all(s[:i] + s[i + 1:] in complex_
                   for i in range(len(s)))
               for s in complex_ if len(s) > 1):
            yield complex_


def check_complexes():
    count = collapses = 0
    for complex_ in all_complexes(4):
        count += 1
        original = homology(complex_)
        for s in complex_:
            assert boundary(boundary({s: 1})) == {}
        for sigma in complex_:
            cofaces = [t for t in complex_
                       if len(t) > len(sigma) and set(sigma) <= set(t)]
            if len(cofaces) != 1:
                continue
            tau = cofaces[0]
            if len(tau) != len(sigma) + 1:
                continue
            collapses += 1
            reduced = complex_ - {sigma, tau}
            new = homology(reduced)
            assert original + [0] * (len(new) - len(original)) == \
                   new + [0] * (len(original) - len(new))
            dtau = boundary({tau: 1})
            epsilon = dtau[sigma]
            b = add(dtau, {sigma: -epsilon})

            def h(chain):
                return scale(epsilon * chain.get(sigma, 0), {tau: 1})

            def retraction(chain):
                ans = {s: c for s, c in chain.items()
                       if s != sigma and s != tau}
                return add(ans, scale(-epsilon * chain.get(sigma, 0), b))

            for s in complex_:
                v = {s: 1}
                assert retraction(v) == add(v, scale(-1, boundary(h(v))),
                                           scale(-1, h(boundary(v))))
                assert boundary(retraction(v)) == retraction(boundary(v))
    return {"complexes_on_four_labels": count,
            "elementary_collapse_certificates": collapses}


def check_prisms():
    simplices = [s for k in range(1, 4)
                 for s in itertools.combinations(range(3), k)]
    maps = list(itertools.product(range(3), repeat=3))
    equations = 0
    for f in maps:
        for g in maps:
            for s in simplices:
                v = {s: 1}
                assert boundary(push(v, f)) == push(boundary(v), f)
                assert add(boundary(prism(v, f, g)),
                           prism(boundary(v), f, g)) == \
                       add(push(v, g), scale(-1, push(v, f)))
                equations += 1
    return {"prism_equations_including_degenerate_maps": equations}


def spanning_forest(n, edges):
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
    parent, depth, components = {}, {}, 0
    for root in range(n):
        if root in parent:
            continue
        components += 1
        parent[root], depth[root] = root, 0
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in sorted(neighbors[u]):
                if v not in parent:
                    parent[v], depth[v] = u, depth[u] + 1
                    queue.append(v)
    return neighbors, parent, depth, components


def two_color_or_cycle(n, edges):
    _, parent, depth, _ = spanning_forest(n, edges)
    color = [depth[i] % 2 for i in range(n)]
    for u, v in edges:
        if color[u] != color[v]:
            continue
        left, right = [u], [v]
        while left[-1] != right[-1]:
            if depth[left[-1]] >= depth[right[-1]]:
                left.append(parent[left[-1]])
            else:
                right.append(parent[right[-1]])
        cycle = left + list(reversed(right[:-1]))
        assert len(cycle) % 2 == 1
        assert len(set(cycle)) == len(cycle) <= n
        assert all(tuple(sorted((cycle[i], cycle[(i + 1) % len(cycle)])))
                   in edges for i in range(len(cycle)))
        return None, cycle
    return color, None


def check_graphs():
    count = odd = 0
    for n in range(6):
        possible = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = {e for i, e in enumerate(possible) if mask >> i & 1}
            count += 1
            neighbors, _, _, c = spanning_forest(n, edges)
            complex_ = {(v,) for v in range(n)} | edges
            betti = homology(complex_) + [0, 0]
            assert betti[0] == c and betti[1] == len(edges) - n + c
            degree = max(map(len, neighbors), default=0)
            greedy = []
            for v in range(n):
                forbidden = {greedy[u] for u in neighbors[v] if u < v}
                greedy.append(next(q for q in range(degree + 1)
                                   if q not in forbidden))
            assert all(greedy[u] != greedy[v] for u, v in edges)
            colors, cycle = two_color_or_cycle(n, edges)
            brute = any(all(a[u] != a[v] for u, v in edges)
                        for a in itertools.product(range(2), repeat=n))
            assert (colors is not None) == brute
            odd += cycle is not None
    return {"graphs_through_five_vertices": count,
            "verified_odd_cycle_certificates": odd}


def generated_by_closure(n, generators):
    full = (1 << n) - 1
    members = {0, full, *generators}
    for _ in range(1 << n):
        enlarged = members | {full ^ x for x in members} | \
                   {x | y for x in members for y in members}
        if enlarged == members:
            return members
        members = enlarged
    raise AssertionError("Finite closure did not stabilize")


def check_atoms():
    count = 0
    for n in range(4):
        for s in range(4):
            for generators in itertools.product(range(1 << n), repeat=s):
                words = {}
                for x in range(n):
                    w = tuple(bool(g >> x & 1) for g in generators)
                    words[w] = words.get(w, 0) | (1 << x)
                atoms = list(words.values())
                unions = {0}
                for a in atoms:
                    unions |= {u | a for u in tuple(unions)}
                assert len(unions) == 1 << len(atoms)
                assert unions == generated_by_closure(n, generators)
                count += 1
    return {"finite_boolean_generator_families": count}


def check_function_gluing():
    # Every ordered triple of subsets covering a three-point discrete space;
    # every assignment of binary-valued local sections; empty members included.
    n, full, count = 3, 7, 0
    for masks in itertools.product(range(8), repeat=3):
        if masks[0] | masks[1] | masks[2] != full:
            continue
        local_sections = []
        for mask in masks:
            points = [x for x in range(n) if mask >> x & 1]
            local_sections.append([dict(zip(points, vals))
                                   for vals in itertools.product(range(2),
                                                                 repeat=len(points))])
        for sections in itertools.product(*local_sections):
            if not all(all(sections[i][x] == sections[j][x]
                           for x in sections[i].keys() & sections[j].keys())
                       for i in range(3) for j in range(3)):
                continue
            glued = {x: sections[next(i for i in range(3)
                                      if masks[i] >> x & 1)][x]
                     for x in range(n)}
            assert all(glued[x] == section[x]
                       for section in sections for x in section)
            candidates = [vals for vals in itertools.product(range(2), repeat=n)
                          if all(vals[x] == section[x]
                                 for section in sections for x in section)]
            assert len(candidates) == 1
            count += 1
    return {"matching_function_families_glued_uniquely": count}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {"status": "passed", "arithmetic": "exact integers and fractions",
              "scope": "finite regression checks; not universal or object-iPRA proofs"}
    for check in (check_complexes, check_prisms, check_graphs, check_atoms,
                  check_function_gluing):
        result.update(check())
    encoded = json.dumps(result, indent=2) + "\n"
    print(encoded, end="")
    if args.output:
        args.output.write_text(encoded)


if __name__ == "__main__":
    main()
