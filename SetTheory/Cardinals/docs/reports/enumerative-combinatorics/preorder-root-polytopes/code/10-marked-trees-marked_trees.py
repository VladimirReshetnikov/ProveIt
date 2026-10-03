#!/usr/bin/env python3
"""Marked-tree stability recognition, weighted enumeration, and optimal repair.

Algorithms accompanying the research article.  No numerical eigenvalues are used.
Requires Python >= 3.11 and NetworkX. Vertex labels may be arbitrary hashable objects.
Polynomial lists are in increasing degree order. Counts are exact integers; rational
weights/scores may be supplied as fractions.Fraction values. The multivariate formula
is evaluated at the supplied vertex weights, keeping the mark-count variable formal.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, permutations
from typing import Hashable, Mapping, Sequence

import networkx as nx

Vertex = Hashable
Number = int | Fraction
EXCEPTIONS = tuple(sorted({p for k in ((0, 1, 1), (0, 1, 2), (0, 1, 3),
                                      (1, 1, 1), (0, 2, 2), (0, 1, 4))
                           for p in permutations(k)}))


def validate_tree(tree: nx.Graph) -> None:
    if tree.is_directed() or tree.is_multigraph():
        raise ValueError("Supply a finite, simple, undirected tree.")
    if not tree or not nx.is_tree(tree):
        raise ValueError("Supply a nonempty tree.")


def hull(tree: nx.Graph, marks: set[Vertex]) -> nx.Graph:
    """Minimal subtree containing marks, obtained by pruning unmarked leaves."""
    if not marks <= set(tree):
        raise ValueError("A marked vertex does not belong to the tree.")
    if not marks:
        return nx.Graph()
    live = set(tree)
    degree = dict(tree.degree())
    queue = [v for v in tree if degree[v] <= 1 and v not in marks]
    while queue:
        v = queue.pop()
        if v not in live:
            continue
        live.remove(v)
        for u in tree[v]:
            if u in live:
                degree[u] -= 1
                if degree[u] <= 1 and u not in marks:
                    queue.append(u)
    return tree.subgraph(live).copy()


def terminal_skeleton(core: nx.Graph, marks: set[Vertex]) -> nx.Graph:
    """Suppress unmarked degree-two vertices; require every branch marked."""
    if any(core.degree(v) >= 3 and v not in marks for v in core):
        raise ValueError("The marked hull has an unmarked branching vertex.")
    result = nx.Graph()
    result.add_nodes_from(marks)
    for a in marks:
        for b in core[a]:
            previous, current = a, b
            while current not in marks:
                nxt = next(v for v in core[current] if v != previous)
                previous, current = current, nxt
            result.add_edge(a, current)
    return result


def ade_type(tree: nx.Graph) -> str | None:
    """Combinatorial classification of trees whose adjacency spectral radius <= 2."""
    if not tree:
        return "empty"
    degree = dict(tree.degree())
    maximum = max(degree.values())
    if maximum <= 2:
        return f"A_{len(tree)}"
    if maximum >= 5:
        return None
    branches = [v for v in tree if degree[v] >= 3]
    if maximum == 4:
        return "affine_D_4" if len(tree) == 5 else None
    if len(branches) >= 2:
        if len(branches) != 2:
            return None
        path = nx.shortest_path(tree, *branches)
        if len(tree) != len(path) + 4:
            return None
        pset = set(path)
        if any(len([w for w in tree[v] if w not in pset]) != 2 or
               any(degree[w] != 1 for w in tree[v] if w not in pset)
               for v in branches):
            return None
        return f"affine_D_{len(tree) - 1}"
    center = branches[0]
    lengths = []
    for b in tree[center]:
        length, previous, current = 1, center, b
        while degree[current] == 2:
            nxt = next(v for v in tree[current] if v != previous)
            previous, current = current, nxt
            length += 1
        lengths.append(length)
    a, b, c = sorted(lengths)
    if a == b == 1:
        return f"D_{len(tree)}"
    return {(1, 2, 2): "E_6", (1, 2, 3): "E_7", (1, 2, 4): "E_8",
            (2, 2, 2): "affine_E_6", (1, 3, 3): "affine_E_7",
            (1, 2, 5): "affine_E_8"}.get((a, b, c))


@dataclass(frozen=True)
class Recognition:
    stable: bool
    kind: str
    hull_vertices: frozenset[Vertex]
    skeleton_edges: frozenset[frozenset[Vertex]]
    unmarked_branch: Vertex | None = None


def recognize(tree: nx.Graph, marks: set[Vertex], *, validate: bool = True) -> Recognition:
    if validate:
        validate_tree(tree)
    core = hull(tree, marks)
    if not marks:
        return Recognition(True, "empty", frozenset(), frozenset())
    bad = next((v for v in core if core.degree(v) >= 3 and v not in marks), None)
    if bad is not None:
        return Recognition(False, "unmarked_branch", frozenset(core), frozenset(), bad)
    skeleton = terminal_skeleton(core, marks)
    kind = ade_type(skeleton)
    return Recognition(kind is not None, kind or "spectral_obstruction", frozenset(core),
                       frozenset(frozenset(e) for e in skeleton.edges()))


def poly_add(a: Sequence[Number], b: Sequence[Number]) -> list[Number]:
    out = list(a) + [0] * max(0, len(b) - len(a))
    for i, x in enumerate(b):
        out[i] += x
    return out


def choices(vertices: Sequence[Vertex], weights: Mapping[Vertex, Number]) -> list[Number]:
    """Coefficients of product_v (1 + weights[v] * t)."""
    out: list[Number] = [1]
    for v in vertices:
        out.append(0)
        for k in range(len(out) - 1, 0, -1):
            out[k] += weights[v] * out[k - 1]
    return out


def product(values) -> Number:
    answer: Number = 1
    for value in values:
        answer *= value
    return answer


def endpoint_templates(tree: nx.Graph):
    """Unique hulls with 2--4 specified leaves, plus their branch/path data."""
    vertices = list(tree)
    paths = dict(nx.all_pairs_shortest_path(tree))
    for size in (2, 3, 4):
        for leaves in combinations(vertices, size):
            nodes = set()
            for leaf in leaves[1:]:
                nodes.update(paths[leaves[0]][leaf])
            core = tree.subgraph(nodes)
            if {v for v in core if core.degree(v) == 1} != set(leaves):
                continue
            branches = tuple(v for v in core if core.degree(v) >= 3)
            if size == 2:
                yield leaves, branches, (tuple(paths[leaves[0]][leaves[1]][1:-1]),)
            elif size == 3:
                assert len(branches) == 1 and core.degree(branches[0]) == 3
                yield leaves, branches, tuple(tuple(paths[branches[0]][v][1:-1]) for v in leaves)
            elif len(branches) == 1:
                assert core.degree(branches[0]) == 4
                yield leaves, branches, ()
            else:
                assert len(branches) == 2 and all(core.degree(v) == 3 for v in branches)
                yield leaves, branches, (tuple(paths[branches[0]][branches[1]][1:-1]),)


def stable_polynomial(tree: nx.Graph,
                      weights: Mapping[Vertex, Number] | None = None) -> list[Number]:
    """Return Z_T(t;weights) exactly, without enumerating 2^n marked sets.

    The reference implementation builds arm products directly. Its worst-case
    arithmetic count is O(n^5): three-leaf arm products cost O(n^2) each; there
    are O(n^3) triples. Four-leaf central-path products are cached by endpoints.
    """
    validate_tree(tree)
    weights = {v: 1 for v in tree} if weights is None else dict(weights)
    if set(weights) != set(tree):
        raise ValueError("Provide exactly one weight per tree vertex.")
    if any(not isinstance(value, (int, Fraction)) for value in weights.values()):
        raise TypeError("Weights must be integers or fractions.Fraction values.")
    n = len(tree)
    result: list[Number] = [0] * (n + 1)
    result[0], result[1] = 1, sum(weights.values())
    cached: dict[frozenset[Vertex], list[Number]] = {}

    def path_product(a, b, internal):
        key = frozenset((a, b))
        if key not in cached:
            cached[key] = choices(internal, weights)
        return cached[key]

    for leaves, branches, regions in endpoint_templates(tree):
        required = leaves + branches
        shift = len(required)
        prefactor = product(weights[v] for v in required)
        if len(leaves) == 2:
            polynomial = path_product(*leaves, regions[0])
        elif len(leaves) == 3:
            arms = [path_product(branches[0], leaf, region)
                    for leaf, region in zip(leaves, regions)]
            polynomial: list[Number] = [-2]
            for p in arms:
                polynomial = poly_add(polynomial, p)
            for k in EXCEPTIONS:
                if any(i >= len(p) for p, i in zip(arms, k)):
                    continue
                degree = sum(k)
                polynomial += [0] * max(0, degree + 1 - len(polynomial))
                polynomial[degree] += product(p[i] for p, i in zip(arms, k))
        elif len(branches) == 1:
            polynomial = [1]
        else:
            polynomial = path_product(*branches, regions[0])
        for k, value in enumerate(polynomial):
            if value:
                result[shift + k] += prefactor * value
    return result


def maximum_weight_stable(tree: nx.Graph, scores: Mapping[Vertex, Number]) -> tuple[Number, set[Vertex]]:
    """Maximize sum(scores[v] for v in S) over all stable marked sets S.

    Arbitrary signed integer/rational scores are allowed. The returned set is
    one optimizer; ties are resolved by traversal order. Complexity O(n^5).
    """
    validate_tree(tree)
    if set(scores) != set(tree):
        raise ValueError("Provide exactly one score per tree vertex.")
    if any(not isinstance(value, (int, Fraction)) for value in scores.values()):
        raise TypeError("Scores must be integers or fractions.Fraction values.")
    best: Number = 0
    answer: set[Vertex] = set()

    def consider(vertices):
        nonlocal best, answer
        candidate = set(vertices)
        value = sum(scores[v] for v in candidate)
        if value > best:
            best, answer = value, candidate

    for v in tree:
        consider((v,))
    for leaves, branches, regions in endpoint_templates(tree):
        required = leaves + branches
        if len(leaves) in (2, 4):
            free = regions[0] if regions else ()
            consider(required + tuple(v for v in free if scores[v] > 0))
        else:
            consider(required)
            for region in regions:
                consider(required + tuple(v for v in region if scores[v] > 0))
            # Only the four largest entries of any arm are ever needed.
            top = []
            for region in regions:
                chosen = []
                for v in region:
                    chosen.append(v)
                    chosen.sort(key=lambda x: scores[x], reverse=True)
                    del chosen[4:]
                top.append(chosen)
            for k in EXCEPTIONS:
                if all(len(region) >= i for region, i in zip(top, k)):
                    extras = tuple(v for region, i in zip(top, k) for v in region[:i])
                    consider(required + extras)
    return best, answer


def nearest_stable(tree: nx.Graph, original: set[Vertex]) -> tuple[int, set[Vertex]]:
    """Minimum number of apex-edge additions/deletions needed for stability."""
    if not original <= set(tree):
        raise ValueError("Original marks must be vertices of the tree.")
    score, result = maximum_weight_stable(tree, {v: 1 if v in original else -1 for v in tree})
    distance = len(original ^ result)
    assert distance == len(original) - score
    return distance, result


if __name__ == "__main__":
    star = nx.star_graph(5)
    print("Five-leaf star Z coefficients:", stable_polynomial(star))
    print("Nearest stable set to its five leaves:", nearest_stable(star, set(range(1, 6))))
