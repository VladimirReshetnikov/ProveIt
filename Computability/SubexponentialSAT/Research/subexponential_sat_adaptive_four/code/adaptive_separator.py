"""Exact streamed mode-graph contraction with adaptive four-cluster trees.

This is a finite mode-graph kernel, not an end-to-end SAT solver.  Domains are
sized indexable sequences (range objects are supported without materializing
them).  Every group-factor evaluation is explicitly counted.  No logarithms
or floating-point comparisons enter tree selection or contraction.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import prod
from typing import Callable, Mapping, Sequence

Edge = tuple[int, int]


@dataclass(frozen=True)
class Tree:
    groups: tuple[int, ...]
    left: "Tree | None" = None
    right: "Tree | None" = None


MATCHINGS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))


@lru_cache(None)
def cardinality_plan(r: int) -> tuple[Fraction, tuple[int, ...]]:
    """Minimum certificate among binary and four-cluster size recurrences.

    This does not claim optimality among all adaptive trees or all algorithms.
    """
    if r < 1:
        raise ValueError("There must be at least one group")
    if r == 1:
        return Fraction(0), ()
    choices: list[tuple[Fraction, tuple[int, ...]]] = []
    for a in range(1, r // 2 + 1):
        b = r - a
        bound = 2 * a * b + max(cardinality_plan(a)[0], cardinality_plan(b)[0])
        choices.append((bound, (a, b)))
    for a in range(1, r // 4 + 1):
        for b in range(a, (r - a) // 3 + 1):
            for c in range(b, (r - a - b) // 2 + 1):
                d = r - a - b - c
                if d < c:
                    continue
                sizes = (a, b, c, d)
                capacity = {(i, j): 2 * sizes[i] * sizes[j]
                            for i in range(4) for j in range(i + 1, 4)}
                top = sum(capacity.values()) - Fraction(5, 9) * sum(
                    min(capacity[e], capacity[f]) for e, f in MATCHINGS)
                bound = top + max(cardinality_plan(x)[0] for x in sizes)
                choices.append((bound, sizes))
    return min(choices)


def _join(left: Tree, right: Tree) -> Tree:
    return Tree(tuple(sorted(left.groups + right.groups)), left, right)


def build_tree(groups: Sequence[int], domain_sizes: Mapping[Edge, int]) -> Tree:
    """Choose every four-cluster matching by exact integer products.

    Missing directed edges are singleton indices. Empty domains must be
    handled before tree construction.
    """
    groups = tuple(groups)
    if len(set(groups)) != len(groups) or not groups:
        raise ValueError("Groups must be distinct and nonempty")
    if any(n < 1 for n in domain_sizes.values()):
        raise ValueError("build_tree requires positive domain sizes")
    if len(groups) == 1:
        return Tree(groups)
    _, parts = cardinality_plan(len(groups))
    clusters = []
    start = 0
    for n in parts:
        clusters.append(groups[start:start + n])
        start += n
    trees = [build_tree(cluster, domain_sizes) for cluster in clusters]
    if len(parts) == 2:
        return _join(trees[0], trees[1])
    products = {}
    for i in range(4):
        for j in range(i + 1, 4):
            products[i, j] = prod(
                domain_sizes.get((a, b), 1) * domain_sizes.get((b, a), 1)
                for a in clusters[i] for b in clusters[j])
    # log is monotone: maximizing min(product_e, product_f) exactly
    # maximizes the smaller of the two summed entropy weights.
    best = max(range(3), key=lambda k: min(products[e] for e in MATCHINGS[k]))
    (a, b), (c, d) = MATCHINGS[best]
    return _join(_join(trees[a], trees[b]), _join(trees[c], trees[d]))


def path_edge_sets(tree: Tree, edges: Sequence[Edge]) -> dict[int, tuple[Edge, ...]]:
    """Return disjoint-cut unions along every root-to-leaf path."""
    result = {}

    def walk(node: Tree, prior: tuple[Edge, ...]) -> None:
        if node.left is None:
            result[node.groups[0]] = prior
            return
        left, right = set(node.left.groups), set(node.right.groups)
        cut = tuple(e for e in edges if (e[0] in left and e[1] in right)
                    or (e[0] in right and e[1] in left))
        walk(node.left, prior + cut)
        walk(node.right, prior + cut)

    walk(tree, ())
    return result


def contract(
    groups: Sequence[int],
    domains: Mapping[Edge, Sequence[int]],
    factor: Callable[[int, Mapping[Edge, int]], object],
    *,
    zero=0,
    one=1,
    add=lambda a, b: a + b,
    multiply=lambda a, b: a * b,
) -> tuple[object, dict]:
    """Stream the exact finite sum of products in any commutative ring.

    factor(g, incident_assignment) is evaluated on every leaf visit; there is
    no unit-cost or precomputed oracle assumption.  The supplied ring callbacks
    can implement residue rings with zero divisors and nilpotents.
    """
    groups = tuple(groups)
    group_set = set(groups)
    for (a, b) in domains:
        if a == b or a not in group_set or b not in group_set:
            raise ValueError("Every edge must join distinct specified groups")
    calls = {g: 0 for g in groups}
    if any(len(domain) == 0 for domain in domains.values()):
        return zero, {"factor_calls": calls, "total_factor_calls": 0,
                      "empty_domain": True}
    sizes = {e: len(domain) for e, domain in domains.items()}
    tree = build_tree(groups, sizes)
    edges = tuple(sorted(domains))
    assignment = {}
    active_contexts = 0
    peak_contexts = 0

    def walk(node: Tree):
        nonlocal active_contexts, peak_contexts
        active_contexts += 1
        peak_contexts = max(peak_contexts, active_contexts)
        try:
            if node.left is None:
                g = node.groups[0]
                calls[g] += 1
                incident = {e: value for e, value in assignment.items() if g in e}
                return factor(g, incident)
            left, right = set(node.left.groups), set(node.right.groups)
            cut = tuple(e for e in edges if (e[0] in left and e[1] in right)
                        or (e[0] in right and e[1] in left))

            def sum_indices(pos):
                if pos == len(cut):
                    return multiply(walk(node.left), walk(node.right))
                edge = cut[pos]
                answer = zero
                for index in range(len(domains[edge])):
                    assignment[edge] = domains[edge][index]
                    answer = add(answer, sum_indices(pos + 1))
                assignment.pop(edge, None)
                return answer

            return sum_indices(0)
        finally:
            active_contexts -= 1

    answer = walk(tree)
    path_sets = path_edge_sets(tree, edges)
    predicted = {g: prod(sizes[e] for e in path_sets[g]) for g in groups}
    if predicted != calls:
        raise ArithmeticError("Observed factor calls disagree with the path product identity")
    return answer, {"factor_calls": calls, "total_factor_calls": sum(calls.values()),
                    "predicted_factor_calls": predicted, "peak_tree_contexts": peak_contexts,
                    "empty_domain": False}
