"""Formal-degree analysis and certified checkpoint selection."""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from math import log2
from .slp import Presentation


@dataclass(frozen=True)
class DegreeProfile:
    checkpoints: tuple[int, ...]
    dimension: int
    delta: int
    kappa: float
    exported_degrees: dict[int, int]
    defining_degrees: dict[int, int]


def profile(p: Presentation, checkpoints=()) -> DegreeProfile:
    chosen = set(checkpoints)
    if chosen - set(p.products()):
        raise ValueError("checkpoints must be live concatenation nodes")
    exported = {0: 0}
    defining = {}
    maximum = 2
    for v in p.live():
        rule = p.rules[v]
        if rule[0] == 't':
            exported[v] = 1
        else:
            d = exported[rule[1]] + exported[rule[2]]
            if v in chosen:
                defining[v] = d
                maximum = max(maximum, d)
                exported[v] = 1
            else:
                exported[v] = d
    maximum = max([maximum] + [exported[v] for pair in p.relations for v in pair])
    count = p.rank + len(chosen)
    return DegreeProfile(tuple(sorted(chosen)), 4 * count, maximum,
                         count * log2(maximum + 2), exported, defining)


def best_small_dag(p: Presentation, max_products=20) -> DegreeProfile:
    """Exponential reference optimizer, intentionally limited to small DAGs."""
    products = p.products()
    if len(products) > max_products:
        raise ValueError("exhaustive checkpoint optimizer limit")
    best = None
    best_score = None
    for size in range(len(products) + 1):
        for chosen in combinations(products, size):
            candidate = profile(p, chosen)
            score = (candidate.delta+2)**(p.rank+len(chosen))
            if best_score is None or score < best_score:
                best, best_score = candidate, score
    return best


def greedy_cap(p: Presentation, cap: int) -> DegreeProfile:
    """Feasible degree cap for a DAG; not an optimal-checkpoint algorithm.

    Checkpoint a node whenever its uncheckpointed degree exceeds cap/2.
    Children then have degree <= floor(cap/2), so each definition stays <=cap.
    """
    if type(cap) is not int or cap < 2:
        raise ValueError("cap must be >=2")
    exported = {0: 0}
    chosen = []
    for v in p.live():
        rule = p.rules[v]
        if rule[0] == 't':
            exported[v] = 1
        else:
            d = exported[rule[1]] + exported[rule[2]]
            if d > cap // 2:
                chosen.append(v)
                exported[v] = 1
            else:
                exported[v] = d
    result = profile(p, chosen)
    assert result.delta <= cap
    return result


def flatten_tree(tree):
    """Separate occurrences even when the Python object is shared."""
    nodes = [None]
    stack = [(tree, 0)]
    while stack:
        node, index = stack.pop()
        if isinstance(node, int):
            nodes[index] = None
        else:
            if not isinstance(node, tuple) or len(node) != 2:
                raise ValueError("binary tuple or integer leaf required")
            a, b = len(nodes), len(nodes)+1
            nodes.extend((None, None))
            nodes[index] = (a, b)
            stack.extend(((node[0], a), (node[1], b)))
    return nodes


def optimal_tree_cap(tree, cap: int):
    """Minimum checkpoints on a binary FORMULA TREE.

    O(size*cap^2) arithmetic operations and O(size*cap) records. Backpointers
    avoid storing a full checkpoint list at each dynamic-programming entry.
    Node ids refer to flatten_tree(tree), not to a shared word DAG.
    """
    if type(cap) is not int or cap < 2:
        raise ValueError("cap must be >=2")
    nodes = flatten_tree(tree)
    tables = [None] * len(nodes)
    for index in reversed(range(len(nodes))):
        children = nodes[index]
        if children is None:
            tables[index] = {1: (0, None)}
            continue
        left, right = (tables[v] for v in children)
        table = {}
        for a, (ca, _) in left.items():
            for b, (cb, _) in right.items():
                d = a+b
                if d > cap:
                    continue
                for degree, cost, cut in ((d, ca+cb, False), (1, ca+cb+1, True)):
                    if degree not in table or cost < table[degree][0]:
                        table[degree] = (cost, (a,b,cut))
        tables[index] = table
    degree, (cost, _) = min(tables[0].items(), key=lambda item: (item[1][0],item[0]))
    stack, cuts = [(0,degree)], []
    while stack:
        index,d = stack.pop()
        back = tables[index][d][1]
        if back is None:
            continue
        a,b,cut = back
        if cut: cuts.append(index)
        u,v = nodes[index]
        stack.extend(((u,a),(v,b)))
    return dict(cost=cost, exported_degree=degree, checkpoints=tuple(sorted(cuts)))
