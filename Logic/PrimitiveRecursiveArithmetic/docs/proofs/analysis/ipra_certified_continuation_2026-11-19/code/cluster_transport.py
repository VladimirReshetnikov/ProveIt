#!/usr/bin/env python3
"""Exact finite reference for the report's cluster-transport correction.

The loops of match_or_defect have explicit bounds.  This is reference code,
not an object-language iPRA derivation or a root-count certificate producer.
Run this file to compare every bipartite graph of size <= 3 with exhaustive
permutation enumeration and check the rational counterexamples/locators.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import permutations
import json


@dataclass(frozen=True)
class MatchResult:
    matching: tuple[int, ...] | None
    defect: tuple[int, ...] | None


def match_or_defect(graph: tuple[tuple[bool, ...], ...]) -> MatchResult:
    """Return a perfect matching or an explicit Hall-deficient left subset."""
    n = len(graph)
    if any(len(row) != n for row in graph):
        raise ValueError("The graph must be square.")
    left = [n] * n
    right = [n] * n
    for root in range(n):
        seen_left = [False] * n
        seen_right = [False] * n
        parent = [n] * n
        seen_left[root] = True
        queue = [root]
        free = n
        for scan in range(n):
            if scan >= len(queue):
                break
            a = queue[scan]
            for b in range(n):
                if not graph[a][b] or seen_right[b]:
                    continue
                seen_right[b] = True
                parent[b] = a
                if right[b] == n:
                    free = b
                    break
                partner = right[b]
                if not seen_left[partner]:
                    seen_left[partner] = True
                    queue.append(partner)
            if free != n:
                break
        if free == n:
            return MatchResult(None, tuple(i for i in range(n) if seen_left[i]))
        b = free
        finished = False
        for _ in range(n):
            a = parent[b]
            assert a < n
            old = left[a]
            left[a] = b
            right[b] = a
            if a == root:
                finished = True
                break
            assert old < n
            b = old
        assert finished
    return MatchResult(tuple(left), None)


def is_matching(graph, p):
    n = len(graph)
    return (len(p) == n and sorted(p) == list(range(n))
            and all(graph[a][p[a]] for a in range(n)))


def neighbors(graph, subset):
    return tuple(b for b in range(len(graph))
                 if any(graph[a][b] for a in subset))


def l1(a, b):
    if len(a) != len(b):
        raise ValueError("Coordinate dimensions differ.")
    return sum((abs(x - y) for x, y in zip(a, b)), Q(0))


def expand(centers, weights):
    if len(centers) != len(weights) or any(w <= 0 for w in weights):
        raise ValueError("Each center needs a positive integer weight.")
    return tuple(c for c, w in zip(centers, weights) for _ in range(w))


def transport(centers_a, weights_a, centers_b, weights_b, delta):
    """Public matching construction; it consumes no hidden root assignments."""
    a = expand(centers_a, weights_a)
    b = expand(centers_b, weights_b)
    if len(a) != len(b):
        raise ValueError("The total multiplicities must agree.")
    graph = tuple(tuple(l1(x, y) <= delta for y in b) for x in a)
    return a, b, graph, match_or_defect(graph)


def nearest_anchors(samples, anchors):
    """Deterministic bounded scan, with numerical tie breaking."""
    if not anchors and samples:
        raise ValueError("A nonempty sample needs an anchor.")
    return tuple(min(range(len(anchors)), key=lambda j: (l1(a, anchors[j]), j))
                 for a in samples)


def run_checks():
    graph_count = 0
    successful = 0
    deficient = 0
    for n in range(4):
        for code in range(1 << (n * n)):
            graph = tuple(tuple(bool((code >> (n * i + j)) & 1)
                                for j in range(n)) for i in range(n))
            result = match_or_defect(graph)
            exists = any(is_matching(graph, p) for p in permutations(range(n)))
            if result.matching is not None:
                assert exists and is_matching(graph, result.matching)
                assert result.defect is None
                successful += 1
            else:
                assert not exists and result.defect is not None
                assert len(neighbors(graph, result.defect)) < len(result.defect)
                deficient += 1
            graph_count += 1

    # Repeated occurrences: only public centers and weights enter transport.
    ca = ((Q(-1), Q(0)), (Q(0), Q(0)), (Q(1), Q(0)))
    cb = ((Q(-11, 10), Q(0)), (Q(1, 10), Q(0)), (Q(9, 10), Q(0)))
    a, b, graph, result = transport(ca, (2, 1, 1), cb, (2, 1, 1), Q(1, 10))
    assert result.matching is not None
    assert max(l1(a[i], b[j]) for i, j in enumerate(result.matching)) <= Q(1, 10)

    # Balanced connected components do not imply a one-edge matching bound.
    red = ((Q(0),), (Q(1, 10),), (Q(2),))
    blue = ((Q(1),), (Q(29, 10),), (Q(3),))
    _, _, graph, result = transport(red, (1, 1, 1), blue, (1, 1, 1), Q(1))
    assert result.defect is not None
    assert neighbors(graph, (0, 1)) == (0,)
    bottleneck = min(max(l1(red[i], blue[p[i]]) for i in range(3))
                     for p in permutations(range(3)))
    assert bottleneck == Q(14, 5)

    # Boxes around +/-i can reverse lexicographic order at arbitrary small h.
    roots = ((Q(0), Q(1)), (Q(0), Q(-1)))
    for exponent in (4, 8, 16):
        h = Q(1, 2 ** exponent)
        first = ((h, Q(1)), (-h, Q(-1)))
        second = ((-h, Q(1)), (h, Q(-1)))
        assert sorted(range(2), key=lambda j: first[j]) == [1, 0]
        assert sorted(range(2), key=lambda j: second[j]) == [0, 1]
        # Fixed anchor labels stay correct in both certificates.
        assert nearest_anchors(first, roots) == (0, 1)
        assert nearest_anchors(second, roots) == (0, 1)
        assert all(l1(first[j], second[j]) == 2 * h for j in range(2))

    return {
        "status": "passed",
        "evidence_kind": "reference algorithm; not an iPRA proof",
        "exhaustive_graph_max_n": 3,
        "graphs_checked": graph_count,
        "perfect_matchings": successful,
        "hall_defects": deficient,
        "component_counterexample_exact_bottleneck": str(bottleneck),
        "locator_and_lexicographic_checks": 3,
    }


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2))
