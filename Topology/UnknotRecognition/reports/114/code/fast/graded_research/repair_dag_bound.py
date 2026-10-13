"""Exact weighted-path bound for a *supplied, justified* repair dependency DAG.

This module does not discover geometric dependencies or prove that they are
acyclic.  Vertex i has counter bound g[i].  A charged event at i must strictly
decrease that counter and may increase only out-neighbor counters.  The exact
combinatorial upper bound is sum of products of g along all nonempty paths.

Run directly to perform independent path-enumeration checks.
"""
from collections import deque


def repair_bound(counter_bounds, edges):
    """Return (total_bound, per_vertex_bounds, topological_order).

    Reject negative/noninteger bounds, invalid endpoints, and directed cycles.
    Duplicate edges have no effect.  Arithmetic is exact over Python integers.
    """
    bounds = tuple(counter_bounds)
    if any(type(g) is not int or g < 0 for g in bounds):
        raise ValueError("counter bounds must be nonnegative integers")
    size = len(bounds)
    outgoing = [set() for _ in bounds]
    indegree = [0] * size
    for edge in edges:
        if len(edge) != 2:
            raise ValueError("each edge must have two endpoints")
        start, end = edge
        if (type(start) is not int or type(end) is not int
                or not 0 <= start < size or not 0 <= end < size):
            raise ValueError("edge endpoint outside vertex range")
        if end not in outgoing[start]:
            outgoing[start].add(end)
            indegree[end] += 1
    pending = deque(i for i, degree in enumerate(indegree) if degree == 0)
    incoming_bound = [0] * size
    vertex_bound = [0] * size
    order = []
    while pending:
        vertex = pending.popleft()
        order.append(vertex)
        vertex_bound[vertex] = bounds[vertex] * (1 + incoming_bound[vertex])
        for following in sorted(outgoing[vertex]):
            incoming_bound[following] += vertex_bound[vertex]
            indegree[following] -= 1
            if indegree[following] == 0:
                pending.append(following)
    if len(order) != size:
        raise ValueError("repair dependency graph is cyclic")
    return sum(vertex_bound), tuple(vertex_bound), tuple(order)


def self_test():
    """Compare the recurrence with independent explicit path enumeration."""
    import random

    def enumerate_paths(bounds, edges):
        outgoing = [[] for _ in bounds]
        for start, end in set(edges):
            outgoing[start].append(end)
        total = 0
        stack = [(i, bounds[i]) for i in range(len(bounds))]
        while stack:
            vertex, product = stack.pop()
            total += product
            stack.extend((j, product * bounds[j]) for j in outgoing[vertex])
        return total

    fixtures = 0
    for size in range(9):
        for bound in range(5):
            weights = [bound] * size
            cases = [
                ([], size * bound),
                ([(i, i + 1) for i in range(size - 1)],
                 sum((size - k + 1) * bound ** k for k in range(1, size + 1))),
                ([(i, j) for i in range(size) for j in range(i + 1, size)],
                 (bound + 1) ** size - 1),
                ([(0, j) for j in range(1, size)],
                 bound + (size - 1) * bound * (1 + bound) if size else 0),
            ]
            for edges, expected in cases:
                assert repair_bound(weights, edges)[0] == expected
                assert enumerate_paths(weights, edges) == expected
                fixtures += 1
    rng = random.Random(20261008)
    for _ in range(200):
        size = rng.randrange(1, 9)
        labels = list(range(size))
        rng.shuffle(labels)
        weights = [rng.randrange(5) for _ in range(size)]
        edges = [(labels[i], labels[j]) for i in range(size)
                 for j in range(i + 1, size) if rng.randrange(2)]
        assert repair_bound(weights, edges)[0] == enumerate_paths(weights, edges)
        fixtures += 1
    for weights, edges in [([1], [(0, 0)]), ([1, 1], [(0, 1), (1, 0)]),
                           ([-1], []), ([True], []), ([1], [(0, 1)])]:
        try:
            repair_bound(weights, edges)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid input was accepted")
    assert repair_bound([2, 3], [(0, 1), (0, 1)])[0] == 11
    return {"status": "PASS", "path_enumeration_fixtures": fixtures,
            "invalid_inputs_rejected": 5, "duplicate_edge_check": True}


if __name__ == "__main__":
    import json
    from pathlib import Path
    import sys
    report = self_test()
    Path(sys.argv[1]).write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, sort_keys=True))
