"""Validate the flow and Hall constructions on small, exhaustively generated inputs.

Run with Python 3.10 or newer. Arc indices distinguish parallel, opposite and
zero-capacity arcs. All counts printed are counts of instances, not proof claims.
"""

from collections import deque
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Arc:
    tail: int
    head: int
    capacity: int


@dataclass
class Solution:
    value: int
    flow: list[int]
    side: int
    reverse_steps: int


def contains(mask, vertex):
    return bool(mask & (1 << vertex))


def boundary_capacity(arcs, side):
    return sum(arc.capacity for arc in arcs
               if contains(side, arc.tail) and not contains(side, arc.head))


def residual_search(n, arcs, flow, source):
    """Search the residual graph and retain a signed original arc per vertex."""
    parent = [None] * n
    side = 1 << source
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for i, arc in enumerate(arcs):
            if arc.tail == u and flow[i] < arc.capacity:
                target, sign = arc.head, 1
            elif arc.head == u and flow[i] > 0:
                target, sign = arc.tail, -1
            else:
                continue
            if not contains(side, target):
                side |= 1 << target
                parent[target] = (u, i, sign)
                queue.append(target)
    return side, parent


def solve(n, arcs, source, sink):
    assert 0 <= source < n and 0 <= sink < n and source != sink
    flow = [0] * len(arcs)
    value = reverse_steps = 0
    for _ in range(boundary_capacity(arcs, 1 << source)):
        side, parent = residual_search(n, arcs, flow, source)
        if not contains(side, sink):
            break
        u = sink
        while u != source:
            u, i, sign = parent[u]
            flow[i] += sign
            reverse_steps += int(sign == -1)
        value += 1
    side, _ = residual_search(n, arcs, flow, source)
    assert not contains(side, sink)
    return Solution(value, flow, side, reverse_steps)


def imbalance(n, arcs, flow):
    """Compute net outflow from original arc endpoints without residual data."""
    net = [0] * n
    for arc, amount in zip(arcs, flow):
        net[arc.tail] += amount
        net[arc.head] -= amount
    return net


def exhaustive_flow_value(n, arcs, source, sink):
    best = 0
    for candidate in product(*(range(e.capacity + 1) for e in arcs)):
        net = imbalance(n, arcs, candidate)
        if all(v in (source, sink) or net[v] == 0 for v in range(n)):
            best = max(best, net[source])
    return best


def validate_network(n, arcs, source, sink):
    sol = solve(n, arcs, source, sink)
    assert all(0 <= f <= e.capacity for f, e in zip(sol.flow, arcs))
    balance = imbalance(n, arcs, sol.flow)
    expected = [0] * n
    expected[source], expected[sink] = sol.value, -sol.value
    assert balance == expected
    costs = [boundary_capacity(arcs, mask) for mask in range(1 << n)
             if contains(mask, source) and not contains(mask, sink)]
    assert min(costs) == boundary_capacity(arcs, sol.side) == sol.value
    assert contains(sol.side, source) and not contains(sol.side, sink)
    assert exhaustive_flow_value(n, arcs, source, sink) == sol.value
    return sol


def matching_optimum(edges, a, b):
    """Enumerate actual matchings independently of the network reduction."""
    best = 0
    for selected in range(1 << len(edges)):
        left = [0] * a
        right = [0] * b
        for i, (x, y) in enumerate(edges):
            if contains(selected, i):
                left[x] += 1
                right[y] += 1
        if max(left + right, default=0) <= 1:
            best = max(best, selected.bit_count())
    return best


def neighbors(edges, subset):
    mask = 0
    for x, y in edges:
        if contains(subset, x):
            mask |= 1 << y
    return mask


def validate_hall(a, b, edges):
    # Vertex blocks are L, R, source, sink; middle arc indices start at a.
    source, sink = a + b, a + b + 1
    arcs = ([Arc(source, x, 1) for x in range(a)] +
            [Arc(x, a + y, a + 1) for x, y in edges] +
            [Arc(a + y, sink, 1) for y in range(b)])
    sol = solve(sink + 1, arcs, source, sink)
    chosen = [edge for i, edge in enumerate(edges) if sol.flow[a + i]]
    assert len({x for x, _ in chosen}) == len({y for _, y in chosen})
    assert len(chosen) == len({x for x, _ in chosen}) == sol.value
    assert matching_optimum(edges, a, b) == sol.value
    left_mask = sol.side & ((1 << a) - 1)
    right_mask = (sol.side >> a) & ((1 << b) - 1)
    assert neighbors(edges, left_mask) == right_mask
    assert all(not contains(left_mask, x) or contains(right_mask, y)
               for x, y in edges)
    assert a - left_mask.bit_count() + right_mask.bit_count() == sol.value
    deficiency = max(w.bit_count() - neighbors(edges, w).bit_count()
                     for w in range(1 << a))
    assert deficiency == left_mask.bit_count() - right_mask.bit_count()
    assert deficiency == a - sol.value


def main():
    network_count = 0
    for n in (2, 3):
        endpoints = [(u, v) for u in range(n) for v in range(n) if u != v]
        for caps in product(range(3), repeat=len(endpoints)):
            arcs = [Arc(u, v, c) for (u, v), c in zip(endpoints, caps)]
            validate_network(n, arcs, 0, n - 1)
            network_count += 1

    extras = [
        (2, []),
        (3, [Arc(0, 0, 2), Arc(2, 2, 1), Arc(2, 0, 2)]),
        (3, [Arc(0, 1, 2), Arc(0, 1, 1), Arc(1, 0, 1),
             Arc(1, 2, 2), Arc(1, 2, 0), Arc(2, 1, 1)]),
    ]
    for n, arcs in extras:
        validate_network(n, arcs, 0, n - 1)
    # First BFS path takes 0-1-3-5. The next must undo arc 1->3.
    reversals = [Arc(u, v, 1) for u, v in
                 [(0, 1), (0, 2), (1, 3), (1, 4), (2, 3), (3, 5), (4, 5)]]
    result = validate_network(6, reversals, 0, 5)
    assert result.value == 2 and result.reverse_steps == 1
    network_count += len(extras) + 1

    hall_count = 0
    for a, b in product(range(4), repeat=2):
        full = list(product(range(a), range(b)))
        for graph in range(1 << len(full)):
            edges = [edge for i, edge in enumerate(full) if contains(graph, i)]
            validate_hall(a, b, edges)
            hall_count += 1
    validate_hall(2, 2, [(0, 0), (0, 0), (1, 0)])
    hall_count += 1
    print(f"{network_count} networks passed exhaustive flow and cut comparison.")
    print(f"{hall_count} bipartite instances passed matching and deficiency comparison.")
    print("Reverse residual step, loops, parallel and opposite arcs all exercised.")


if __name__ == "__main__":
    main()
