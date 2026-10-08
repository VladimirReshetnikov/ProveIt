"""Deterministic integer min cuts, with independently checkable flow witnesses."""
from __future__ import annotations
from collections import deque
from .algebra import Budget, Graph, cut_capacity


def minimum_pinned_cut(graph: Graph, vertices: tuple[int, ...], inside: set[int],
                       outside: set[int], budget: Budget) -> dict | None:
    """Minimum cut with several pinned vertices. None means conflicting pins."""
    V = set(vertices)
    if not inside <= V or not outside <= V:
        raise ValueError("pin outside vertex set")
    if inside & outside:
        return None
    if inside | outside == V:
        budget.tick(len(graph) + 1)
        return {"kind": "forced", "shore": sorted(inside),
                "capacity": cut_capacity(graph, inside)}
    source, sink = max(V, default=-1)+1, max(V, default=-1)+2
    # Every feasible original cut costs <= sum(graph.values()).
    inf = sum(graph.values()) + 1
    network = dict(graph)
    for v in inside:
        network[tuple(sorted((v, source)))] = inf
    for v in outside:
        network[tuple(sorted((v, sink)))] = inf
    residual = {v: {} for v in vertices+(source, sink)}
    for (u, v), capacity in sorted(network.items()):
        residual[u][v] = residual[v][u] = capacity
    flow_value = 0
    while True:
        budget.tick()
        parent = {source: None}
        queue = deque([source])
        while queue and sink not in parent:
            u = queue.popleft()
            budget.tick(len(residual[u])+1)
            for v, capacity in residual[u].items():
                if capacity > 0 and v not in parent:
                    parent[v] = u
                    queue.append(v)
        if sink not in parent:
            shore = set(parent) & V
            break
        v = sink
        delta = inf
        while parent[v] is not None:
            u = parent[v]
            delta = min(delta, residual[u][v])
            v = u
        flow_value += delta
        v = sink
        while parent[v] is not None:
            u = parent[v]
            residual[u][v] -= delta
            residual[v][u] += delta
            v = u
    certificate = {"kind": "flow", "shore": sorted(shore), "capacity": flow_value,
                   "flow": [[u, v, c-residual[u][v]] for (u, v), c in sorted(network.items())]}
    assert inside <= shore and not (outside & shore)
    assert cut_capacity(graph, shore) == flow_value
    return certificate


def verify_pinned_cut(graph: Graph, vertices: tuple[int, ...], inside: set[int],
                      outside: set[int], certificate: dict) -> bool:
    """Verify optimality using conservation and weak duality, without max flow."""
    try:
        V = set(vertices)
        if inside & outside or not inside <= V or not outside <= V:
            return False
        if type(certificate) is not dict or certificate.get("kind") not in ("flow", "forced"):
            return False
        expected = {"kind", "shore", "capacity"} | ({"flow"} if certificate["kind"] == "flow" else set())
        if set(certificate) != expected:
            return False
        raw_shore = certificate["shore"]
        if (type(raw_shore) is not list or any(type(v) is not int for v in raw_shore)
                or len(set(raw_shore)) != len(raw_shore)):
            return False
        shore = set(raw_shore)
        value = certificate["capacity"]
        if (type(value) is not int or value < 0 or not shore <= V or not inside <= shore
                or outside & shore or cut_capacity(graph, shore) != value):
            return False
        if certificate["kind"] == "forced":
            return inside | outside == V and shore == inside
        source, sink = max(V, default=-1)+1, max(V, default=-1)+2
        inf = sum(graph.values()) + 1
        network = dict(graph)
        for v in inside:
            network[tuple(sorted((v, source)))] = inf
        for v in outside:
            network[tuple(sorted((v, sink)))] = inf
        balances = dict.fromkeys(V | {source, sink}, 0)
        seen = set()
        if type(certificate["flow"]) is not list:
            return False
        for triple in certificate["flow"]:
            if type(triple) is not list or len(triple) != 3 or any(type(x) is not int for x in triple):
                return False
            u, v, f = triple
            if (u, v) not in network or (u, v) in seen or abs(f) > network[u, v]:
                return False
            seen.add((u, v))
            balances[u] += f
            balances[v] -= f
        return (seen == set(network) and balances[source] == value and balances[sink] == -value
                and all(balances[v] == 0 for v in V))
    except (KeyError, TypeError, ValueError):
        return False
