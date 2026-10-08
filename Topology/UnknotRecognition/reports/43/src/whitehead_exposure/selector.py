"""Complete one-Whitehead singleton exposure via unit-bridge contraction."""
from __future__ import annotations
from collections import Counter
from .algebra import (Budget, Graph, add_graphs, degrees, cut_capacity, validate_graph,
                      validate_words, word_graph)
from .flow import minimum_pinned_cut, verify_pinned_cut


def unit_bridges(graph: Graph, vertices: tuple[int, ...]) -> list[tuple[int, int]]:
    """Unit-capacity bridges of the positive support; iterative DFS, no expansion."""
    adjacency = {v: [] for v in vertices}
    for u, v in sorted(graph):
        adjacency[u].append(v)
        adjacency[v].append(u)
    discovery: dict[int, int] = {}
    low: dict[int, int] = {}
    parent: dict[int, int | None] = {}
    answer = []
    clock = 0
    for root in vertices:
        if root in discovery:
            continue
        discovery[root] = low[root] = clock
        clock += 1
        parent[root] = None
        stack = [(root, iter(adjacency[root]))]
        while stack:
            u, it = stack[-1]
            try:
                v = next(it)
            except StopIteration:
                stack.pop()
                p = parent[u]
                if p is not None:
                    edge = tuple(sorted((p, u)))
                    if low[u] > discovery[p] and graph[edge] == 1:
                        answer.append(edge)
                    low[p] = min(low[p], low[u])
                continue
            if v == parent[u]:
                continue
            if v in discovery:
                low[u] = min(low[u], discovery[v])
            else:
                parent[v] = u
                discovery[v] = low[v] = clock
                clock += 1
                stack.append((v, iter(adjacency[v])))
    return sorted(answer)


def bridge_quotient(local: Graph, total: Graph, vertices: tuple[int, ...],
                    bridge: tuple[int, int]) -> tuple[dict[int, int], Graph, tuple[int, ...]]:
    parent = dict(zip(vertices, vertices))
    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    for u, v in local:
        if (u, v) != bridge:
            a, b = root(u), root(v)
            if a != b:
                parent[max(a, b)] = min(a, b)
    components = sorted({root(v) for v in vertices})
    names = {c: i for i, c in enumerate(components)}
    owner = {v: names[root(v)] for v in vertices}
    quotient: Counter[tuple[int, int]] = Counter()
    for (u, v), weight in total.items():
        a, b = owner[u], owner[v]
        if a != b:
            quotient[tuple(sorted((a, b)))] += weight
    return owner, dict(quotient), tuple(range(len(components)))


def exposure_from_graphs(graphs: list[Graph], alive: tuple[int, ...], *,
                         objective: str = "allocation", max_after: int | None = None,
                         max_increase: int | None = None, budget: Budget | None = None,
                         stats: dict | None = None) -> dict | None:
    """Minimize a proved allocation bound or total Whitehead length change.

    Inputs must be exact Whitehead graphs of cyclically reduced words.
    Graph well-formedness alone does NOT establish this provenance.
    """
    if not alive or any(type(g) is not int or g <= 0 for g in alive) or len(set(alive)) != len(alive):
        raise ValueError("invalid generator list")
    if objective not in ("allocation", "length"):
        raise ValueError("unknown objective")
    for cap in (max_after, max_increase):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("caps must be nonnegative integers or None")
    budget = budget or Budget()
    stats = stats if stats is not None else {}
    stats.update(relations=len(graphs), bridges=0, candidates=0, flows=0, forced=0,
                 quotient_patterns=0, largest_quotient=0)
    V = tuple(sorted([-g for g in alive] + list(alive)))
    for graph in graphs:
        validate_graph(graph, V)
    total = add_graphs(graphs)
    L = sum(total.values())
    dt = degrees(total, V)
    # This necessary condition catches corrupted summaries, but is not a
    # replacement for constructing the graphs from the actual words.
    for graph in graphs:
        ds = degrees(graph, V)
        if any(ds[g] != ds[-g] for g in alive):
            raise ValueError("unbalanced signed degrees")
    best = None
    best_key = None
    for j, local in enumerate(graphs):
        budget.tick(len(local)+len(V)+1)
        dl = degrees(local, V)
        ell = sum(local.values())
        bridges = unit_bridges(local, V)
        stats["bridges"] += len(bridges)
        for bridge in bridges:
            budget.tick(len(total)+len(local)+len(V)+1)
            owner, quotient, Q = bridge_quotient(local, total, V, bridge)
            stats["largest_quotient"] = max(stats["largest_quotient"], len(Q))
            u, v = (owner[x] for x in bridge)
            assert u != v
            cache: dict[tuple[int, int], dict | None] = {}
            for a in V:
                A, B = owner[a], owner[-a]
                if A == B:
                    continue
                pattern = (A, B)
                if pattern not in cache:
                    inside, outside = {u, A}, {v, B}
                    proof = minimum_pinned_cut(quotient, Q, inside, outside, budget)
                    cache[pattern] = proof
                    stats["quotient_patterns"] += 1
                    if proof is not None:
                        stats["flows" if proof["kind"] == "flow" else "forced"] += 1
                proof = cache[pattern]
                if proof is None:
                    continue
                stats["candidates"] += 1
                c = proof["capacity"]
                t = ell-dl[a]
                delta = c-dt[a]
                allocation = L-dt[a] + t*(c-2)
                budget.tick()
                if max_after is not None and allocation > max_after:
                    continue
                if max_increase is not None and delta > max_increase:
                    continue
                small_shore = set(proof["shore"])
                shore = [x for x in V if owner[x] in small_shore]
                key = ((allocation, delta) if objective == "allocation" else (delta, allocation))
                key += (j, a, tuple(shore), bridge)
                if best_key is None or key < best_key:
                    best_key = key
                    best = {"relation": j, "multiplier": a, "subset": shore,
                            "bridge": list(bridge), "cut_capacity": c,
                            "length_change": delta, "target_after": t+1,
                            "allocation_bound": allocation, "cut_proof": proof}
    stats["work"] = budget.used
    return best


def find_exposure(words, alive, **kwargs) -> dict | None:
    W, generators = validate_words(words, alive)
    return exposure_from_graphs([word_graph(w) for w in W], generators, **kwargs)


def verify_exposure_graphs(graphs: list[Graph], alive: tuple[int, ...], witness: dict) -> bool:
    """Check a witness and its pinned-cut optimum; NOT global selector optimality."""
    try:
        fields = {"relation", "multiplier", "subset", "bridge", "cut_capacity",
                  "length_change", "target_after", "allocation_bound", "cut_proof"}
        if type(witness) is not dict or set(witness) != fields:
            return False
        if (not alive or any(type(g) is not int or g <= 0 for g in alive)
                or len(set(alive)) != len(alive)):
            return False
        V = tuple(sorted([-g for g in alive]+list(alive)))
        for graph in graphs:
            validate_graph(graph, V)
        j, a = witness["relation"], witness["multiplier"]
        if type(j) is not int or not 0 <= j < len(graphs) or type(a) is not int or a not in V:
            return False
        for name in ("cut_capacity", "length_change", "target_after", "allocation_bound"):
            if type(witness[name]) is not int:
                return False
        subset = witness["subset"]
        if type(subset) is not list or any(type(x) is not int for x in subset) or len(set(subset)) != len(subset):
            return False
        shore = set(subset)
        if not shore <= set(V) or a not in shore or -a in shore:
            return False
        if (type(witness["bridge"]) is not list or len(witness["bridge"]) != 2
                or any(type(x) is not int for x in witness["bridge"])):
            return False
        bridge = tuple(witness["bridge"])
        local = graphs[j]
        # Independently checking cut size one suffices for exposure.
        crossing = [e for e in local if (e[0] in shore) != (e[1] in shore)]
        if crossing != [bridge] or local.get(bridge) != 1:
            return False
        total = add_graphs(graphs)
        owner, quotient, Q = bridge_quotient(local, total, V, bridge)
        u, v = (owner[x] for x in bridge)
        small = {owner[x] for x in shore}
        if any((x in shore) != (owner[x] in small) for x in V):
            return False
        if not verify_pinned_cut(quotient, Q, {u, owner[a]}, {v, owner[-a]}, witness["cut_proof"]):
            return False
        if small != set(witness["cut_proof"]["shore"]):
            return False
        c = cut_capacity(total, shore)
        da = sum(w for e, w in total.items() if a in e)
        dj = sum(w for e, w in local.items() if a in e)
        t = sum(local.values())-dj
        L = sum(total.values())
        return (witness["cut_capacity"] == c and witness["length_change"] == c-da
                and witness["target_after"] == t+1 and witness["allocation_bound"] == L-da+t*(c-2))
    except (KeyError, TypeError, ValueError, IndexError):
        return False
