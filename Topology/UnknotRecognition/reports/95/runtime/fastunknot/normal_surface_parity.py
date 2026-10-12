"""Finite boundary cohomology witnesses, adapted from report 47 (MIT-0).

An odd closed edge chain proves nonzero cohomology. Vertex potentials prove
zero cohomology. The graph has one edge per ambient boundary edge, regardless
of normal-coordinate magnitudes.
"""

from collections import deque


def _parity_certificate(graph, check):
    """Prove a boundary cocycle exact by vertex values, or nonexact by a cycle."""
    adjacency = {}
    for index, (a, b, parity) in enumerate(graph):
        check()
        adjacency.setdefault(a, []).append((b, parity, index))
        adjacency.setdefault(b, []).append((a, parity, index))
    values, parent = {}, {}
    for root in sorted(adjacency):
        check()
        if root in values:
            continue
        values[root] = 0
        parent[root] = None
        pending = deque([root])
        while pending:
            check()
            current = pending.popleft()
            for other, parity, index in adjacency[current]:
                expected = values[current] ^ parity
                if other not in values:
                    values[other] = expected
                    parent[other] = (current, index)
                    pending.append(other)
                elif values[other] != expected:
                    cycle = {index}
                    for start in (current, other):
                        while parent[start] is not None:
                            check()
                            previous, edge = parent[start]
                            cycle.symmetric_difference_update((edge,))
                            start = previous
                    return {"nonzero": True, "cycle_edges": sorted(cycle)}
    return {"nonzero": False, "vertex_values": [[key, values[key]] for key in sorted(values)]}


def _verify_parity(graph, proof, check):
    if type(proof) is not dict or type(proof.get("nonzero")) is not bool:
        return False
    if proof["nonzero"]:
        if set(proof) != {"nonzero", "cycle_edges"}:
            return False
        chosen = proof["cycle_edges"]
        if (type(chosen) is not list or not chosen or
                any(type(i) is not int or not 0 <= i < len(graph) for i in chosen) or
                len(set(chosen)) != len(chosen)):
            return False
        odd, parity = set(), 0
        for index in chosen:
            check()
            a, b, bit = graph[index]
            odd.symmetric_difference_update((a,))
            odd.symmetric_difference_update((b,))
            parity ^= bit
        return not odd and parity == 1
    if set(proof) != {"nonzero", "vertex_values"}:
        return False
    values = proof["vertex_values"]
    if type(values) is not list:
        return False
    assigned = {}
    for pair in values:
        check()
        if (type(pair) is not list or len(pair) != 2 or
                type(pair[0]) is not int or type(pair[1]) is not int or
                pair[1] not in (0, 1) or pair[0] in assigned):
            return False
        assigned[pair[0]] = pair[1]
    if set(assigned) != {v for a, b, _ in graph for v in (a, b)}:
        return False
    return all(assigned[a] ^ assigned[b] == parity for a, b, parity in graph)


