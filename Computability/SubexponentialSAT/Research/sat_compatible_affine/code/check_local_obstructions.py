"""Finite illustrations and scope controls for asymptotic_ideas.md.

The mathematical proofs are in the note. These checks do not establish
asymptotic bounds. Uses only Python's standard library.
"""
from itertools import product
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def good_shifts(row, col):
    p = len(row)
    return tuple(d for d in range(p)
                 if all(row[t] == col[(t + d) % p] for t in range(p)))


def prime_checks():
    table = []
    for p in (2, 3, 5, 7):
        all_nonzero = nonconstant = checked = 0
        for row in product((0, 1), repeat=p):
            for col in product((0, 1), repeat=p):
                checked += 1
                shifts = good_shifts(row, col)
                constant = len(set(row + col)) == 1
                require(len(shifts) < 2 or constant,
                        f"Prime-cycle lemma violated at p={p}")
                if all(d in shifts for d in range(1, p)):
                    all_nonzero += 1
                    nonconstant += not constant
        require((all_nonzero, nonconstant) ==
                ((4, 2) if p == 2 else (2, 0)),
                f"Unexpected enumeration count at p={p}")
        table.append(dict(p=p, pairs_checked=checked,
                          all_nonzero_good=all_nonzero,
                          nonconstant_all_nonzero_good=nonconstant))

    # Scope control: the prime assumption cannot simply be removed.
    col = (0, 1, 0, 1)
    row = (1, 0, 1, 0)
    require(good_shifts(row, col) == (1, 3),
            "Composite-cycle scope control failed")

    # Scope control: a vector-space digit can retain several good shifts.
    elements = tuple(product((0, 1), repeat=2))
    vector_shifts = []
    for d in elements:
        if all(1 - t[0] == (t[0] ^ d[0]) for t in elements):
            vector_shifts.append(d)
    require(vector_shifts == [(1, 0), (1, 1)],
            "Vector-space scope control failed")
    return table


def coherence_checks():
    vertices = tuple(range(6))
    possible_edges = tuple((v, 3 + f) for v in range(3) for f in range(3))
    admissible = 0
    for edge_mask in range(1 << len(possible_edges)):
        edges = [e for i, e in enumerate(possible_edges)
                 if edge_mask >> i & 1]
        adjacency = {v: [] for v in vertices}
        for a, b in edges:
            adjacency[a].append(b)
            adjacency[b].append(a)
        components = []
        unseen = set(vertices)
        while unseen:
            start = min(unseen)
            reached, pending = set(), [start]
            while pending:
                v = pending.pop()
                if v in reached:
                    continue
                reached.add(v)
                pending.extend(adjacency[v])
            unseen -= reached
            components.append(reached)
        for labels in product((0, 1), repeat=6):
            if not all(labels[a] == labels[b] for a, b in edges):
                continue
            admissible += 1
            require(all(len({labels[v] for v in c}) == 1 for c in components),
                    "Component-label coherence failed")
    return dict(graphs_checked=512, labelings_per_graph=64,
                admissible_labelings=admissible)


if __name__ == "__main__":
    result = dict(prime_cycles=prime_checks(),
                  coherence=coherence_checks(),
                  scope_controls="passed",
                  status="finite checks passed; proofs are in the note")
    print(json.dumps(result, indent=2, sort_keys=True))
