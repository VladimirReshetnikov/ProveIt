"""Planar matching geometry. Adapted from ProveIt's MIT-0 geometry.py.
See SOURCES.json for the audited upstream blob; this is a compact reimplementation.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass

SMOOTHINGS = (((0, 1), (2, 3)), ((0, 3), (1, 2)))
Matching = frozenset

class ScanLimit(RuntimeError):
    """Resource exhaustion, never a knot verdict."""

def find(parent: dict, x):
    root = x
    while parent[root] != root:
        root = parent[root]
    while parent[x] != root:
        parent[x], x = root, parent[x]
    return root

@dataclass
class Glued:
    points: frozenset
    matching: frozenset
    closed: int
    arc_of: dict

def glue(m: Matching, i: int, points: frozenset, slots: tuple) -> Glued:
    adj = defaultdict(list)
    def edge(a, b, arc=None):
        adj[a].append((b, arc)); adj[b].append((a, arc))
    for pair in m:
        p, q = pair
        edge(('P', p), ('P', q), ('m', pair))
    for j, (s, t) in enumerate(SMOOTHINGS[i]):
        edge(('S', s), ('S', t), ('s', j))
    seen_labels = {}
    for j, label in enumerate(slots):
        if label in points:
            edge(('S', j), ('P', label))
        elif label in seen_labels:
            edge(('S', j), ('S', seen_labels[label]))
        else:
            seen_labels[label] = j
    def label(node):
        return node[1] if node[0] == 'P' else slots[node[1]]
    visited, pairs, arc_of = set(), [], {}
    closed = 0
    # Walk by edge indices, not just the preceding vertex: parallel arcs matter.
    for start in [x for x in adj if len(adj[x]) == 1] + list(adj):
        if start in visited:
            continue
        component, stack = set(), [start]
        while stack:
            u = stack.pop()
            if u in component:
                continue
            component.add(u)
            stack.extend(v for v, _ in adj[u])
        visited.update(component)
        ends = [x for x in component if len(adj[x]) == 1]
        arcs = {a for x in component for _, a in adj[x] if a is not None}
        if ends:
            if len(ends) != 2:
                raise ArithmeticError('non-manifold smoothing component')
            pair = frozenset(label(x) for x in ends)
            if len(pair) != 2:
                raise ArithmeticError('degenerate boundary arc')
            pairs.append(pair)
            ref = ('new', pair)
        else:
            ref = ('closed', closed)
            closed += 1
        for a in arcs:
            arc_of[a] = ref
    matching = frozenset(pairs)
    return Glued(frozenset(p for pair in matching for p in pair), matching, closed, arc_of)
