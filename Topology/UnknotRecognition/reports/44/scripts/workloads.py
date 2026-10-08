"""Deterministic planar graph/merge-tree observer workloads (not knot benchmarks)."""
from __future__ import annotations
from terminal_updates.terminal import SignedGraph


def wheel(b: int, signed: bool = False):
    if b < 3:
        raise ValueError('a wheel needs at least three rim vertices')
    edges = []
    for i in range(b):
        edges.append((i, (i+1) % b, -1 if signed and i % 3 == 0 else 1))
        edges.append((i, b, -1 if signed and i % 5 == 0 else 1))
    return SignedGraph(b+1, tuple(edges)), tuple(range(b))


def triangular_grid(w: int):
    if w < 2:
        raise ValueError('width must be at least two')
    edges = []
    for i in range(w):
        for j in range(w):
            v = i*w+j
            if j+1 < w:
                edges.append((v, v+1, 1))
            if i+1 < w:
                edges.append((v, v+w, 1))
            if i+1 < w and j+1 < w:
                edges.append((v, v+w+1, 1))
    boundary = (tuple(range(w)) + tuple(i*w+w-1 for i in range(1, w))
                + tuple((w-1)*w+j for j in range(w-2, -1, -1))
                + tuple(i*w for i in range(w-2, 0, -1)))
    return SignedGraph(w*w, tuple(edges)), boundary


def shallow_tree(b: int, branches: int | None = None):
    """Merge one or two noncrossing adjacent pairs; parents precede children.

    Each entry is (parent node index, retained anchor, removed anchor).
    The singleton partition is node zero, entries number nodes 1..J.
    """
    pairs = [(i, i+1) for i in range(0, b-1, 2)]
    if branches is not None:
        pairs = pairs[:branches]
    events = []
    for j, (a, z) in enumerate(pairs):
        events.append((0, a, z))
        parent = len(events)
        for c, d in pairs[j+1:]:
            events.append((parent, c, d))
    return events


def chain(b: int):
    return [(i-1, 0, i) for i in range(1, b)]


def partition_labels(b: int, events):
    labels = [tuple(range(b))]
    for parent, a, z in events:
        old = labels[parent]
        labels.append(tuple(a if v == z else v for v in old))
    return labels


def children(events):
    tree = [[] for _ in range(len(events)+1)]
    for i, (parent, a, z) in enumerate(events, 1):
        tree[parent].append((i, a, z))
    return tree


def dynamic_queries(kernel, events):
    """DFS uses only one branch of persistent states, not the whole tree in memory."""
    tree = children(events)
    answers = [0]*(len(events)+1)
    root = kernel.cursor()
    def visit(node, state):
        answers[node] = state.residue
        for child, a, z in tree[node]:
            visit(child, state.merged(a, z))
    visit(0, root)
    return answers


def static_queries(kernel, labels):
    return [kernel.query(partition) for partition in labels]
