"""Signed connectivity extension, separate from the disk-specific kernel."""
from __future__ import annotations
from itertools import product
from disk_kernel import validate_partition


def validate_signs(p, signs):
    p = validate_partition(p)
    signs = tuple(signs)
    if len(signs) != len(p) or any(type(x) is not int or x not in (0, 1) for x in signs):
        raise ValueError("one binary sign per port is required")
    return p, signs


def signed_row(p, signs) -> int:
    p, signs = validate_signs(p, signs)
    c = max(p) + 1
    out = 0
    for flips in product((0, 1), repeat=c - 1):
        phase = (signs[0],) + flips
        mask = 0
        for i in range(1, len(p)):
            if signs[i] ^ phase[p[i]]:
                mask |= 1 << (i - 1)
        out |= 1 << mask
    return out


def signed_graph_completion(p, signs, q, other_signs) -> bool:
    """Connected plus consistent parity equations, checked by graph traversal."""
    p, signs = validate_signs(p, signs)
    q, other_signs = validate_signs(q, other_signs)
    if len(p) != len(q):
        raise ValueError("width mismatch")
    cp, cq = max(p) + 1, max(q) + 1
    adj = [[] for _ in range(cp + cq)]
    for a, x, b, y in zip(p, signs, q, other_signs):
        adj[a].append((cp + b, x ^ y))
        adj[cp + b].append((a, x ^ y))
    phase = {0: 0}
    todo = [0]
    while todo:
        a = todo.pop()
        for b, parity in adj[a]:
            need = phase[a] ^ parity
            if b in phase and phase[b] != need:
                return False
            if b not in phase:
                phase[b] = need
                todo.append(b)
    return len(phase) == cp + cq


def signed_states(r):
    from disk_kernel import partitions
    for p in partitions(r):
        leaders = {p.index(a) for a in set(p)}
        free = [i for i in range(r) if i not in leaders]
        for bits in product((0, 1), repeat=len(free)):
            signs = [0] * r
            for i, b in zip(free, bits):
                signs[i] = b
            yield p, tuple(signs)
