"""Independent slow finite replay: no producer row builder or DSU calls."""
from __future__ import annotations
from typing import Sequence
from .core import Candidate, SignedPartition, BasisCertificate, BudgetExceeded


def assignments(p: SignedPartition, max_dimension: int = 1 << 18) -> frozenset[int]:
    if type(max_dimension) is not int or max_dimension < 1:
        raise ValueError("max_dimension must be a positive exact integer")
    if p.r - 1 >= max_dimension.bit_length() or (1 << (p.r - 1)) > max_dimension:
        raise BudgetExceeded("independent replay dimension exceeded")
    out = set()
    for x in range(1 << (p.r - 1)):
        spin = [0] + [(x >> (i - 1)) & 1 for i in range(1, p.r)]
        values = {}
        okay = True
        for i, block in enumerate(p.labels):
            value = spin[i] ^ p.offsets[i]
            if block in values and values[block] != value:
                okay = False; break
            values[block] = value
        if okay:
            out.add(x)
    return frozenset(out)


def graph_compatible(a: SignedPartition, b: SignedPartition) -> bool:
    """BFS from port zero, rebuilding relations from all within-block pairs."""
    if a.r != b.r:
        raise ValueError("different widths")
    graph = [[] for _ in range(a.r)]
    for p in (a, b):
        for i in range(p.r):
            for j in range(i):
                if p.labels[i] == p.labels[j]:
                    sign = p.offsets[i] ^ p.offsets[j]
                    graph[i].append((j, sign)); graph[j].append((i, sign))
    colors = {0: 0}; todo = [0]
    while todo:
        i = todo.pop()
        for j, sign in graph[i]:
            value = colors[i] ^ sign
            if j in colors:
                if colors[j] != value:
                    return False
            else:
                colors[j] = value; todo.append(j)
    return len(colors) == a.r


def verify_basis(family: Sequence[Candidate], cert: BasisCertificate,
                 *, max_dimension: int = 1 << 18) -> bool:
    """Check subset, size, independent rows, every identity and cost dominance.

    Purely algebraic: tokens identify the original witnesses but do not certify
    ambient embeddings, essential boundary, Euler weights, or geometry keys.
    """
    try:
        if not family:
            return cert == BasisCertificate((), (), 0, "")
        if type(cert.width) is not int or cert.width != family[0].partition.r:
            return False
        if cert.geometry_key != family[0].geometry_key:
            return False
        if any(c.partition.r != cert.width or c.geometry_key != cert.geometry_key for c in family):
            return False
        if len(cert.expressions) != len(family) or len(cert.selected) != len(set(cert.selected)):
            return False
        if len(cert.selected) > 1 << (cert.width - 1):
            return False
        if any(type(i) is not int or not 0 <= i < len(family) for i in cert.selected):
            return False
        rows = [assignments(family[i].partition, max_dimension) for i in cert.selected]
        # Independent finite-set Gaussian elimination.
        pivots = {}
        for row in rows:
            v = set(row)
            while v and max(v) in pivots:
                v.symmetric_difference_update(pivots[max(v)])
            if not v:
                return False
            pivots[max(v)] = set(v)
        for i, mask in enumerate(cert.expressions):
            if type(mask) is not int or mask < 0 or mask.bit_length() > len(rows):
                return False
            value = set()
            for j, selected_i in enumerate(cert.selected):
                if (mask >> j) & 1:
                    if family[selected_i].cost > family[i].cost:
                        return False
                    value.symmetric_difference_update(rows[j])
            if value != assignments(family[i].partition, max_dimension):
                return False
        return True
    except (ValueError, TypeError, AttributeError, IndexError):
        return False
