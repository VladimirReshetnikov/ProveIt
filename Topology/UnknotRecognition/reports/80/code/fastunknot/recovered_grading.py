"""Recover relative quantum shifts from a connected homogeneous complex.

The differential equation is q[target]-q[source] = m-c+2*dot_degree,
where 2m is the frontier size and c counts overlay circles. The additive
constant on each connected component is immaterial for scalar basis changes.
"""
from .frobenius.subset import homogeneous_degree


def recover_shifts(scan, group, *, check=lambda: None):
    """Return verified relative shifts; reject mixed entries or inconsistent cycles.

    This does not claim an arbitrary graded complex arises from a knot. It
    certifies the precise constraint needed for homogeneous scalar splitting.
    The caller supplies an entire differential-graph component.
    """
    adjacency = {v: [] for v in group}
    m = len(scan.points) // 2
    for v in group:
        check()
        for w, value in scan.out[v].items():
            degree = homogeneous_degree(value, check=check)
            if degree is None or degree < 0:
                raise ValueError('quantum shifts require nonzero homogeneous entries')
            circles = scan.algebra.basis(scan.mid[v], scan.mid[w])[1]
            delta = m - circles + 2 * degree
            adjacency[v].append((w, delta))
            adjacency[w].append((v, -delta))
    shifts = {}
    for root in group:
        if root in shifts:
            continue
        shifts[root] = 0
        pending = [root]
        while pending:
            v = pending.pop()
            for w, delta in adjacency[v]:
                proposed = shifts[v] + delta
                if w in shifts:
                    if shifts[w] != proposed:
                        raise ValueError('inconsistent quantum shifts around a cycle')
                else:
                    shifts[w] = proposed
                    pending.append(w)
    return shifts
