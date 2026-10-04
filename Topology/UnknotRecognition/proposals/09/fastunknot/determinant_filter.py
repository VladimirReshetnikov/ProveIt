"""One-sided Fox-determinant obstruction, using exact finite-field arithmetic."""
from time import monotonic
from .diagram import DisjointSet
from .scan import ScanLimit

MODULUS = 1_000_000_007


def determinant_residue(diagram, *, deadline=None):
    """An unnormalised Delta(-1) residue; +/-1 are inconclusive.

    Fixed known prime. Sparse row dictionaries avoid dense polynomial entries.
    The positive crossing and negative crossing both give 2*over-under-under.
    """
    p = MODULUS
    n = diagram.crossings
    if n <= 1:
        return {"modulus": p, "residue": 1, "obstructs": False}
    arcs = DisjointSet(2*n)
    for _, b, _, d in diagram.pd:
        arcs.union(b, d)
    roots = sorted({arcs.find(e) for e in range(2*n)})
    if len(roots) != n:
        raise ArithmeticError("unexpected number of Wirtinger arcs")
    col = {r: i for i, r in enumerate(roots)}
    rows = []
    for a, b, c, _ in diagram.pd[:-1]:
        row = {}
        for edge, value in ((b, 2), (a, -1), (c, -1)):
            j = col[arcs.find(edge)]
            if j < n-1:
                row[j] = (row.get(j, 0) + value) % p
        rows.append({j: v for j, v in row.items() if v})
    det = 1
    for k in range(n-1):
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted in determinant filter")
        candidates = [i for i in range(k, n-1) if rows[i].get(k)]
        if not candidates:
            det = 0
            break
        pivot_row = min(candidates, key=lambda i: len(rows[i]))
        if k != pivot_row:
            rows[k], rows[pivot_row] = rows[pivot_row], rows[k]
            det = -det
        pivot = rows[k][k]
        det = det * pivot % p
        inv = pow(pivot, -1, p)
        tail = [(j, v) for j, v in rows[k].items() if j > k]
        for i in range(k+1, n-1):
            value = rows[i].pop(k, 0)
            if not value:
                continue
            factor = value * inv % p
            for j, v in tail:
                nv = (rows[i].get(j, 0) - factor*v) % p
                if nv:
                    rows[i][j] = nv
                else:
                    rows[i].pop(j, None)
    return {"modulus": p, "residue": det, "obstructs": det not in (1, p-1)}
