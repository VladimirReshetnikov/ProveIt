"""Original STANDARD equations and incidence Euler; no Q elimination or LP.

This independent research check retains all triangle columns in its rank test.
"""
from fractions import Fraction
from math import gcd
from fastunknot.normal_surface_geometry import _prepare, _EDGES, _quad

def rank(matrix, check=lambda: None):
    rows = [[Fraction(x) for x in row] for row in matrix]
    if not rows:
        return 0
    pivot = 0
    for column in range(len(rows[0])):
        check()
        chosen = next((i for i in range(pivot, len(rows)) if rows[i][column]), None)
        if chosen is None:
            continue
        rows[pivot], rows[chosen] = rows[chosen], rows[pivot]
        divisor = rows[pivot][column]
        rows[pivot] = [x/divisor for x in rows[pivot]]
        for i in range(pivot+1, len(rows)):
            if rows[i][column]:
                factor = rows[i][column]
                rows[i] = [a-factor*b for a, b in zip(rows[i], rows[pivot])]
        pivot += 1
    return pivot


def boundary_edges(prepared):
    return {prepared['edge_roots'][6*t+i]
            for t, f in prepared['boundary_faces']
            for i, (v, w) in enumerate(_EDGES) if v != f and w != f}


def observation(source, rows, *, check=lambda: None):
    """Check matching, canonical formal Euler, and Q extremality directly."""
    p = _prepare(source, check)
    n = len(p['tetrahedra'])
    assert p['vertices'] == 1 and len(p['boundary_faces']) == 2
    assert type(rows) is list and len(rows) == n
    assert all(type(row) is list and len(row) == 7 for row in rows)
    flat = [x for row in rows for x in row]
    assert all(type(x) is int and x >= 0 for x in flat)
    assert all(sum(a*flat[j] for j, a in eq.items()) == 0 for eq in p['matching'])
    assert min(x for row in rows for x in row[:4]) == 0
    edge_weights = {}
    for t, row in enumerate(rows):
        for e, (a, b) in enumerate(_EDGES):
            edge = p['edge_roots'][6*t+e]
            value = row[a]+row[b]+sum(row[4:])-row[4+_quad(a, b)]
            assert edge_weights.setdefault(edge, value) == value
    faces = p['boundary_faces']+[(t, f) for t, f, _, _, _ in p['pairs']]
    arcs = sum(sum(rows[t][v] for v in range(4) if v != f)+sum(rows[t][4:])
               for t, f in faces)
    chi = sum(edge_weights.values())-arcs+sum(flat)
    q = [x for row in rows for x in row[4:]]
    assert gcd(*q) == 1
    support = [(t, q) for t, row in enumerate(rows) for q in range(3) if row[4+q]]
    triangles = [7*t+v for t in range(n) for v in range(4)]
    columns = triangles+[7*t+4+q for t, q in support]
    triangle_rank = rank([[eq.get(j, 0) for j in triangles] for eq in p['matching']], check)
    assert len(triangles)-triangle_rank == 1
    standard_rank = rank([[eq.get(j, 0) for j in columns] for eq in p['matching']], check)
    q_nullity = len(columns)-standard_rank-1
    assert q_nullity == 1
    be = boundary_edges(p)
    result = dict(canonical_euler=chi,
        conflicts=[t for t, row in enumerate(rows) if sum(bool(x) for x in row[4:]) > 1],
        original_matching=True, nonnegative_integral=True, canonical=True,
        support_size=len(support), support_rank=len(support)-1, support_nullity=1,
        vertices=1, boundary_faces=[list(pair) for pair in p['boundary_faces']],
        boundary_edges=sorted(be), boundary_edge_tetrahedra=[t for t in range(n)
            if be.intersection(p['edge_roots'][6*t:6*t+6])])
    rank_proof = dict(standard_columns=len(columns), standard_rank=standard_rank,
                     triangle_columns=len(triangles), triangle_rank=triangle_rank,
                     triangle_kernel_dimension=1, q_support_nullity=q_nullity)
    return result, rank_proof

