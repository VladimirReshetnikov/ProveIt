"""Replay formal positive root-ray witnesses without the producer or an LP.

These checks do not interpret incompatible coordinates as embedded surfaces.
Q equations come from the independent certificate model. Matching, canonicality,
and formal Euler are checked directly against original source incidences.
"""
from fractions import Fraction
from math import gcd

from fastunknot.normal_surface_geometry import _prepare, _EDGES, _quad
from fastunknot.normal_euler_verify import _reference_model
from .common import digest


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


def formal_observation(prepared, rows, check=lambda: None):
    n = len(prepared['tetrahedra'])
    assert type(rows) is list and len(rows) == n
    assert all(type(row) is list and len(row) == 7 for row in rows)
    flat = [x for row in rows for x in row]
    assert all(type(x) is int and x >= 0 for x in flat)
    for equation in prepared['matching']:
        check()
        assert sum(a*flat[j] for j, a in equation.items()) == 0
    minima, edges = {}, {}
    for t, row in enumerate(rows):
        check()
        for v in range(4):
            vertex = prepared['vertex_roots'][4*t+v]
            minima[vertex] = min(minima.get(vertex, row[v]), row[v])
        for e, (a, b) in enumerate(_EDGES):
            edge = prepared['edge_roots'][6*t+e]
            value = row[a]+row[b]+sum(row[4:])-row[4+_quad(a, b)]
            if edge in edges:
                assert edges[edge] == value
            edges[edge] = value
    assert not any(minima.values())
    faces = prepared['boundary_faces']+[(t, f) for t, f, _, _, _ in prepared['pairs']]
    arcs = sum(sum(rows[t][v] for v in range(4) if v != f)+sum(rows[t][4:]) for t, f in faces)
    chi = sum(edges.values())-arcs+sum(flat)
    return dict(canonical_euler=chi,
                conflicts=[t for t, row in enumerate(rows) if sum(bool(x) for x in row[4:]) > 1],
                original_matching=True, nonnegative_integral=True, canonical=True)


def lower_bound_record(source, fixture, check=lambda: None):
    # Labelled equality is mandatory: these finite h witnesses cannot migrate
    # to another successor merely because its knot type or size is the same.
    assert source == fixture['source'] and digest(source) == fixture['source_sha256']
    prepared = _prepare(source, check)
    assert prepared['vertices'] == 1 and prepared['boundary_faces']
    support = tuple((t, q) for t in range(len(source['tetrahedra'])) for q in range(3))
    matrix, _, groups, _, weights = _reference_model(prepared, support, check)
    assert len(groups) == 1 and tuple(weights) == (1,)
    observed, edges = [], set()
    for witness in fixture['witnesses']:
        check()
        q, rows = witness['q'], witness['coordinates']
        assert type(q) is list and len(q) == len(support)
        assert all(type(x) is int and x >= 0 for x in q) and gcd(*q) == 1
        assert q == [x for row in rows for x in row[4:]]
        assert all(sum(a*b for a, b in zip(row, q)) == 0 for row in matrix)
        point = formal_observation(prepared, rows, check)
        assert point['canonical_euler'] == witness['canonical_euler'] > 0
        assert point['conflicts'] == witness['conflicts'] and point['conflicts']
        indices = [j for j, x in enumerate(q) if x]
        restricted_rank = rank([[row[j] for j in indices] for row in matrix], check)
        assert restricted_rank == len(indices)-1
        assert restricted_rank == witness['support_rank']
        assert len(indices) == witness['support_size']
        edges.add(tuple(point['conflicts']))
        observed.append(dict(point, q_support=len(indices), q_support_rank=restricted_rank,
                             q_support_nullity=1, primitive=True))
    assert sorted(edges) == [tuple(edge) for edge in fixture['hyperedges']]
    packing = fixture['disjoint_conflict_lower_bound']
    assert all(tuple(edge) in edges for edge in packing)
    assert sum(map(len, packing)) == len(set().union(*map(set, packing)))
    assert len(packing) == fixture['expected_exact_h']
    return dict(id=fixture['id'], source_sha256=digest(source),
                lower_bound=len(packing), disjoint_conflicts=packing,
                witness_observations=observed)
