"""Solver-free original-STANDARD replay; no Regina, LP, or Q elimination."""
import argparse
from fractions import Fraction
import json
from math import gcd
from pathlib import Path

from fastunknot.normal_surface_geometry import _prepare, _EDGES, _quad
from .common import digest, load, source_hashes, verify_generation_provenance


def rank(matrix):
    rows = [[Fraction(x) for x in row] for row in matrix]
    if not rows:
        return 0
    pivot = 0
    for column in range(len(rows[0])):
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


def observation(source, rows):
    """Check matching, canonical formal Euler, and Q extremality directly."""
    p = _prepare(source, lambda: None)
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
    triangle_rank = rank([[eq.get(j, 0) for j in triangles] for eq in p['matching']])
    assert len(triangles)-triangle_rank == 1
    standard_rank = rank([[eq.get(j, 0) for j in columns] for eq in p['matching']])
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


def check_layer(before, step):
    after = step['source']
    n = len(before['tetrahedra'])
    assert type(step['new_tetrahedron']) is int and step['new_tetrahedron'] == n
    assert len(after['tetrahedra']) == n+1
    p, q = _prepare(before, lambda: None), _prepare(after, lambda: None)
    t, e = step['flipped_original_local_edge']
    assert type(t) is int and type(e) is int and 0 <= t < n and 0 <= e < 6
    chosen = p['edge_roots'][6*t+e]
    assert chosen in boundary_edges(p)
    joins = [(f, r) for f, r in enumerate(after['tetrahedra'][n]) if r is not None]
    assert len(joins) == 2
    attached = {(r['tetrahedron'], r['permutation'][f]) for f, r in joins}
    assert len(attached) == 2 and attached == set(p['boundary_faces'])
    for i, row in enumerate(before['tetrahedra']):
        for f, r in enumerate(row):
            if (i, f) in attached:
                assert r is None and after['tetrahedra'][i][f]['tetrahedron'] == n
            else:
                assert after['tetrahedra'][i][f] == r
    shared = sorted(set(range(4))-{f for f, _ in joins})
    orientations = []
    for _, r in joins:
        a, b = [r['permutation'][v] for v in shared]
        edge = _EDGES.index(tuple(sorted((a, b))))
        assert p['edge_roots'][6*r['tetrahedron']+edge] == chosen
        orientations.append(p['edge_orientations'][6*r['tetrahedron']+edge]^int(a > b))
    assert orientations[0] == orientations[1]
    mapping = {}
    for old, new in zip(p['edge_roots'], q['edge_roots'][:6*n]):
        assert mapping.setdefault(old, new) == new
    assert len(set(mapping.values())) == len(mapping)
    assert {mapping[e] for e in boundary_edges(p)}-boundary_edges(q) == {mapping[chosen]}
    assert len(boundary_edges(q)-set(mapping.values())) == 1
    assert q['vertices'] == 1 and q['edges'] == p['edges']+1


def audit():
    pins = source_hashes()
    provenance = verify_generation_provenance()
    fixtures = {f['id']: f for f in load('lower_witnesses.json')['records']}
    endpoints = []
    for fixture in fixtures.values():
        source = fixture['source']
        witnesses = []
        for index, witness in enumerate(fixture['witnesses']):
            obs, proof = observation(source, witness['coordinates'])
            assert witness['q'] == [x for row in witness['coordinates'] for x in row[4:]]
            for field in ('canonical_euler', 'conflicts', 'support_size', 'support_rank'):
                assert obs[field] == witness[field]
            assert obs['canonical_euler'] > 0 and obs['conflicts']
            face_tets = sorted({t for t, _ in obs['boundary_faces']})
            witnesses.append(dict(index=index, observation=obs, rank_proof=proof,
                avoids_boundary_faces=set(obs['conflicts']).isdisjoint(face_tets),
                avoids_boundary_edge_stars=set(obs['conflicts']).isdisjoint(obs['boundary_edge_tetrahedra'])))
        endpoints.append(dict(id=fixture['id'], source_sha256=digest(source),
                              tetrahedra=len(source['tetrahedra']), witnesses=witnesses))
    layered = []
    for record in load('provenance/layer-refuter.json')['records']:
        fixture = fixtures[record['id']]
        assert record['initial_source'] == fixture['source']
        assert digest(fixture['source']) == record['initial_source_sha256'] == fixture['source_sha256']
        rows = fixture['witnesses'][record['initial_witness_index']]['coordinates']
        assert rows == record['initial_coordinates']
        obs, _ = observation(fixture['source'], rows)
        assert obs == record['initial']
        source, steps = fixture['source'], []
        for step in record['steps']:
            check_layer(source, step)
            assert step['coordinates'][:-1] == rows
            assert sum(bool(x) for x in step['coordinates'][-1][4:]) <= 1
            next_obs, proof = observation(step['source'], step['coordinates'])
            assert next_obs == step['observation']
            assert next_obs['canonical_euler'] == obs['canonical_euler'] > 0
            assert next_obs['conflicts'] == obs['conflicts']
            source, rows, obs = step['source'], step['coordinates'], next_obs
            steps.append(dict(source_sha256=digest(source), tetrahedra=len(rows),
                observation=obs, rank_proof=proof,
                avoids_boundary_edge_stars=set(obs['conflicts']).isdisjoint(obs['boundary_edge_tetrahedra'])))
        assert digest(source) == record['final_source_sha256']
        assert steps[-1]['avoids_boundary_edge_stars']
        layered.append(dict(id=record['id'], initial_source_sha256=fixture['source_sha256'], steps=steps))
    assert [sum(w['avoids_boundary_faces'] for w in r['witnesses']) for r in endpoints] == [8, 9]
    assert layered[0]['steps'][0]['avoids_boundary_edge_stars']
    assert source_hashes() == pins, 'source changed during replay'
    return dict(schema='boundary-transversal-audit-v1', passed=True, source_sha256=pins,
        generation_provenance_sha256=digest(provenance), regina_used=False, lp_used=False,
        q_cycle_elimination_used=False, endpoints=endpoints, layered=layered,
        scope='Exact supplied-source root-Q-extreme counterexamples; new layers are outside maintained crushing-chain schema; no negative-cone, h-family, or quasi-polynomial claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check-evidence', type=Path)
    args = parser.parse_args()
    result = audit()
    if args.check_evidence:
        assert json.loads(args.check_evidence.read_text()) == result
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    for record in result['layered']:
        for step in record['steps']:
            obs = step['observation']
            print(record['id'], step['tetrahedra'], 'F', obs['canonical_euler'],
                  'conflicts', obs['conflicts'], 'boundary-edge tets', obs['boundary_edge_tetrahedra'],
                  'refutes', step['avoids_boundary_edge_stars'])
    print('PASSED: 19 endpoint rays, 6 exact boundary layers, original STANDARD ranks.')


if __name__ == '__main__':
    main()
