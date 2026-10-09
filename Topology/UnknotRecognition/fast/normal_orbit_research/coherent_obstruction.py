"""Reproduce and independently replay a whole coherent-family obstruction.

The fixed six moves and final disc vector need no topology engine. Optional
Regina auditing checks additional random moves and both final surfaces.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import random

from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner23_verify import verify_pachner_23
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details
from fastunknot.normal_surface_geometry import _edge
from fastunknot.coherent_family_verify import inspect_one_vertex_family
from fastunknot.integer_determinant import bareiss
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate)
from normal_orbit_research.fixtures import (
    layered_torus, regina_triangulation, regina_surface)

MOVES = ((1, 2), (0, 1), (2, 2), (3, 1), (3, 2), (6, 0))
DISC = [[2,2,0,0,0,0,2], [0,0,2,2,0,2,0], [0,2,3,2,0,0,0],
        [2,2,0,0,0,0,3], [0,0,2,2,0,3,0], [0,1,2,3,1,0,0],
        [0,1,2,0,2,0,0], [0,1,2,3,0,0,0]]


def family_proof(raw):
    """Find a full-rank minor by rational elimination; replay uses Bareiss."""
    seed, p = _rank_one_cocycle_seed_details(raw)
    labels = sorted(set(p['edge_roots']))
    index = {e:i for i,e in enumerate(labels)}
    matrix = []
    for t,f in p['boundary_faces'] + [(t,f) for t,f,u,g,perm in p['pairs']]:
        x,y,z = (v for v in range(4) if v != f)
        row = [0]*len(labels)
        for v,w,sign in ((x,y,1),(y,z,1),(x,z,-1)):
            local = _edge(t,v,w)
            row[index[p['edge_roots'][local]]] += sign*(-1 if p['edge_orientations'][local] else 1)
        matrix.append(row)
    a = [[Fraction(x) for x in row] for row in matrix]
    order = list(range(len(a)))
    rank, columns = 0, []
    for col in range(len(labels)):
        pivot = next((i for i in range(rank,len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank],a[pivot] = a[pivot],a[rank]
        order[rank],order[pivot] = order[pivot],order[rank]
        value = a[rank][col]
        a[rank] = [x/value for x in a[rank]]
        for i in range(rank+1,len(a)):
            factor = a[i][col]
            a[i] = [x-factor*y for x,y in zip(a[i],a[rank])]
        columns.append(col)
        rank += 1
    rows = order[:rank]
    determinant = bareiss([[matrix[i][j] for j in columns] for i in rows], lambda n:None)
    return dict(schema='one-vertex-cocycle-family-v1', heights=seed['heights'],
                coordinates=seed['coordinates'], minor_rows=rows,
                minor_columns=columns, determinant=determinant)


def reproduce():
    initial, _ = layered_torus(2)
    raw, moves = initial, []
    for t,f in MOVES:
        result = pachner_23(raw,t,f)
        assert verify_pachner_23(raw,result['triangulation'],result['certificate'])
        raw = result['triangulation']
        moves.append(dict(certificate=result['certificate'],triangulation=raw))
    proof = family_proof(raw)
    summary = inspect_one_vertex_family(raw,proof)
    assert summary is not None
    surface = normal_surface_topology(raw,proof['coordinates'],record_certificate=True)
    assert verify_normal_surface_certificate(raw,proof['coordinates'],surface['certificate'])
    answer = normal_compressing_disk_count(raw,DISC,record_certificate=True)
    assert answer['compressing_disk_components'] == 1
    assert verify_normal_disk_count_certificate(raw,DISC,answer['certificate'])
    return dict(initial=initial,moves=moves,family_certificate=proof,family_summary=summary,
                coherent_surface=surface,disc_coordinates=DISC,
                disc_certificate=answer['certificate'],disc_pieces=sum(map(sum,DISC)))


def replay(record):
    """Validate saved arithmetic and topology without any discovery call."""
    initial, _ = layered_torus(2)
    assert record['initial'] == initial
    raw = record['initial']
    for move in record['moves']:
        assert verify_pachner_23(raw,move['triangulation'],move['certificate'])
        raw = move['triangulation']
    proof = record['family_certificate']
    summary = inspect_one_vertex_family(raw,proof)
    assert summary is not None and summary == record['family_summary']
    assert verify_normal_surface_certificate(raw,proof['coordinates'],record['coherent_surface']['certificate'])
    assert verify_normal_disk_count_certificate(raw,record['disc_coordinates'],record['disc_certificate'])
    # Top-level discovery summaries are not trusted by the proof checkers.
    topology = record['coherent_surface']['certificate']['topology']
    assert [topology[k] for k in ('components','orientable_components','boundary_components','genus')] == [1,1,1,2]
    assert record['disc_certificate']['compressing_disk_components'] == 1
    assert summary['primitive_euler_characteristic'] == -3
    assert summary['primitive_normal_pieces'] == 41
    return raw


def audit(record):
    import regina
    raw = replay(record)
    tri = regina_triangulation(raw)
    assert tri.isSolidTorus() and tri.countVertices() == 1
    surface = regina_surface(tri,record['family_certificate']['coordinates'])
    assert surface.isConnected() and surface.isOrientable()
    assert int(str(surface.eulerChar())) == -3 and surface.countBoundaries() == 1
    disc = regina_surface(tri,record['disc_coordinates'])
    assert disc.isCompressingDisc(True)
    rng = random.Random(261009512)
    fixtures = [layered_torus(n)[0] for n in (2,3,8)]
    fixtures.append(diagram_exterior(Diagram.from_braid(2,[1])))
    records = []
    for fixture in fixtures:
        for trial in range(3):
            before = fixture
            for step in range(20):
                choices = [(t,f) for t,row in enumerate(before['tetrahedra'])
                           for f,r in enumerate(row) if r is not None and r['tetrahedron'] != t]
                t,f = rng.choice(choices)
                independent = regina_triangulation(before)
                assert independent.pachner(independent.tetrahedron(t).triangle(f))
                result = pachner_23(before,t,f)
                after = result['triangulation']
                assert verify_pachner_23(before,after,result['certificate'])
                signature = regina_triangulation(after).isoSig()
                assert signature == independent.isoSig()
                records.append([len(fixture['tetrahedra']),trial,step,t,f,signature])
                before = after
    return dict(regina_version=regina.versionString(), random_moves=len(records),
                records=records, final_iso_signature=tri.isoSig(),
                solid_torus=True, coherent_genus=2, coherent_boundary_components=1,
                independent_compressing_disc=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('reproduce','replay','audit'))
    parser.add_argument('--record',type=Path,required=True)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    if args.mode == 'reproduce':
        result = reproduce()
        args.record.write_text(json.dumps(result,indent=2)+'\n')
    else:
        record = json.loads(args.record.read_text())
        if args.mode == 'replay':
            replay(record)
            result = dict(replayed=True)
        else:
            result = audit(record)
        result['record_sha256'] = sha256(args.record.read_bytes()).hexdigest()
        root = Path(__file__).resolve().parents[1]
        paths = list((root/'fastunknot').glob('*.py')) + [Path(__file__),
                 root/'normal_orbit_research/fixtures.py',
                 root/'tests/test_coherent_obstruction.py',
                 root/'tests/test_normal_surface_orbits.py']
        result['source_sha256'] = {str(p.relative_to(root)):sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}
        if args.output:
            args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in
                     ('records','source_sha256','moves','coherent_surface','disc_certificate','initial','family_certificate')}))


if __name__ == '__main__':
    main()
