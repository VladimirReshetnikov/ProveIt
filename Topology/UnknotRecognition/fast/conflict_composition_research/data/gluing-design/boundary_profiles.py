"""Small exact boundary/H1 probe; no search, LP, Regina, or source mutation.

Run from Topology/UnknotRecognition/fast with python -B -S SCRIPT.
Original endpoint witnesses are retained discoveries already audited by the
boundary-transversal publication. This probe checks matching again and derives
boundary traces and a primitive integral cocycle from original source faces.
"""
from fractions import Fraction
from hashlib import sha256
from math import gcd, lcm
import json
from pathlib import Path
from fastunknot.normal_surface_geometry import _prepare, _EDGES, _quad
from boundary_transversal_research.common import load, digest, PACKAGE


def nullvector(matrix, n):
    rows = [[Fraction(x) for x in row] for row in matrix]
    pivot, pivots = 0, []
    for j in range(n):
        k = next((i for i in range(pivot, len(rows)) if rows[i][j]), None)
        if k is None:
            continue
        rows[pivot], rows[k] = rows[k], rows[pivot]
        a = rows[pivot][j]
        rows[pivot] = [x/a for x in rows[pivot]]
        for i in range(len(rows)):
            if i != pivot and rows[i][j]:
                a = rows[i][j]
                rows[i] = [x-a*y for x, y in zip(rows[i], rows[pivot])]
        pivots.append(j)
        pivot += 1
    free = [j for j in range(n) if j not in pivots]
    assert len(free) == 1
    vector = [Fraction(int(j == free[0])) for j in range(n)]
    for i, j in enumerate(pivots):
        vector[j] = -rows[i][free[0]]
    denominator = lcm(*(x.denominator for x in vector))
    vector = [int(x*denominator) for x in vector]
    divisor = gcd(*vector)
    return [x//divisor for x in vector]


def main():
    records = []
    for fixture in load('lower_witnesses.json')['records']:
        assert digest(fixture['source']) == fixture['source_sha256']
        prepared = _prepare(fixture['source'], lambda: None)
        assert prepared['vertices'] == 1
        edges = sorted(set(prepared['edge_roots']))
        index = {e: i for i, e in enumerate(edges)}
        matrix = []
        faces = prepared['boundary_faces']+[(t, f) for t, f, _, _, _ in prepared['pairs']]
        for t, face in faces:
            a, b, c = [v for v in range(4) if v != face]
            row = [0]*len(edges)
            for x, y in ((a, b), (b, c), (c, a)):
                e = _EDGES.index(tuple(sorted((x, y))))
                root = prepared['edge_roots'][6*t+e]
                sign = (-1)**(prepared['edge_orientations'][6*t+e]+int(x > y))
                row[index[root]] += sign
            matrix.append(row)
        cocycle = nullvector(matrix, len(edges))
        assert gcd(*cocycle) == 1
        assert all(sum(a*b for a, b in zip(row, cocycle)) == 0 for row in matrix)
        witnesses = []
        for i, witness in enumerate(fixture['witnesses']):
            rows = witness['coordinates']
            flat = [x for row in rows for x in row]
            assert all(sum(a*flat[j] for j, a in eq.items()) == 0 for eq in prepared['matching'])
            boundary = []
            for t, face in prepared['boundary_faces']:
                arcs = {v: rows[t][v]+rows[t][4+_quad(v, face)]
                        for v in range(4) if v != face}
                local = []
                for e, (x, y) in enumerate(_EDGES):
                    if x == face or y == face:
                        continue
                    root = prepared['edge_roots'][6*t+e]
                    local.append(dict(local=e, vertices=[x, y], root=root,
                        cocycle=cocycle[index[root]],
                        weight=rows[t][x]+rows[t][y]+sum(rows[t][4:])-rows[t][4+_quad(x, y)]))
                boundary.append(dict(face=[t, face], arcs=arcs, edges=local))
            minimum = min(x for record in boundary for x in record['arcs'].values())
            residual = {e['root']: e['weight']-2*minimum for e in boundary[0]['edges']}
            copies = gcd(*residual.values())
            witnesses.append(dict(index=i, canonical_euler=witness['canonical_euler'],
                conflicts=witness['conflicts'], boundary_vertex_link_circles=minimum,
                boundary=boundary, residual_edge_weights=residual,
                residual_gcd=copies))
        records.append(dict(id=fixture['id'], source_sha256=fixture['source_sha256'],
            edge_cocycle=dict(zip(edges, cocycle)), witnesses=witnesses))
        print(fixture['id'], [(r['index'], r['canonical_euler'],
                              r['boundary_vertex_link_circles']) for r in witnesses])
    files = [Path(__file__), PACKAGE/'data/lower_witnesses.json',
             PACKAGE.parent/'fastunknot/normal_surface_geometry.py']
    result = dict(scope='Exact boundary traces and original-face integral H1 cocycles on retained endpoint witnesses; no new root-ray enumeration or composition.',
                  input_sha256={str(p): sha256(p.read_bytes()).hexdigest() for p in files},
                  records=records)
    Path(__file__).with_name('boundary-profiles.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
