"""A torus-boundary geometric counterexample to singleton peeled-score additivity.

Reproducible fixture.  A cone on a sphere with two subdivided faces is a ball.
Attach an unchanged boundary face to an embedded boundary triangle in a
barycentrically subdivided solid torus.  All heights come from one vertex
potential (the zero cohomology class).

The default construction uses the accompanying fixed 24-tetrahedron base
and only the standard library plus repository modules.  Regina is optional:
--regenerate-torus-with-regina independently regenerates and compares that
base.  The retained base was produced with Regina 7.4.1 under Python 3.12.14
on 2026-10-09; exact replay does not rely on those versions being installed.
"""
import argparse
from copy import deepcopy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
for candidate in (HERE.parents[1]/'code'/'fast', HERE.parent/'work'/'fast',
                  HERE.parent/'fast', HERE.parent):
    if (candidate/'fastunknot').is_dir():
        sys.path.insert(0, str(candidate))
        break
from fastunknot.cocycle_transport import transport_cocycle
from fastunknot.normal_cocycle import local_coordinates, _height_summary
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.pachner32 import pachner_32
from fastunknot.pachner32_verify import verify_pachner_32
from normal_orbit_research.fixtures import layered_torus


def join(rows, t, f, u, g, mapping):
    perm = [g] * 4
    for a, b in mapping:
        perm[a] = b
    assert sorted(perm) == [0, 1, 2, 3]
    assert rows[t][f] is None and rows[u][g] is None
    rows[t][f] = dict(tetrahedron=u, permutation=perm)
    rows[u][g] = dict(tetrahedron=t, permutation=[perm.index(a) for a in range(4)])


def subdivided_torus_regina():
    """Optional provenance regeneration, not required by ordinary replay."""
    import regina
    raw, _ = layered_torus(1)
    original = raw['tetrahedra']
    tri = regina.Triangulation3()
    tri.newTetrahedra(len(original))
    for t, row in enumerate(original):
        for f, entry in enumerate(row):
            if entry is None:
                continue
            u, p = entry['tetrahedron'], entry['permutation']
            if (t, f) < (u, p[f]):
                tri.tetrahedron(t).join(f, tri.tetrahedron(u), regina.Perm4(*p))
    tri.subdivide()
    rows = []
    for t in range(tri.size()):
        tet, row = tri.tetrahedron(t), []
        for f in range(4):
            neighbor = tet.adjacentTetrahedron(f)
            row.append(None if neighbor is None else dict(
                tetrahedron=neighbor.index(),
                permutation=[tet.adjacentGluing(f)[i] for i in range(4)]))
        rows.append(row)
    return dict(tetrahedra=rows)


def subdivided_torus():
    return json.loads((HERE/'peeling_barycentric_torus.json').read_text())


def make_example():
    torus = subdivided_torus()
    p = _prepare(torus, lambda: None)
    attach_t, attach_f = next((t, f) for t, f in p['boundary_faces']
        if len({p['vertex_roots'][4*t+i] for i in range(4) if i != f}) == 3)
    # Original link vertices 0,1,2,3; face-centre vertices B1=4 and B2=5;
    # cone vertex v=6.
    link_faces = [(4,0,1), (4,1,2), (4,2,0),
                  (5,0,1), (5,1,3), (5,3,0), (0,2,3), (1,2,3)]
    labels = [(6,) + face for face in link_faces]
    rows = deepcopy(torus['tetrahedra'])
    offset = len(rows)
    rows.extend([[None] * 4 for _ in labels])
    facets = {}
    for i, verts in enumerate(labels):
        for f in range(4):
            key = tuple(sorted(verts[v] for v in range(4) if v != f))
            facets.setdefault(key, []).append((offset+i, f))
    for key, occurrences in facets.items():
        if len(occurrences) == 2:
            (t,f), (u,g) = occurrences
            join(rows,t,f,u,g,[(i,labels[u-offset].index(labels[t-offset][i]))
                              for i in range(4) if i != f])
        else:
            assert len(occurrences) == 1 and 6 not in key
    # Attach along untouched face (0,2,3), opposite v in tetrahedron 6.
    join(rows,offset+6,0,attach_t,attach_f,
         list(zip((1,2,3),(i for i in range(4) if i != attach_f))))
    potential = {0:-1,1:-1,2:-1,3:-1,4:1,5:1,6:0}
    heights = [[-1] * 4 for _ in range(offset)]
    heights.extend([[potential[v] for v in row] for row in labels])
    return dict(tetrahedra=rows), heights, offset


def summary(raw, heights):
    p = _prepare(raw, lambda: None)
    coords = [local_coordinates(row) for row in heights]
    mins = {}
    for t, row in enumerate(coords):
        for i in range(4):
            v = p['vertex_roots'][4*t+i]
            mins[v] = min(mins.get(v, row[i]), row[i])
    boundary = {p['vertex_roots'][4*t+i] for t,f in p['boundary_faces']
                for i in range(4) if i != f}
    raw_euler = _height_summary(p, heights)['euler_characteristic']
    penalty = sum((1 if v in boundary else 2)*m for v,m in mins.items())
    return dict(tetrahedra=len(coords), raw_euler=raw_euler,
                peel_penalty=penalty, peeled_euler=raw_euler-penalty,
                nonzero_minima={str(v):m for v,m in mins.items() if m})


def move(raw, heights, tet):
    replacement = pachner_32(raw, tet, [0,1])
    after = replacement['triangulation']
    assert verify_pachner_32(raw, after, replacement['certificate'])
    result = transport_cocycle(raw, heights, after, replacement['certificate'])
    return after, result['heights'], result['certificate']


def run(output=None, regenerate=False):
    if regenerate:
        assert subdivided_torus_regina() == subdivided_torus()
    raw, heights, offset = make_example()
    baseline = summary(raw,heights)
    one,h1,c1 = move(raw,heights,offset)
    two,h2,c2 = move(raw,heights,offset+3)
    # Old site offset+3 survives the first removal and shifts down by 3.
    both,h12,c12 = move(one,h1,offset)
    s1,s2,s12 = summary(one,h1),summary(two,h2),summary(both,h12)
    gains = [s['peeled_euler']-baseline['peeled_euler'] for s in (s1,s2,s12)]
    assert gains == [1,1,0], gains
    result = dict(before=dict(triangulation=raw,heights=heights,summary=baseline),
        singleton_one=dict(triangulation=one,transport=c1,summary=s1),
        singleton_two=dict(triangulation=two,transport=c2,summary=s2),
        after_both=dict(triangulation=both,transport=c12,summary=s12),
        peeled_gains=dict(first=1,second=1,combined=0),
        construction=dict(ball_offset=offset,cone_vertex=6,
                          first_site=offset,second_site=offset+3,
                          base_fixture='peeling_barycentric_torus.json',
                          base_provenance=dict(regina='7.4.1',python='3.12.14',
                                               generated='2026-10-09'),
                          default_replay_dependencies='Python standard library and fastunknot repository modules'))
    output = Path(output) if output is not None else Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(before=baseline,first=s1,second=s2,combined=s12,
                          gains=gains,output=str(output)),indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', help='output record (default: sibling JSON)')
    parser.add_argument('--regenerate-torus-with-regina', action='store_true')
    args = parser.parse_args()
    run(args.output, args.regenerate_torus_with_regina)
