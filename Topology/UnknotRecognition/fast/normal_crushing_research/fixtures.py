"""Reproducible supplied-manifold and diagram-bound crushing fixtures."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RETAINED = ROOT/'synthesis/data/filtered-atlas-native.json'


def regina_triangulation(source):
    import regina
    result = regina.Triangulation3()
    tetrahedra = result.newTetrahedra(len(source['tetrahedra']))
    for t, faces in enumerate(source['tetrahedra']):
        for f, record in enumerate(faces):
            if record is not None and tetrahedra[t].adjacentTetrahedron(f) is None:
                tetrahedra[t].join(f, tetrahedra[record['tetrahedron']],
                                   regina.Perm4(*record['permutation']))
    return result


def face_pairing(triangulation):
    return dict(tetrahedra=[[
        None if tetrahedron.adjacentTetrahedron(f) is None else
        dict(tetrahedron=tetrahedron.adjacentTetrahedron(f).index(),
             permutation=[tetrahedron.adjacentGluing(f)[j] for j in range(4)])
        for f in range(4)] for tetrahedron in triangulation.tetrahedra()])


def coordinates(surface, triangulation):
    return [[int(str(surface.triangles(t, j) if j < 4 else surface.quads(t, j-4)))
             for j in range(7)] for t in range(triangulation.size())]


def retained_cases():
    bank = json.loads(RETAINED.read_text())
    seen = set()
    for case in bank['records']:
        for query in case['results']['filtered']['answers']:
            for trace in query['result']['trace']:
                source, flat = case['triangulation'], trace['coordinates']
                key = json.dumps([source, flat], sort_keys=True)
                if key in seen:
                    continue
                seen.add(key)
                yield dict(id=case['id'], source=source,
                    coordinates=[flat[j:j+7] for j in range(0, len(flat), 7)],
                    accepted=trace['evidence']['accepted'],
                    disc_certificate=trace['evidence']['certificate']['disk_certificate'])


def capped_two_tetrahedra():
    return json.loads(RETAINED.read_text())['records'][0]['triangulation']


def expanded_cases():
    import regina
    tri = regina_triangulation(capped_two_tetrahedra())
    assert tri.pachner(tri.tetrahedron(0))
    assert tri.pachner(tri.tetrahedron(0))
    for stage in range(5):
        if stage:
            face = next((face for face in tri.triangles() if tri.hasPachner(face)), None)
            if face is not None:
                assert tri.pachner(face)
        surfaces = []
        if stage == 0:
            surfaces.extend(('vertex', i, s) for i, s in enumerate(regina.NormalSurfaces(
                tri, regina.NormalCoords.Standard, regina.NormalList.Vertex)) if s.eulerChar() > 0)
        surfaces.extend(('edge', edge.index(), edge.linkingSurface()[0]) for edge in tri.edges())
        for method, index, surface in surfaces:
            if not surface.isConnected() or surface.eulerChar() <= 0:
                continue
            kind = ('sphere' if surface.eulerChar() == 2 else 'disc') + (
                '_link' if surface.isVertexLinking() else '_nonlink')
            yield dict(id=f'stage_{stage}_{method}_{index}', source=face_pairing(tri),
                       coordinates=coordinates(surface, tri), kind=kind)


def isolated_cycle_case():
    tri = regina_triangulation(capped_two_tetrahedra())
    assert tri.pachner(tri.tetrahedron(0))
    assert tri.pachner(tri.tetrahedron(tri.size()-1))
    edge = tri.edge(10)
    assert not edge.vertex(0).isBoundary() and not edge.vertex(1).isBoundary()
    sphere, thin = edge.linkingSurface()
    assert thin and sphere.isConnected() and sphere.eulerChar() == 2 and not sphere.isVertexLinking()
    return dict(id='interior_edge_sphere', source=face_pairing(tri),
                coordinates=coordinates(sphere, tri))


def one_tetrahedron_cases():
    import regina
    tri = regina_triangulation(capped_two_tetrahedra())
    tri.simplify()
    assert tri.size() == 1
    for index, surface in enumerate(regina.NormalSurfaces(
            tri, regina.NormalCoords.Standard, regina.NormalList.Vertex)):
        if surface.eulerChar() > 0:
            yield dict(id=f'one_tetrahedron_{index}', source=face_pairing(tri),
                       coordinates=coordinates(surface, tri), vertex_link=surface.isVertexLinking())


def diagram_cases():
    """No Regina dependency: exact arrays discovered once on the native exterior."""
    from fastunknot.diagram import Diagram
    from fastunknot.diagram_exterior import diagram_exterior
    from fastunknot.boundary_shellings import shell_boundary
    diagram = Diagram.from_pd([])
    initial = diagram_exterior(diagram)
    shelling = shell_boundary(initial)
    assert shelling['moves'] == [3,14,8,9,13,4,18,19,0,7,5,6,12,11,15]
    shelling = dict(triangulation=shelling['triangulation'], moves=shelling['moves'])
    direct = [[0,0,0,0,1,0,0], [0,0,1,1,0,0,0], [0,0,0,0,1,0,0],
              [0,0,0,0,1,0,0], [0,0,0,0,1,0,0]]
    first = [[1,0,0,1,0,0,1], [1,1,1,1,0,0,0], [0,1,1,0,0,0,1],
             [1,0,0,1,0,0,1], [0,1,1,0,0,0,1]]
    second = [[0,0,1,1,0,0,1]]
    return diagram, initial, shelling, [('no_torus_after_one', [direct]),
                                      ('one_tet_terminal_after_two', [first, second])]
