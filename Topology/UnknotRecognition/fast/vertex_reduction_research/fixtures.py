"""Fresh deterministic solid-torus refinements and classical knot diagrams."""
from pathlib import Path
from random import Random

from fastunknot.diagram import Diagram
from normal_orbit_research.fixtures import layered_torus, boundary_cap, interior_vertex_torus
from normal_crushing_research.fixtures import regina_triangulation, face_pairing


ROOT = Path(__file__).resolve().parents[2]
SEED = 12020261012


def relabel(source, random):
    """Independently rename tetrahedra and local vertices, retaining all gluings."""
    count = len(source['tetrahedra'])
    order = list(range(count))
    random.shuffle(order)
    maps = [random.sample(range(4), 4) for _ in range(count)]
    faces = [[None]*4 for _ in range(count)]
    for t, row in enumerate(source['tetrahedra']):
        mapping = maps[t]
        for f, record in enumerate(row):
            if record is None:
                continue
            u, permutation = record['tetrahedron'], record['permutation']
            changed = [0]*4
            for v in range(4):
                changed[mapping[v]] = maps[u][permutation[v]]
            faces[order[t]][mapping[f]] = dict(tetrahedron=order[u], permutation=changed)
    return dict(tetrahedra=faces)


def supplied_sources():
    """Known solid tori; boundary caps and Pachner moves preserve that topology.

    The fixed random walk is generated afresh. Iteration 157 is a retained
    control where normalisation creates a vertex-link sphere and a double
    triangle coordinate; canonical peeling must remove that sphere.
    """
    for count in (1, 2, 3):
        source, rows = layered_torus(count)
        yield dict(id=f'one_vertex_layered_{count}', source=source,
                   construction='layered solid torus', enumerate_standard=True)
        capped, _ = boundary_cap(source, rows)
        yield dict(id=f'boundary_cap_{count}', source=capped,
                   construction='one boundary cap on a layered solid torus', enumerate_standard=True)
    interior, _ = interior_vertex_torus()
    yield dict(id='interior_vertex', source=interior,
               construction='one interior stellar subdivision of a solid torus', enumerate_standard=True)
    source, rows = layered_torus(2)
    base, _ = boundary_cap(source, rows)
    random = Random(SEED)
    triangulation = None
    for iteration in range(300):
        if iteration % 50 == 0:
            triangulation = regina_triangulation(base)
            assert triangulation.pachner(triangulation.tetrahedron(0))
        for _ in range(3):
            if triangulation.size() < 7 or (triangulation.size() < 18 and random.random() < .5):
                candidates = [face for face in triangulation.triangles() if triangulation.hasPachner(face)]
            else:
                candidates = [edge for edge in triangulation.edges() if triangulation.hasPachner(edge)]
            if candidates:
                assert triangulation.pachner(random.choice(candidates))
        labelled = relabel(face_pairing(triangulation), random)
        if iteration % 10 == 0 or iteration == 157:
            yield dict(id=f'fresh_pachner_{iteration}', source=labelled,
                construction='boundary-capped layered torus, interior subdivision, deterministic 2-3/3-2 moves and relabelling',
                random_seed=SEED, iteration=iteration,
                enumerate_standard=len(labelled['tetrahedra']) <= 8)


def diagram_cases():
    return [('circle', Diagram.from_pd([])),
            ('trefoil', Diagram.from_braid(2, [1, 1, 1])),
            ('figure_eight', Diagram.from_braid(3, [1, -2, 1, -2]))]
