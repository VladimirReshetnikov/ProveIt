"""Fixed source families and genuine small diagram inputs."""
import json
from random import Random

from fastunknot.diagram import Diagram
from normal_orbit_research.fixtures import layered_torus
from .common import COLLARS, digest

SEED = 2026101209


def relabel(source, seed):
    random = Random(seed)
    count = len(source['tetrahedra'])
    order = list(range(count))
    random.shuffle(order)
    maps = [random.sample(range(4), 4) for _ in range(count)]
    rows = [[None]*4 for _ in range(count)]
    for t, row in enumerate(source['tetrahedra']):
        for f, record in enumerate(row):
            if record is None:
                continue
            u, permutation = record['tetrahedron'], record['permutation']
            changed = [0]*4
            for v in range(4):
                changed[maps[t][v]] = maps[u][permutation[v]]
            rows[order[t]][maps[t][f]] = dict(tetrahedron=order[u], permutation=changed)
    return dict(tetrahedra=rows), dict(seed=seed, tetrahedra=order, local_vertices=maps)


def supplied_sources():
    for count in (1, 2, 4, 8, 16):
        source, _ = layered_torus(count)
        yield dict(id=f'layered_torus_{count}', source=source, solid_torus=True,
                   expected_predecessors=[layered_torus(k)[0] for k in range(count-1, 0, -1)],
                   expected_moves=count-1)
    for count in (4, 8):
        source, labels = relabel(layered_torus(count)[0], SEED+count)
        yield dict(id=f'relabelled_torus_{count}', source=source, solid_torus=True,
                   relabelling=labels, expected_moves=count-1)
    for record in json.loads(COLLARS.read_text())['records']:
        all_sources = [record['initial_source']]+[step['source'] for step in record['steps']]
        assert digest(all_sources[0]) == record['initial_source_sha256']
        assert digest(all_sources[-1]) == record['final_source_sha256']
        yield dict(id=record['id']+'_collar', source=all_sources[-1], solid_torus=False,
                   expected_predecessors=list(reversed(all_sources[:-1])), expected_moves=3,
                   provenance='Exact retained supplied-source layers; their initial sources are native diagram endpoints, but these forward layerings are outside the diagram chain schema.')


def diagram_cases(*, extended=False):
    cases = [('circle', 1, []),
             ('trefoil', 2, [1, 1, 1]), ('figure_eight', 3, [1, -2, 1, -2])]
    if extended:
        cases += [('curl', 2, [1]), ('two_crossing_unknot', 3, [1, 2]), ('cinquefoil', 2, [1]*5),
                  ('stabilized_trefoil', 3, [1, 1, 1, 2])]
    return [(name, Diagram.from_braid(strands, word)) for name, strands, word in cases]
