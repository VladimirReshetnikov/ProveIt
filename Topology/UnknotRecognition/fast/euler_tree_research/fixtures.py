"""Deterministic complete small mask family and selected vertex-link controls."""
from itertools import product

from fastunknot.diagram import Diagram
from normal_orbit_research.fixtures import layered_torus, boundary_cap, interior_vertex_torus


def _mask(bits):
    return [[t, q] for t, choices in enumerate(bits) for q in range(3)
            if choices & (1 << q)]


def supplied_cases():
    """All 8**2 masks of one source; twelve masks each on two other sources."""
    source, _ = layered_torus(2)
    for left, right in product(range(8), repeat=2):
        yield dict(id=f'layered_two_mask_{left}_{right}', family='complete_two_tetrahedra',
                   source=source, mask_bits=[left, right], allowed_types=_mask([left, right]))
    interior, _ = interior_vertex_torus()
    capped, _ = boundary_cap(*layered_torus(2))
    for name, source in (('interior_vertex', interior), ('multiple_boundary_vertices', capped)):
        count = len(source['tetrahedra'])
        assignments = [(choice,)*count for choice in range(8)]
        assignments.extend(tuple(pair[t % 2] for t in range(count))
                           for pair in ((0, 7), (1, 6), (3, 5), (7, 0)))
        assert len(assignments) == len(set(assignments)) == 12
        for index, assignment in enumerate(assignments):
            yield dict(id=f'{name}_mask_{index}', family=name, source=source,
                       mask_bits=list(assignment), allowed_types=_mask(assignment))


def diagram_cases():
    return [('circle', Diagram.from_pd([])),
            ('trefoil', Diagram.from_braid(2, [1, 1, 1])),
            ('figure_eight', Diagram.from_braid(3, [1, -2, 1, -2]))]
