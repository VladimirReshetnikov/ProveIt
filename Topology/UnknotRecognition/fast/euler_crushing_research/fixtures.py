"""Deterministic supplied-sector fixtures, reconstructed without an LP oracle."""
from pathlib import Path
from random import Random

from projective_port_research.native import cases as retained_cases
from normal_orbit_research.fixtures import layered_torus, boundary_cap, interior_vertex_torus


ROOT = Path(__file__).resolve().parents[2]


def cases():
    """The retained 22 sectors plus two eight-sector vertex-link controls."""
    result = retained_cases()
    interior, _ = interior_vertex_torus()
    raw, meridian = layered_torus(2)
    capped, _ = boundary_cap(raw, meridian)
    for name, source in (('interior_vertex', interior), ('multiple_boundary_vertices', capped)):
        count = len(source['tetrahedra'])
        assignments = [(-1,)*count]+[(q,)*count for q in range(3)]
        rng = Random(11720261012)
        while len(assignments) < 8:
            assignment = tuple(rng.randrange(-1, 3) for _ in range(count))
            if assignment not in assignments:
                assignments.append(assignment)
        result.extend(dict(id=f'{name}_{i}', triangulation=source,
                           support=tuple((t, q) for t, q in enumerate(assignment) if q >= 0))
                      for i, assignment in enumerate(assignments))
    return result


def nonextreme_control():
    """Canonical annulus-plus-disc sum with exact full-source support nullity 2."""
    source, meridian = layered_torus(1)
    source, _ = boundary_cap(source, meridian)
    return dict(id='canonical_positive_nonextreme_mixture', triangulation=source,
                coordinates=[[1, 1, 2, 2, 1, 0, 0], [1, 1, 0, 0, 3, 0, 0]])
