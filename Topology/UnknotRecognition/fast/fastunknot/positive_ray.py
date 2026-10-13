"""Extract a crushable full-source ray from a canonical positive normal point.

Only coordinate-zero restrictions are imposed on the original matching
matrix. Such restrictions give a face of the full nonnegative matching cone,
so an extreme ray of that face is an extreme ray of the source cone. Exact
support descent preserves every existing zero, including a triangle zero at
each global vertex, as well as the one-quad-type compatibility condition.
Canonicality therefore excludes a terminal pure vertex-link ray.

The supplied positive point may be disconnected or nonprimitive. This module
does not search for one, enumerate rays, or authenticate a knot exterior.
"""
from types import SimpleNamespace

from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from .sector_euler import SourceEuler
from .source_kernel import SourceKernel


def extract_positive_ray(triangulation, coordinates, *, check=lambda: None):
    """Return ``coordinates`` and ``stats`` for a primitive positive source ray.

    Input uses the usual integral normal-coordinate transport. Matching,
    admissibility, positive Euler and canonical triangle zeros are validated
    from the supplied source. All original zero coordinates are retained.
    Output coordinates are exact Python integers; use ``json_safe`` for
    transporting very large values. Caller callback exceptions propagate.
    """
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    rows = analysed['rows']
    if analysed['euler_characteristic'] <= 0:
        raise NormalOrbitError('positive Euler characteristic required')
    if not any(any(row[4:]) for row in rows):
        raise NormalOrbitError('a nonzero quadrilateral coordinate is required')
    minima = {}
    for corner, vertex in enumerate(prepared['vertex_roots']):
        check()
        value = rows[corner//4][corner % 4]
        minima[vertex] = min(value, minima.get(vertex, value))
    if any(minima.values()):
        raise NormalOrbitError('canonical triangle zeros are required at every vertex')

    flat = tuple(x for row in rows for x in row)
    support = tuple(j for j, x in enumerate(flat) if x)
    equations = []
    for row in prepared['matching']:
        check()
        equations.append(tuple(row.get(j, 0) for j in support))
    # Only coefficients are needed here: the empty sparse potentials disable
    # the unused Q extension while SourceEuler still checks the vertex links.
    euler = SourceEuler(prepared, ({},)*(4*len(rows)), check)
    coefficients = tuple(x for row in euler.coefficients for x in row)
    objective = tuple(coefficients[j] for j in support)
    initial = tuple(flat[j] for j in support)
    if sum(a*b for a, b in zip(initial, objective)) != analysed['euler_characteristic']:
        raise ArithmeticError('source Euler coefficients disagree with the input census')
    kernel = SourceKernel(SimpleNamespace(n=len(support), equations=tuple(equations),
                                          conflicts=()), check=check)
    result = kernel.extreme_witness(initial, objective, check=check)
    output = [[0]*7 for _ in rows]
    for j, value in zip(support, result['coordinates']):
        check()
        output[j//7][j % 7] = value
    validated = _coordinates(prepared, output, check)
    if validated['euler_characteristic'] <= 0 or not any(any(r[4:]) for r in output):
        raise ArithmeticError('support descent lost a positive nonlink witness')
    check()
    return dict(coordinates=output, stats=dict(
        input_positive_coordinates=len(support),
        output_positive_coordinates=sum(bool(x) for row in output for x in row),
        source_equations=len(equations), matching_nullity=result['nullity'],
        initial_direction_dimension=result['initial_direction_dimension'],
        descent_steps=result['descent_steps'],
        input_euler_characteristic=analysed['euler_characteristic'],
        euler_characteristic=validated['euler_characteristic']))
