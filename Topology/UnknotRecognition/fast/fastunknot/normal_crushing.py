"""Binary-coordinate crushing of a supplied positive normal extreme ray.

The geometric quotient is conditional: this API validates a compact orientable
one-torus source, but does not authenticate it as a classical knot exterior.
Only the diagram-bound chain verifier may interpret loss of the torus as an
unknot certificate. Discovery of the supplied ray is a separate problem.

Retained tetrahedra contain no quadrilaterals. Face tracing uses only the
nonzero quad type, with at most four directed states per crushed tetrahedron;
normal discs, coordinate multiplicities and interval points are never expanded.
"""
from math import gcd
from fractions import Fraction

from .integer_codec import json_safe
from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from .port_subspace import _rref
from .normal_crushing_verify import quotient_census


class _NonPrimitiveNormalPoint(NormalOrbitError):
    """Internal recovery signal: valid positive nonlink point needs scaling.

    Canonicality and extremality have not been established by this signal.
    """


class _NonExtremeNormalPoint(NormalOrbitError):
    """Internal recovery signal: valid primitive point has support nullity > 1.

    Canonicality has not been established by this signal.
    """


def _component(quotient, ids, check):
    index = {old:new for new,old in enumerate(ids)}
    rows = []
    for old in ids:
        check()
        rows.append([None if face is None else
                     dict(tetrahedron=index[face['tetrahedron']],
                          permutation=list(face['permutation']))
                     for face in quotient['tetrahedra'][old]])
    return dict(tetrahedra=rows)


def _trace_quotient(prepared, rows, check):
    source = prepared['tetrahedra']
    types = [next((q for q in range(3) if row[4+q]), None) for row in rows]
    kept = [t for t,q in enumerate(types) if q is None]
    index = {old:new for new,old in enumerate(kept)}
    quotient = [[None]*4 for _ in kept]
    visited = set()
    steps = longest = 0
    for start in kept:
        for start_face in range(4):
            check()
            current, face = start, start_face
            permutation = list(range(4))
            length = 0
            while True:
                check()
                gluing = source[current][face]
                if gluing is None:
                    break
                permutation = [gluing['permutation'][v] for v in permutation]
                current = gluing['tetrahedron']
                face = permutation[start_face]
                if current in index:
                    quotient[index[start]][start_face] = dict(
                        tetrahedron=index[current], permutation=permutation)
                    break
                state = current, face
                # Distinct retained-face walks have disjoint directed entry
                # states. The reverse walk uses the paired exit states.
                if state in visited:
                    raise NormalOrbitError('repeated reachable crushing face state')
                visited.add(state)
                length += 1
                steps += 1
                first = (0, types[current]+1)
                second = tuple(v for v in range(4) if v not in first)
                a,b = first if face in first else second
                swap = list(range(4))
                swap[a],swap[b] = b,a
                permutation = [swap[v] for v in permutation]
                face = permutation[start_face]
            longest = max(longest, length)
    return dict(tetrahedra=quotient), kept, dict(face_steps=steps, longest_path=longest)


def crush_normal_ray(triangulation, coordinates, *, check=lambda: None):
    """Construct a replayable quotient for a positive primitive full-cone ray.

    Invalid, nonpositive, nonextreme and triangle-only inputs raise ValueError.
    ``successor=None`` means no torus-boundary component of this quotient; it
    is not by itself a knot verdict. Caller cancellation propagates unchanged.
    The returned certificate is checked by verify_normal_crushing, separately.
    """
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    rows = analysed['rows']
    flat = tuple(v for row in rows for v in row)
    if analysed['euler_characteristic'] <= 0:
        raise NormalOrbitError('positive Euler characteristic required')
    if not any(any(row[4:]) for row in rows):
        raise NormalOrbitError('a quadrilateral is required for strict crushing progress')
    divisor = 0
    for x in flat:
        check()
        divisor = gcd(divisor, x)
    if divisor != 1:
        raise _NonPrimitiveNormalPoint('primitive integer normal ray required')
    # Coordinate-zero restrictions are faces of the full matching cone. A
    # one-shot ray check needs only its positive support, not a reusable chart
    # on all 7t coordinates. Retain every original matching equation.
    support = tuple(j for j,x in enumerate(flat) if x)
    equations = []
    for row in prepared['matching']:
        check()
        equations.append(tuple(Fraction(row.get(j,0)) for j in support))
    _,pivots = _rref(equations, len(support), check)
    if len(pivots) > len(support)-1:
        raise ArithmeticError('nonzero matching vector has impossible support rank')
    if len(pivots) < len(support)-1:
        raise _NonExtremeNormalPoint('primitive full matching-cone extreme ray required')
    quotient, kept, statistics = _trace_quotient(prepared, rows, check)
    components = quotient_census(quotient, check=check)
    torus = [i for i,c in enumerate(components) if c['boundary_euler'] == [0]]
    if len(torus) > 1 or any(c['boundary_euler'] != [0] and
                           any(chi != 2 for chi in c['boundary_euler']) for c in components):
        raise NormalOrbitError('unsupported crushing component boundary')
    chosen = torus[0] if torus else None
    successor = None if chosen is None else _component(quotient, components[chosen]['tetrahedra'], check)
    if successor is not None:
        _prepare(successor, check)
    certificate = dict(schema='normal-ray-crushing-v1', coordinates=json_safe(rows),
        retained_tetrahedra=kept, triangulation=quotient, components=components,
        torus_component=chosen, successor=successor)
    statistics.update(initial_tetrahedra=len(rows), quotient_tetrahedra=len(kept),
                      successor_tetrahedra=0 if successor is None else len(successor['tetrahedra']),
                      components=len(components), maximum_coordinate_bits=analysed['maximum_coordinate_bits'])
    check()
    return dict(status='COMPLETE', certificate=certificate, successor=successor, stats=statistics)
