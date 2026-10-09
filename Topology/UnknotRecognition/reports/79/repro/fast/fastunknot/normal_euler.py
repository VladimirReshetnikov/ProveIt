"""Certificate-producing positive-Euler screening in a supplied quad sector.

Canonical triangle peeling makes Euler characteristic a maximum of linear
forms indexed by one retained corner class per active global vertex.  Test
these forms by exact rational LP, without enumerating the quadrilateral rays.
Positive Euler by itself is not an essential-disc or knot certificate.
"""

from itertools import product
from math import prod
from fractions import Fraction

from .exact_lp import solve_nonnegative_kernel
from .normal_sector import build_sector_kernel, _source_hash
from .normal_surface_geometry import _coordinates, _EDGES, _quad


def _euler_model(kernel, check=lambda: None):
    """Return the linear unpeeled Euler functional and positive link weights."""
    p, k = len(kernel.classes), len(kernel.support)
    position = {c: i for i, c in enumerate(kernel.classes)}
    quadrilateral = {item: p+j for j, item in enumerate(kernel.support)}
    coefficients = [0] * (p+k)

    def triangle(t, v, amount):
        c = kernel.corner_class[4*t+v]
        if c in position:
            coefficients[position[c]] += amount

    # Each global edge is counted using its first local representative.
    represented = set()
    for t in range(len(kernel.prepared['tetrahedra'])):
        check()
        for v in range(4):
            triangle(t, v, 1)
        for q in range(3):
            if (t, q) in quadrilateral:
                coefficients[quadrilateral[t, q]] += 1
        for j, (a, b) in enumerate(_EDGES):
            root = kernel.prepared['edge_roots'][6*t+j]
            if root in represented:
                continue
            represented.add(root)
            triangle(t, a, 1)
            triangle(t, b, 1)
            absent = _quad(a, b)
            for q in range(3):
                if q != absent and (t, q) in quadrilateral:
                    coefficients[quadrilateral[t, q]] += 1
    faces = kernel.prepared['boundary_faces'] + [
        (t, f) for t, f, _, _, _ in kernel.prepared['pairs']]
    for t, f in faces:
        check()
        for v in range(4):
            if v != f:
                triangle(t, v, -1)
        for q in range(3):
            if (t, q) in quadrilateral:
                coefficients[quadrilateral[t, q]] -= 1
    boundary = {kernel.prepared['vertex_roots'][4*t+v]
                for t, f in kernel.prepared['boundary_faces'] for v in range(4) if v != f}
    weights = []
    for group in kernel.groups:
        check()
        root = kernel.prepared['vertex_roots'][group[0]]
        weight = 1 if root in boundary else 2
        if sum(coefficients[position[c]] for c in group) != weight:
            raise ArithmeticError('Euler coefficients disagree with the vertex-link census')
        weights.append(weight)
    linear = coefficients[p:]
    for c, i in position.items():
        check()
        for j, height in enumerate(kernel.potentials[c]):
            linear[j] += coefficients[i]*height
    return tuple(linear), tuple(weights)


def decide_sector_euler(triangulation, allowed_types, *, strategy='anchors',
                        max_anchors=None, max_pivots=None, check=lambda: None):
    """Return POSITIVE_EULER, NO_POSITIVE_EULER, or INCONCLUSIVE.

    The source is a supplied finite triangulation, not an authenticated knot
    diagram.  All anchors share max_pivots.  A negative certificate contains
    one exact homogeneous Farkas dual for every Cartesian anchor tuple.  A
    positive result supplies a primitive Q ray, its rational LP vertex and
    its complete canonical normal coordinates for subsequent topology checks.

    strategy='envelope' first tests the componentwise maximum of all anchor
    objectives.  A nonpositive result excludes the entire sector with one
    dual.  A positive envelope point alone proves nothing about canonical
    Euler; the ordinary anchor search then runs under the remaining budget.
    Certified duals, including the initial zero dual, are reused for later
    coordinatewise dominated anchor objectives.  All anchors still appear
    in an ordinary negative certificate, even when their dual is reused.

    With one active global vertex there are at most 8k anchor LPs; arbitrary
    matching nullity is allowed.  Rational LP has polynomial algorithms, but
    the shipped exact Bland simplex has no polynomial pivot guarantee.
    """
    for name, cap in (('max_anchors', max_anchors), ('max_pivots', max_pivots)):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError(name+' must be a nonnegative integer or None')
    if strategy not in ('anchors', 'envelope'):
        raise ValueError('strategy must be anchors or envelope')
    check()
    kernel = build_sector_kernel(triangulation, allowed_types, check=check)
    linear, weights = _euler_model(kernel, check)
    statistics = dict(kernel.stats, active_vertices=len(kernel.groups),
                      anchors_total=prod(map(len, kernel.groups)), anchors_tested=0,
                      strategy=strategy, lp_calls=0, reused_anchors=0, envelope_calls=0,
                      lp_pivots=0, lp_tableau_updates=0, maximum_tableau_bits=0)
    duals = []
    # Every objective dominated by zero has an immediate homogeneous dual.
    cache = [(tuple(0 for _ in kernel.support), [[0, 1] for _ in kernel.cycle_rows])]

    def solve(objective):
        remaining = None if max_pivots is None else max_pivots-statistics['lp_pivots']
        result = solve_nonnegative_kernel(kernel.cycle_rows, objective,
                                         max_pivots=remaining, check=check)
        statistics['lp_calls'] += 1
        statistics['lp_pivots'] += result['stats']['pivots']
        statistics['lp_tableau_updates'] += result['stats']['tableau_updates']
        statistics['maximum_tableau_bits'] = max(statistics['maximum_tableau_bits'],
                                                 result['stats']['maximum_tableau_bits'])
        return result

    if strategy == 'envelope':
        envelope = list(linear)
        for group, weight in zip(kernel.groups, weights):
            check()
            for j in range(len(kernel.support)):
                envelope[j] -= weight*min(kernel.potentials[c][j] for c in group)
        statistics['envelope_calls'] += 1
        result = solve(envelope)
        if result['status'] == 'INCONCLUSIVE':
            return dict(status='INCONCLUSIVE', reason=result['reason'], stats=statistics)
        if result['status'] == 'NONPOSITIVE':
            certificate = dict(schema='normal-sector-euler-lp-v1', status='NO_POSITIVE_EULER',
                source_sha256=_source_hash(triangulation),
                allowed_types=[list(x) for x in kernel.support], proof_kind='envelope',
                multipliers=result['y'])
            check()
            return dict(status='NO_POSITIVE_EULER', certificate=certificate, stats=statistics,
                        trust='canonical positive-Euler exclusion in this sector only')
        # Even a positive basic envelope point can have negative canonical
        # Euler.  Only a subsequently positive anchor may return a surface.
    for anchors in product(*kernel.groups):
        check()
        if max_anchors is not None and statistics['anchors_tested'] >= max_anchors:
            return dict(status='INCONCLUSIVE', reason='anchor allowance exhausted',
                        stats=statistics)
        objective = list(linear)
        for anchor, weight in zip(anchors, weights):
            for j, height in enumerate(kernel.potentials[anchor]):
                objective[j] -= weight*height
        statistics['anchors_tested'] += 1
        reused = None
        for bound, dual in reversed(cache):
            check()
            if all(a <= b for a, b in zip(objective, bound)):
                reused = dual
                break
        if reused is not None:
            statistics['reused_anchors'] += 1
            duals.append(dict(anchors=list(anchors), multipliers=reused))
            continue
        result = solve(objective)
        if result['status'] == 'INCONCLUSIVE':
            return dict(status='INCONCLUSIVE', reason=result['reason'], stats=statistics)
        if result['status'] == 'POSITIVE':
            q = result['primitive_x']
            coordinates = kernel.lift(q, check)
            chi = _coordinates(kernel.prepared, coordinates, check)['euler_characteristic']
            if chi <= 0:
                raise ArithmeticError('positive anchor objective did not survive canonical lifting')
            certificate = dict(schema='normal-sector-euler-lp-v1', status='POSITIVE_EULER',
                source_sha256=_source_hash(triangulation),
                allowed_types=[list(x) for x in kernel.support],
                quadrilaterals=q, coordinates=coordinates, euler_characteristic=chi)
            check()
            return dict(status='POSITIVE_EULER', quadrilaterals=q,
                        rational_quadrilaterals=result['x'], coordinates=coordinates,
                        euler_characteristic=chi, certificate=certificate, stats=statistics,
                        trust='positive Euler in this supplied sector; no disc or knot verdict')
        duals.append(dict(anchors=list(anchors), multipliers=result['y']))
        multipliers = [Fraction(*pair) for pair in result['y']]
        bound = tuple(sum(row[j]*y for row, y in zip(kernel.cycle_rows, multipliers))
                      for j in range(len(kernel.support)))
        cache.append((bound, result['y']))
    certificate = dict(schema='normal-sector-euler-lp-v1', status='NO_POSITIVE_EULER',
        source_sha256=_source_hash(triangulation),
        allowed_types=[list(x) for x in kernel.support], proof_kind='anchors', duals=duals)
    check()
    return dict(status='NO_POSITIVE_EULER', certificate=certificate, stats=statistics,
                trust='canonical positive-Euler exclusion in this sector only')
