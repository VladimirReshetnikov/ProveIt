"""Independent coverage replay for low-dimensional standard-sector rays.

This module never imports the envelope producer, its hull routine, the sector
kernel builder, or a ray enumerator.  It reconstructs an uncontracted triangle
graph from native matching equations and uses the older independent rational
eliminator only to certify its quadrilateral solution-space dimension.
"""

from fractions import Fraction
from math import gcd, lcm

from .integer_codec import encoded_integer, certificate_equal
from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from .normal_sector_verify import _allowed, _digest, _kernel


def independent_sector_model(triangulation, allowed_types, *, check=lambda: None):
    """Recover corner potentials from full matching rows, without contraction."""
    prepared = _prepare(triangulation, check)
    count = len(prepared['tetrahedra'])
    support = _allowed([list(pair) for pair in allowed_types], count)
    k = len(support)
    selected = {7*t+4+q: j for j, (t, q) in enumerate(support)}
    edges, pure = [], []
    adjacency = [[] for _ in range(4*count)]
    for row in prepared['matching']:
        check()
        triangles = [(4*(i//7)+i % 7, value) for i, value in row.items()
                     if i % 7 < 4 and value]
        label = [0]*k
        for column, value in row.items():
            if column in selected:
                label[selected[column]] += value
        if not triangles:
            if any(label):
                pure.append(tuple(label))
            continue
        if len(triangles) != 2 or sorted(v for _, v in triangles) != [-1, 1]:
            raise ArithmeticError('unexpected native triangle matching row')
        a = next(i for i, value in triangles if value == 1)
        b = next(i for i, value in triangles if value == -1)
        label = tuple(label)
        # The source equation is t_a - t_b + label.q = 0.
        edges.append((a, b, label))
        adjacency[a].append((b, label))
        adjacency[b].append((a, tuple(-x for x in label)))
    potentials = [None]*(4*count)
    for start in range(4*count):
        check()
        if potentials[start] is not None:
            continue
        potentials[start] = (0,)*k
        queue = [start]
        for a in queue:
            check()
            for b, label in adjacency[a]:
                if potentials[b] is None:
                    potentials[b] = tuple(x+y for x, y in zip(potentials[a], label))
                    queue.append(b)
    constraints = list(pure)
    for a, b, label in edges:
        check()
        row = tuple(y-x-z for x, y, z in zip(potentials[a], potentials[b], label))
        if any(row):
            constraints.append(row)
    constraints = sorted(set(constraints))
    basis = _kernel(constraints, k, check)
    groups = {}
    for corner, vertex in enumerate(prepared['vertex_roots']):
        groups.setdefault(vertex, []).append(corner)
    return dict(prepared=prepared, support=support, potentials=potentials,
                groups=groups, constraints=constraints, basis=basis)


def _rational(value):
    if type(value) is not list or len(value) != 2:
        raise ValueError('rational must be a numerator-denominator pair')
    numerator, denominator = map(encoded_integer, value)
    if denominator <= 0 or gcd(numerator, denominator) != 1:
        raise ValueError('noncanonical rational')
    return Fraction(numerator, denominator)


def _direction(values):
    multiplier = 1
    for x in values:
        multiplier = lcm(multiplier, x.denominator)
    integers = [int(x*multiplier) for x in values]
    common = 0
    for x in integers:
        common = gcd(common, abs(x))
    if not common:
        raise ValueError('zero projective vector')
    return tuple(x//common for x in integers)


def _bounds(origin, direction):
    lower, upper = None, None
    for a, b in zip(origin, direction):
        if b > 0:
            candidate = -a/b
            lower = candidate if lower is None else max(lower, candidate)
        elif b < 0:
            candidate = -a/b
            upper = candidate if upper is None else min(upper, candidate)
        elif a < 0:
            return None
    if lower is None or upper is None or lower > upper:
        return None
    return lower, upper


def _section_empty(basis):
    if not basis:
        return True
    if len(basis) == 1:
        row = basis[0]
        return any(x > 0 for x in row) and any(x < 0 for x in row)
    sums = [sum(row) for row in basis]
    pivot = next((i for i, value in enumerate(sums) if value), None)
    if pivot is None:
        return True
    origin = [x/sums[pivot] for x in basis[pivot]]
    direction = [x-sums[1-pivot]*a for x, a in zip(basis[1-pivot], origin)]
    return _bounds(origin, direction) is None


def _lift(model, q, check):
    values = [sum(a*b for a, b in zip(row, q)) for row in model['potentials']]
    for group in model['groups'].values():
        minimum = min(values[i] for i in group)
        for i in group:
            values[i] -= minimum
    rows = [[0]*7 for _ in model['prepared']['tetrahedra']]
    for i, value in enumerate(values):
        rows[i//4][i % 4] = value
    for (t, typ), value in zip(model['support'], q):
        rows[t][4+typ] = value
    _coordinates(model['prepared'], rows, check)
    return rows


def _cover_group(lines, corners, active, lower, upper, hints, check, stats):
    """Check a concave envelope and one slope-bracket test per source line."""
    if (type(active) is not list or not active
            or any(type(i) is not int or i not in corners for i in active)
            or len(set(active)) != len(active)):
        return None
    pieces = [lines[i] for i in active]
    switches = []
    for (a, b), (c, d) in zip(pieces, pieces[1:]):
        check()
        if b <= d:
            return None
        switch = (c-a)/(b-d)
        if not lower < switch < upper or switches and switch <= switches[-1]:
            return None
        switches.append(switch)
    if type(hints) is not list or len(hints) != len(corners):
        return None
    slopes = [line[1] for line in pieces]
    for corner, bracket in zip(corners, hints):
        check()
        if type(bracket) is not int or not 0 <= bracket <= len(active):
            return None
        a, slope = lines[corner]
        # bracket 0 means the minimum difference occurs at the left endpoint;
        # bracket r means the right endpoint; otherwise at switch[bracket-1].
        if bracket == 0:
            if slope < slopes[0]:
                return None
            position, piece = lower, pieces[0]
        elif bracket == len(active):
            if slope > slopes[-1]:
                return None
            position, piece = upper, pieces[-1]
        else:
            if not slopes[bracket-1] >= slope >= slopes[bracket]:
                return None
            position, piece = switches[bracket-1], pieces[bracket-1]
        if a+slope*position < piece[0]+piece[1]*position:
            return None
        stats['dominance_tests'] += 1
    return switches


def verify_sector_envelope_certificate(triangulation, certificate, *,
                                       check=lambda: None, stats=None):
    """Certify all non-link standard rays without running a ray producer.

    Source topology and matching validation are shared native primitives.
    All nullity, section, envelope, primitive-coordinate, and coverage claims
    are independently checked.  An empty list only certifies this sector.
    """
    check()
    if stats is None:
        stats = {}
    stats.update(dominance_tests=0, rays_checked=0, envelope_pieces=0)
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-sector-envelope-v1'
            or certificate.get('source_sha256') != _digest(triangulation)):
        return False
    callback_failure = []

    def validation_check():
        try:
            check()
        except BaseException as exc:
            callback_failure.append(exc)
            raise

    try:
        prepared = _prepare(triangulation, validation_check)
    except NormalOrbitError:
        if callback_failure:
            raise
        return False
    try:
        support = _allowed(certificate.get('allowed_types'), len(prepared['tetrahedra']))
    except ValueError:
        return False
    model = independent_sector_model(triangulation, support, check=check)
    dimension = len(model['basis'])
    if (dimension > 2 or type(certificate.get('matching_dimension')) is not int
            or certificate['matching_dimension'] != dimension):
        return False
    section = certificate.get('section_dimension')
    if type(section) is not int or section not in (-1, 0, 1):
        return False
    rays, envelopes = certificate.get('rays'), certificate.get('envelopes')
    if type(rays) is not list or type(envelopes) is not list:
        return False
    if section == -1:
        return (not rays and not envelopes
                and all(certificate.get(name) is None for name in
                        ('q_origin', 'q_direction', 'lower', 'upper'))
                and _section_empty(model['basis']))
    if dimension == 0:
        return False
    try:
        origin = [_rational(x) for x in certificate['q_origin']]
        direction = [_rational(x) for x in certificate['q_direction']]
        lower, upper = _rational(certificate['lower']), _rational(certificate['upper'])
    except (KeyError, TypeError, ValueError):
        return False
    k = len(support)
    if (len(origin) != k or len(direction) != k or sum(origin) != 1
            or sum(direction) != 0 or any(sum(a*b for a, b in zip(row, vector))
            for row in model['constraints'] for vector in (origin, direction))):
        return False
    if dimension == 1:
        if (section != 0 or any(direction) or lower != 0 or upper != 0
                or any(x < 0 for x in origin)):
            return False
    else:
        if not any(direction) or _bounds(origin, direction) != (lower, upper):
            return False
        if section != (0 if lower == upper else 1):
            return False
    positions = {lower, upper}
    if section == 0:
        if envelopes:
            return False
    else:
        groups = model['groups']
        if len(envelopes) != len(groups):
            return False
        lines = [(sum(x*y for x, y in zip(potential, origin)),
                  sum(x*y for x, y in zip(potential, direction)))
                 for potential in model['potentials']]
        seen = set()
        for record in envelopes:
            check()
            if type(record) is not dict:
                return False
            vertex = record.get('vertex')
            if type(vertex) is not int or vertex not in groups or vertex in seen:
                return False
            seen.add(vertex)
            switches = _cover_group(lines, groups[vertex], record.get('corners'),
                lower, upper, record.get('brackets'), check, stats)
            if switches is None:
                return False
            positions.update(switches)
            stats['envelope_pieces'] += len(record['corners'])
    expected = []
    for position in sorted(positions):
        check()
        q = _direction([a+position*b for a, b in zip(origin, direction)])
        rows = _lift(model, q, check)
        expected.append(rows)
        stats['rays_checked'] += 1
    return certificate_equal(rays, expected)
