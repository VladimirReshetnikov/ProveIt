"""Independent complete ray-set checking for sectors of nullity at most three.

The producer clips winning polygons.  This checker instead starts with dense
standard matching equations, intersects every potential tie with *all* minimum
inequalities, and solves the resulting one-dimensional interval.  It imports
neither sector_planar nor normal_sector.  The shared trust boundary consists
of native triangulation validation and the older dense matching model.
"""

from fractions import Fraction
from itertools import combinations
from math import gcd

from .normal_sector_verify import (
    _digest, _integer_direction, _lift, dense_sector_model,
)
from .normal_surface_geometry import NormalOrbitError, _coordinates
from .normal_disk_kernel import verify_normal_disk_count_certificate
from .integer_codec import encoded_integer


SCHEMA = 'normal-sector-planar-rays-v1'


class PlanarVerificationLimit(RuntimeError):
    """The explicitly configured verification allowance was exhausted."""


def _value(form, point):
    return form[0] + sum(a * b for a, b in zip(form[1:], point))


def _minus(left, right):
    return tuple(a - b for a, b in zip(left, right))


def _line_intersection(left, right):
    c, a, b = left
    f, d, e = right
    determinant = a * e - b * d
    if not determinant:
        return None
    return ((b * f - c * e) / determinant,
            (c * d - a * f) / determinant)


def _interval(constraints, tick):
    lower = upper = None
    for constant, slope in constraints:
        tick('interval_inequalities')
        if not slope:
            if constant < 0:
                return None
            continue
        bound = -constant / slope
        if slope > 0:
            lower = bound if lower is None else max(lower, bound)
        else:
            upper = bound if upper is None else min(upper, bound)
        if lower is not None and upper is not None and lower > upper:
            return None
    if lower is None or upper is None:
        raise ArithmeticError('a nonempty projective section must be bounded')
    return lower, upper


def _at(base, direction, parameter):
    return tuple(a + parameter * b for a, b in zip(base, direction))


def _segment_intersection(left, right):
    a, b = left
    c, d = right
    u = _minus(b, a)
    v = _minus(d, c)
    w = _minus(c, a)
    determinant = u[0] * v[1] - u[1] * v[0]
    if not determinant:
        # A collinear overlap has only already-listed endpoints as vertices.
        return None
    s = (w[0] * v[1] - w[1] * v[0]) / determinant
    t = (w[0] * u[1] - w[1] * u[0]) / determinant
    if 0 <= s <= 1 and 0 <= t <= 1:
        return _at(a, u, s)
    return None


def _affine_dimension(points):
    if not points:
        return -1
    if len(points) == 1:
        return 0
    origin, second = points[:2]
    direction = _minus(second, origin)
    for point in points[2:]:
        displacement = _minus(point, origin)
        if direction[0] * displacement[1] != direction[1] * displacement[0]:
            return 2
    return 1


def _interval_points(endpoints, groups, tick):
    """All true minimum ties along a segment, using no envelope hull code."""
    left, right = endpoints
    direction = _minus(right, left)
    points = {left, right}
    for group in groups:
        restricted = sorted(set((_value(form, left),
                                 sum(a * b for a, b in zip(form[1:], direction)))
                                for form in group))
        for first, second in combinations(restricted, 2):
            tick('minimum_pairs')
            if first[1] == second[1]:
                continue
            parameter = (second[0] - first[0]) / (first[1] - second[1])
            if not 0 < parameter < 1:
                continue
            minimum = first[0] + parameter * first[1]
            if all(c + parameter * s >= minimum for c, s in restricted):
                points.add(_at(left, direction, parameter))
    return points


def independent_planar_directions(model, *, check=lambda: None,
                                  max_work=None, stats=None):
    """Return the complete primitive quadrilateral projections independently.

    The bound is polynomial in the dense model size.  After O(tk) projection
    and deduplication of dense triangle rows, geometry takes O(k^3 + p^2(k+p))
    exact operations before output, where p counts distinct projected forms
    across vertex groups. Dense elimination is charged separately.
    max_work counts disclosed predicate/interval events,
    not bit operations and not construction of the dense model.
    """
    if max_work is not None and (type(max_work) is not int or max_work < 0):
        raise ValueError('max_work must be a nonnegative integer or None')
    if stats is None:
        stats = {}
    stats.update(verification_work=0, domain_pairs=0, minimum_pairs=0,
                 interval_inequalities=0, crossing_pairs=0)

    def tick(kind):
        check()
        if max_work is not None and stats['verification_work'] >= max_work:
            raise PlanarVerificationLimit('planar verification allowance exhausted')
        stats['verification_work'] += 1
        stats[kind] = stats.get(kind, 0) + 1

    check()
    basis = model['basis']
    d = len(basis)
    stats['matching_nullity'] = d
    if d > 3:
        raise ValueError('planar verification requires matching nullity at most three')
    if not d:
        stats['section_dimension'] = -1
        return ()
    sums = [sum(vector) for vector in basis]
    # Choosing the LAST pivot is deliberate: this chart is independently built.
    pivot = next((i for i in reversed(range(d)) if sums[i]), None)
    if pivot is None:
        stats['section_dimension'] = -1
        return ()
    origin = tuple(x / sums[pivot] for x in basis[pivot])
    directions = [tuple(a - sums[i] * b for a, b in zip(basis[i], origin))
                  for i in range(d) if i != pivot]
    frame = [origin] + directions
    domain = [tuple(vector[i] for vector in frame) for i in range(len(origin))]
    groups = []
    for corners in model['groups'].values():
        forms = sorted(set(tuple(sum(a * b for a, b in zip(model['potentials'][c], v))
                                 for v in frame) for c in corners))
        if len(forms) > 1:
            groups.append(forms)
    stats['projected_forms'] = sum(map(len, groups))

    def output(points):
        result = set()
        for point in points:
            tick('output_directions')
            q = _integer_direction(_value(form, point) for form in domain)
            if not any(q) or any(x < 0 for x in q):
                raise ArithmeticError('independent direction left the nonnegative cone')
            result.add(q)
        stats['emitted_rays'] = len(result)
        return tuple(sorted(result))

    if d == 1:
        feasible = all(x >= 0 for x in origin)
        stats['section_dimension'] = 0 if feasible else -1
        return output([()]) if feasible else ()
    if d == 2:
        bounds = _interval(domain, tick)
        if bounds is None:
            stats['section_dimension'] = -1
            return ()
        left, right = ((bounds[0],), (bounds[1],))
        stats['section_dimension'] = 0 if left == right else 1
        return output([left] if left == right else
                      _interval_points((left, right), groups, tick))

    # Enumerating vertices of k halfplanes is cubic, including feasibility.
    vertices = set()
    for first, second in combinations(domain, 2):
        tick('domain_pairs')
        point = _line_intersection(first, second)
        if point is not None and all(_value(form, point) >= 0 for form in domain):
            vertices.add(point)
    vertices = sorted(vertices)
    dimension = _affine_dimension(vertices)
    stats['section_dimension'] = dimension
    if dimension < 0:
        return ()
    if dimension == 0:
        return output(vertices)
    if dimension == 1:
        return output(_interval_points((vertices[0], vertices[-1]), groups, tick))

    points = set(vertices)
    segments_by_group = []
    for forms in groups:
        segments = set()
        for first, second in combinations(forms, 2):
            tick('minimum_pairs')
            constant, a, b = _minus(first, second)
            if not a and not b:
                continue
            base = (-constant / a, Fraction(0)) if a else (Fraction(0), -constant / b)
            direction = (-b, a)
            constraints = list(domain) + [_minus(form, first) for form in forms]
            bounds = _interval([(_value(form, base),
                                 form[1] * direction[0] + form[2] * direction[1])
                                for form in constraints], tick)
            if bounds is None:
                continue
            ends = tuple(sorted((_at(base, direction, bounds[0]),
                                 _at(base, direction, bounds[1]))))
            points.update(ends)
            if ends[0] == ends[1]:
                continue
            on_boundary = any((form[1] or form[2])
                              and _value(form, ends[0]) == _value(form, ends[1]) == 0
                              for form in domain)
            if not on_boundary:
                segments.add(ends)
        segments_by_group.append(sorted(segments))
    stats['minimum_segments'] = sum(map(len, segments_by_group))
    for left, right in combinations(segments_by_group, 2):
        for first in left:
            for second in right:
                tick('crossing_pairs')
                point = _segment_intersection(first, second)
                if point is not None:
                    points.add(point)
    return output(points)


def verify_planar_sector_certificate(triangulation, certificate, *,
                                     check=lambda: None, max_work=None, stats=None):
    """Verify exact source binding and the complete non-link standard ray set.

    Success certifies a sector enumeration, never an unknot verdict.  Timeout
    and cancellation propagate; no incomplete verification returns True.
    """
    check()
    if type(certificate) is not dict or certificate.get('schema') != SCHEMA:
        return False
    if certificate.get('source_sha256') != _digest(triangulation):
        return False
    support = certificate.get('allowed_types')
    entries = certificate.get('quadrilateral_rays')
    if type(support) is not list or type(entries) is not list:
        return False
    if any(type(pair) is not list or len(pair) != 2
           or any(type(x) is not int for x in pair) for pair in support):
        return False
    if (support != sorted(support) or len({pair[0] for pair in support}) != len(support)
            or any(pair[0] < 0 or not 0 <= pair[1] < 3 for pair in support)):
        return False
    parsed = []
    for row in entries:
        check()
        if (type(row) is not list or len(row) != len(support)
                or any(type(x) is not int or x < 0 for x in row)
                or not any(row)):
            return False
        divisor = 0
        for x in row:
            divisor = gcd(divisor, x)
        if divisor != 1:
            return False
        parsed.append(tuple(row))
    if parsed != sorted(set(parsed)):
        return False
    try:
        tetrahedra = triangulation['tetrahedra']
        if any(pair[0] >= len(tetrahedra) for pair in support):
            return False
    except (KeyError, TypeError):
        return False
    try:
        model = dense_sector_model(triangulation, support, check=check)
    except NormalOrbitError:
        return False
    if len(model['basis']) > 3:
        return False
    expected = independent_planar_directions(model, check=check,
                                             max_work=max_work, stats=stats)
    return tuple(parsed) == expected


def verify_planar_exhaustion(triangulation, certificate, *, check=lambda: None,
                              max_work=None, stats=None):
    """Check complete enumeration and every positive-Euler negative disc test."""
    check()
    if (type(certificate) is not dict or
            certificate.get('schema') != 'normal-sector-planar-exhaustion-v1'):
        return False
    enumeration = certificate.get('enumeration')
    if not verify_planar_sector_certificate(triangulation, enumeration, check=check,
                                             max_work=max_work, stats=stats):
        return False
    entries = certificate.get('rays')
    if type(entries) is not list or len(entries) != len(enumeration['quadrilateral_rays']):
        return False
    model = dense_sector_model(triangulation, enumeration['allowed_types'], check=check)
    positive = False
    for entry, q in zip(entries, enumeration['quadrilateral_rays']):
        check()
        if type(entry) is not dict or entry.get('quadrilaterals') != q:
            return False
        rows = _lift(model, q, check)
        chi = _coordinates(model['prepared'], rows, check)['euler_characteristic']
        if type(entry.get('euler_characteristic')) is not int:
            return False
        if entry['euler_characteristic'] != chi:
            return False
        if chi <= 0:
            if 'disk_certificate' in entry:
                return False
            continue
        positive = True
        proof = entry.get('disk_certificate')
        if not verify_normal_disk_count_certificate(triangulation, rows, proof, check=check):
            return False
        try:
            if encoded_integer(proof['compressing_disk_components']) != 0:
                return False
        except (KeyError, TypeError, ValueError):
            return False
    expected = 'NO_VERTEX_DISC_IN_SECTOR' if positive else 'NO_POSITIVE_EULER'
    return certificate.get('status') == expected
