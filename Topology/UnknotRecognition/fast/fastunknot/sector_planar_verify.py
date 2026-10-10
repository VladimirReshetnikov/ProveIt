"""Independent replay of complete planar normal-sector ray certificates.

The producer, sparse constructor, polygon clipper, and ray enumerator are
never imported.  The source model is reconstructed from uncontracted native
matching equations, following the prior minimum-envelope checker.  Coverage
uses dominance and area (or length), not reconstruction of the producer's
clipping sequence.  Native manifold/coordinate validation is shared.
"""

from fractions import Fraction
from itertools import combinations
from math import gcd, lcm

from .integer_codec import encoded_integer, certificate_equal
from .normal_sector_verify import _allowed, _digest, _kernel
from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError


def independent_planar_model(triangulation, allowed_types, *, check=lambda: None):
    """Recover all corner potentials without producer graph contraction."""
    prepared = _prepare(triangulation, check)
    count = len(prepared['tetrahedra'])
    support = _allowed([list(pair) for pair in allowed_types], count)
    width = len(support)
    selected = {7*t+4+q: j for j, (t, q) in enumerate(support)}
    adjacency = [[] for _ in range(4*count)]
    edges, constraints = [], []
    for equation in prepared['matching']:
        check()
        triangles = [(4*(i//7)+i % 7, value) for i, value in equation.items()
                     if i % 7 < 4 and value]
        label = [0]*width
        for column, value in equation.items():
            if column in selected:
                label[selected[column]] += value
        if not triangles:
            if any(label):
                constraints.append(tuple(label))
            continue
        if len(triangles) != 2 or sorted(value for _, value in triangles) != [-1, 1]:
            raise ArithmeticError('unexpected native triangle matching equation')
        a = next(i for i, value in triangles if value == 1)
        b = next(i for i, value in triangles if value == -1)
        label = tuple(label)
        edges.append((a, b, label))
        adjacency[a].append((b, label))
        adjacency[b].append((a, tuple(-value for value in label)))
    potentials = [None]*(4*count)
    zero = (0,)*width
    for start in range(4*count):
        check()
        if potentials[start] is not None:
            continue
        potentials[start] = zero
        queue = [start]
        for a in queue:
            check()
            for b, label in adjacency[a]:
                if potentials[b] is None:
                    potentials[b] = tuple(x+y for x, y in zip(potentials[a], label))
                    queue.append(b)
    for a, b, label in edges:
        row = tuple(y-x-z for x, y, z in zip(potentials[a], potentials[b], label))
        if any(row):
            constraints.append(row)
    constraints = sorted(set(constraints))
    basis = _kernel(constraints, width, check)
    groups = {}
    for corner, vertex in enumerate(prepared['vertex_roots']):
        groups.setdefault(vertex, []).append(corner)
    return dict(prepared=prepared, support=support, potentials=potentials,
                groups=groups, constraints=constraints, basis=basis)


def _fraction(value):
    if type(value) is not list or len(value) != 2:
        raise ValueError('rational pair required')
    numerator, denominator = map(encoded_integer, value)
    if denominator <= 0 or gcd(numerator, denominator) != 1:
        raise ValueError('noncanonical rational')
    return Fraction(numerator, denominator)


def _point_list(value, dimension):
    if type(value) is not list:
        raise ValueError('point list required')
    result = []
    for point in value:
        if type(point) is not list or len(point) != dimension:
            raise ValueError('point dimension mismatch')
        result.append(tuple(_fraction(x) for x in point))
    return tuple(result)


def _evaluate(form, point):
    answer = form[0]
    for coefficient, coordinate in zip(form[1:], point):
        answer += coefficient*coordinate
    return answer


def _turn(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def _hull(points):
    ordered = sorted(set(points))
    if len(ordered) <= 1:
        return tuple(ordered)
    lower, upper = [], []
    for point in ordered:
        while len(lower) >= 2 and _turn(lower[-2], lower[-1], point) <= 0:
            lower.pop()
        lower.append(point)
    for point in reversed(ordered):
        while len(upper) >= 2 and _turn(upper[-2], upper[-1], point) <= 0:
            upper.pop()
        upper.append(point)
    return tuple(lower[:-1]+upper[:-1])


def _twice_area(polygon):
    total = Fraction(0)
    for i, point in enumerate(polygon):
        after = polygon[(i+1) % len(polygon)]
        total += point[0]*after[1]-point[1]*after[0]
    return total


def _feasible_vertices(forms, check):
    """Independent bounded H-to-V fallback for empty or degenerate sections."""
    halfspaces = list(forms)+[(0, 1, 0), (1, -1, 0), (0, 0, 1), (1, 0, -1)]
    points = set()
    for (a, b, c), (d, e, f) in combinations(halfspaces, 2):
        check()
        determinant = b*f-c*e
        if not determinant:
            continue
        point = (Fraction(c*d-a*f, determinant), Fraction(a*e-b*d, determinant))
        if all(_evaluate(form, point) >= 0 for form in halfspaces):
            points.add(point)
    return _hull(points)


def _check_chart(model, encoded, check):
    dimension = len(model['basis'])
    if encoded is None:
        if not dimension or all(sum(vector) == 0 for vector in model['basis']):
            return None
        raise ValueError('missing nonempty affine section chart')
    if type(encoded) is not dict or set(encoded) != {'coordinates', 'forms'}:
        raise ValueError('invalid chart fields')
    coordinates = encoded['coordinates']
    width = len(model['support'])
    if (not dimension or type(coordinates) is not list
            or len(coordinates) != dimension-1
            or len(set(coordinates)) != len(coordinates)
            or any(type(x) is not int or not 0 <= x < width for x in coordinates)):
        raise ValueError('invalid chart coordinate indices')
    forms = _point_list(encoded['forms'], dimension)
    if len(forms) != width:
        raise ValueError('wrong quadrilateral chart width')
    columns = tuple(tuple(row[j] for row in forms) for j in range(dimension))
    if tuple(map(sum, columns)) != (1,)+(0,)*(dimension-1):
        raise ValueError('chart does not normalize quadrilaterals')
    for row in model['constraints']:
        check()
        if any(sum(a*b for a, b in zip(row, column)) for column in columns):
            raise ValueError('chart violates a matching equation')
    for j, index in enumerate(coordinates):
        if forms[index] != tuple(Fraction(a == j+1) for a in range(dimension)):
            raise ValueError('chart coordinates are not the claimed actual q entries')
    # Sum and the actual coordinates form a left inverse of the chart columns.
    # Together with independently established nullity this proves completeness.
    return dict(coordinates=coordinates, forms=forms)


def _check_section(chart, polygon, check):
    if chart is None:
        return not polygon
    forms, dimension = chart['forms'], len(chart['coordinates'])
    if dimension == 0:
        expected = ((),) if all(row[0] >= 0 for row in forms) else ()
        return polygon == expected
    if dimension == 1:
        lower, upper = Fraction(0), Fraction(1)
        for a, b in forms:
            check()
            if b > 0:
                lower = max(lower, -a/b)
            elif b < 0:
                upper = min(upper, -a/b)
            elif a < 0:
                return not polygon
        expected = () if lower > upper else (
            ((lower,),) if lower == upper else ((lower,), (upper,)))
        return polygon == expected
    if len(polygon) < 3:
        return polygon == _feasible_vertices(forms, check)
    if polygon != _hull(polygon) or _twice_area(polygon) <= 0:
        return False
    for point in polygon:
        check()
        if any(_evaluate(row, point) < 0 for row in forms):
            return False
    # Inclusion in both directions: feasible vertices, and every facet is a
    # nontrivial source inequality.  No polygon search is used on this branch.
    for a, b in zip(polygon, polygon[1:]+polygon[:1]):
        check()
        if not any(any(row[1:]) and _evaluate(row, a) == _evaluate(row, b) == 0
                   for row in forms):
            return False
    return True


def _parameter(point, first, last):
    coordinate = next(i for i, (a, b) in enumerate(zip(first, last)) if a != b)
    parameter = (point[coordinate]-first[coordinate])/(last[coordinate]-first[coordinate])
    if any(x != a+parameter*(b-a) for x, a, b in zip(point, first, last)):
        raise ValueError('point is not on the section segment')
    return parameter


def _boundary_edge(a, b, polygon):
    for left, right in zip(polygon, polygon[1:]+polygon[:1]):
        if _turn(left, right, a) == 0 and _turn(left, right, b) == 0:
            return True
    return False


def _crossing_by_lines(left, right):
    a, b = left
    c, d = right
    ab = (a[1]-b[1], b[0]-a[0], a[0]*b[1]-a[1]*b[0])
    cd = (c[1]-d[1], d[0]-c[0], c[0]*d[1]-c[1]*d[0])
    determinant = ab[0]*cd[1]-cd[0]*ab[1]
    if not determinant:
        return None
    x = (ab[1]*cd[2]-cd[1]*ab[2])/determinant
    y = (cd[0]*ab[2]-ab[0]*cd[2])/determinant
    if all(min(p[i], q[i]) <= z <= max(p[i], q[i])
           for p, q in (left, right) for i, z in enumerate((x, y))):
        return (x, y)
    return None


def _check_groups(model, chart, polygon, section, records, check, stats):
    if type(records) is not list:
        raise ValueError('minimum-group records must be a list')
    dimension = len(chart['coordinates'])
    forms = []
    for potential in model['potentials']:
        check()
        forms.append(tuple(sum(a*row[j] for a, row in zip(potential, chart['forms']))
                           for j in range(dimension+1)))
    if section <= 0:
        if records:
            raise ValueError('zero-dimensional section cannot have cell records')
        return set(polygon), forms
    expected = {}
    for vertex, corners in model['groups'].items():
        if section == 1:
            keys = {(_evaluate(forms[c], polygon[0]), _evaluate(forms[c], polygon[1]))
                    for c in corners}
        else:
            keys = {forms[c] for c in corners}
        if len(keys) > 1:
            expected[vertex] = corners
    if len(records) != len(expected):
        raise ValueError('wrong minimum-group inventory')
    seen, points, all_segments = set(), set(polygon), []
    for record in records:
        check()
        if type(record) is not dict or set(record) != {'vertex', 'cells'}:
            raise ValueError('invalid group record')
        vertex, cells = record['vertex'], record['cells']
        if (type(vertex) is not int or vertex not in expected or vertex in seen
                or type(cells) is not list or not cells):
            raise ValueError('invalid group identity or cell list')
        seen.add(vertex)
        corners = expected[vertex]
        used_forms, measure, segments = set(), Fraction(0), set()
        for cell in cells:
            check()
            if type(cell) is not dict or set(cell) != {'corner', 'vertices'}:
                raise ValueError('invalid minimum cell')
            corner = cell['corner']
            if type(corner) is not int or corner not in corners:
                raise ValueError('cell label is not a source corner')
            poly = _point_list(cell['vertices'], dimension)
            key = forms[corner] if section == 2 else (
                _evaluate(forms[corner], polygon[0]), _evaluate(forms[corner], polygon[1]))
            if key in used_forms:
                raise ValueError('one affine function may label only one convex cell')
            used_forms.add(key)
            if section == 2:
                if len(poly) < 3 or poly != _hull(poly) or _twice_area(poly) <= 0:
                    raise ValueError('cell is not a strict convex polygon')
                measure += _twice_area(poly)
            else:
                if len(poly) != 2:
                    raise ValueError('cell is not a nondegenerate interval')
                lower = _parameter(poly[0], polygon[0], polygon[1])
                upper = _parameter(poly[1], polygon[0], polygon[1])
                if not 0 <= lower < upper <= 1:
                    raise ValueError('cell interval is outside section')
                measure += upper-lower
            for point in poly:
                check()
                if any(_evaluate(row, point) < 0 for row in chart['forms']):
                    raise ValueError('cell vertex is outside source section')
                selected = _evaluate(forms[corner], point)
                if any(_evaluate(forms[other], point) < selected for other in corners):
                    raise ValueError('cell label does not minimize source potentials')
                stats['dominance_tests'] += len(corners)
            points.update(poly)
            if section == 2:
                for a, b in zip(poly, poly[1:]+poly[:1]):
                    if not _boundary_edge(a, b, polygon):
                        segments.add(tuple(sorted((a, b))))
        target = _twice_area(polygon) if section == 2 else Fraction(1)
        if measure != target:
            raise ValueError('minimum cells do not cover the entire section')
        # Distinct affine labels and dominance imply disjoint relative interiors.
        # Equal total measure of closed convex cells then proves full coverage.
        all_segments.append(tuple(sorted(segments)))
        stats['cells_checked'] += len(cells)
    for first, second in combinations(all_segments, 2):
        for a in first:
            for b in second:
                check()
                stats['intersection_tests'] += 1
                point = _crossing_by_lines(a, b)
                if point is not None:
                    points.add(point)
    return points, forms


def _lift_at(model, chart, forms, point, check):
    values = [_evaluate(form, point) for form in chart['forms']]
    denominator = lcm(*(x.denominator for x in values))
    integers = [int(x*denominator) for x in values]
    common = gcd(*integers)
    if not common or any(x < 0 for x in integers):
        raise ValueError('invalid projective direction')
    q = [x//common for x in integers]
    scale = sum(q)
    triangles = [_evaluate(form, point)*scale for form in forms]
    for corners in model['groups'].values():
        minimum = min(triangles[corner] for corner in corners)
        for corner in corners:
            triangles[corner] -= minimum
    rows = [[0]*7 for _ in model['prepared']['tetrahedra']]
    for corner, value in enumerate(triangles):
        check()
        if value.denominator != 1:
            raise ArithmeticError('native canonical triangles are not integral')
        rows[corner//4][corner % 4] = value.numerator
    for (tetrahedron, kind), value in zip(model['support'], q):
        rows[tetrahedron][4+kind] = value
    _coordinates(model['prepared'], rows, check)
    return rows


def _verify(triangulation, certificate, check, stats):
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-sector-planar-v1'
            or certificate.get('source_sha256') != _digest(triangulation)):
        return False
    if (type(certificate.get('allowed_types')) is not list
            or any(type(pair) is not list for pair in certificate['allowed_types'])):
        return False
    model = independent_planar_model(triangulation, certificate['allowed_types'], check=check)
    dimension = len(model['basis'])
    if (dimension > 3 or type(certificate.get('matching_dimension')) is not int
            or certificate['matching_dimension'] != dimension):
        return False
    chart = _check_chart(model, certificate['chart'], check)
    chart_dimension = 0 if chart is None else len(chart['coordinates'])
    polygon = _point_list(certificate['polygon'], chart_dimension)
    if not _check_section(chart, polygon, check):
        return False
    section = -1 if not polygon else min(2, len(polygon)-1)
    if (type(certificate.get('section_dimension')) is not int
            or certificate['section_dimension'] != section):
        return False
    if not polygon:
        return certificate.get('groups') == [] and certificate.get('rays') == []
    points, forms = _check_groups(model, chart, polygon, section,
                                  certificate['groups'], check, stats)
    expected = []
    for point in sorted(points):
        check()
        expected.append(_lift_at(model, chart, forms, point, check))
        stats['rays_checked'] += 1
    return certificate_equal(certificate.get('rays'), expected)


def verify_planar_sector_certificate(triangulation, certificate, *,
                                     check=lambda: None, stats=None):
    """Check the whole supplied sector, including empty-list coverage claims.

    Wrong-source, malformed, missing-cell and incomplete-ray claims fail.
    Cooperative callback exceptions propagate rather than becoming False.
    """
    check()
    if stats is None:
        stats = {}
    stats.update(cells_checked=0, dominance_tests=0, intersection_tests=0,
                 rays_checked=0)
    failures = []

    def callback():
        try:
            check()
        except BaseException as exc:
            failures.append(exc)
            raise

    try:
        return _verify(triangulation, certificate, callback, stats)
    except (ValueError, TypeError, KeyError, IndexError, ZeroDivisionError,
            NormalOrbitError):
        if failures:
            raise failures[0]
        return False


def verify_planar_disc_exhaustion(triangulation, certificate, *, check=lambda: None):
    """Replay full ray coverage and every claimed zero disk-component count."""
    from .normal_disk_kernel import verify_normal_disk_count_certificate
    check()
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-sector-planar-disc-scan-v1'
            or certificate.get('status') != 'NO_VERTEX_DISC_IN_SECTOR'
            or certificate.get('source_sha256') != _digest(triangulation)):
        return False
    coverage, checks = certificate.get('coverage'), certificate.get('checks')
    if not verify_planar_sector_certificate(triangulation, coverage, check=check):
        return False
    if type(checks) is not list or len(checks) != len(coverage['rays']):
        return False
    for index, (entry, rows) in enumerate(zip(checks, coverage['rays'])):
        check()
        if (type(entry) is not dict or set(entry) != {'ray', 'disk_certificate'}
                or type(entry['ray']) is not int or entry['ray'] != index):
            return False
        proof = entry['disk_certificate']
        if not verify_normal_disk_count_certificate(triangulation, rows, proof, check=check):
            return False
        try:
            if encoded_integer(proof['compressing_disk_components']) != 0:
                return False
        except (TypeError, ValueError, KeyError):
            return False
    return True
