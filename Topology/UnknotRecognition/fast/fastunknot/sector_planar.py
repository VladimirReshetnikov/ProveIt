"""Complete standard normal-sector rays from planar minimum diagrams.

The matching nullspace must have dimension at most three.  Its nonnegative
cone may have smaller dimension, including being zero.  Arithmetic is exact;
no general knot verdict or completeness across different sectors is implied.
The existing recognizer's dispatcher is deliberately not changed.
"""

from fractions import Fraction
from itertools import combinations
from math import gcd, lcm

from .normal_sector import SearchLimit, _source_hash
from .normal_surface_geometry import _coordinates
from .integer_codec import json_safe


def _cross(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def _area2(poly):
    return sum(a[0]*b[1]-a[1]*b[0]
               for a, b in zip(poly, poly[1:]+poly[:1]))


def _clean_polygon(points):
    """Canonical CCW convex polygon, segment, point, or empty tuple."""
    points = list(points)
    unique = []
    for point in points:
        point = tuple(point)
        if not unique or point != unique[-1]:
            unique.append(point)
    if len(unique) > 1 and unique[0] == unique[-1]:
        unique.pop()
    if len(unique) <= 1:
        return tuple(unique)
    if len(unique) == 2 or _area2(unique) == 0:
        a, b = min(unique), max(unique)
        return (a,) if a == b else (a, b)
    if _area2(unique) < 0:
        unique.reverse()
    stack = []
    for point in unique:
        while len(stack) >= 2 and _cross(stack[-2], stack[-1], point) == 0:
            stack.pop()
        stack.append(point)
    start = 0
    changed = True
    while changed and len(stack)-start >= 3:
        changed = False
        if _cross(stack[-2], stack[-1], stack[start]) == 0:
            stack.pop()
            changed = True
        if (len(stack)-start >= 3
                and _cross(stack[-1], stack[start], stack[start+1]) == 0):
            start += 1
            changed = True
    stack = stack[start:]
    first = min(range(len(stack)), key=stack.__getitem__)
    return tuple(stack[first:]+stack[:first])


def _value(form, point):
    return form[0] + sum(a*b for a, b in zip(form[1:], point))


def _interpolate(a, b, fraction):
    return tuple(x+fraction*(y-x) for x, y in zip(a, b))


def _clip_polygon(poly, form):
    """Intersect a convex polygon with the closed halfplane form >= 0."""
    if not poly:
        return ()
    if len(poly) == 1:
        return poly if _value(form, poly[0]) >= 0 else ()
    if len(poly) == 2:
        a, b = poly
        fa, fb = _value(form, a), _value(form, b)
        if fa >= 0 and fb >= 0:
            return poly
        if fa < 0 and fb < 0:
            return ()
        point = _interpolate(a, b, fa/(fa-fb))
        return _clean_polygon((a, point) if fa >= 0 else (point, b))
    output = []
    for a, b in zip(poly, poly[1:]+poly[:1]):
        fa, fb = _value(form, a), _value(form, b)
        if fa >= 0:
            output.append(a)
        if (fa > 0 and fb < 0) or (fa < 0 and fb > 0):
            output.append(_interpolate(a, b, fa/(fa-fb)))
    return _clean_polygon(output)


def _rank(rows, width):
    matrix = [list(map(Fraction, row)) for row in rows]
    rank = 0
    for col in range(width):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        scale = matrix[rank][col]
        matrix[rank] = [x/scale for x in matrix[rank]]
        for i in range(rank+1, len(matrix)):
            scale = matrix[i][col]
            if scale:
                matrix[i] = [x-scale*y for x, y in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


def _inverse(matrix):
    size = len(matrix)
    rows = [list(map(Fraction, row))+[Fraction(i == j) for j in range(size)]
            for i, row in enumerate(matrix)]
    for col in range(size):
        pivot = next(i for i in range(col, size) if rows[i][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        scale = rows[col][col]
        rows[col] = [x/scale for x in rows[col]]
        for i in range(size):
            if i != col and rows[i][col]:
                scale = rows[i][col]
                rows[i] = [x-scale*y for x, y in zip(rows[i], rows[col])]
    return [row[size:] for row in rows]


def _section_chart(basis, check):
    """Use actual q coordinates as a bounded affine chart for sum(q)=1."""
    dimension = len(basis)
    if not dimension:
        return None
    sums = [sum(vector) for vector in basis]
    if not any(sums):
        return None
    equations, coordinates = [sums], []
    for i in range(len(basis[0])):
        check()
        if len(equations) == dimension:
            break
        row = [vector[i] for vector in basis]
        if _rank(equations+[row], dimension) > len(equations):
            equations.append(row)
            coordinates.append(i)
    inverse = _inverse(equations)
    forms = tuple(tuple(sum(basis[j][i]*inverse[j][a] for j in range(dimension))
                        for a in range(dimension))
                  for i in range(len(basis[0])))
    return dict(coordinates=tuple(coordinates), forms=forms)


def _section_polygon(chart, check):
    if chart is None:
        return ()
    dimension = len(chart['coordinates'])
    forms = chart['forms']
    if dimension == 0:
        return ((),) if all(form[0] >= 0 for form in forms) else ()
    if dimension == 1:
        lower, upper = Fraction(0), Fraction(1)
        for a, b in forms:
            check()
            if b > 0:
                lower = max(lower, -a/b)
            elif b < 0:
                upper = min(upper, -a/b)
            elif a < 0:
                return ()
        if lower > upper:
            return ()
        return ((lower,),) if lower == upper else ((lower,), (upper,))
    poly = tuple(tuple(map(Fraction, p)) for p in ((0, 0), (1, 0), (1, 1), (0, 1)))
    for form in forms:
        check()
        poly = _clip_polygon(poly, form)
        if not poly:
            break
    return poly


def _lower_lines(lines, check):
    """Lower envelope of (intercept, slope, corner) on the real line."""
    by_slope = {}
    for a, b, corner in lines:
        check()
        value = (a, corner)
        if b not in by_slope or value < by_slope[b]:
            by_slope[b] = value
    hull, starts = [], []
    for slope in sorted(by_slope, reverse=True):
        intercept, corner = by_slope[slope]
        line = (intercept, slope, corner)
        while hull:
            old_a, old_b, _ = hull[-1]
            at = (intercept-old_a)/(old_b-slope)
            if starts[-1] is None or at > starts[-1]:
                break
            hull.pop()
            starts.pop()
        start = None if not hull else (intercept-hull[-1][0])/(hull[-1][1]-slope)
        hull.append(line)
        starts.append(start)
    return hull, starts


def _on_boundary(a, b, polygon):
    return any(_cross(c, d, a) == 0 and _cross(c, d, b) == 0
               for c, d in zip(polygon, polygon[1:]+polygon[:1]))


def _segment_crossing(first, second):
    a, b = first
    c, d = second
    r = (b[0]-a[0], b[1]-a[1])
    s = (d[0]-c[0], d[1]-c[1])
    determinant = r[0]*s[1]-r[1]*s[0]
    if not determinant:
        # Any endpoint of a collinear overlap is an input endpoint already.
        return None
    delta = (c[0]-a[0], c[1]-a[1])
    u = (delta[0]*s[1]-delta[1]*s[0])/determinant
    v = (delta[0]*r[1]-delta[1]*r[0])/determinant
    if 0 <= u <= 1 and 0 <= v <= 1:
        return _interpolate(a, b, u)
    return None


def _section_plan(kernel, check, stats):
    """Prepare the Q-section and projected forms without minimum cells."""
    check()
    if len(kernel.basis) > 3:
        raise ValueError('planar enumeration requires matching nullity at most three')
    if stats is None:
        stats = {}
    stats.update(matching_dimension=len(kernel.basis), clipping_steps=0,
                 active_cells=0, internal_segments=0, intersection_tests=0,
                 distinct_forms=0, points=0)
    chart = _section_chart(kernel.basis, check)
    polygon = _section_polygon(chart, check)
    section = -1 if not polygon else min(2, len(polygon)-1)
    stats['section_dimension'] = section
    stats['polygon_vertices'] = len(polygon)
    plan = dict(chart=chart, polygon=polygon, section_dimension=section,
                groups=[], class_forms={}, points=())
    if not polygon:
        return plan
    qforms = chart['forms']
    width = len(chart['coordinates'])+1
    projected = {}
    for corner in kernel.classes:
        check()
        potential = kernel.potentials[corner]
        projected[corner] = tuple(sum(x*form[j] for x, form in zip(potential, qforms))
                                  for j in range(width))
    plan['class_forms'] = projected
    return plan


def _minimum_overlay(kernel, plan, check, stats):
    polygon = plan['polygon']
    if not polygon:
        return plan
    section = plan['section_dimension']
    projected = plan['class_forms']
    points = set(polygon)
    segments_by_group = []
    if section == 0:
        plan['points'] = tuple(sorted(points))
        stats['points'] = 1
        return plan
    for group in kernel.groups:
        check()
        vertex = kernel.prepared['vertex_roots'][group[0]]
        if section == 1:
            a, b = polygon
            forms = {}
            for corner in group:
                at_a, at_b = _value(projected[corner], a), _value(projected[corner], b)
                forms.setdefault((at_a, at_b-at_a), corner)
            if len(forms) <= 1:
                continue
            stats['distinct_forms'] += len(forms)
            hull, starts = _lower_lines([(x, y, c) for (x, y), c in forms.items()], check)
            cells = []
            for i, (_, _, corner) in enumerate(hull):
                lower = max(Fraction(0), starts[i]) if starts[i] is not None else Fraction(0)
                upper = min(Fraction(1), starts[i+1]) if i+1 < len(starts) else Fraction(1)
                if lower >= upper:
                    continue
                left, right = _interpolate(a, b, lower), _interpolate(a, b, upper)
                cells.append(dict(corner=corner, vertices=(left, right)))
                points.update((left, right))
            plan['groups'].append(dict(vertex=vertex, cells=cells))
            stats['active_cells'] += len(cells)
            continue
        forms = {}
        for corner in group:
            forms.setdefault(projected[corner], corner)
        if len(forms) <= 1:
            continue
        stats['distinct_forms'] += len(forms)
        cells, segments = [], set()
        for form, corner in forms.items():
            check()
            cell = polygon
            for other in forms:
                if other == form:
                    continue
                check()
                stats['clipping_steps'] += 1
                cell = _clip_polygon(cell, tuple(x-y for x, y in zip(other, form)))
                if len(cell) < 3:
                    break
            if len(cell) < 3:
                continue
            cells.append(dict(corner=corner, vertices=cell))
            points.update(cell)
            for a, b in zip(cell, cell[1:]+cell[:1]):
                if not _on_boundary(a, b, polygon):
                    segments.add(tuple(sorted((a, b))))
        if not cells:
            raise ArithmeticError('nonempty section has no full-dimensional minimum cell')
        plan['groups'].append(dict(vertex=vertex, cells=cells))
        segments_by_group.append(tuple(sorted(segments)))
        stats['active_cells'] += len(cells)
        stats['internal_segments'] += len(segments)
    for first, second in combinations(segments_by_group, 2):
        for left in first:
            for right in second:
                check()
                stats['intersection_tests'] += 1
                crossing = _segment_crossing(left, right)
                if crossing is not None:
                    points.add(crossing)
    plan['points'] = tuple(sorted(points))
    stats['points'] = len(points)
    return plan


def sector_planar_plan(kernel, *, check=lambda: None, stats=None):
    """Build the complete projective min-diagram; no normal disks expanded."""
    if stats is None:
        stats = {}
    return _minimum_overlay(kernel, _section_plan(kernel, check, stats), check, stats)


def _primitive_nonnegative(values):
    denominator = lcm(*(x.denominator for x in values))
    integers = [int(x*denominator) for x in values]
    common = gcd(*integers)
    if common == 0 or any(x < 0 for x in integers):
        raise ArithmeticError('invalid nonzero projective quadrilateral vector')
    return tuple(x//common for x in integers)


def _projected_lift(kernel, plan, point, check):
    q = _primitive_nonnegative([_value(form, point) for form in plan['chart']['forms']])
    scale = sum(q)
    values = {}
    for corner, form in plan['class_forms'].items():
        check()
        value = _value(form, point)*scale
        if value.denominator != 1:
            raise ArithmeticError('integral quadrilateral direction has nonintegral potential')
        values[corner] = value.numerator
    for group in kernel.groups:
        minimum = min(values[corner] for corner in group)
        for corner in group:
            values[corner] -= minimum
    rows = [[0]*7 for _ in kernel.prepared['tetrahedra']]
    for corner, cls in enumerate(kernel.corner_class):
        check()
        rows[corner//4][corner % 4] = values.get(cls, 0)
    for (tetrahedron, kind), value in zip(kernel.support, q):
        rows[tetrahedron][4+kind] = value
    _coordinates(kernel.prepared, rows, check)
    return rows


def sector_planar_rays(kernel, *, check=lambda: None, max_rays=None, stats=None):
    """Yield all primitive non-link standard rays, in projective-chart order.

    A limit counts begun coordinate lifts, not bit operations.  An interrupted
    generator is not a coverage certificate.  Use the callback for a work cap.
    """
    if max_rays is not None and (type(max_rays) is not int or max_rays < 0):
        raise ValueError('max_rays must be a nonnegative integer or None')
    if stats is None:
        stats = {}
    stats['emitted_rays'] = 0
    plan = sector_planar_plan(kernel, check=check, stats=stats)
    for point in plan['points']:
        check()
        if max_rays is not None and stats['emitted_rays'] >= max_rays:
            raise SearchLimit('planar ray allowance exhausted')
        rows = _projected_lift(kernel, plan, point, check)
        stats['emitted_rays'] += 1
        yield rows


def sector_planar_discovery_rays(kernel, *, check=lambda: None, max_rays=None, stats=None):
    """Q-corners first; build the complete minimum overlay only on demand.

    Every Q-corner lift is standard-extreme.  The tail omits those exact
    already-yielded points, so one ray allowance covers both stages and
    exhaustion still includes every non-link standard ray exactly once.
    Enumeration/certificate APIs keep their existing canonical ordering.
    """
    if max_rays is not None and (type(max_rays) is not int or max_rays < 0):
        raise ValueError('max_rays must be a nonnegative integer or None')
    if stats is None:
        stats = {}
    stats.update(method='planar-adaptive', hyperplanes=0, emitted_rays=0,
                 bases_attempted=0, positive_directions=0, nonextreme_directions=0,
                 corner_rays=0, overlay_refinements=0)
    plan = _section_plan(kernel, check, stats)
    corners = tuple(sorted(plan['polygon'], key=lambda point:
        (-_value(plan['chart']['forms'][0], point), point)))
    def emit(point):
        check()
        if max_rays is not None and stats['emitted_rays'] >= max_rays:
            raise SearchLimit('adaptive planar ray allowance exhausted')
        rows = _projected_lift(kernel, plan, point, check)
        stats['emitted_rays'] += 1
        stats['bases_attempted'] = stats['positive_directions'] = stats['emitted_rays']
        return rows
    for point in corners:
        rows = emit(point)
        stats['corner_rays'] += 1
        yield rows
    if plan['section_dimension'] <= 0:
        stats['points'] = len(corners)
        return
    # Resuming the generator is evidence that the corner prelude found no
    # disc.  Reuse its source chart and projected potentials for the tail.
    stats['overlay_refinements'] = 1
    _minimum_overlay(kernel, plan, check, stats)
    seen = set(corners)
    for point in plan['points']:
        if point not in seen:
            yield emit(point)


def _encoded(value):
    if isinstance(value, Fraction):
        return json_safe([value.numerator, value.denominator])
    if isinstance(value, tuple):
        return [_encoded(x) for x in value]
    if isinstance(value, list):
        return [_encoded(x) for x in value]
    if isinstance(value, dict):
        return {key: _encoded(item) for key, item in value.items()}
    return value


def certify_planar_sector(triangulation, allowed_types, *, check=lambda: None,
                          max_rays=None, source=None):
    """Complete source-bound ray list with a geometric coverage certificate."""
    from .sector_sparse import PreparedSectorSource
    if max_rays is not None and (type(max_rays) is not int or max_rays < 0):
        raise ValueError('invalid planar ray allowance')
    if source is None:
        source = PreparedSectorSource(triangulation, check=check)
    # A reused source must refer to exactly the supplied triangulation.
    if source.source_sha256 != _source_hash(triangulation):
        raise ValueError('prepared source does not match triangulation')
    kernel = source.build(allowed_types, check=check)
    stats = dict(kernel.stats, emitted_rays=0)
    plan = sector_planar_plan(kernel, check=check, stats=stats)
    rays = []
    for point in plan['points']:
        check()
        if max_rays is not None and len(rays) >= max_rays:
            return dict(status='INCONCLUSIVE', reason='planar ray allowance exhausted',
                        stats=stats)
        rays.append(_projected_lift(kernel, plan, point, check))
        stats['emitted_rays'] += 1
    certificate = dict(schema='normal-sector-planar-v1',
        source_sha256=_source_hash(triangulation),
        allowed_types=[list(pair) for pair in kernel.support],
        matching_dimension=len(kernel.basis),
        section_dimension=plan['section_dimension'],
        chart=_encoded(plan['chart']), polygon=_encoded(plan['polygon']),
        groups=_encoded(plan['groups']), rays=json_safe(rays))
    return dict(status='COMPLETE', rays=rays, certificate=certificate, stats=stats,
                scope='all non-link standard rays of this supplied sector')


def discover_in_planar_sector(triangulation, allowed_types, *, check=lambda: None,
                              max_rays=None, max_orbit_cycles=None, source=None):
    """Search the complete planar ray list using the maintained disk checker.

    A positive result uses the existing normal-sector-witness-v1 schema.
    Exhaustion excludes essential disk components of these vertex rays only.
    Neither outcome authenticates an independently supplied knot diagram.
    """
    from .normal_disk_kernel import (
        normal_compressing_disk_count, verify_normal_disk_count_certificate,
    )
    if max_orbit_cycles is not None and (
            type(max_orbit_cycles) is not int or max_orbit_cycles < 0):
        raise ValueError('invalid orbit allowance')
    result = certify_planar_sector(triangulation, allowed_types, check=check,
                                  max_rays=max_rays, source=source)
    if result['status'] != 'COMPLETE':
        return result
    stats = dict(result['stats'], orbit_queries=0)
    checks = []
    # Inspect every ray.  This avoids relying on a separate connectedness
    # theorem to skip nonpositive-Euler vectors when composing certificates.
    for index, rows in enumerate(result['rays']):
        check()
        stats['orbit_queries'] += 1
        query = normal_compressing_disk_count(triangulation, rows,
            max_cycles=max_orbit_cycles, record_certificate=True, check=check)
        if query['status'] != 'COMPLETE':
            return dict(status='INCONCLUSIVE', reason=query['reason'], stats=stats)
        proof = query['certificate']
        if not verify_normal_disk_count_certificate(triangulation, rows, proof, check=check):
            raise ArithmeticError('independent disk-component replay rejected')
        checks.append(dict(ray=index, disk_certificate=proof))
        if query['contains_compressing_disk']:
            certificate = dict(schema='normal-sector-witness-v1',
                source_sha256=_source_hash(triangulation),
                allowed_types=result['certificate']['allowed_types'],
                coordinates=rows, disk_certificate=proof)
            return dict(status='DISC_FOUND', coordinates=rows,
                        certificate=json_safe(certificate), stats=stats,
                        scope='essential disk in this supplied triangulation')
    certificate = dict(schema='normal-sector-planar-disc-scan-v1',
        source_sha256=_source_hash(triangulation),
        status='NO_VERTEX_DISC_IN_SECTOR',
        coverage=result['certificate'], checks=json_safe(checks))
    return dict(status='NO_VERTEX_DISC_IN_SECTOR', certificate=certificate,
                stats=stats, scope='these non-link standard rays only')
