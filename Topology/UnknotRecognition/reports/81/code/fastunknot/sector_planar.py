"""Exact minimum-subdivision enumeration for matching nullity at most three.

This is a supplied-sector query, not an unknot recognizer.  The projective
quadrilateral cone is a polygon, segment, point, or empty.  Convex clipping
constructs each vertex group's genuine minimum cells.  Their internal edges
are overlaid, and exactly the subdivision vertices are canonically lifted.
No supported-rank test or arrangement of inactive potential equalities is
used.  Pure vertex links are omitted.

``max_work`` bounds disclosed implementation checkpoints, not bit operations
or elapsed time.  All preparation and lifts share the allowance; a limit
raises SearchLimit and supplies no completeness certificate.  An independent
``check`` callback supports cooperative cancellation.
"""

from fractions import Fraction
from itertools import combinations

from .normal_sector import SearchLimit, _primitive, build_sector_kernel
from .normal_surface_geometry import _coordinates


class _Work:
    def __init__(self, check, maximum, stats):
        if maximum is not None and (type(maximum) is not int or maximum < 0):
            raise ValueError('max_work must be a nonnegative integer or None')
        if not callable(check):
            raise TypeError('check must be callable')
        self.check = check
        self.maximum = maximum
        self.stats = stats
        stats['work_units'] = 0

    def step(self, name='checkpoints', amount=1):
        self.check()
        used = self.stats['work_units']
        if self.maximum is not None and used + amount > self.maximum:
            raise SearchLimit('planar-sector work allowance exhausted')
        self.stats['work_units'] = used + amount
        self.stats[name] = self.stats.get(name, 0) + amount


def _dot(left, right, work):
    total = Fraction(0)
    for a, b in zip(left, right):
        work.step('projection_terms')
        total += a*b
    return total


def _value(form, point, work):
    total = form[0]
    work.step('affine_evaluations')
    for coefficient, coordinate in zip(form[1:], point):
        total += coefficient*coordinate
    return total


def _cross(a, b, c, work):
    work.step('orientation_tests')
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def _clean_polygon(points, work):
    """Normalize a cyclically ordered convex polygon, including degeneracy.

    Clipping preserves cyclic convex order.  Only consecutive duplicates
    and collinear intermediate points are removed, in linear work; a fully
    collinear polygon becomes its two extreme endpoints.
    """
    unique = []
    for point in points:
        work.step('polygon_cleanup_points')
        if not unique or point != unique[-1]:
            unique.append(point)
    if len(unique) > 1 and unique[0] == unique[-1]:
        unique.pop()
    if len(unique) < 2:
        return tuple(unique)
    if all(_cross(unique[0], unique[1], point, work) == 0
           for point in unique[2:]):
        ends = (min(unique), max(unique))
        return ends[:1] if ends[0] == ends[1] else ends
    stack = []
    for point in unique:
        while len(stack) > 1 and _cross(stack[-2], stack[-1], point, work) == 0:
            stack.pop()
        stack.append(point)
    while len(stack) > 2 and _cross(stack[-2], stack[-1], stack[0], work) == 0:
        stack.pop()
    start = 0
    while len(stack)-start > 2 and _cross(stack[-1], stack[start],
                                        stack[start+1], work) == 0:
        start += 1
    stack = stack[start:]
    first = min(range(len(stack)), key=stack.__getitem__)
    return tuple(stack[first:] + stack[:first])


def _clip_polygon(polygon, form, work):
    """Intersect a closed convex polygon with form >= 0, exactly."""
    work.step('clip_calls')
    if not polygon:
        return ()
    values = [_value(form, point, work) for point in polygon]
    if all(value >= 0 for value in values):
        return polygon
    if all(value < 0 for value in values):
        return ()
    result = []
    for index, left in enumerate(polygon):
        right = polygon[(index+1) % len(polygon)]
        a, b = values[index], values[(index+1) % len(polygon)]
        work.step('clip_edges')
        if a >= 0:
            result.append(left)
        if (a < 0 < b) or (b < 0 < a):
            scale = a/(a-b)
            result.append(tuple(x+scale*(y-x) for x, y in zip(left, right)))
    return _clean_polygon(result, work)


def _dimension(polygon):
    return -1 if not polygon else min(2, len(polygon)-1)


def _chart(kernel, work):
    """Affine coordinates on sum(q)=1 and its exact nonnegative domain."""
    basis = tuple(tuple(Fraction(x) for x in row) for row in kernel.basis)
    dimension = len(basis)
    if dimension > 3:
        raise ValueError('planar sectors require matching nullity at most three')
    if not dimension:
        return None, (), ()
    totals = [sum(row) for row in basis]
    pivot = next((i for i, total in enumerate(totals) if total), None)
    if pivot is None:
        return None, (), ()
    origin = tuple(x/totals[pivot] for x in basis[pivot])
    directions = tuple(tuple(x-total*y for x, y in zip(row, origin))
                       for i, (row, total) in enumerate(zip(basis, totals))
                       if i != pivot)
    for _ in origin:
        work.step('chart_coordinates')
    if not directions:
        domain = ((),) if all(x >= 0 for x in origin) else ()
        return origin, directions, domain
    if len(directions) == 1:
        lower, upper = None, None
        for a, b in zip(origin, directions[0]):
            work.step('section_inequalities')
            if b > 0:
                lower = max(lower, -a/b) if lower is not None else -a/b
            elif b < 0:
                upper = min(upper, -a/b) if upper is not None else -a/b
            elif a < 0:
                return origin, directions, ()
        if lower is None or upper is None:
            raise ArithmeticError('matching basis is not independent')
        domain = () if lower > upper else ((lower,), (upper,))
        if lower == upper:
            domain = domain[:1]
        return origin, directions, domain
    first, second = directions
    selected = None
    for i, j in combinations(range(len(origin)), 2):
        work.step('chart_minor_tests')
        determinant = first[i]*second[j] - first[j]*second[i]
        if determinant:
            selected = i, j, determinant
            break
    if selected is None:
        raise ArithmeticError('matching basis is not independent')
    i, j, determinant = selected
    # Every feasible q lies in [0,1]^k.  Invert two independent coordinate
    # rows to obtain a finite rational rectangle containing the entire P.
    box_points = []
    for qi in (0, 1):
        for qj in (0, 1):
            x, y = qi-origin[i], qj-origin[j]
            box_points.append(((x*second[j]-y*second[i])/determinant,
                               (first[i]*y-first[j]*x)/determinant))
    xmin, xmax = min(x for x, _ in box_points), max(x for x, _ in box_points)
    ymin, ymax = min(y for _, y in box_points), max(y for _, y in box_points)
    polygon = ((xmin, ymin), (xmax, ymin), (xmax, ymax), (xmin, ymax))
    for a, b, c in zip(origin, first, second):
        work.step('section_inequalities')
        polygon = _clip_polygon(polygon, (a, b, c), work)
        if not polygon:
            break
    return origin, directions, polygon


def _line_envelope(forms, work):
    """(anchor, intercept, slope) -> active pieces with increasing starts."""
    by_slope = {}
    for anchor, intercept, slope in forms:
        work.step('line_forms')
        prior = by_slope.get(slope)
        if prior is None or (intercept, anchor) < prior:
            by_slope[slope] = intercept, anchor
    hull = []
    for slope in sorted(by_slope, reverse=True):
        intercept, anchor = by_slope[slope]
        start = None
        while hull:
            work.step('line_hull_tests')
            _, old_intercept, old_slope, old_start = hull[-1]
            start = (intercept-old_intercept)/(old_slope-slope)
            if old_start is None or start > old_start:
                break
            hull.pop()
        if not hull:
            start = None
        hull.append((anchor, intercept, slope, start))
    return tuple(hull)


def _interpolate(left, right, value):
    return tuple(a+value*(b-a) for a, b in zip(left, right))


def _segment_groups(kernel, domain, projected, work):
    left, right = domain
    points = {left, right}
    groups = []
    bound = 2
    for group in kernel.groups:
        lines = []
        for corner in group:
            form = projected[corner]
            intercept = _value(form, left, work)
            slope = _value(form, right, work)-intercept
            lines.append((corner, intercept, slope))
        hull = _line_envelope(lines, work)
        cells = []
        bound += max(0, len(group)-1)
        for index, (corner, _, _, start) in enumerate(hull):
            work.step('line_envelope_pieces')
            stop = hull[index+1][3] if index+1 < len(hull) else None
            lo = max(Fraction(0), start) if start is not None else Fraction(0)
            hi = min(Fraction(1), stop) if stop is not None else Fraction(1)
            if lo < hi:
                ends = (_interpolate(left, right, lo),
                        _interpolate(left, right, hi))
                points.update(ends)
                cells.append(dict(corner=corner, vertices=ends))
        groups.append(dict(corners=tuple(group), cells=tuple(cells)))
    return tuple(groups), tuple(sorted(points)), bound


def _boundary_edge(a, b, domain, work):
    for index, c in enumerate(domain):
        d = domain[(index+1) % len(domain)]
        if _cross(c, d, a, work) == 0 and _cross(c, d, b, work) == 0:
            return True
    return False


def _intersection(first, second, work):
    """The unique nonparallel intersection, or None.

    Collinear overlaps create no new vertices beyond segment endpoints,
    which are inserted before this call.
    """
    work.step('segment_intersection_tests')
    a, b = first
    c, d = second
    u = b[0]-a[0], b[1]-a[1]
    v = d[0]-c[0], d[1]-c[1]
    determinant = u[0]*v[1]-u[1]*v[0]
    if not determinant:
        return None
    w = c[0]-a[0], c[1]-a[1]
    s = (w[0]*v[1]-w[1]*v[0])/determinant
    t = (w[0]*u[1]-w[1]*u[0])/determinant
    if 0 <= s <= 1 and 0 <= t <= 1:
        return a[0]+s*u[0], a[1]+s*u[1]
    return None


def _polygon_groups(kernel, domain, projected, work, stats):
    groups = []
    owners = {}
    for group_index, group in enumerate(kernel.groups):
        representatives = {}
        for corner in group:
            form = projected[corner]
            representatives[form] = min(corner, representatives.get(form, corner))
        forms = sorted((corner, form) for form, corner in representatives.items())
        cells = []
        for corner, form in forms:
            cell = domain
            work.step('candidate_minimum_cells')
            for other, compared in forms:
                if other == corner:
                    continue
                difference = tuple(x-y for x, y in zip(compared, form))
                cell = _clip_polygon(cell, difference, work)
                if not cell:
                    break
            if _dimension(cell) != 2:
                if cell:
                    stats['discarded_lower_dimensional_cells'] += 1
                continue
            stats['minimum_cells'] += 1
            stats['max_cell_vertices'] = max(stats['max_cell_vertices'], len(cell))
            cells.append(dict(corner=corner, vertices=cell))
            for index, a in enumerate(cell):
                b = cell[(index+1) % len(cell)]
                work.step('minimum_cell_edges')
                if not _boundary_edge(a, b, domain, work):
                    segment = tuple(sorted((a, b)))
                    owners.setdefault(segment, set()).add(group_index)
        if not cells:
            raise ArithmeticError('nonempty polygon has no full minimum cell')
        groups.append(dict(corners=tuple(group), cells=tuple(cells)))
    segments = tuple(sorted(owners))
    points = set(domain)
    for a, b in segments:
        points.add(a)
        points.add(b)
    pair_bound = 0
    # Edges belonging to a common convex subdivision cannot cross in their
    # relative interiors.  Skipping those pairs also preserves the linear
    # one-group output bound.
    if len(groups) > 1:
        for first, second in combinations(segments, 2):
            work.step('segment_pair_screenings')
            if owners[first] & owners[second]:
                continue
            pair_bound += 1
            point = _intersection(first, second, work)
            if point is not None:
                points.add(point)
    stats['skeleton_segments'] = len(segments)
    bound = len(domain)+2*len(segments)+pair_bound
    return tuple(groups), segments, tuple(sorted(points)), bound


def _plan(kernel, work, stats):
    stats.update(method='planar', matching_dimension=len(kernel.basis),
                 section_dimension=-1, potential_projections=0,
                 minimum_cells=0, discarded_lower_dimensional_cells=0,
                 max_cell_vertices=0, skeleton_segments=0,
                 overlay_points=0, output_bound=0)
    work.step('plan_checkpoints')
    origin, directions, domain = _chart(kernel, work)
    dimension = _dimension(domain)
    stats['section_dimension'] = dimension
    result = dict(matching_dimension=len(kernel.basis), section_dimension=dimension,
                  q_origin=origin, q_directions=directions, domain=domain,
                  projected_potentials={}, groups=(), skeleton=(), points=())
    if not domain:
        return result
    projected = {}
    for corner in kernel.classes:
        potential = kernel.potentials[corner]
        projected[corner] = tuple(_dot(potential, direction, work)
                                  for direction in (origin,)+directions)
        stats['potential_projections'] += 1+len(directions)
    result['projected_potentials'] = projected
    if dimension == 0:
        points, bound = domain, 1
    elif dimension == 1:
        groups, points, bound = _segment_groups(kernel, domain, projected, work)
        result['groups'] = groups
        stats['minimum_cells'] = sum(len(group['cells']) for group in groups)
    else:
        groups, skeleton, points, bound = _polygon_groups(
            kernel, domain, projected, work, stats)
        result.update(groups=groups, skeleton=skeleton)
    result['points'] = points
    stats['overlay_points'] = len(points)
    stats['output_bound'] = bound
    return result


def sector_planar_plan(kernel, *, check=lambda: None, max_work=None, stats=None):
    """Return the exact rational projective minimum subdivision's vertices.

    ``q_origin + sum(point[j] * q_directions[j])`` recovers a normalized
    quadrilateral vector.  ``domain`` and all cell vertices use this chart.
    ``points`` is the full set of subdivision vertices, in sorted order.
    Cell records contain original corner anchors; retained polygon cells
    have nonempty interior.  A raw three-dimensional kernel can still have
    an empty, zero-dimensional, or one-dimensional nonnegative section.

    This is a producer, not an independent completeness verifier.
    """
    if stats is None:
        stats = {}
    return _plan(kernel, _Work(check, max_work, stats), stats)


def _projected_lift(kernel, plan, point, q, work):
    scale = sum(q)
    values = {corner: _value(form, point, work)
              for corner, form in plan['projected_potentials'].items()}
    for group in kernel.groups:
        minimum = min(values[corner] for corner in group)
        for corner in group:
            work.step('lift_triangle_classes')
            value = scale*(values[corner]-minimum)
            if value < 0 or value.denominator != 1:
                raise ArithmeticError('projected lift is not nonnegative integral')
            values[corner] = int(value)
    rows = [[0]*7 for _ in kernel.prepared['tetrahedra']]
    for corner, contracted in enumerate(kernel.corner_class):
        work.step('lift_triangle_corners')
        rows[corner//4][corner % 4] = values.get(contracted, 0)
    for (tetrahedron, typ), count in zip(kernel.support, q):
        work.step('lift_quadrilaterals')
        rows[tetrahedron][4+typ] = count
    _coordinates(kernel.prepared, rows, lambda: work.step('coordinate_checkpoints'))
    return rows


def _rays(kernel, work, stats):
    stats.update(candidate_lifts=0, emitted_rays=0, projected_lifts=0)
    plan = _plan(kernel, work, stats)
    for point in plan['points']:
        work.step('candidate_lifts')
        values = list(plan['q_origin'])
        for coordinate, direction in zip(point, plan['q_directions']):
            for i, value in enumerate(direction):
                work.step('output_quadrilateral_terms')
                values[i] += coordinate*value
        q = _primitive(values)
        if not any(q) or any(value < 0 for value in q):
            raise ArithmeticError('invalid projective subdivision vertex')
        rows = _projected_lift(kernel, plan, point, q, work)
        if max(value for row in rows for value in row) > 4**len(kernel.support):
            raise ArithmeticError('primitive extreme-ray height bound failed')
        stats['projected_lifts'] += 1
        stats['emitted_rays'] += 1
        yield rows


def sector_planar_rays(kernel, *, check=lambda: None, max_work=None, stats=None):
    """Yield every primitive nonlink standard ray of a supplied kernel.

    The matching nullity must be at most three.  All actual feasible section
    dimensions are supported.  The work limit applies throughout plan
    construction and full coordinate output.  Exhaustion or cancellation
    interrupts the iterator; a partial list proves no completeness claim.
    """
    if stats is None:
        stats = {}
    yield from _rays(kernel, _Work(check, max_work, stats), stats)


def enumerate_planar_sector(triangulation, allowed_types, *,
                            check=lambda: None, max_work=None):
    """Return (complete ray list, stats), including kernel construction.

    The same work allowance and callback span source geometry, kernel
    construction, clipping, overlay, lifting, and coordinate validation.
    No default recognition policy is changed.  Raises SearchLimit on an
    allowance exhaustion, rather than returning a partial complete list.
    """
    stats = {}
    work = _Work(check, max_work, stats)
    kernel = build_sector_kernel(triangulation, allowed_types,
                                check=lambda: work.step('kernel_checkpoints'))
    stats.update(kernel.stats)
    rays = list(_rays(kernel, work, stats))
    return rays, stats
