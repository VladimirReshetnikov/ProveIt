"""Exact standard-ray enumeration when matching nullity is at most two.

The normalized quadrilateral cone is empty, a point, or an interval.  On an
interval, canonical triangle coordinates change linear formula only where a
vertex's minimum corner potential changes.  Those actual lower-envelope
breakpoints, together with the interval endpoints, are exactly the non-link
standard rays.  This module forms neither pairwise potential hyperplanes nor
supported-rank tests.  It does not decide the topology of an emitted surface.
"""

from fractions import Fraction

from .normal_sector import SearchLimit, _primitive
from .normal_surface_geometry import _coordinates


def _dot(left, right, check):
    check()
    sparse_dot=getattr(left,'dot',None)
    if sparse_dot is not None:return sparse_dot(right)
    return sum(a * b for a, b in zip(left, right))


def _unit_section(basis, check):
    """Return q(s)=a+s*b and its closed nonnegative interval, or None.

    The basis must consist of two independent rational rows.  Normalization
    uses sum(q)=1, which meets every nonzero nonnegative ray exactly once.
    A section with equal endpoints is retained: the feasible cone can have
    smaller dimension than its ambient matching kernel.
    """
    totals = [sum(row) for row in basis]
    selected = next((i for i, value in enumerate(totals) if value), None)
    if selected is None:
        return None
    other = 1 - selected
    a = tuple(Fraction(x, totals[selected]) for x in basis[selected])
    b = tuple(y - totals[other] * x for x, y in zip(a, basis[other]))
    lower, upper = None, None
    for value, direction in zip(a, b):
        check()
        if direction > 0:
            bound = -value / direction
            lower = bound if lower is None else max(lower, bound)
        elif direction < 0:
            bound = -value / direction
            upper = bound if upper is None else min(upper, bound)
        elif value < 0:
            return None
    # sum(b)=0 and b!=0 force both signs, hence a bounded interval.
    if lower is None or upper is None:
        raise ArithmeticError('matching basis is not independent')
    if lower > upper:
        return None
    return a, b, lower, upper


def _lower_envelope(lines, check=lambda: None):
    """Return an exact lower hull of affine lines (slope, intercept).

    Each returned triple is (slope, intercept, start).  The first start is
    None, denoting negative infinity; every subsequent start is rational and
    strictly increasing.  Parallel lines retain their smallest intercept.
    Coincident lines and lines attaining the minimum at a single point need
    no separate piece.  The breakpoint itself remains represented.
    """
    intercepts = {}
    for slope, intercept in lines:
        check()
        slope, intercept = Fraction(slope), Fraction(intercept)
        if slope not in intercepts or intercept < intercepts[slope]:
            intercepts[slope] = intercept
    hull = []
    for slope in sorted(intercepts, reverse=True):
        check()
        intercept = intercepts[slope]
        start = None
        while hull:
            check()
            old_slope, old_intercept, old_start = hull[-1]
            start = (intercept - old_intercept) / (old_slope - slope)
            if old_start is None or start > old_start:
                break
            hull.pop()
        if not hull:
            start = None
        hull.append((slope, intercept, start))
    return tuple(hull)


def sector_envelope_plan(kernel, *, check=lambda: None, stats=None):
    """Return an exact normalized section and its true minimum-fan breaks.

    ``groups`` records a corner representative for every lower-envelope
    piece with nonempty interior in the feasible interval.  Its breakpoint
    list lies strictly inside that interval.  These small records can be
    encoded for separate coverage verification; this function is a producer,
    not an independent verifier.  Fraction values are deliberately preserved.
    """
    if len(kernel.basis) > 2:
        raise ValueError('sector envelope requires matching nullity at most two')
    if stats is None:
        stats = {}
    stats.update(envelope_groups=0, envelope_lines=0, envelope_hull_lines=0,
                 envelope_breakpoints=0, output_bound=0, potential_projections=0)
    dimension = len(kernel.basis)
    stats['matching_dimension'] = dimension
    stats['section_dimension'] = -1
    result = dict(matching_dimension=dimension, section_dimension=-1,
                  q_origin=None, q_direction=None, lower=None, upper=None,
                  parameters=(), groups=(), projected_potentials={})
    check()
    if dimension == 0:
        return result
    if dimension == 1:
        q = _primitive(kernel.basis[0])
        if any(q) and all(x >= 0 for x in q):
            stats['section_dimension'] = 0
            stats['output_bound'] = 1
            total = sum(q)
            result.update(section_dimension=0,
                q_origin=tuple(Fraction(x, total) for x in q),
                q_direction=(Fraction(0),) * len(q), lower=Fraction(0),
                upper=Fraction(0), parameters=(Fraction(0),))
        return result
    section = _unit_section(kernel.basis, check)
    if section is None:
        return result
    a, b, lower, upper = section
    result.update(q_origin=a, q_direction=b, lower=lower, upper=upper)
    if lower == upper:
        stats['section_dimension'] = 0
        stats['output_bound'] = 1
        result.update(section_dimension=0, parameters=(lower,))
        return result
    stats['section_dimension'] = 1
    positions = {lower, upper}
    bound = 2
    groups = []
    projected = {}
    for group in kernel.groups:
        check()
        corners = {}
        for corner in group:
            line = (_dot(kernel.potentials[corner], b, check),
                    _dot(kernel.potentials[corner], a, check))
            projected[corner] = (line[1], line[0])
            stats['potential_projections'] += 2
            corners[line] = min(corner, corners.get(line, corner))
        lines = list(corners)
        hull = _lower_envelope(lines, check)
        stats['envelope_groups'] += 1
        stats['envelope_lines'] += len(group)
        stats['envelope_hull_lines'] += len(hull)
        bound += max(0, len(group) - 1)
        active, breaks = [], []
        for index, (slope, intercept, start) in enumerate(hull):
            check()
            end = hull[index + 1][2] if index + 1 < len(hull) else None
            if ((end is None or lower < end)
                    and (start is None or start < upper)):
                active.append(corners[(slope, intercept)])
                if start is not None and lower < start < upper:
                    breaks.append(start)
            if start is not None and lower < start < upper:
                positions.add(start)
        groups.append(dict(vertex=kernel.prepared['vertex_roots'][group[0]],
                           corners=tuple(active), breakpoints=tuple(breaks)))
    stats['envelope_breakpoints'] = len(positions) - 2
    stats['output_bound'] = bound
    result.update(section_dimension=1, parameters=tuple(sorted(positions)),
                  groups=tuple(groups), projected_potentials=projected)
    return result


def _projected_lift(kernel, plan, position, q, check):
    """Lift from already projected affine potentials in O(t+p+k) work."""
    scale = sum(q)
    values = {}
    for corner, (intercept, slope) in plan['projected_potentials'].items():
        check()
        values[corner] = intercept + position * slope
    for group in kernel.groups:
        minimum = min(values[c] for c in group)
        for corner in group:
            value = scale * (values[corner] - minimum)
            if value.denominator != 1 or value < 0:
                raise ArithmeticError('projected lift is not nonnegative integral')
            values[corner] = int(value)
    rows = [[0] * 7 for _ in kernel.prepared['tetrahedra']]
    for corner, group in enumerate(kernel.corner_class):
        check()
        rows[corner // 4][corner % 4] = values.get(group, 0)
    for (tetrahedron, typ), count in zip(kernel.support, q):
        rows[tetrahedron][4 + typ] = count
    _coordinates(kernel.prepared, rows, check)
    return rows


def sector_envelope_rays(kernel, *, check=lambda: None, max_bases=None,
                         stats=None):
    """Yield exactly the primitive non-link standard rays for nullity <= 2.

    ``max_bases`` counts candidate rays whose full lift has begun.  Unlike the
    arrangement method, no nonextreme candidates or redundant bases are
    attempted.  Exhaustion raises the existing SearchLimit before another
    lift starts.  Callers must not infer absence from a partial iteration.

    For p retained corner potentials, lower hull construction and all full
    lifts use O(pk + p log p + R(t+p+k)) exact arithmetic operations, where
    R <= 2 + sum_v (p_v - 1) <= 4k+2 is the number of rays.  Storage beyond
    the supplied kernel and one emitted vector is O(p+k).  The normalized
    affine potentials are projected once and reused by every full lift.
    """
    if len(kernel.basis) > 2:
        raise ValueError('sector envelope requires matching nullity at most two')
    if max_bases is not None and (type(max_bases) is not int or max_bases < 0):
        raise ValueError('max_bases must be a nonnegative integer or None')
    if stats is None:
        stats = {}
    stats.update(method='envelope', bases_attempted=0, positive_directions=0,
                 nonextreme_directions=0, emitted_rays=0, hyperplanes=0,
                 envelope_groups=0, envelope_lines=0, envelope_hull_lines=0,
                 envelope_breakpoints=0, output_bound=0, projected_lifts=0)
    check()
    plan = sector_envelope_plan(kernel, check=check, stats=stats)
    a, b = plan['q_origin'], plan['q_direction']
    for position in plan['parameters']:
        check()
        if max_bases is not None and stats['bases_attempted'] >= max_bases:
            raise SearchLimit('candidate-basis allowance exhausted')
        stats['bases_attempted'] += 1
        q = _primitive(x + position * y for x, y in zip(a, b))
        stats['positive_directions'] += 1
        if plan['section_dimension'] == 1:
            rows = _projected_lift(kernel, plan, position, q, check)
            stats['projected_lifts'] += 1
        else:
            rows = kernel.lift(q, check)
        if max(x for row in rows for x in row) > 4 ** len(kernel.support):
            raise ArithmeticError('primitive extreme-ray height bound failed')
        stats['emitted_rays'] += 1
        yield rows
