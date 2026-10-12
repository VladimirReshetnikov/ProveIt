"""Exact normal vertex-disc search by connected cancellation profiles.

The source must have one global vertex and rank-one cocycles.  If b is
the primitive coherent edge vector, completeness is promised for standard
vertex discs with w=b+u, at most max_defect positive increments, and at
most max_components components of their tetrahedron-incidence graph.

This extends the incoming normal_weight_defect module.  It does not change
the maintained recognizer, certify an input diagram's exterior, or certify
a globally negative knot verdict.  Positive outputs use the incoming
polynomial rank-and-boundary gate and independent certificate replay.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import gcd

from .normal_cocycle import _rank_one_cocycle_seed_details
from .normal_sector import _primitive, SearchLimit
from .normal_surface_geometry import _coordinates, _edge, NormalOrbitError
from .normal_weight_defect import local_coordinates_from_weights, _global_hyperplanes
from .normal_vertex_gate import (
    produce_vertex_disc_certificate, verify_vertex_disc_certificate,
)


class _ClusterLimit(SearchLimit):
    pass


def _nonnegative(value, name, optional=False):
    if optional and value is None:
        return
    if type(value) is not int or value < 0:
        raise ValueError(name + ' must be a nonnegative integer'
                         + (' or None' if optional else ''))


class _Budget:
    def __init__(self, check, limits, stats):
        self.external = check
        self.limits = limits
        self.stats = stats

    def __call__(self):
        self.external()
        cap = self.limits.get('work')
        if cap is not None and self.stats['work'] >= cap:
            raise _ClusterLimit('cluster work allowance exhausted')
        self.stats['work'] += 1

    def begin(self, name):
        self()
        cap = self.limits.get(name)
        if cap is not None and self.stats[name] >= cap:
            raise _ClusterLimit('cluster ' + name + ' allowance exhausted')
        self.stats[name] += 1


def _square_solve(matrix, rhs, check):
    """Rational Gaussian elimination, or None for a singular square matrix."""
    n = len(matrix)
    if len(rhs) != n or any(len(row) != n for row in matrix):
        raise ValueError('square system shape mismatch')
    a = [[Fraction(x) for x in row] + [Fraction(y)]
         for row, y in zip(matrix, rhs)]
    for column in range(n):
        check()
        pivot = next((r for r in range(column, n) if a[r][column]), None)
        if pivot is None:
            return None
        a[column], a[pivot] = a[pivot], a[column]
        value = a[column][column]
        a[column] = [x / value for x in a[column]]
        for r in range(n):
            check()
            if r != column and a[r][column]:
                value = a[r][column]
                a[r] = [x - value*y for x, y in zip(a[r], a[column])]
    return tuple(row[-1] for row in a)


@dataclass
class ClusterContext:
    triangulation: dict
    prepared: dict
    baseline_rows: tuple
    baseline: dict
    baseline_euler: int
    edges: tuple
    stars: dict
    graph: dict
    planes: tuple
    row_incidence: dict
    face_occurrences: dict
    degree: int


@dataclass(frozen=True)
class Profile:
    support: tuple
    increments: tuple
    replacements: tuple
    euler_change: int


def prepare_clusters(triangulation, *, check=lambda: None):
    """Prepare sparse equations and edge stars; never mutate the source."""
    seed, prepared = _rank_one_cocycle_seed_details(triangulation, check=check)
    if prepared['vertices'] != 1:
        raise NormalOrbitError('cluster discovery requires one global vertex')
    data = _coordinates(prepared, seed['coordinates'], check)
    edges = tuple(sorted(data['weights']))
    stars = {e: set() for e in edges}
    graph = {e: set() for e in edges}
    for t in range(len(prepared['tetrahedra'])):
        check()
        local = set(prepared['edge_roots'][6*t:6*t+6])
        for e in local:
            check()
            stars[e].add(t)
            graph[e].update(local - {e})
    planes = _global_hyperplanes(prepared, check)
    row_incidence = {e: set() for e in edges}
    for j, plane in enumerate(planes):
        check()
        for e, coefficient in plane:
            row_incidence[e].add(j)
    counts = {e: 0 for e in edges}
    faces = prepared['boundary_faces'] + [(t, f) for t, f, _, _, _ in prepared['pairs']]
    for t, f in faces:
        check()
        for a, b in combinations((v for v in range(4) if v != f), 2):
            counts[prepared['edge_roots'][_edge(t, a, b)]] += 1
    return ClusterContext(triangulation, prepared,
        tuple(tuple(row) for row in seed['coordinates']), dict(data['weights']),
        data['euler_characteristic'], edges,
        {e: frozenset(value) for e, value in stars.items()},
        {e: frozenset(value) for e, value in graph.items()},
        planes, {e: frozenset(value) for e, value in row_incidence.items()},
        counts, max(map(len, stars.values()), default=0))


def support_components(context, support, *, check=lambda: None):
    """Return the components induced by a supplied set of global edge labels."""
    remaining = set(support)
    if any(e not in context.graph for e in remaining):
        raise ValueError('unknown edge in support')
    answer = []
    while remaining:
        check()
        root = min(remaining)
        remaining.remove(root)
        component, queue = {root}, [root]
        for e in queue:
            check()
            for f in sorted(context.graph[e] & remaining):
                remaining.remove(f)
                component.add(f)
                queue.append(f)
        answer.append(tuple(sorted(component)))
    return tuple(answer)


def _connected_levels(context, maximum, check):
    """Connected supports by size; each level is deduplicated before use."""
    level = {(e,) for e in context.edges}
    for size in range(1, maximum+1):
        check()
        yield size, tuple(sorted(level))
        if size == maximum:
            return
        following = set()
        for support in sorted(level):
            check()
            present = set(support)
            for e in support:
                for f in sorted(context.graph[e]):
                    check()
                    if f > support[0] and f not in present:
                        following.add(tuple(sorted(present | {f})))
        level = following


def _support_rows(context, support, check):
    indices = set()
    for e in support:
        check()
        indices.update(context.row_incidence[e])
    rows = set()
    for j in sorted(indices):
        check()
        plane = dict(context.planes[j])
        restricted = tuple(plane.get(e, 0) for e in support)
        constant = sum(value*context.baseline[e] for e, value in plane.items())
        # At a promised point every increment is strictly positive.  A sum
        # of terms of one sign cannot be zero.  Such a row also cannot
        # support a strictly positive homogeneous exceptional ray.
        if ((constant >= 0 and all(value >= 0 for value in restricted))
                or (constant <= 0 and all(value <= 0 for value in restricted))):
            continue
        normalized = _primitive((constant,) + restricted)
        rows.add((normalized[1:], normalized[0]))
    return sorted(rows)


def _make_profile(context, support, increments, budget, stats):
    changed = dict(zip(support, increments))
    touched = set()
    for e in support:
        budget()
        touched.update(context.stars[e])
    replacements = []
    delta = sum(Fraction(value*(2-context.face_occurrences[e]), 2)
                for e, value in changed.items())
    for t in sorted(touched):
        budget()
        stats['local_reconstructions'] += 1
        weights = [context.baseline[e]+changed.get(e, 0)
                   for e in context.prepared['edge_roots'][6*t:6*t+6]]
        try:
            row = local_coordinates_from_weights(weights)
        except NormalOrbitError:
            return None
        if any(value.denominator != 1 for value in row):
            raise ArithmeticError('even increments broke normal-coordinate parity')
        row = tuple(map(int, row))
        replacements.append((t, row))
        delta += sum(row)-sum(context.baseline_rows[t])
    if delta.denominator != 1:
        raise ArithmeticError('integral local profile has nonintegral Euler change')
    return Profile(support, tuple(increments), tuple(replacements), int(delta))


def _profiles(context, support, rows, budget, stats):
    seen = set()
    size = len(support)
    for selected in combinations(rows, size):
        budget.begin('systems')
        stats['affine_systems'] += 1
        increments = _square_solve([row for row, _ in selected],
                                   [-constant for _, constant in selected], budget)
        if increments is None:
            continue
        stats['nonsingular_systems'] += 1
        if any(x <= 0 or x.denominator != 1 or int(x) % 2 for x in increments):
            continue
        increments = tuple(map(int, increments))
        if increments in seen:
            stats['duplicate_solutions'] += 1
            continue
        seen.add(increments)
        profile = _make_profile(context, support, increments, budget, stats)
        if profile is not None:
            stats['profiles'] += 1
            yield profile


def _exceptional(context, support, rows, budget, stats):
    """Homogeneous coordinate rays, including the dependent-baseline case."""
    if any(context.baseline[e] for e in context.edges if e not in support):
        return
    size = len(support)
    seen = set()
    for selected in combinations(rows, size-1):
        budget.begin('systems')
        stats['homogeneous_systems'] += 1
        matrix = [row for row, _ in selected] + [(1,)*size]
        values = _square_solve(matrix, [0]*(size-1)+[1], budget)
        if values is None or any(value <= 0 for value in values):
            continue
        if values in seen:
            stats['duplicate_solutions'] += 1
            continue
        seen.add(values)
        weights = dict.fromkeys(context.edges, Fraction(0))
        weights.update(zip(support, values))
        assembled = []
        valid = True
        for t in range(len(context.baseline_rows)):
            budget()
            stats['local_reconstructions'] += 1
            try:
                assembled.append(local_coordinates_from_weights([
                    weights[e] for e in context.prepared['edge_roots'][6*t:6*t+6]]))
            except NormalOrbitError:
                valid = False
                break
        if valid:
            flat = _primitive(x for row in assembled for x in row)
            yield [list(flat[7*t:7*t+7]) for t in range(len(assembled))]


def _profile_products(profiles, total_size, max_components, context, budget, stats):
    """Yield each nonadjacent profile product of the prescribed total size."""
    def walk(start, remaining, chosen, forbidden):
        if remaining == 0:
            budget.begin('combinations')
            yield tuple(chosen)
            return
        if len(chosen) == max_components:
            return
        for i in range(start, len(profiles)):
            budget()
            stats['profile_extensions'] += 1
            profile = profiles[i]
            if len(profile.support) > remaining:
                # Profiles are appended in increasing support size.  Scanning
                # larger profiles at every prefix would spoil the degree bound.
                break
            if any(e in forbidden for e in profile.support):
                stats['incompatible_extensions'] += 1
                continue
            enlarged = set(forbidden)
            for e in profile.support:
                budget()
                enlarged.add(e)
                enlarged.update(context.graph[e])
            yield from walk(i+1, remaining-len(profile.support),
                            chosen+[profile], enlarged)
    yield from walk(0, total_size, [], set())


def _actual_defect(context, rows, maximum, components, budget):
    data = _coordinates(context.prepared, rows, budget)
    increments = {e: data['weights'][e]-context.baseline[e] for e in context.edges}
    if any(value < 0 or value % 2 for value in increments.values()):
        return None
    support = tuple(e for e in context.edges if increments[e])
    if len(support) > maximum:
        return None
    parts = support_components(context, support, check=budget)
    if len(parts) > components:
        return None
    return support, parts, data


def _candidate_iterator(context, maximum, components, budget, stats):
    seen = set()

    def retain(rows):
        flat = _primitive(x for row in rows for x in row)
        if flat in seen:
            stats['duplicate_candidates'] += 1
            return None
        seen.add(flat)
        rows = [list(flat[7*t:7*t+7]) for t in range(len(rows))]
        actual = _actual_defect(context, rows, maximum, components, budget)
        if actual is None:
            return None
        stats['candidates'] += 1
        return rows, actual

    budget.begin('combinations')
    initial = retain([list(row) for row in context.baseline_rows])
    if initial is not None:
        yield initial
    if components == 0:
        return
    profiles = []
    for size, supports in _connected_levels(context, maximum, budget):
        for support in supports:
            budget.begin('supports')
            rows = _support_rows(context, support, budget)
            profiles.extend(_profiles(context, support, rows, budget, stats))
            for assembled in _exceptional(context, support, rows, budget, stats):
                budget.begin('combinations')
                value = retain(assembled)
                if value is not None:
                    yield value
        for selected in _profile_products(profiles, size, components, context, budget, stats):
            assembled = [list(row) for row in context.baseline_rows]
            touched = set()
            euler = context.baseline_euler
            for profile in selected:
                budget()
                euler += profile.euler_change
                for t, row in profile.replacements:
                    if t in touched:
                        raise ArithmeticError('nonadjacent profiles shared a tetrahedron')
                    touched.add(t)
                    assembled[t] = list(row)
            # The local Euler formula is checked independently before scaling.
            data = _coordinates(context.prepared, assembled, budget)
            if data['euler_characteristic'] != euler:
                raise ArithmeticError('local profile Euler sum disagreed')
            value = retain(assembled)
            if value is not None:
                yield value


def _run(triangulation, max_defect, max_components, limits, check, collect):
    _nonnegative(max_defect, 'max_defect')
    if max_components is None:
        max_components = max_defect
    _nonnegative(max_components, 'max_components')
    max_components = min(max_components, max_defect)
    for name, value in limits.items():
        _nonnegative(value, 'max_'+name, optional=True)
    stats = {name: 0 for name in (
        'work', 'supports', 'systems', 'combinations', 'affine_systems',
        'homogeneous_systems', 'nonsingular_systems', 'duplicate_solutions',
        'profiles', 'local_reconstructions', 'profile_extensions',
        'incompatible_extensions', 'candidates', 'duplicate_candidates',
        'gate_queries', 'positive_replays')}
    stats.update(max_defect=max_defect, max_components=max_components)
    budget = _Budget(check, limits, stats)
    candidates = []
    try:
        context = prepare_clusters(triangulation, check=budget)
        if max_defect > len(context.edges):
            raise ValueError('max_defect exceeds the number of global edges')
        stats.update(tetrahedra=len(context.baseline_rows), edges=len(context.edges),
                     edge_degree=context.degree, hyperplanes=len(context.planes))
        for rows, (support, parts, data) in _candidate_iterator(
                context, max_defect, max_components, budget, stats):
            if collect:
                candidates.append(rows)
                continue
            if data['euler_characteristic'] != 1:
                continue
            budget()
            stats['gate_queries'] += 1
            proof = produce_vertex_disc_certificate(triangulation, rows, check=budget)
            if proof is None:
                continue
            if not verify_vertex_disc_certificate(triangulation, rows, proof, check=budget):
                raise ArithmeticError('independent vertex-disc replay rejected')
            stats['positive_replays'] += 1
            return dict(status='DISC_FOUND', coordinates=rows, certificate=proof,
                        cancellation_edges=list(support),
                        cancellation_components=[list(part) for part in parts], stats=stats,
                        trust='essential vertex disc in this supplied triangulation only')
    except _ClusterLimit as exc:
        answer = dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
        if collect:
            answer['coordinates'] = candidates
        return answer
    if collect:
        return dict(status='COMPLETE', coordinates=candidates, stats=stats)
    return dict(status='NO_VERTEX_DISC_IN_CANCELLATION_CLASS', stats=stats,
                trust='restricted search exhaustion only; no knot verdict '
                      'or independent exhaustion certificate')


def cluster_defect_search(triangulation, *, max_defect, max_components=None,
                         max_work=None, max_supports=None, max_systems=None,
                         max_combinations=None, check=lambda: None):
    """Find a promised vertex disc, or return restricted exhaustion/inconclusive.

    Work counts cooperative checkpoints, supports counts begun connected-set
    profiles, systems counts all begun square solves (including singular
    ones), and combinations counts complete candidate products, the coherent
    attempt, and exceptional directions.  Limits are global for the query.
    External cancellation propagates, including ValueError or SearchLimit.
    """
    return _run(triangulation, max_defect, max_components,
                dict(work=max_work, supports=max_supports, systems=max_systems,
                     combinations=max_combinations), check, False)


def enumerate_cluster_candidates(triangulation, *, max_defect, max_components=None,
                                 max_work=None, max_supports=None, max_systems=None,
                                 max_combinations=None, check=lambda: None):
    """Return admissible candidates with the promised unsigned defect bounds.

    This may include nonvertex surfaces.  Every promised standard vertex
    meridian is included.  A capped list is explicitly INCONCLUSIVE and is
    not an exhaustive set.  Coordinates are primitive standard vectors.
    """
    return _run(triangulation, max_defect, max_components,
                dict(work=max_work, supports=max_supports, systems=max_systems,
                     combinations=max_combinations), check, True)
