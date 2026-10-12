"""Exact normal-disc discovery in small homogeneous edge-weight spaces.

For a finite one-vertex triangulation with first Betti number one, let b be
the absolute value of its primitive integral cocycle.  For a selected set F
of global edges, retain the space span(b, {unit_e: e in F}) throughout the
search.  Its dimension is at most |F|+1, even if quadrilaterals occur in every
tetrahedron.  Arrangement intersections recover every standard vertex normal
surface whose edge weights belong to this space; additional rays are harmless.

Every reported disc is independently replayed by the existing native disc
checker.  Exhaustion is a restricted vertex-disc statement, with no supplied
knot-diagram correspondence and no claim that all discs have small defect.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import gcd

from .normal_cocycle import _rank_one_cocycle_seed_details
from .normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from .normal_sector import _nullspace, _primitive, SearchLimit
from .normal_surface_geometry import (
    _coordinates, _edge, _EDGES, NormalOrbitError,
)


def local_coordinates_from_weights(weights):
    """Reconstruct seven rational coordinates from six local edge weights.

    Edge order is 01,02,03,12,13,23.  The largest two opposite-edge sums
    must agree.  Triangle counts are the minima of their three face-corner
    arc counts.  Invalid metrics are rejected; parity is not required here,
    since an entire rational ray is scaled to primitive integral coordinates.
    """
    if (not isinstance(weights, (list, tuple)) or len(weights) != 6
            or any(type(x) not in (int, Fraction) or x < 0 for x in weights)):
        raise NormalOrbitError('expected six nonnegative rational edge weights')
    weights = [Fraction(x) for x in weights]
    indexed = {edge: value for edge, value in zip(_EDGES, weights)}

    def weight(a, b):
        return indexed[tuple(sorted((a, b)))]

    sums = [weights[0]+weights[5], weights[1]+weights[4],
            weights[2]+weights[3]]
    maximum = max(sums)
    if sums.count(maximum) < 2:
        raise NormalOrbitError('largest opposite-edge sums must agree')
    quadrilaterals = [(maximum-value)/2 for value in sums]
    triangles = []
    for vertex in range(4):
        arcs = [(weight(vertex, a)+weight(vertex, b)-weight(a, b))/2
                for a, b in combinations((v for v in range(4) if v != vertex), 2)]
        if min(arcs) < 0:
            raise NormalOrbitError('normal face triangle inequality fails')
        triangles.append(min(arcs))
    return triangles + quadrilaterals


def _limit(value, name):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError(name+' must be a nonnegative integer or None')


def _one_vertex_data(triangulation, check):
    seed, prepared = _rank_one_cocycle_seed_details(triangulation, check=check)
    if prepared['vertices'] != 1:
        raise NormalOrbitError('edge-defect discovery requires one global vertex')
    baseline = _coordinates(prepared, seed['coordinates'], check)['weights']
    return prepared, baseline


@dataclass
class WeightSubspace:
    """An injective edge-coordinate image and its defining arrangement."""

    prepared: dict
    edges: tuple
    defect_edges: tuple
    forms: tuple
    hyperplanes: tuple
    dimension: int
    raw_hyperplanes: int


def _build_subspace(prepared, baseline, defect_edges, check):
    edges = tuple(sorted(baseline))
    if (not isinstance(defect_edges, (list, tuple))
            or any(type(e) is not int or e not in baseline for e in defect_edges)
            or len(set(defect_edges)) != len(defect_edges)):
        raise ValueError('defect_edges must be distinct global edge labels')
    selected = tuple(sorted(defect_edges))
    index = {edge: i for i, edge in enumerate(selected)}
    # If b is supported in F, its column is dependent and must be dropped.
    # The resulting image is still exactly span(b, {unit_e: e in F}).
    keep_baseline = any(baseline[e] and e not in index for e in edges)
    dimension = len(selected)+int(keep_baseline)
    if dimension == 0:
        raise ArithmeticError('a rank-one cocycle has a nonzero absolute vector')
    forms = {}
    for edge in edges:
        check()
        forms[edge] = ((baseline[edge],) if keep_baseline else ()) + tuple(
            int(edge == selected[i]) for i in range(len(selected)))
    planes = set()
    raw_count = 0

    def add(row):
        nonlocal raw_count
        check()
        raw_count += 1
        normal = _primitive(row)
        if any(normal):
            planes.add(normal)

    for form in forms.values():
        add(form)
    for tetrahedron in range(len(prepared['tetrahedra'])):
        local = {edge: forms[prepared['edge_roots'][_edge(tetrahedron, *edge)]]
                 for edge in _EDGES}

        def form(a, b):
            return local[tuple(sorted((a, b)))]

        opposite = [tuple(a+b for a, b in zip(form(0, v), form(*pair)))
                    for v, pair in ((1, (2, 3)), (2, (1, 3)), (3, (1, 2)))]
        for a, b in combinations(opposite, 2):
            add(tuple(x-y for x, y in zip(a, b)))
        for vertex in range(4):
            for a, b in combinations((v for v in range(4) if v != vertex), 2):
                add(tuple(x+y-z for x, y, z
                          in zip(form(vertex, a), form(vertex, b), form(a, b))))
    return WeightSubspace(prepared, edges, selected,
                          tuple(forms[edge] for edge in edges),
                          tuple(sorted(planes)), dimension, raw_count)


def build_weight_subspace(triangulation, defect_edges, *, check=lambda: None):
    """Build the retained space for caller-supplied global edge labels."""
    prepared, baseline = _one_vertex_data(triangulation, check)
    return _build_subspace(prepared, baseline, defect_edges, check)


def _initial_stats():
    return dict(subspaces_visited=0, bases_attempted=0, null_lines=0,
                nonnegative_directions=0, duplicate_directions=0,
                admissible_rays=0, positive_euler_rays=0, orbit_queries=0,
                peak_dimension=0, peak_hyperplanes=0, raw_hyperplanes=0)


def weight_subspace_rays(subspace, *, max_bases=None, check=lambda: None,
                         stats=None, seen=None):
    """Yield primitive admissible arrangement rays in the retained space.

    These need not all be standard vertex rays.  Every such standard vertex
    ray in the space is included.  max_bases is a shared count of begun
    (dimension-1)-hyperplane intersections; caller cancellation propagates.
    """
    _limit(max_bases, 'max_bases')
    if stats is None:
        stats = _initial_stats()
    if seen is None:
        seen = set()
    stats['subspaces_visited'] += 1
    stats['peak_dimension'] = max(stats['peak_dimension'], subspace.dimension)
    stats['peak_hyperplanes'] = max(stats['peak_hyperplanes'], len(subspace.hyperplanes))
    stats['raw_hyperplanes'] += subspace.raw_hyperplanes
    for indices in combinations(range(len(subspace.hyperplanes)), subspace.dimension-1):
        check()
        if max_bases is not None and stats['bases_attempted'] >= max_bases:
            raise SearchLimit('edge-weight intersection allowance exhausted')
        stats['bases_attempted'] += 1
        null = _nullspace([subspace.hyperplanes[i] for i in indices],
                          subspace.dimension, check)
        if len(null) != 1:
            continue
        stats['null_lines'] += 1
        for sign in (1, -1):
            check()
            weights = tuple(sign*sum(x*y for x, y in zip(form, null[0]))
                            for form in subspace.forms)
            if any(x < 0 for x in weights) or not any(weights):
                continue
            stats['nonnegative_directions'] += 1
            direction = _primitive(weights)
            if direction in seen:
                stats['duplicate_directions'] += 1
                continue
            # Invalid local metrics are deterministic for a weight direction;
            # caching them also avoids repeated reconstruction across spaces.
            seen.add(direction)
            indexed = dict(zip(subspace.edges, direction))
            rational_rows = []
            valid = True
            for t in range(len(subspace.prepared['tetrahedra'])):
                check()
                try:
                    rational_rows.append(local_coordinates_from_weights([
                        indexed[subspace.prepared['edge_roots'][_edge(t, a, b)]]
                        for a, b in _EDGES]))
                except NormalOrbitError:
                    valid = False
                    break
            if not valid:
                continue
            flat = _primitive(x for row in rational_rows for x in row)
            rows = [list(flat[7*t:7*t+7]) for t in range(len(rational_rows))]
            # Matching is independently reconstructed by the geometry layer,
            # rather than inferred solely from the local edge metric formulas.
            _coordinates(subspace.prepared, rows, check)
            stats['admissible_rays'] += 1
            yield rows


def enumerate_weight_subspace(triangulation, defect_edges, *, max_bases=None,
                              check=lambda: None):
    """Return all admissible arrangement rays for one supplied edge set."""
    _limit(max_bases, 'max_bases')
    subspace = build_weight_subspace(triangulation, defect_edges, check=check)
    stats = _initial_stats()
    rows = list(weight_subspace_rays(subspace, max_bases=max_bases,
                                    check=check, stats=stats))
    return rows, stats


def _observe_candidate(triangulation, prepared, rows, stats, max_orbit_cycles, check):
    analysed = _coordinates(prepared, rows, check)
    if analysed['euler_characteristic'] <= 0:
        return None
    stats['positive_euler_rays'] += 1
    stats['orbit_queries'] += 1
    answer = normal_compressing_disk_count(triangulation, rows,
        max_cycles=max_orbit_cycles, record_certificate=True, check=check)
    if answer['status'] != 'COMPLETE':
        raise SearchLimit('normal-disc component query did not complete')
    if not verify_normal_disk_count_certificate(
            triangulation, rows, answer['certificate'], check=check):
        raise ArithmeticError('independent normal-disc replay rejected')
    return answer['certificate'] if answer['contains_compressing_disk'] else None


def discover_in_weight_subspace(triangulation, defect_edges, *, max_bases=None,
                               max_orbit_cycles=None, check=lambda: None):
    """Search one supplied edge set, including independent positive replay."""
    _limit(max_bases, 'max_bases')
    _limit(max_orbit_cycles, 'max_orbit_cycles')
    subspace = build_weight_subspace(triangulation, defect_edges, check=check)
    stats = _initial_stats()
    try:
        for rows in weight_subspace_rays(subspace, max_bases=max_bases,
                                        check=check, stats=stats):
            proof = _observe_candidate(triangulation, subspace.prepared, rows,
                                       stats, max_orbit_cycles, check)
            if proof is not None:
                return dict(status='DISC_FOUND', coordinates=rows, certificate=proof,
                            searched_edges=list(subspace.defect_edges), stats=stats,
                            trust='disc in this supplied triangulation only')
    except SearchLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
    return dict(status='NO_VERTEX_DISC_IN_WEIGHT_SUBSPACE', stats=stats,
                trust='restricted vertex-disc search exhaustion only; '
                'no knot verdict or independent exhaustion certificate')


def weight_defect_search(triangulation, *, max_defect, exact_size=False,
                        max_subspaces=None, max_bases=None, max_orbit_cycles=None,
                        check=lambda: None):
    """Search vertex discs using at most max_defect exceptional global edges.

    The default schedule increases |F| from zero to max_defect.  exact_size
    searches only sets of that size; padding still covers all smaller sets.
    Candidate coordinates are binary integers and are never expanded into
    individual normal discs.  Both search allowances are global, not reset
    per subspace.  Preparation and exact replay are outside these two counts.
    """
    if type(max_defect) is not int or max_defect < 0:
        raise ValueError('max_defect must be a nonnegative integer')
    if type(exact_size) is not bool:
        raise ValueError('exact_size must be bool')
    for value, name in ((max_subspaces, 'max_subspaces'), (max_bases, 'max_bases'),
                        (max_orbit_cycles, 'max_orbit_cycles')):
        _limit(value, name)
    prepared, baseline = _one_vertex_data(triangulation, check)
    edges = tuple(sorted(baseline))
    if max_defect > len(edges):
        raise ValueError('max_defect exceeds the number of global edges')
    stats = _initial_stats()
    stats.update(tetrahedra=len(prepared['tetrahedra']), edges=len(edges),
                 max_defect=max_defect, exact_size=exact_size)
    seen = set()
    sizes = (max_defect,) if exact_size else range(max_defect+1)
    try:
        for size in sizes:
            for selected in combinations(edges, size):
                check()
                if (max_subspaces is not None
                        and stats['subspaces_visited'] >= max_subspaces):
                    raise SearchLimit('edge-weight subspace allowance exhausted')
                subspace = _build_subspace(prepared, baseline, selected, check)
                for rows in weight_subspace_rays(subspace, max_bases=max_bases,
                                                 check=check, stats=stats, seen=seen):
                    proof = _observe_candidate(triangulation, prepared, rows,
                                               stats, max_orbit_cycles, check)
                    if proof is not None:
                        return dict(status='DISC_FOUND', coordinates=rows,
                                    certificate=proof,
                                    searched_edges=list(selected), stats=stats,
                                    trust='disc in this supplied triangulation only')
    except SearchLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
    return dict(status='NO_VERTEX_DISC_UP_TO_EDGE_DEFECT', max_defect=max_defect,
                stats=stats, trust='restricted vertex-disc search exhaustion only; '
                'no knot verdict or independent exhaustion certificate')


def _global_hyperplanes(prepared, check):
    """Sparse unprojected arrangement; every row involves at most four edges."""
    planes = set()

    def add(terms):
        check()
        row = {}
        for edge, coefficient in terms:
            row[edge] = row.get(edge, 0)+coefficient
        row = {edge: value for edge, value in row.items() if value}
        if not row:
            return
        divisor = 0
        for value in row.values():
            divisor = gcd(divisor, abs(value))
        if row[min(row)] < 0:
            divisor = -divisor
        planes.add(tuple((edge, row[edge]//divisor) for edge in sorted(row)))

    for edge in sorted(set(prepared['edge_roots'])):
        add([(edge, 1)])
    for t in range(len(prepared['tetrahedra'])):
        def edge(a, b):
            return prepared['edge_roots'][_edge(t, a, b)]

        sums = [(edge(0, v), edge(*pair))
                for v, pair in ((1, (2, 3)), (2, (1, 3)), (3, (1, 2)))]
        for left, right in combinations(sums, 2):
            add([(e, 1) for e in left]+[(e, -1) for e in right])
        for vertex in range(4):
            for a, b in combinations((v for v in range(4) if v != vertex), 2):
                add([(edge(vertex, a), 1), (edge(vertex, b), 1), (edge(a, b), -1)])
    return tuple(sorted(planes))


def one_edge_defect_search(triangulation, *, max_bases=None, max_orbit_cycles=None,
                           check=lambda: None):
    """Search defects zero and one by global sparse constraint incidences.

    An active hyperplane L(w)=0 at a vertex disc with w=b+delta*unit_e
    yields delta=-L(b)/L_e.  There are O(t) hyperplane-edge incidences.
    Genuine meridian candidates require a positive even integer delta;
    the baseline is tested separately.  Only incident tetrahedra are
    reconstructed before the Euler prefilter.  Independent native disc
    replay decides every positive.  max_bases counts the baseline plus
    all begun hyperplane-edge incidences, including arithmetic rejections.
    """
    _limit(max_bases, 'max_bases')
    _limit(max_orbit_cycles, 'max_orbit_cycles')
    seed, prepared = _rank_one_cocycle_seed_details(triangulation, check=check)
    if prepared['vertices'] != 1:
        raise NormalOrbitError('edge-defect discovery requires one global vertex')
    base_data = _coordinates(prepared, seed['coordinates'], check)
    baseline = base_data['weights']
    stats = _initial_stats()
    stats.update(method='global-one-edge', tetrahedra=len(prepared['tetrahedra']),
                 edges=len(baseline), max_defect=1, global_hyperplanes=0,
                 incidence_attempts=0, distinct_offsets=0,
                 local_tetrahedron_queries=0, admissible_offsets=0)

    def begin():
        check()
        if max_bases is not None and stats['bases_attempted'] >= max_bases:
            raise SearchLimit('edge-weight incidence allowance exhausted')
        stats['bases_attempted'] += 1

    try:
        begin()
        stats['admissible_rays'] += 1
        proof = _observe_candidate(triangulation, prepared, seed['coordinates'],
                                   stats, max_orbit_cycles, check)
        if proof is not None:
            return dict(status='DISC_FOUND', coordinates=seed['coordinates'],
                        certificate=proof, searched_edges=[], stats=stats,
                        trust='disc in this supplied triangulation only')
        planes = _global_hyperplanes(prepared, check)
        stats['global_hyperplanes'] = len(planes)
        incidence = {e: set() for e in baseline}
        for t in range(len(prepared['tetrahedra'])):
            check()
            for j in range(6):
                incidence[prepared['edge_roots'][6*t+j]].add(t)
        face_occurrences = {e: 0 for e in baseline}
        faces = prepared['boundary_faces']+[(t, f) for t, f, _, _, _ in prepared['pairs']]
        for t, f in faces:
            check()
            for a, b in combinations((v for v in range(4) if v != f), 2):
                face_occurrences[prepared['edge_roots'][_edge(t, a, b)]] += 1
        seen = set()
        for plane in planes:
            constant = sum(value*baseline[e] for e, value in plane)
            for exceptional, coefficient in plane:
                begin()
                stats['incidence_attempts'] += 1
                delta = Fraction(-constant, coefficient)
                if delta <= 0 or delta.denominator != 1 or int(delta) % 2:
                    continue
                delta = int(delta)
                if (exceptional, delta) in seen:
                    continue
                seen.add((exceptional, delta))
                stats['distinct_offsets'] += 1
                replacements = {}
                euler_change = delta*(2-face_occurrences[exceptional])//2
                valid = True
                for t in sorted(incidence[exceptional]):
                    check()
                    stats['local_tetrahedron_queries'] += 1
                    local_weights = []
                    for j in range(6):
                        e = prepared['edge_roots'][6*t+j]
                        local_weights.append(baseline[e]+(delta if e == exceptional else 0))
                    try:
                        row = local_coordinates_from_weights(local_weights)
                    except NormalOrbitError:
                        valid = False
                        break
                    if any(x.denominator != 1 for x in row):
                        raise ArithmeticError('even edge defect broke normal parity')
                    row = [int(x) for x in row]
                    replacements[t] = row
                    euler_change += sum(row)-sum(seed['coordinates'][t])
                if not valid:
                    continue
                stats['admissible_offsets'] += 1
                if base_data['euler_characteristic']+euler_change <= 0:
                    continue
                rows = [replacements.get(t, row).copy()
                        for t, row in enumerate(seed['coordinates'])]
                checked = _coordinates(prepared, rows, check)
                if checked['euler_characteristic'] != base_data['euler_characteristic']+euler_change:
                    raise ArithmeticError('local edge-defect Euler update disagreed')
                primitive = _primitive(x for row in rows for x in row)
                rows = [list(primitive[7*t:7*t+7]) for t in range(len(rows))]
                stats['admissible_rays'] += 1
                proof = _observe_candidate(triangulation, prepared, rows,
                                           stats, max_orbit_cycles, check)
                if proof is not None:
                    return dict(status='DISC_FOUND', coordinates=rows, certificate=proof,
                                searched_edges=[exceptional], edge_increment=delta,
                                stats=stats, trust='disc in this supplied triangulation only')
    except SearchLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
    return dict(status='NO_VERTEX_DISC_UP_TO_EDGE_DEFECT', max_defect=1, stats=stats,
                trust='restricted vertex-disc search exhaustion only; '
                'no knot verdict or independent exhaustion certificate')
