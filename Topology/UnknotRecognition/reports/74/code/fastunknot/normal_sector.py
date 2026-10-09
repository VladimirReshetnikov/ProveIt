"""Exact quadrilateral-sector kernels and normal vertex-surface discovery.

This is a supplied-triangulation search module, not a diagram recognizer.
Every successful essential-disc query includes native independent replay.
Pure vertex links are omitted.  Coordinates and linear algebra are exact.
"""

from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from math import comb, gcd, lcm
import json

from .normal_surface_geometry import _prepare, _coordinates, _quad
from .normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)


class SearchLimit(RuntimeError):
    """An explicitly configured search allowance was exhausted."""


def _rref(rows, width, check=lambda: None):
    a = [[Fraction(x) for x in row] for row in rows if any(row)]
    pivots = []
    r = 0
    for col in range(width):
        check()
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        value = a[r][col]
        a[r] = [x / value for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][col]:
                value = a[i][col]
                a[i] = [x - value*y for x, y in zip(a[i], a[r])]
        pivots.append(col)
        r += 1
        if r == len(a):
            break
    return a[:r], pivots


def _nullspace(rows, width, check=lambda: None):
    reduced, pivots = _rref(rows, width, check)
    result = []
    for free in (i for i in range(width) if i not in pivots):
        vector = [Fraction(0)] * width
        vector[free] = Fraction(1)
        for row, pivot in zip(reduced, pivots):
            vector[pivot] = -row[free]
        result.append(vector)
    return result


def _primitive(values):
    values = [Fraction(x) for x in values]
    denominator = lcm(*(x.denominator for x in values)) if values else 1
    integers = [int(x*denominator) for x in values]
    divisor = 0
    for value in integers:
        divisor = gcd(divisor, abs(value))
    if not divisor:
        return tuple(integers)
    if next(x for x in integers if x) < 0:
        divisor = -divisor
    return tuple(x//divisor for x in integers)


def _dot(left, right):
    return sum(x*y for x, y in zip(left, right))


def _source_hash(triangulation):
    raw = json.dumps(triangulation, sort_keys=True, separators=(',', ':'))
    return sha256(raw.encode('utf-8')).hexdigest()


def _support(value, tetrahedra):
    if not isinstance(value, (list, tuple)):
        raise ValueError('allowed_types must be a list or tuple')
    answer = []
    for item in value:
        if (not isinstance(item, (list, tuple)) or len(item) != 2
                or any(type(x) is not int for x in item)):
            raise ValueError('each allowed type must be an integer pair')
        t, q = item
        if not 0 <= t < tetrahedra or not 0 <= q < 3:
            raise ValueError('allowed quadrilateral type out of range')
        answer.append((t, q))
    if len({t for t, _ in answer}) != len(answer):
        raise ValueError('allow at most one quadrilateral type per tetrahedron')
    return tuple(sorted(answer))


@dataclass
class SectorKernel:
    triangulation: dict
    prepared: dict
    support: tuple
    corner_class: tuple
    classes: tuple
    groups: tuple
    matrix: tuple
    potentials: dict
    cycle_rows: tuple
    basis: tuple
    stats: dict

    def lift(self, quadrilaterals, check=lambda: None):
        """Canonical integral lift; one minimum zero per global vertex."""
        q = tuple(quadrilaterals)
        if (len(q) != len(self.support) or any(type(x) is not int or x < 0 for x in q)
                or any(_dot(row, q) for row in self.cycle_rows)):
            raise ValueError('quadrilateral vector is outside the sector cone')
        values = {c: _dot(self.potentials[c], q) for c in self.classes}
        for group in self.groups:
            minimum = min(values[c] for c in group)
            for c in group:
                values[c] -= minimum
        rows = [[0]*7 for _ in self.prepared['tetrahedra']]
        for corner, c in enumerate(self.corner_class):
            check()
            rows[corner//4][corner % 4] = values.get(c, 0)
        for (t, typ), count in zip(self.support, q):
            rows[t][4+typ] = count
        _coordinates(self.prepared, rows, check)
        return rows

    def kernel_vector(self, rows):
        flat = [rows[c//4][c % 4] for c in self.classes]
        return flat + [rows[t][4+q] for t, q in self.support]

    def is_standard_ray(self, rows, check=lambda: None):
        positive = [i for i, x in enumerate(self.kernel_vector(rows)) if x]
        if not positive:
            return False
        restricted = [[row[i] for i in positive] for row in self.matrix]
        return len(_nullspace(restricted, len(positive), check)) == 1


def build_sector_kernel(triangulation, allowed_types, *, check=lambda: None):
    """Contract all triangle matching edges with identically zero q-label.

    For k allowed types, the retained cone has at most 8k triangle variables,
    k quadrilateral variables, and 4k equations of Euclidean row norm <= 2.
    Every dropped class is an independent pure vertex-link factor.
    """
    prepared = _prepare(triangulation, check)
    count = len(prepared['tetrahedra'])
    support = _support(allowed_types, count)
    index = {item: j for j, item in enumerate(support)}
    k = len(support)
    parent = list(range(4*count))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        a, b = find(a), find(b)
        if a != b:
            parent[max(a, b)] = min(a, b)

    edges = []
    for t, f, u, g, permutation in prepared['pairs']:
        check()
        for v in range(4):
            if v == f:
                continue
            w = permutation[v]
            a, b = 4*t+v, 4*u+w
            label = [0]*k
            for key, sign in (((t, _quad(f, v)), 1),
                              ((u, _quad(g, w)), -1)):
                if key in index:
                    label[index[key]] += sign
            edges.append((a, b, tuple(label)))
            if not any(label):
                union(a, b)
    corner_class = tuple(find(i) for i in range(4*count))
    vertex_groups = {}
    for i, c in enumerate(corner_class):
        vertex_groups.setdefault(prepared['vertex_roots'][i], set()).add(c)
    groups = tuple(tuple(sorted(group)) for _, group in sorted(vertex_groups.items())
                   if len(group) > 1)
    classes = tuple(sorted(c for group in groups for c in group))
    class_index = {c: i for i, c in enumerate(classes)}
    adjacency = {c: [] for c in set(corner_class)}
    active = []
    matrix = []
    for a, b, label in edges:
        if not any(label):
            continue
        a, b = corner_class[a], corner_class[b]
        active.append((a, b, label))
        adjacency[a].append((b, label))
        adjacency[b].append((a, tuple(-x for x in label)))
        row = [0]*(len(classes)+k)
        if a in class_index:
            row[class_index[a]] -= 1
        if b in class_index:
            row[class_index[b]] += 1
        for j, value in enumerate(label):
            row[len(classes)+j] -= value
        if any(row):
            matrix.append(tuple(row))
    potentials = {}
    for root in sorted(adjacency):
        if root in potentials:
            continue
        potentials[root] = (0,)*k
        queue = [root]
        for a in queue:
            check()
            for b, label in adjacency[a]:
                if b not in potentials:
                    potentials[b] = tuple(x+y for x, y in zip(potentials[a], label))
                    queue.append(b)
    cycle_set = set()
    for a, b, label in active:
        row = _primitive(x+y-z for x, y, z
                         in zip(potentials[a], label, potentials[b]))
        if any(row):
            cycle_set.add(row)
    cycle_rows = tuple(sorted(cycle_set))
    basis = tuple(tuple(row) for row in _nullspace(cycle_rows, k, check))
    stats = dict(tetrahedra=count, allowed_types=k, active_equations=len(active),
                 triangle_classes=len(classes), kernel_variables=len(classes)+k,
                 kernel_equations=len(matrix), matching_nullity=len(basis),
                 matching_rank=k-len(basis),
                 removed_link_factors=sum(len(g) == 1 for g in vertex_groups.values()))
    if (len(active) > 4*k or len(classes) > 8*k
            or any(sum(x*x for x in row) > 4 for row in matrix)):
        raise ArithmeticError('support-kernel size or row-norm invariant failed')
    return SectorKernel(triangulation, prepared, support, corner_class, classes,
                        groups, tuple(matrix), potentials, cycle_rows, basis, stats)


def _hyperplanes(kernel, phase, check):
    k = len(kernel.support)
    normals = [[int(i == j) for i in range(k)] for j in range(k)]
    if phase == 'standard':
        for group in kernel.groups:
            for a, b in combinations(group, 2):
                normals.append([x-y for x, y
                                in zip(kernel.potentials[a], kernel.potentials[b])])
    projected = set()
    for row in normals:
        check()
        vector = _primitive(_dot(row, column) for column in kernel.basis)
        if any(vector):
            projected.add(vector)
    return tuple(sorted(projected))


def _support_rays(kernel, check, max_bases, stats):
    """Enumerate exact positive supports of the small standard cone."""
    p = len(kernel.classes)
    width = p + len(kernel.support)
    rank = len(_rref(kernel.matrix, width, check)[1])
    for size in range(1, min(width, rank+1)+1):
        for indices in combinations(range(width), size):
            if indices[-1] < p:
                continue
            check()
            if max_bases is not None and stats['bases_attempted'] >= max_bases:
                raise SearchLimit('candidate-basis allowance exhausted')
            stats['bases_attempted'] += 1
            matrix = [[row[i] for i in indices] for row in kernel.matrix]
            null = _nullspace(matrix, size, check)
            if len(null) != 1:
                continue
            vector = _primitive(null[0])
            if any(x <= 0 for x in vector):
                continue
            full = [0]*width
            for i, value in zip(indices, vector):
                full[i] = value
            rows = kernel.lift(tuple(full[p:]), check)
            if kernel.kernel_vector(rows) != full:
                raise ArithmeticError('non-link extreme ray was not canonical')
            if max(full) > 4**len(kernel.support):
                raise ArithmeticError('primitive extreme-ray height bound failed')
            stats['positive_directions'] += 1
            stats['emitted_rays'] += 1
            yield rows


def sector_rays(kernel, *, phase='standard', method='auto', check=lambda: None,
                max_bases=None, stats=None):
    """Yield primitive non-link standard rays in a supplied quad sector.

    'quadrilateral' yields only canonical lifts of Q-cone extreme rays.
    'standard' enumerates the potential arrangement, then filters by exact
    standard-cone extremality.  k=0 and nullity=0 yield no non-link ray.
    max_bases limits attempted linear systems, not just successful rays.
    """
    if phase not in ('quadrilateral', 'standard'):
        raise ValueError('phase must be quadrilateral or standard')
    if method not in ('auto', 'arrangement', 'supports', 'envelope'):
        raise ValueError('method must be auto, arrangement, supports, or envelope')
    if method == 'envelope':
        if phase != 'standard':
            raise ValueError('envelope is a complete standard-ray method')
        from .sector_envelope import sector_envelope_rays
        yield from sector_envelope_rays(kernel, check=check, max_bases=max_bases,
                                        stats=stats)
        return
    if phase == 'quadrilateral' and method == 'supports':
        raise ValueError('support enumeration is a standard-ray method')
    if max_bases is not None and (type(max_bases) is not int or max_bases < 0):
        raise ValueError('max_bases must be a nonnegative integer or None')
    if stats is None:
        stats = {}
    stats.update(bases_attempted=0, positive_directions=0,
                 nonextreme_directions=0, emitted_rays=0)
    d = len(kernel.basis)
    if d == 0:
        stats['hyperplanes'] = 0
        stats['method'] = 'empty'
        return
    planes = _hyperplanes(kernel, phase, check)
    stats['hyperplanes'] = len(planes)
    stats['method'] = 'arrangement'
    if phase == 'standard':
        p = len(kernel.classes)
        width = p + len(kernel.support)
        rank = len(_rref(kernel.matrix, width, check)[1])
        support_work = sum(comb(width, s)-(comb(p, s) if s <= p else 0)
                           for s in range(1, min(width, rank+1)+1))
        arrangement_work = comb(len(planes), d-1)
        stats.update(support_work_bound=support_work,
                     arrangement_work_bound=arrangement_work)
        if method == 'supports' or (method == 'auto' and support_work < arrangement_work):
            stats['method'] = 'supports'
            yield from _support_rays(kernel, check, max_bases, stats)
            return
    seen = set()
    for indices in combinations(range(len(planes)), d-1):
        check()
        if max_bases is not None and stats['bases_attempted'] >= max_bases:
            raise SearchLimit('candidate-basis allowance exhausted')
        stats['bases_attempted'] += 1
        nullspace = _nullspace([planes[i] for i in indices], d, check)
        if len(nullspace) != 1:
            continue
        z = nullspace[0]
        q = _primitive(sum(kernel.basis[j][i]*z[j] for j in range(d))
                       for i in range(len(kernel.support)))
        if q in seen or not any(q) or any(x < 0 for x in q):
            continue
        seen.add(q)
        stats['positive_directions'] += 1
        rows = kernel.lift(q, check)
        if not kernel.is_standard_ray(rows, check):
            stats['nonextreme_directions'] += 1
            if phase == 'quadrilateral':
                raise ArithmeticError('canonical Q-ray lift was not standard extreme')
            continue
        if max(x for row in rows for x in row) > 4**len(kernel.support):
            raise ArithmeticError('primitive extreme-ray height bound failed')
        stats['emitted_rays'] += 1
        yield rows


def enumerate_sector(triangulation, allowed_types, *, phase='standard', method='auto',
                     max_bases=None, check=lambda: None):
    kernel = build_sector_kernel(triangulation, allowed_types, check=check)
    stats = dict(kernel.stats)
    rows = list(sector_rays(kernel, phase=phase, method=method, max_bases=max_bases,
                            check=check, stats=stats))
    return rows, stats


def discover_in_sector(triangulation, allowed_types, *, phase='quadrilateral', method='auto',
                       max_bases=None, max_orbit_cycles=None, check=lambda: None):
    """Find a independently certified essential-disc component, if encountered.

    A complete Q phase also decides existence of a positive-Euler canonical
    surface in the sector.  Positive Euler alone is never a disc verdict.
    A complete standard phase excludes only vertex discs in this sector.
    A cap returns INCONCLUSIVE without an absence claim or partial proof.
    """
    if phase not in ('quadrilateral', 'standard'):
        raise ValueError('unknown search phase')
    if max_bases is not None and (type(max_bases) is not int or max_bases < 0):
        raise ValueError('invalid basis allowance')
    if max_orbit_cycles is not None and (
            type(max_orbit_cycles) is not int or max_orbit_cycles < 0):
        raise ValueError('invalid orbit allowance')
    kernel = build_sector_kernel(triangulation, allowed_types, check=check)
    stats = dict(kernel.stats, positive_euler_rays=0, orbit_queries=0)
    transcript = []
    try:
        for rows in sector_rays(kernel, phase=phase, method=method, max_bases=max_bases,
                                check=check, stats=stats):
            analysed = _coordinates(kernel.prepared, rows, check)
            chi = analysed['euler_characteristic']
            q = [rows[t][4+j] for t, j in kernel.support]
            record = dict(quadrilaterals=q, euler_characteristic=chi)
            transcript.append(record)
            if chi <= 0:
                continue
            stats['positive_euler_rays'] += 1
            stats['orbit_queries'] += 1
            count = normal_compressing_disk_count(
                triangulation, rows, max_cycles=max_orbit_cycles,
                record_certificate=True, check=check)
            if count['status'] != 'COMPLETE':
                raise SearchLimit('normal-component query did not complete')
            proof = count['certificate']
            if not verify_normal_disk_count_certificate(
                    triangulation, rows, proof, check=check):
                raise ArithmeticError('independent native disc replay rejected')
            record['disk_certificate'] = proof
            if count['contains_compressing_disk']:
                certificate = dict(schema='normal-sector-witness-v1',
                    source_sha256=_source_hash(triangulation),
                    allowed_types=[list(x) for x in kernel.support],
                    coordinates=rows, disk_certificate=proof)
                return dict(status='DISC_FOUND', coordinates=rows, certificate=certificate,
                            stats=stats, trust='this supplied triangulation only')
    except SearchLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
    if not stats['positive_euler_rays']:
        status = 'NO_POSITIVE_EULER'
    elif phase == 'quadrilateral':
        status = 'POSITIVE_EULER_ONLY'
    else:
        status = 'NO_VERTEX_DISC_IN_SECTOR'
    certificate = dict(schema='normal-sector-exhaustion-v1',
        source_sha256=_source_hash(triangulation),
        allowed_types=[list(x) for x in kernel.support], phase=phase,
        status=status, rays=transcript)
    return dict(status=status, stats=stats, certificate=certificate,
                trust='sector statement only; no knot-diagram correspondence asserted')


def sparse_disc_search(triangulation, *, max_active, max_sectors=None,
                       max_bases_per_sector=None, check=lambda: None):
    """Search all exact allowed supports of size <= max_active.

    Uses Q-ray screening and, when necessary, all standard rays.  Exhaustion
    gives NO_VERTEX_DISC_UP_TO_SUPPORT, never an unqualified knot verdict.
    The triangulation itself is not asserted to come from a knot diagram.
    """
    count = len(_prepare(triangulation, check)['tetrahedra'])
    if type(max_active) is not int or not 0 <= max_active <= count:
        raise ValueError('max_active must lie between zero and tetrahedron count')
    if max_sectors is not None and (type(max_sectors) is not int or max_sectors < 0):
        raise ValueError('invalid sector allowance')
    if max_bases_per_sector is not None and (
            type(max_bases_per_sector) is not int or max_bases_per_sector < 0):
        raise ValueError('invalid basis allowance')
    visited = 0
    for size in range(1, max_active+1):
        for tets in combinations(range(count), size):
            for types in product(range(3), repeat=size):
                check()
                if max_sectors is not None and visited >= max_sectors:
                    return dict(status='INCONCLUSIVE', reason='sector allowance exhausted',
                                sectors_visited=visited)
                visited += 1
                support = list(zip(tets, types))
                result = discover_in_sector(triangulation, support,
                    phase='quadrilateral', max_bases=max_bases_per_sector, check=check)
                if result['status'] == 'POSITIVE_EULER_ONLY':
                    result = discover_in_sector(triangulation, support,
                        phase='standard', max_bases=max_bases_per_sector, check=check)
                if result['status'] in ('DISC_FOUND', 'INCONCLUSIVE'):
                    return dict(result, sectors_visited=visited)
    return dict(status='NO_VERTEX_DISC_UP_TO_SUPPORT', max_active=max_active,
                sectors_visited=visited,
                trust='restricted search exhaustion only, not a knot verdict')
