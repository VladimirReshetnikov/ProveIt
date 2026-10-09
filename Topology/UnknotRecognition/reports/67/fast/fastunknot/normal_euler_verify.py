"""Independent source-bound replay of canonical sector Euler certificates.

This checker imports no LP solver, sector constructor, ray enumerator, or
Euler producer.  It reconstructs triangle components from the original
normal matching rows, then checks finite rational Farkas inequalities.
Native finite-manifold validation and coordinate incidence are shared.
"""

from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import gcd, prod
import json

from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare, _coordinates, _EDGES, _quad, NormalOrbitError


class _BadCertificate(ValueError):
    pass


def _integer(value):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise _BadCertificate(str(exc)) from exc


def _rational(value):
    if type(value) is not list or len(value) != 2:
        raise _BadCertificate('missing rational pair')
    numerator, denominator = map(_integer, value)
    if denominator <= 0:
        raise _BadCertificate('nonpositive rational denominator')
    return Fraction(numerator, denominator)


def _support(value, tetrahedra):
    if type(value) is not list:
        raise _BadCertificate('missing allowed types')
    answer = []
    for pair in value:
        if (type(pair) is not list or len(pair) != 2
                or any(type(x) is not int for x in pair)
                or not 0 <= pair[0] < tetrahedra or not 0 <= pair[1] < 3):
            raise _BadCertificate('malformed allowed type')
        answer.append(tuple(pair))
    if answer != sorted(answer) or len({t for t, q in answer}) != len(answer):
        raise _BadCertificate('noncanonical or overlapping allowed types')
    return tuple(answer)


def _primitive_row(row):
    common = 0
    for x in row:
        common = gcd(common, abs(x))
    if not common:
        return tuple(row)
    if next(x for x in row if x) < 0:
        common = -common
    return tuple(x//common for x in row)


def _reference_model(prepared, support, check):
    """Rebuild the algebra from matching rows, rather than sector face edges."""
    n, k = len(prepared['tetrahedra']), len(support)
    zero = [[] for _ in range(4*n)]
    records = []
    for equation in prepared['matching']:
        check()
        triangle = [(4*(i//7)+i % 7, a) for i, a in equation.items() if i % 7 < 4]
        label = tuple(equation.get(7*t+4+q, 0) for t, q in support)
        if not triangle:
            # A glued face can identify its two triangle variables directly.
            records.append((None, None, label))
            continue
        if len(triangle) != 2 or sorted(a for i, a in triangle) != [-1, 1]:
            raise ArithmeticError('unexpected triangle part of a normal matching equation')
        a = next(i for i, coefficient in triangle if coefficient == 1)
        b = next(i for i, coefficient in triangle if coefficient == -1)
        records.append((a, b, label))
        if not any(label):
            zero[a].append(b)
            zero[b].append(a)
    classes = [-1] * (4*n)
    for root in range(4*n):
        check()
        if classes[root] >= 0:
            continue
        classes[root] = root
        queue = [root]
        for a in queue:
            check()
            for b in zero[a]:
                if classes[b] < 0:
                    classes[b] = root
                    queue.append(b)
    vertices = {}
    for corner, c in enumerate(classes):
        vertices.setdefault(prepared['vertex_roots'][corner], set()).add(c)
    groups = tuple(tuple(sorted(cs)) for vertex, cs in sorted(vertices.items()) if len(cs) > 1)
    adjacency = {c: [] for c in sorted(set(classes))}
    for a, b, label in records:
        check()
        if a is None or not any(label):
            continue
        u, v = classes[a], classes[b]
        adjacency[u].append((v, label))
        adjacency[v].append((u, tuple(-x for x in label)))
    potentials = {}
    for root in adjacency:
        check()
        if root in potentials:
            continue
        potentials[root] = (0,)*k
        queue = [root]
        for a in queue:
            check()
            for b, increment in adjacency[a]:
                if b not in potentials:
                    potentials[b] = tuple(x+y for x, y in zip(potentials[a], increment))
                    queue.append(b)
    cycles = set()
    for a, b, label in records:
        check()
        row = label if a is None else tuple(x+y-z for x, y, z in
            zip(potentials[classes[a]], label, potentials[classes[b]]))
        row = _primitive_row(row)
        if any(row):
            cycles.add(row)

    # Compute the signed, unpeeled Euler value of each unit q vector directly.
    # This differs from the producer's accumulated class coefficient method.
    linear = []
    faces = prepared['boundary_faces'] + [(t, f) for t, f, _, _, _ in prepared['pairs']]
    for j, (selected_t, selected_q) in enumerate(support):
        check()
        heights = [[potentials[classes[4*t+v]][j] for v in range(4)] for t in range(n)]
        pieces = sum(map(sum, heights)) + 1
        arcs = sum(sum(heights[t][v] for v in range(4) if v != f)
                   + int(t == selected_t) for t, f in faces)
        weights = {}
        for t in range(n):
            check()
            for e, (a, b) in enumerate(_EDGES):
                root = prepared['edge_roots'][6*t+e]
                if root not in weights:
                    weights[root] = heights[t][a] + heights[t][b] + int(
                        t == selected_t and selected_q != _quad(a, b))
        linear.append(sum(weights.values())-arcs+pieces)
    boundary = {prepared['vertex_roots'][4*t+v] for t, f in prepared['boundary_faces']
                for v in range(4) if v != f}
    weights = tuple(1 if prepared['vertex_roots'][group[0]] in boundary else 2
                    for group in groups)
    return tuple(sorted(cycles)), tuple(linear), groups, potentials, weights


def verify_sector_euler_certificate(triangulation, certificate, *, check=lambda: None):
    """Verify exactly the source and sector named in this Euler certificate.

    The positive branch proves canonical nonzero coordinates and positive
    Euler characteristic, not extremality, connectedness, or a disc.  The
    negative branch proves absence of positive canonical Euler throughout
    the supplied allowed quadrilateral sector, using either all anchor
    inequalities or one componentwise envelope.  No knot verdict is inferred.
    """
    check()
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-sector-euler-lp-v1'
            or certificate.get('status') not in ('POSITIVE_EULER', 'NO_POSITIVE_EULER')):
        return False
    try:
        prepared = _prepare(triangulation, check)
    except NormalOrbitError:
        return False
    digest = sha256(json.dumps(triangulation, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    if certificate.get('source_sha256') != digest:
        return False
    try:
        support = _support(certificate.get('allowed_types'), len(prepared['tetrahedra']))
        if certificate['status'] == 'POSITIVE_EULER':
            if set(certificate) != {'schema', 'status', 'source_sha256', 'allowed_types',
                                    'quadrilaterals', 'coordinates', 'euler_characteristic'}:
                return False
            raw_q = certificate['quadrilaterals']
            if type(raw_q) is not list or len(raw_q) != len(support):
                return False
            q = [_integer(x) for x in raw_q]
            if not any(q) or any(x < 0 for x in q):
                return False
            common = 0
            for x in q:
                common = gcd(common, x)
            if common != 1:
                return False
            try:
                analysed = _coordinates(prepared, certificate['coordinates'], check)
            except NormalOrbitError:
                return False
            allowed = {pair: value for pair, value in zip(support, q)}
            minima = {}
            for t, row in enumerate(analysed['rows']):
                check()
                for typ in range(3):
                    if row[4+typ] != allowed.get((t, typ), 0):
                        return False
                for v in range(4):
                    root = prepared['vertex_roots'][4*t+v]
                    minima[root] = min(minima.get(root, row[v]), row[v])
            chi = analysed['euler_characteristic']
            if (any(minima.values()) or chi <= 0
                    or _integer(certificate['euler_characteristic']) != chi):
                return False
            check()
            return True
        matrix, linear, groups, potentials, weights = _reference_model(prepared, support, check)
        kind = certificate.get('proof_kind', 'anchors')
        common_fields = {'schema', 'status', 'source_sha256', 'allowed_types'}
        if 'proof_kind' in certificate:
            common_fields.add('proof_kind')
        if kind == 'envelope':
            if set(certificate) != common_fields | {'multipliers'}:
                return False
            raw = certificate['multipliers']
            if type(raw) is not list or len(raw) != len(matrix):
                return False
            dual = [_rational(value) for value in raw]
            envelope = list(linear)
            for group, weight in zip(groups, weights):
                check()
                for j in range(len(support)):
                    envelope[j] -= weight*min(potentials[c][j] for c in group)
            for j, target in enumerate(envelope):
                check()
                if sum(row[j]*coefficient for row, coefficient in zip(matrix, dual)) < target:
                    return False
            check()
            return True
        if kind != 'anchors' or set(certificate) != common_fields | {'duals'}:
            return False
        duals = certificate['duals']
        if type(duals) is not list or len(duals) != prod(map(len, groups)):
            return False
        for anchors, record in zip(product(*groups), duals):
            check()
            if (type(record) is not dict or set(record) != {'anchors', 'multipliers'}
                    or type(record['anchors']) is not list
                    or any(type(x) is not int for x in record['anchors'])
                    or record['anchors'] != list(anchors)
                    or type(record['multipliers']) is not list
                    or len(record['multipliers']) != len(matrix)):
                return False
            dual = [_rational(value) for value in record['multipliers']]
            objective = list(linear)
            for a, w in zip(anchors, weights):
                for j, value in enumerate(potentials[a]):
                    objective[j] -= w*value
            for j, target in enumerate(objective):
                check()
                if sum(row[j]*coefficient for row, coefficient in zip(matrix, dual)) < target:
                    return False
        check()
        return True
    except _BadCertificate:
        return False
