"""Independent exact replay for active-cone and active-face certificates.

This module imports neither the active producer nor any LP or rank routine.
The arithmetic proof is maximal support, nonnegative duality, and an exhaustive
binary incompatibility disjunction.  Normal-source replay independently builds
matching rows and Euler coefficients on the maintained manifold validator.
"""

from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from math import prod
import json

from .integer_codec import encoded_integer


class _CallbackFailure(BaseException):
    def __init__(self, original):
        self.original = original


def _preserve_callback(check):
    def invoke():
        try:
            check()
        except BaseException as error:
            raise _CallbackFailure(error) from error
    return invoke


def _rational(value):
    if type(value) is Fraction:
        return value
    if type(value) in (list, tuple):
        if len(value) != 2:
            raise ValueError('invalid rational pair')
        numerator, denominator = map(encoded_integer, value)
        if denominator <= 0:
            raise ValueError('nonpositive denominator')
        return Fraction(numerator, denominator)
    return Fraction(encoded_integer(value))


def _source(matrix, objective):
    if type(matrix) not in (list, tuple) or type(objective) not in (list, tuple):
        raise ValueError('invalid source sequences')
    c = [_rational(v) for v in objective]
    if any(type(row) not in (list, tuple) or len(row) != len(c) for row in matrix):
        raise ValueError('invalid source matrix width')
    return [[_rational(v) for v in row] for row in matrix], c


def _vector(data, width):
    if type(data) is not list or len(data) != width:
        raise ValueError('invalid certificate vector length')
    values = []
    for pair in data:
        if type(pair) is not list or len(pair) != 2:
            raise ValueError('certificate rationals require JSON pairs')
        values.append(_rational(pair))
    return values


def verify_active_cone_certificate(matrix, objective, certificate, *,
                                    check=lambda: None):
    """Verify either a complete active-support pair or an ordinary negative dual.

    A valid ACTIVE_POSITIVE proof is a statement about the relaxed cone.  It
    makes no assertion of quadrilateral admissibility or surface topology.
    """
    check = _preserve_callback(check)
    try:
        a, c = _source(matrix, objective)
        check()
        m, n = len(a), len(c)
        if type(certificate) is not dict or certificate.get('schema') != 'active-positive-cone-v1':
            return False
        status = certificate.get('status')
        if status == 'NONPOSITIVE':
            if set(certificate) != {'schema', 'status', 'y'}:
                return False
            y = _vector(certificate['y'], m)
            for j in range(n):
                check()
                if sum(a[i][j]*y[i] for i in range(m)) < c[j]:
                    return False
            return True
        if status != 'ACTIVE_POSITIVE' or set(certificate) != {'schema', 'status', 'x', 'y'}:
            return False
        x, y = _vector(certificate['x'], n), _vector(certificate['y'], m)
        if any(v < 0 for v in x) or sum(v*w for v, w in zip(c, x)) < 1:
            return False
        for row in a:
            check()
            if sum(v*w for v, w in zip(row, x)):
                return False
        for j in range(n):
            check()
            residual = sum(a[i][j]*y[i] for i in range(m))
            if residual < 0 or x[j]+residual < 1:
                return False
        return True
    except _CallbackFailure as error:
        raise error.original
    except (ValueError, TypeError, KeyError, IndexError, OverflowError):
        return False


def verify_active_search_certificate(matrix, objective, conflict_groups,
                                      certificate, *, check=lambda: None):
    """Check an admissible positive vector or a complete active binary tree."""
    check = _preserve_callback(check)
    try:
        a, c = _source(matrix, objective)
        n = len(c)
        if type(conflict_groups) not in (list, tuple):
            return False
        groups = []
        for group in conflict_groups:
            if (type(group) not in (list, tuple) or len(group) < 2
                    or any(type(j) is not int or not 0 <= j < n for j in group)
                    or len(set(group)) != len(group)):
                return False
            groups.append(set(group))
        if type(certificate) is not dict or certificate.get('schema') != 'active-face-search-v1':
            return False
        if certificate.get('status') == 'ADMISSIBLE_POSITIVE':
            if set(certificate) != {'schema', 'status', 'x'}:
                return False
            if type(certificate['x']) is not list or len(certificate['x']) != n:
                return False
            x = [encoded_integer(v) for v in certificate['x']]
            if (any(v < 0 for v in x) or sum(v*w for v, w in zip(c, x)) <= 0
                    or any(sum(v*w for v, w in zip(row, x)) for row in a)
                    or any(sum(x[j] > 0 for j in group) > 1 for group in groups)):
                return False
            check()
            return True
        if (certificate.get('status') != 'NO_ADMISSIBLE_POSITIVE'
                or set(certificate) != {'schema', 'status', 'tree'}):
            return False
        stack = [(certificate['tree'], list(range(n)))]
        seen = set()
        while stack:
            check()
            node, columns = stack.pop()
            if type(node) is not dict or id(node) in seen:
                return False
            seen.add(id(node))
            restricted = [[row[j] for j in columns] for row in a]
            objective = [c[j] for j in columns]
            if node.get('kind') == 'NONPOSITIVE':
                if set(node) != {'kind', 'dual'}:
                    return False
                proof = dict(schema='active-positive-cone-v1', status='NONPOSITIVE',
                             y=node['dual'])
                if not verify_active_cone_certificate(restricted, objective, proof, check=check):
                    return False
                continue
            if node.get('kind') != 'PAIR' or set(node) != {
                    'kind', 'active_certificate', 'pair', 'children'}:
                return False
            support_proof = node['active_certificate']
            if (type(support_proof) is not dict
                    or support_proof.get('status') != 'ACTIVE_POSITIVE'
                    or not verify_active_cone_certificate(
                        restricted, objective, support_proof, check=check)):
                return False
            x = _vector(support_proof['x'], len(columns))
            active = [j for j, value in zip(columns, x) if value > 0]
            pair, children = node['pair'], node['children']
            if (type(pair) is not list or len(pair) != 2
                    or any(type(j) is not int or j not in active for j in pair)
                    or pair[0] == pair[1] or not any(set(pair) <= group for group in groups)
                    or type(children) is not list or len(children) != 2):
                return False
            for forbidden, child in zip(pair, children):
                stack.append((child, [j for j in active if j != forbidden]))
        return True
    except _CallbackFailure as error:
        raise error.original
    except (ValueError, TypeError, KeyError, IndexError, OverflowError):
        return False


def _quad(a, b):
    pair = {a, b}
    return next(q for q in range(3)
                if pair in ({0, q+1}, set(range(4))-{0, q+1}))


def _normal_source(triangulation, check):
    from .normal_surface_geometry import _prepare
    prepared = _prepare(triangulation, check)
    n = len(prepared['tetrahedra'])
    equations = []
    for a, f, b, g, permutation in prepared['pairs']:
        check()
        for v in range(4):
            if v == f:
                continue
            w = permutation[v]
            row = [0]*(7*n)
            for column, sign in ((7*a+v, 1), (7*a+4+_quad(f, v), 1),
                                 (7*b+w, -1), (7*b+4+_quad(g, w), -1)):
                row[column] += sign
            equations.append(row)
    faces = set(prepared['boundary_faces'])
    faces.update((a, f) for a, f, _, _, _ in prepared['pairs'])
    representatives = {}
    edge_pairs = tuple(combinations(range(4), 2))
    for local, global_edge in enumerate(prepared['edge_roots']):
        representatives.setdefault(global_edge, (local//6, edge_pairs[local % 6]))
    euler = []
    for a in range(n):
        check()
        for disk in range(7):
            edge_count = sum(a == b and (disk >= 4 or disk != f) for b, f in faces)
            vertex_count = sum(a == b and ((disk < 4 and disk in (u, v))
                               or (disk >= 4 and disk-4 != _quad(u, v)))
                               for b, (u, v) in representatives.values())
            euler.append(1-edge_count+vertex_count)
    groups = {}
    for corner, global_vertex in enumerate(prepared['vertex_roots']):
        groups.setdefault(global_vertex, []).append(7*(corner//4)+corner % 4)
    return prepared, equations, euler, [groups[v] for v in sorted(groups)]


def verify_active_normal_certificate(triangulation, certificate, *, check=lambda: None):
    """Source-bound normal positive-Euler replay, without an unknot verdict."""
    from .normal_surface_geometry import _coordinates, NormalOrbitError
    check = _preserve_callback(check)
    try:
        if type(certificate) is not dict or certificate.get('schema') != 'active-normal-search-v1':
            return False
        digest = sha256(json.dumps(triangulation, sort_keys=True,
                                   separators=(',', ':')).encode()).hexdigest()
        if certificate.get('source_sha256') != digest:
            return False
        prepared, matrix, euler, groups = _normal_source(triangulation, check)
        t, width = len(prepared['tetrahedra']), len(euler)
        if certificate.get('status') == 'POSITIVE_EULER':
            if set(certificate) != {'schema', 'source_sha256', 'status', 'anchors', 'coordinates'}:
                return False
            anchors = certificate['anchors']
            if (type(anchors) is not list or len(anchors) != len(groups)
                    or any(type(a) is not int or a not in group for a, group in zip(anchors, groups))):
                return False
            analysed = _coordinates(prepared, certificate['coordinates'], check)
            flat = [encoded_integer(v) for row in certificate['coordinates'] for v in row]
            return (all(flat[a] == 0 for a in anchors)
                    and sum(v*w for v, w in zip(flat, euler)) > 0
                    and analysed['euler_characteristic'] > 0)
        if (certificate.get('status') != 'NO_POSITIVE_EULER'
                or set(certificate) != {'schema', 'source_sha256', 'status', 'anchor_trees'}):
            return False
        trees = certificate['anchor_trees']
        if type(trees) is not list or len(trees) != prod(map(len, groups)):
            return False
        for item, anchors in zip(trees, product(*groups)):
            check()
            if (type(item) is not dict or set(item) != {'anchors', 'proof'}
                    or type(item['anchors']) is not list
                    or any(type(a) is not int for a in item['anchors'])
                    or item['anchors'] != list(anchors)):
                return False
            zero = set(anchors)
            columns = [j for j in range(width) if j not in zero]
            position = {j: k for k, j in enumerate(columns)}
            conflicts = [[position[7*a+4+q] for q in range(3)] for a in range(t)]
            if (type(item['proof']) is not dict
                    or item['proof'].get('status') != 'NO_ADMISSIBLE_POSITIVE'
                    or not verify_active_search_certificate(
                        [[row[j] for j in columns] for row in matrix],
                        [euler[j] for j in columns], conflicts, item['proof'], check=check)):
                return False
        return True
    except _CallbackFailure as error:
        raise error.original
    except (ValueError, TypeError, KeyError, IndexError, OverflowError, NormalOrbitError):
        return False
