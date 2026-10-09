"""Independent arithmetic replay of positive-Euler propagation certificates.

No search, simplex solver, or producer model builder is imported.  Source
matching rows, Euler coefficients, and vertex-anchor coverage are rebuilt.
Negative trees are checked solely by rational Farkas inequalities and exhaustive
quadrilateral branch coverage.  Shared low-level manifold/coordinate validation
is the trust boundary; these certificates do not establish knot provenance.
"""

from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from math import gcd, prod
import json

from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError


def _quad(a, b):
    pair = {a, b}
    return next(q for q in range(3)
                if pair in ({0, q+1}, set(range(4))-{0, q+1}))


def _source_model(triangulation, check):
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
    # Independently reconstruct each local disk's F-E+V contribution.
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
            edge_count = 0
            for b, f in faces:
                if a == b and (disk >= 4 or disk != f):
                    edge_count += 1
            vertex_count = 0
            for b, (u, v) in representatives.values():
                if a == b and ((disk < 4 and disk in (u, v))
                               or (disk >= 4 and disk-4 != _quad(u, v))):
                    vertex_count += 1
            euler.append(1-edge_count+vertex_count)
    groups = {}
    for corner, global_vertex in enumerate(prepared['vertex_roots']):
        groups.setdefault(global_vertex, []).append(7*(corner//4)+corner % 4)
    return prepared, equations, euler, [groups[v] for v in sorted(groups)]


def _dual(dual, equations, euler, columns, check):
    if type(dual) is not list or len(dual) != len(equations):
        return False
    values = []
    for pair in dual:
        check()
        if type(pair) is not list or len(pair) != 2:
            return False
        try:
            numerator, denominator = map(encoded_integer, pair)
        except ValueError:
            return False
        if denominator <= 0:
            return False
        values.append(Fraction(numerator, denominator))
    for column in columns:
        check()
        if sum(row[column]*value for row, value in zip(equations, values)) < euler[column]:
            return False
    return True


def _index(value, size):
    return type(value) is int and 0 <= value < size


def verify_normal_propagation_certificate(triangulation, certificate, *, check=lambda: None):
    """Check a positive witness or a complete negative branch certificate.

    NO_POSITIVE_EULER excludes admissible normal surfaces having positive Euler
    characteristic and a zero triangle at every global vertex.  It is not a
    verdict about arbitrary normal surfaces, compressibility, or a knot diagram.
    """
    check()
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-positive-euler-propagation-v1'):
        return False
    try:
        prepared, equations, euler, groups = _source_model(triangulation, check)
    except NormalOrbitError:
        return False
    source = json.dumps(triangulation, sort_keys=True, separators=(',', ':')).encode()
    if certificate.get('source_sha256') != sha256(source).hexdigest():
        return False
    n, width = len(prepared['tetrahedra']), len(euler)
    if certificate.get('status') == 'POSITIVE_EULER':
        if set(certificate) != {'schema', 'source_sha256', 'status', 'anchors', 'coordinates'}:
            return False
        anchors = certificate['anchors']
        if (type(anchors) is not list or len(anchors) != len(groups)
                or any(type(a) is not int or a not in group for a, group in zip(anchors, groups))):
            return False
        try:
            analysed = _coordinates(prepared, certificate['coordinates'], check)
        except NormalOrbitError:
            return False
        flat = [x for row in analysed['rows'] for x in row]
        common = 0
        for x in flat:
            common = gcd(common, x)
        return (common == 1 and all(flat[a] == 0 for a in anchors)
                and sum(x*c for x, c in zip(flat, euler)) > 0
                and analysed['euler_characteristic'] > 0)
    if (certificate.get('status') != 'NO_POSITIVE_EULER'
            or set(certificate) != {'schema', 'source_sha256', 'status', 'anchor_trees'}):
        return False
    trees = certificate['anchor_trees']
    if type(trees) is not list or len(trees) != prod(map(len, groups)):
        return False
    seen = set()
    for record, anchors in zip(trees, product(*groups)):
        check()
        if (type(record) is not dict or set(record) != {'anchors', 'tree'}
                or type(record['anchors']) is not list
                or any(type(a) is not int for a in record['anchors'])
                or record['anchors'] != list(anchors)):
            return False
        zeros = set(anchors)
        stack = [(record['tree'], ((0, 1, 2),)*n)]
        while stack:
            check()
            tree, allowed = stack.pop()
            if (type(tree) is not dict or id(tree) in seen
                    or set(tree) != {'propagations', 'terminal'}
                    or type(tree['propagations']) is not list):
                return False
            seen.add(id(tree))

            def columns(forbidden=None):
                return [j for j in range(width) if j not in zeros and j != forbidden
                        and (j % 7 < 4 or j % 7-4 in allowed[j//7])]

            for step in tree['propagations']:
                check()
                if type(step) is not dict or set(step) != {'tetrahedron', 'type', 'y'}:
                    return False
                a, q = step['tetrahedron'], step['type']
                if (not _index(a, n) or not _index(q, 3)
                        or len(allowed[a]) < 2 or q not in allowed[a]
                        or not _dual(step['y'], equations, euler, columns(7*a+4+q), check)):
                    return False
                allowed = allowed[:a] + ((q,),) + allowed[a+1:]
            terminal = tree['terminal']
            if type(terminal) is not dict:
                return False
            if terminal.get('kind') == 'NONPOSITIVE':
                if (set(terminal) != {'kind', 'y'}
                        or not _dual(terminal['y'], equations, euler, columns(), check)):
                    return False
            elif terminal.get('kind') == 'BRANCH':
                if set(terminal) != {'kind', 'tetrahedron', 'children'}:
                    return False
                a, children = terminal['tetrahedron'], terminal['children']
                if (not _index(a, n) or len(allowed[a]) < 2
                        or type(children) is not list or len(children) != len(allowed[a])):
                    return False
                for child, q in zip(children, allowed[a]):
                    if (type(child) is not dict or set(child) != {'type', 'tree'}
                            or type(child['type']) is not int or child['type'] != q):
                        return False
                    stack.append((child['tree'], allowed[:a] + ((q,),) + allowed[a+1:]))
            else:
                return False
    return True
