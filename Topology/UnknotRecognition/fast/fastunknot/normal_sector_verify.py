"""Independent witness and complete-sector replay using dense elimination.

This module does not import the sector producer or its contraction, potential,
nullspace, or enumeration helpers.  Native geometry validation and the older
independent weighted-disc checker are the deliberately shared trust boundary.
"""

from fractions import Fraction
from hashlib import sha256
from itertools import combinations
from math import gcd, lcm
import json

from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from .normal_disk_kernel import verify_normal_disk_count_certificate
from .integer_codec import encoded_integer


def _digest(triangulation):
    encoded = json.dumps(triangulation, sort_keys=True, separators=(',', ':')).encode()
    return sha256(encoded).hexdigest()


def _allowed(value, t):
    if type(value) is not list:
        raise ValueError('allowed type list missing')
    result = []
    for pair in value:
        if (type(pair) is not list or len(pair) != 2
                or any(type(x) is not int for x in pair)
                or not 0 <= pair[0] < t or not 0 <= pair[1] < 3):
            raise ValueError('malformed allowed type')
        result.append(tuple(pair))
    if result != sorted(result) or len(set(x[0] for x in result)) != len(result):
        raise ValueError('unordered or overlapping types')
    return result


def _eliminate(matrix, columns, check):
    matrix = [[Fraction(x) for x in row] for row in matrix]
    pivots = []
    target = 0
    for column in range(columns):
        check()
        selected = next((r for r in range(target, len(matrix))
                         if matrix[r][column] != 0), None)
        if selected is None:
            continue
        matrix[target], matrix[selected] = matrix[selected], matrix[target]
        scale = matrix[target][column]
        matrix[target] = [x / scale for x in matrix[target]]
        for r, row in enumerate(matrix):
            if r != target:
                scale = row[column]
                if scale:
                    matrix[r] = [a-scale*b for a, b in zip(row, matrix[target])]
        pivots.append(column)
        target += 1
    return matrix, pivots


def _kernel(matrix, columns, check):
    reduced, pivots = _eliminate(matrix, columns, check)
    vectors = []
    for column in range(columns):
        if column in pivots:
            continue
        v = [Fraction(int(j == column)) for j in range(columns)]
        for r, p in enumerate(pivots):
            v[p] = -reduced[r][column]
        vectors.append(v)
    return vectors


def _integer_direction(vector):
    vector = [Fraction(x) for x in vector]
    multiplier = 1
    for x in vector:
        multiplier = lcm(multiplier, x.denominator)
    ints = [int(multiplier*x) for x in vector]
    common = 0
    for x in ints:
        common = gcd(common, x)
    if not common:
        return tuple(ints)
    sign = 1 if next(x for x in ints if x) > 0 else -1
    return tuple(sign*x//common for x in ints)


def dense_sector_model(triangulation, allowed_types, *, check=lambda: None):
    """Reference model from dense standard matching, without graph contraction."""
    prepared = _prepare(triangulation, check)
    t = len(prepared['tetrahedra'])
    support = _allowed([list(x) for x in allowed_types], t)
    columns = [7*i+j for i in range(t) for j in range(4)]
    columns += [7*i+4+j for i, j in support]
    matrix = [[row.get(column, 0) for column in columns]
              for row in prepared['matching']]
    reduced, pivots = _eliminate(matrix, 4*t, check)
    constraints = [row[4*t:] for row in reduced[len(pivots):] if any(row[4*t:])]
    basis = _kernel(constraints, len(support), check)
    potentials = [[Fraction(0)]*len(support) for _ in range(4*t)]
    for row, column in zip(reduced, pivots):
        potentials[column] = [-x for x in row[4*t:]]
    groups = {}
    for corner, vertex in enumerate(prepared['vertex_roots']):
        groups.setdefault(vertex, []).append(corner)
    return dict(prepared=prepared, support=support, matrix=matrix,
                potentials=potentials, groups=groups, basis=basis,
                constraints=constraints)


def _lift(model, q, check):
    values = [sum(a*b for a, b in zip(row, q)) for row in model['potentials']]
    for group in model['groups'].values():
        minimum = min(values[i] for i in group)
        for i in group:
            values[i] -= minimum
    if any(x.denominator != 1 for x in values):
        raise ArithmeticError('dense canonical lift is not integral')
    rows = [[0]*7 for _ in model['prepared']['tetrahedra']]
    for i, x in enumerate(values):
        rows[i//4][i % 4] = int(x)
    for (i, typ), value in zip(model['support'], q):
        rows[i][4+typ] = value
    _coordinates(model['prepared'], rows, check)
    return rows


def dense_reference_rays(model, phase, *, check=lambda: None):
    """Exact ray set used to certify enumeration coverage."""
    if phase not in ('quadrilateral', 'standard'):
        raise ValueError('invalid enumeration phase')
    k, d = len(model['support']), len(model['basis'])
    if d == 0:
        return {}
    projected = set()

    def insert(row):
        vector = _integer_direction(sum(a*b for a, b in zip(row, v))
                                    for v in model['basis'])
        if any(vector):
            projected.add(vector)

    for i in range(k):
        insert([int(i == j) for j in range(k)])
    if phase == 'standard':
        for group in model['groups'].values():
            # Deduplication is exact, after the independent dense solve.
            local = sorted(set(tuple(model['potentials'][i]) for i in group))
            for a, b in combinations(local, 2):
                insert([x-y for x, y in zip(a, b)])
    planes = sorted(projected)
    result = {}
    seen = set()
    for selected in combinations(planes, d-1):
        check()
        null = _kernel(selected, d, check)
        if len(null) != 1:
            continue
        q = _integer_direction(sum(v[j]*z for v, z in zip(model['basis'], null[0]))
                               for j in range(k))
        if q in seen or not any(q) or any(x < 0 for x in q):
            continue
        seen.add(q)
        rows = _lift(model, q, check)
        flat = [row[j] for row in rows for j in range(4)] + list(q)
        active = [i for i, x in enumerate(flat) if x]
        restricted = [[row[i] for i in active] for row in model['matrix']]
        if len(_kernel(restricted, len(active), check)) != 1:
            continue
        chi = _coordinates(model['prepared'], rows, check)['euler_characteristic']
        result[q] = (rows, chi)
    return result


def verify_sector_witness(triangulation, certificate, *, check=lambda: None):
    check()
    if type(certificate) is not dict or certificate.get('schema') != 'normal-sector-witness-v1':
        return False
    if certificate.get('source_sha256') != _digest(triangulation):
        return False
    try:
        prepared = _prepare(triangulation, check)
    except NormalOrbitError:
        return False
    try:
        support = _allowed(certificate.get('allowed_types'), len(prepared['tetrahedra']))
    except ValueError:
        return False
    try:
        rows = _coordinates(prepared, certificate.get('coordinates'), check)['rows']
    except NormalOrbitError:
        return False
    allowed = set(support)
    if any(row[4+q] and (t, q) not in allowed for t, row in enumerate(rows) for q in range(3)):
        return False
    proof = certificate.get('disk_certificate')
    if not verify_normal_disk_count_certificate(triangulation, rows, proof, check=check):
        return False
    try:
        return encoded_integer(proof['compressing_disk_components']) > 0
    except (KeyError, ValueError, TypeError):
        return False


def verify_sector_exhaustion(triangulation, certificate, *, check=lambda: None):
    """Independently reconstruct every ray, its Euler value and negative disc proof.

    A successfully checked Q certificate with NO_POSITIVE_EULER excludes every
    positive-Euler canonical surface in the sector.  The other statuses have
    exactly their advertised restricted meanings; none is a knot verdict.
    """
    check()
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-sector-exhaustion-v1'
            or certificate.get('source_sha256') != _digest(triangulation)):
        return False
    phase, status = certificate.get('phase'), certificate.get('status')
    if phase not in ('quadrilateral', 'standard'):
        return False
    try:
        prepared = _prepare(triangulation, check)
    except NormalOrbitError:
        return False
    try:
        support = _allowed(certificate.get('allowed_types'), len(prepared['tetrahedra']))
    except ValueError:
        return False
    if 'q_support_certificate'in certificate:
        qproof=certificate['q_support_certificate']
        # No producer data or inferred support is trusted. Independently
        # reconstruct the complete original Q cone first; recursion is limited
        # to one ordinary Q certificate, which cannot itself carry a reduction.
        if (phase!='standard' or type(qproof)is not dict
                or qproof.get('phase')!='quadrilateral'
                or qproof.get('status')!='POSITIVE_EULER_ONLY'
                or qproof.get('allowed_types')!=certificate.get('allowed_types')
                or 'q_support_certificate'in qproof):return False
        if not verify_sector_exhaustion(triangulation,qproof,check=check):return False
        present=[False]*len(support)
        for entry in qproof['rays']:
            check()
            for i,value in enumerate(entry['quadrilaterals']):
                check()
                if value:present[i]=True
        retained=[i for i,value in enumerate(present)if value]
        if not retained or len(retained)==len(support):return False
        reduced_support=[support[i]for i in retained]
        model=dense_sector_model(triangulation,reduced_support,check=check)
        reduced_expected=dense_reference_rays(model,phase,check=check)
        expected={}
        for q,value in reduced_expected.items():
            check();full=[0]*len(support)
            for i,count in zip(retained,q):full[i]=count
            expected[tuple(full)]=value
    else:
        model = dense_sector_model(triangulation, support, check=check)
        expected = dense_reference_rays(model, phase, check=check)
    entries = certificate.get('rays')
    if type(entries) is not list or len(entries) != len(expected):
        return False
    seen = set()
    positive = False
    for entry in entries:
        check()
        if type(entry) is not dict or type(entry.get('quadrilaterals')) is not list:
            return False
        values = entry['quadrilaterals']
        if any(type(x) is not int for x in values):
            return False
        q = tuple(values)
        if q in seen or q not in expected:
            return False
        seen.add(q)
        rows, chi = expected[q]
        if type(entry.get('euler_characteristic')) is not int or entry['euler_characteristic'] != chi:
            return False
        if chi > 0:
            positive = True
            proof = entry.get('disk_certificate')
            if not verify_normal_disk_count_certificate(triangulation, rows, proof, check=check):
                return False
            try:
                if encoded_integer(proof['compressing_disk_components']) != 0:
                    return False
            except (KeyError, ValueError, TypeError):
                return False
        elif 'disk_certificate' in entry:
            return False
    correct = ('NO_POSITIVE_EULER' if not positive else
               'POSITIVE_EULER_ONLY' if phase == 'quadrilateral' else
               'NO_VERTEX_DISC_IN_SECTOR')
    return status == correct
