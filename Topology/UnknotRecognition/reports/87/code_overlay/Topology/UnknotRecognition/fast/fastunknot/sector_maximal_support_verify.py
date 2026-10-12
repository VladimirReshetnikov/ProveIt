"""Independent exact replay of maximal nonnegative matching support.

The checker uses source equations and supplied primal/dual witnesses only.
It imports no sector builder, elimination helper, LP solver or producer.
The deliberately shared geometry validator authenticates the supplied finite
triangulation and the primal normal coordinates, not a knot-diagram source.
"""

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd

from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError


def _fraction(value):
    if type(value) is not list or len(value) != 2:
        raise ValueError('expected a rational numerator/denominator pair')
    numerator, denominator = (encoded_integer(x) for x in value)
    if denominator <= 0 or gcd(numerator, denominator) != 1:
        raise ValueError('rational must be reduced with positive denominator')
    return Fraction(numerator, denominator)


def _matrix(matrix, width):
    if type(matrix) not in (list, tuple):
        raise ValueError('matrix must be a sequence of rational rows')
    if width is None:
        width = len(matrix[0]) if matrix else 0
    if type(width) is not int or width < 0:
        raise ValueError('invalid matrix width')
    rows = []
    for row in matrix:
        if type(row) not in (list, tuple) or len(row) != width:
            raise ValueError('matrix row width mismatch')
        if any(type(x) not in (int, Fraction) for x in row):
            raise ValueError('matrix coefficients must be integers or Fractions')
        rows.append(tuple(Fraction(x) for x in row))
    return tuple(rows), width


def _matrix_digest(rows, width):
    # Hexadecimal strings avoid the interpreter's decimal big-integer limit.
    data = [width, [[[hex(x.numerator), hex(x.denominator)] for x in row]
                    for row in rows]]
    return sha256(json.dumps(data, separators=(',', ':')).encode()).hexdigest()


def verify_nonnegative_kernel_support_certificate(matrix, certificate, *,
                                                  width=None, check=lambda: None):
    """Verify the complete support of {x >= 0: matrix*x = 0}.

    The certificate checks Ax=0, y=A^T*lambda, x,y>=0 and x+y>=1.
    Orthogonality then makes the two supports a partition of the coordinates.
    Source row order is authenticated; a reordered matrix needs a new proof.
    Callback exceptions propagate instead of being interpreted as rejection.
    """
    check()
    try:
        rows, width = _matrix(matrix, width)
    except (ValueError, TypeError):
        return False
    if (type(certificate) is not dict
            or certificate.get('schema') != 'rational-kernel-maximal-support-v1'
            or certificate.get('input_sha256') != _matrix_digest(rows, width)):
        return False
    try:
        primal = [_fraction(x) for x in certificate['primal']]
        dual = [_fraction(x) for x in certificate['dual']]
        multipliers = [_fraction(x) for x in certificate['multipliers']]
        retained = certificate['retained_indices']
    except (KeyError, TypeError, ValueError):
        return False
    if (len(primal) != width or len(dual) != width
            or len(multipliers) != len(rows) or type(retained) is not list
            or any(type(i) is not int for i in retained)):
        return False
    for row in rows:
        check()
        if sum(a*x for a, x in zip(row, primal)):
            return False
    for j, (x, y) in enumerate(zip(primal, dual)):
        check()
        if (x < 0 or y < 0 or x+y < 1 or x*y
                or sum(a*row[j] for a, row in zip(multipliers, rows)) != y):
            return False
    return retained == [j for j, x in enumerate(primal) if x > 0]


def _allowed(value, count, *, canonical):
    if type(value) not in (list, tuple):
        raise ValueError('allowed types must be a sequence')
    result = []
    for pair in value:
        if (type(pair) not in (list, tuple) or len(pair) != 2
                or any(type(x) is not int for x in pair)
                or not 0 <= pair[0] < count or not 0 <= pair[1] < 3):
            raise ValueError('invalid allowed type')
        result.append(tuple(pair))
    if len(set(t for t, _ in result)) != len(result):
        raise ValueError('incompatible or repeated allowed types')
    if canonical and result != sorted(result):
        raise ValueError('certificate support must be sorted')
    return sorted(result)


def verify_maximal_support_certificate(triangulation, allowed_types, certificate, *,
                                      check=lambda: None):
    """Check a source-normal primal and one source-row dual consequence.

    The primal is an actual integral normal vector. The dual combination must
    cancel every triangle coefficient, be nonnegative on all allowed quad
    types, and complement the primal quad vector with x+y>=1. Nonallowed quad
    coefficients are unrestricted because those source coordinates are zero.
    This licenses a maximal-support restriction, never an unknot verdict.
    """
    check()
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-sector-maximal-support-v1'):
        return False
    digest = sha256(json.dumps(triangulation, sort_keys=True,
                              separators=(',', ':')).encode()).hexdigest()
    if certificate.get('source_sha256') != digest:
        return False
    callback_failed = False
    def source_check():
        nonlocal callback_failed
        try:
            check()
        except BaseException:
            callback_failed = True
            raise
    try:
        prepared = _prepare(triangulation, source_check)
    except NormalOrbitError:
        if callback_failed:
            raise
        return False
    try:
        requested = _allowed(allowed_types, len(prepared['tetrahedra']), canonical=False)
        support = _allowed(certificate['allowed_types'], len(prepared['tetrahedra']),
                           canonical=True)
    except (KeyError, ValueError, TypeError):
        return False
    if requested != support:
        return False
    try:
        primal = _coordinates(prepared, certificate.get('primal_coordinates'), source_check)['rows']
    except NormalOrbitError:
        if callback_failed:
            raise
        return False
    allowed = set(support)
    for t, row in enumerate(primal):
        check()
        if any(row[4+q] and (t, q) not in allowed for q in range(3)):
            return False
    combination = certificate.get('row_combination')
    retained = certificate.get('retained_indices')
    if (type(combination) is not list or type(retained) is not list
            or any(type(i) is not int for i in retained)):
        return False
    consequence = {}
    previous = -1
    for term in combination:
        check()
        if (type(term) is not list or len(term) != 3 or type(term[0]) is not int
                or not previous < term[0] < len(prepared['matching'])):
            return False
        previous = term[0]
        try:
            weight = _fraction(term[1:])
        except (ValueError, TypeError):
            return False
        if not weight:
            return False
        for column, value in prepared['matching'][term[0]].items():
            consequence[column] = consequence.get(column, 0) + weight*value
    if any(value for column, value in consequence.items() if column % 7 < 4):
        return False
    positive = []
    for j, (t, q) in enumerate(support):
        check()
        x = primal[t][4+q]
        y = consequence.get(7*t+4+q, 0)
        if y < 0 or x+y < 1 or x*y:
            return False
        if x:
            positive.append(j)
    return retained == positive
