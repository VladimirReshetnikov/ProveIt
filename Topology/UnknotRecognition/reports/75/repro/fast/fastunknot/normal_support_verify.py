"""Independent rank and integer-decoder verification for normal support.

No producer elimination, block decomposition or decoder routine is imported.
Exact matching residuals certify a lower nullity bound. Unit-pivot modular
elimination of a supplied minor certifies the complementary rank bound.
The modulus need not be prime; nonzero nonunit pivots are never inverted.
"""

from math import gcd

from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError


_FIELDS = {'schema', 'support', 'selected', 'pivots', 'pivot_rows', 'rank',
           'nullity', 'denominator', 'numerators', 'modulus'}
_BAD = object()


def _integer(value):
    try:
        return encoded_integer(value)
    except ValueError:
        return _BAD


def _indices(value, check):
    if type(value) is not list:
        return None
    result = []
    for item in value:
        check()
        item = _integer(item)
        if item is _BAD:
            return None
        result.append(item)
    return result


def _unit_minor(equations, rows, columns, modulus, check):
    """Independent sparse modular row elimination with certified unit pivots."""
    position = {column: i for i, column in enumerate(columns)}
    matrix = []
    for index in rows:
        check()
        row = {}
        for column, value in equations[index].items():
            if column in position and value % modulus:
                row[position[column]] = value % modulus
        matrix.append(row)
    for column in range(len(columns)):
        check()
        chosen = None
        for i in range(column, len(matrix)):
            if gcd(matrix[i].get(column, 0), modulus) == 1:
                chosen = i
                break
        if chosen is None:
            return False
        matrix[column], matrix[chosen] = matrix[chosen], matrix[column]
        pivot = matrix[column]
        inverse = pow(pivot[column], -1, modulus)
        for i in range(column + 1, len(matrix)):
            check()
            target = matrix[i]
            factor = target.get(column, 0) * inverse % modulus
            if not factor:
                continue
            for j, value in pivot.items():
                updated = (target.get(j, 0) - factor * value) % modulus
                if updated:
                    target[j] = updated
                else:
                    target.pop(j, None)
    return True


def verify_support(prepared, analysed, certificate, check=lambda: None):
    """Return False for malformed algebraic evidence; cancellation propagates.

    The caller supplies already validated finite geometry and coordinates.
    A certificate may be reused with different magnitudes on the same support.
    Coordinate selection need not be the producer's optimum to be sound.
    """
    check()
    if (type(certificate) is not dict or set(certificate) != _FIELDS
            or certificate['schema'] != 'normal-support-kernel-v1'):
        return False
    source = [value for row in analysed['rows'] for value in row]
    expected_support = [i for i, value in enumerate(source) if value > 0]
    support = _indices(certificate['support'], check)
    selected = _indices(certificate['selected'], check)
    pivots = _indices(certificate['pivots'], check)
    rows = _indices(certificate['pivot_rows'], check)
    if (support != expected_support or selected is None or pivots is None
            or rows is None):
        return False
    rank = _integer(certificate['rank'])
    dimension = _integer(certificate['nullity'])
    denominator = _integer(certificate['denominator'])
    modulus = _integer(certificate['modulus'])
    if any(value is _BAD for value in (rank, dimension, denominator, modulus)):
        return False
    size = len(support)
    if (not 0 <= rank <= size or dimension != size - rank
            or len(pivots) != rank or len(rows) != rank
            or len(selected) != dimension or selected != sorted(set(selected))
            or len(set(pivots)) != rank or len(set(rows)) != rank
            or set(selected) & set(pivots) or set(selected) | set(pivots) != set(support)
            or any(not 0 <= i < len(prepared['matching']) for i in rows)
            or not 1 <= denominator <= 1 << rank or modulus < 2
            or modulus.bit_length() > rank + 2):
        return False
    raw = certificate['numerators']
    if type(raw) is not list or len(raw) != size:
        return False
    numerators = {}
    bound = 1 << rank
    for i, row in zip(support, raw):
        check()
        values = _indices(row, check)
        if values is None or len(values) != dimension or any(abs(x) > bound for x in values):
            return False
        numerators[i] = values
    for j, i in enumerate(selected):
        check()
        if any(value != (denominator if j == k else 0)
               for k, value in enumerate(numerators[i])):
            return False
    # Reconstruct every restricted row separately from the producer; check
    # both the source and every claimed kernel column against all rows.
    present = set(support)
    for equation in prepared['matching']:
        check()
        restricted = [(i, value) for i, value in equation.items() if i in present]
        if sum(value * source[i] for i, value in restricted):
            return False
        for j in range(dimension):
            if sum(value * numerators[i][j] for i, value in restricted):
                return False
    return _unit_minor(prepared['matching'], rows, pivots, modulus, check)


def verify_normal_support(triangulation, coordinates, certificate, *, check=lambda: None):
    """Reconstruct finite geometry and validate a supported matching decoder."""
    callback_error = [None]

    def checked():
        try:
            check()
        except BaseException as exc:
            callback_error[0] = exc
            raise

    checked()
    try:
        prepared = _prepare(triangulation, checked)
        analysed = _coordinates(prepared, coordinates, checked)
    except NormalOrbitError:
        if callback_error[0] is not None:
            raise
        return False
    return verify_support(prepared, analysed, certificate, checked)
