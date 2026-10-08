"""Exact two-field test components d=xI+yA over the two-dot algebra.

Construction is excluded from timed reduction calls.  `bridge` is the
explicit connected family in the proof; `dense` applies a seeded invertible
change of basis and independently checks its differential graph is connected.
These are valid graded complexes, not asserted realizations of knot scans.
"""
from random import Random

from fastunknot.scalar_split import FittingScan


def poly_multiply(left, right):
    result = 0
    while right:
        if right & 1:
            result ^= left
        left <<= 1
        right >>= 1
    return result


def poly_remainder(value, modulus):
    while value.bit_length() >= modulus.bit_length():
        value ^= modulus << (value.bit_length() - modulus.bit_length())
    return value


def poly_gcd(left, right):
    while right:
        left, right = right, poly_remainder(left, right)
    return left


def is_irreducible(polynomial):
    degree = polynomial.bit_length() - 1
    if degree < 1:
        return False
    x = poly_remainder(2, polynomial)
    power = x
    for step in range(1, degree + 1):
        power = poly_remainder(poly_multiply(power, power), polynomial)
        if step <= degree // 2 and poly_gcd(power ^ x, polynomial) != 1:
            return False
    return power == x


def irreducible_pair(degree):
    if type(degree) is not int or degree < 3:
        raise ValueError('the two-field family requires degree at least three')
    found = []
    for candidate in range((1 << degree) + 1, 1 << (degree + 1), 2):
        if is_irreducible(candidate):
            found.append(candidate)
            if len(found) == 2:
                return tuple(found)
    raise ArithmeticError('two irreducibles of the requested degree were not found')


def multiplication_matrix(value, modulus):
    degree = modulus.bit_length() - 1
    return [poly_remainder(value << col, modulus) for col in range(degree)]


def apply_matrix(matrix, vector):
    result = 0
    for col, value in enumerate(matrix):
        if vector >> col & 1:
            result ^= value
    return result


def multiply_matrices(left, right):
    return [apply_matrix(left, column) for column in right]


def inverse_matrix(matrix):
    size = len(matrix)
    rows = [sum(((column >> row) & 1) << col for col, column in enumerate(matrix))
            | (1 << (size + row)) for row in range(size)]
    for col in range(size):
        pivot = next(row for row in range(col, size) if rows[row] >> col & 1)
        rows[col], rows[pivot] = rows[pivot], rows[col]
        for row in range(size):
            if row != col and rows[row] >> col & 1:
                rows[row] ^= rows[col]
    return [sum(((rows[row] >> (size + col)) & 1) << row for row in range(size))
            for col in range(size)]


def two_field_matrix(degree, *, mixing='bridge', seed=2026100809):
    f, g = irreducible_pair(degree)
    size = 2 * degree
    direct = multiplication_matrix(2, f) + [value << degree for value in multiplication_matrix(2, g)]
    change = [1 << col for col in range(size)]
    change[degree] ^= 1  # S=[[I,e_1 e_1^T],[0,I]], with S^(-1)=S.
    if mixing == 'dense':
        rng = Random(seed)
        for _ in range(12 * size):
            source, target = rng.sample(range(size), 2)
            change[target] ^= change[source]
    elif mixing != 'bridge':
        raise ValueError('mixing must be bridge or dense')
    inverse = inverse_matrix(change)
    matrix = multiply_matrices(change, multiply_matrices(direct, inverse))
    identity = [1 << col for col in range(size)]
    if multiply_matrices(change, inverse) != identity:
        raise ArithmeticError('fixture change of basis is singular')
    return matrix, dict(degree=degree, f=f, g=g, change=change, inverse=inverse,
                        mixing=mixing, seed=seed, kind='graded algebraic component, not a knot fixture')


def two_field_scan(degree, *, mixing='bridge', seed=2026100809, **options):
    matrix, evidence = two_field_matrix(degree, mixing=mixing, seed=seed)
    size = len(matrix)
    options.setdefault('fitting_max_objects', 2 * size)
    options.setdefault('fitting_max_variables', 2 * size * size)
    scan = FittingScan(shape_cache=False, **options)
    matching = scan.algebra.intern(((0, 1), (2, 3)))
    scan.points = frozenset(range(4))
    scan.mid = [matching] * (2 * size)
    scan.deg = [0] * size + [1] * size
    scan.out = [{} for _ in scan.mid]
    for source in range(size):
        for target in range(size):
            coefficient = (2 if source == target else 0) ^ (4 if matrix[source] >> target & 1 else 0)
            if coefficient:
                scan.out[source][size + target] = coefficient
    scan.inc = [set() for _ in scan.mid]
    for source, row in enumerate(scan.out):
        for target in row:
            scan.inc[target].add(source)
    scan.live = len(scan.mid)
    scan.owner, scan.weights = [0] * scan.live, [{0: 1}]
    from fastunknot.component_scan import components
    if len(list(components(scan))) != 1:
        raise ArithmeticError('the chosen field fixture is not a connected differential graph')
    scan.check_d_squared()
    evidence['generator_columns'] = matrix
    return scan, evidence
