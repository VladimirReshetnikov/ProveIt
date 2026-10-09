"""Exact coordinates for the matching space supported by a normal surface.

The producer chooses a minimum-source-bit-cost coordinate projection using
column-matroid greedy selection. Sparse fraction-free elimination supplies
an integer decoder. Independent validation is in normal_support_verify;
the producer never invokes that checker or claims a knot verdict.
"""

from math import gcd

from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare, _coordinates


def _blocks(support, equations, check):
    """Connected column blocks, including unconstrained singleton columns."""
    parent = {i: i for i in support}

    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for _, row in equations:
        check()
        columns = list(row)
        if columns:
            a = root(columns[0])
            for i in columns[1:]:
                b = root(i)
                if a != b:
                    parent[b] = a
    groups, grouped_rows = {}, {}
    for i in support:
        check()
        groups.setdefault(root(i), []).append(i)
    for index, row in equations:
        if row:
            grouped_rows.setdefault(root(next(iter(row))), []).append((index, row))
    return [(columns, grouped_rows.get(key, []))
            for key, columns in sorted(groups.items(), key=lambda item: min(item[1]))]


def _fraction_free(columns, equations, costs, check):
    """Bareiss elimination in greedy column order, then integral backsolve.

    Intermediate entries are signed minors. A zero pivot column is skipped;
    a nonzero pivot row is chosen by current sparsity and original row index.
    Only trailing rows and their nonzero entries are stored.
    """
    order = sorted(columns, key=lambda i: (-costs[i], i))
    rows = [dict(row) for _, row in equations]
    identifiers = [index for index, _ in equations]
    pivots, pivot_rows, rank, previous = [], [], 0, 1
    for column in order:
        check()
        candidates = [i for i in range(rank, len(rows)) if rows[i].get(column)]
        if not candidates:
            continue
        chosen = min(candidates, key=lambda i: (len(rows[i]), identifiers[i]))
        rows[rank], rows[chosen] = rows[chosen], rows[rank]
        identifiers[rank], identifiers[chosen] = identifiers[chosen], identifiers[rank]
        donor = rows[rank]
        pivot = donor[column]
        for i in range(rank + 1, len(rows)):
            check()
            row = rows[i]
            if not row:
                continue
            coefficient = row.get(column, 0)
            positions = row.keys() | donor.keys() if coefficient else row.keys()
            updated = {}
            for j in positions:
                if j == column:
                    continue
                value = pivot * row.get(j, 0) - coefficient * donor.get(j, 0)
                quotient, remainder = divmod(value, previous)
                if remainder:
                    raise ArithmeticError('fraction-free matching division was not exact')
                if quotient:
                    updated[j] = quotient
            rows[i] = updated
        pivots.append(column)
        pivot_rows.append(identifiers[rank])
        rank += 1
        previous = pivot
        if rank == len(rows):
            break
    selected = sorted(set(columns) - set(pivots))
    denominator = abs(previous)
    dimension = len(selected)
    numerators = {i: [0] * dimension for i in columns}
    for j, column in enumerate(selected):
        numerators[column][j] = denominator
    for pivot, row in reversed(list(zip(pivots, rows[:rank]))):
        check()
        for j in range(dimension):
            value = -sum(coefficient * numerators[i][j]
                         for i, coefficient in row.items() if i != pivot)
            quotient, remainder = divmod(value, row[pivot])
            if remainder:
                raise ArithmeticError('Cramer-scaled matching decoder was not integral')
            numerators[pivot][j] = quotient
    return pivots, pivot_rows, selected, denominator, numerators


def _modulus(denominator, check):
    """First prime not dividing the selected minor; primality is not trusted."""
    primes, candidate = [], 2
    while True:
        check()
        if all(candidate % p for p in primes if p * p <= candidate):
            primes.append(candidate)
            if denominator % candidate:
                return candidate
        candidate += 1


def compile_support(prepared, analysed, check=lambda: None):
    """Compile the exact supported matching space to a JSON-shaped certificate.

    The certificate is reusable for any validated surface having exactly the
    same positive support. Minimum bit cost refers to this compilation input;
    verification establishes the decoder and rank, not cost optimality.
    Empty support has rank and nullity zero, with no artificial coordinate.
    """
    check()
    source = [value for row in analysed['rows'] for value in row]
    if any(type(value) is not int or value < 0 for value in source):
        raise ValueError('analysed coordinates must be nonnegative integers')
    support = [i for i, value in enumerate(source) if value]
    present = set(support)
    equations = []
    for index, equation in enumerate(prepared['matching']):
        check()
        if (any(type(i) is not int or not 0 <= i < len(source)
                or type(value) is not int for i, value in equation.items())
                or sum(value * value for value in equation.values()) > 4):
            raise ValueError('matching row violates the finite normal-row contract')
        row = {i: value for i, value in equation.items() if i in present and value}
        if sum(value * source[i] for i, value in row.items()):
            raise ValueError('analysed source fails the matching equations')
        if row:
            equations.append((index, row))
    costs = {i: source[i].bit_length() for i in support}
    pieces, denominator = [], 1
    for columns, rows in _blocks(support, equations, check):
        piece = _fraction_free(columns, rows, costs, check)
        pieces.append(piece)
        denominator *= piece[3]
    selected = sorted(i for piece in pieces for i in piece[2])
    positions = {i: j for j, i in enumerate(selected)}
    dimension = len(selected)
    numerators = {i: [0] * dimension for i in support}
    pivots, pivot_rows = [], []
    for local_pivots, local_rows, local_free, scale, local in pieces:
        check()
        pivots.extend(local_pivots)
        pivot_rows.extend(local_rows)
        factor = denominator // scale
        for i, row in local.items():
            for j, value in enumerate(row):
                numerators[i][positions[local_free[j]]] = value * factor
    rank = len(pivots)
    limit = 1 << rank
    if denominator > limit or any(abs(value) > limit
                                  for row in numerators.values() for value in row):
        raise ArithmeticError('matching decoder violates the minor height bound')
    # A failed exact nullspace check identifies implementation errors before
    # publication; it is not a substitute for independent certificate replay.
    for _, row in equations:
        check()
        for j in range(dimension):
            if sum(value * numerators[i][j] for i, value in row.items()):
                raise ArithmeticError('matching decoder has a nonzero residual')
    return dict(schema='normal-support-kernel-v1', support=support,
                selected=selected, pivots=pivots, pivot_rows=pivot_rows,
                rank=rank, nullity=dimension, denominator=denominator,
                numerators=[numerators[i] for i in support],
                modulus=_modulus(denominator, check))


def compile_normal_support(triangulation, coordinates, *, check=lambda: None):
    """Validate a finite supplied triangulation and compile its source support."""
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    return compile_support(prepared, analysed, check)


def decode_support(analysed, certificate, weight, check=lambda: None):
    """Decode one weight after independent certificate validation.

    This helper checks integer transport, divisibility and source bounds. It
    intentionally does not reverify the entire rank certificate per component.
    The empty-space weight is [], regardless of an outer API's dummy weight.
    """
    check()
    dimension = encoded_integer(certificate['nullity'])
    if type(weight) not in (list, tuple) or len(weight) != dimension:
        raise ValueError('supported coordinate dimension differs')
    values = [encoded_integer(value) for value in weight]
    source = [value for row in analysed['rows'] for value in row]
    support = [encoded_integer(i) for i in certificate['support']]
    denominator = encoded_integer(certificate['denominator'])
    if denominator <= 0 or len(certificate['numerators']) != len(support):
        raise ValueError('invalid supported coordinate decoder')
    vector = [0] * len(source)
    for i, row in zip(support, certificate['numerators']):
        check()
        if not 0 <= i < len(source) or type(row) is not list or len(row) != dimension:
            raise ValueError('invalid supported decoder row')
        numerator = sum(encoded_integer(a) * b for a, b in zip(row, values))
        value, remainder = divmod(numerator, denominator)
        if remainder or not 0 <= value <= source[i]:
            raise ValueError('decoded component is nonintegral or outside its source')
        vector[i] = value
    return vector
