"""Exact coefficient compression for the scalar commutant of a typed complex.

For each ordered pair of scalar types, write the differential block as
sum(g_i A_i), with linearly independent packed morphisms g_i.  Scalar
commutation with that block is equivalent to commutation with every A_i.
The ``forest`` mode also eliminates matrix unknowns along a forest of
invertible A_i.  These are substitutions in the endomorphism equations;
objects with different matching or grading types are never identified.

The resulting complete solution space is returned in the original variable
ordering and canonical basis.  Thus the bounded scalar candidate policy is
unchanged.  No equations or bases may be reused after differential mutation.
"""
from __future__ import annotations

from .barcode_scan import _apply


MODES = ('direct', 'span', 'forest')
STAT_KEYS = ('blocks', 'entries', 'input_terms', 'rank', 'coordinate_terms',
             'equations', 'forest_edges', 'original_variables',
             'reduced_variables', 'transported_vectors')


def validate_mode(mode):
    if type(mode) is not str or mode not in MODES:
        raise ValueError('coefficient_mode must be direct, span, or forest')


def _poll(check):
    if check is not None:
        check()


def factor_coefficients(entries, source_size, target_size, *, check=None):
    """Factor a sparse matrix of binary morphisms without enumerating its bits.

    ``entries`` contains (source, target, packed_morphism), with unique matrix
    positions.  Return independent morphism values and binary column matrices.
    Their linear combination reconstructs the input matrix exactly.  Gaussian
    elimination acts on the packed morphisms themselves, so the coefficient
    rank is at most the number of nonzero matrix entries.
    """
    if (type(source_size) is not int or source_size < 0
            or type(target_size) is not int or target_size < 0):
        raise ValueError('matrix dimensions must be nonnegative integers')
    pivots, values, matrices, occupied = {}, [], [], set()
    for source, target, original in entries:
        _poll(check)
        if (type(source) is not int or not 0 <= source < source_size
                or type(target) is not int or not 0 <= target < target_size
                or type(original) is not int or original < 0):
            raise ValueError('invalid sparse morphism-matrix entry')
        if (source, target) in occupied:
            raise ValueError('matrix positions must be unique')
        occupied.add((source, target))
        value, coordinates, steps = original, 0, 0
        while value:
            if not steps & 127:
                _poll(check)
            steps += 1
            pivot = value.bit_length() - 1
            if pivot in pivots:
                residual, index = pivots[pivot]
                value ^= residual
                coordinates ^= 1 << index
            else:
                index = len(values)
                values.append(value)
                matrices.append([0] * source_size)
                pivots[pivot] = value, index
                coordinates ^= 1 << index
                break
        while coordinates:
            bit = coordinates & -coordinates
            matrices[bit.bit_length() - 1][source] ^= 1 << target
            coordinates ^= bit
    return values, matrices


def _typed_coefficients(scan, group, blocks, check, stats):
    locations = {v: (bi, i) for bi, block in enumerate(blocks)
                 for i, v in enumerate(block)}
    entries = {}
    for source in group:
        _poll(check)
        si, source_index = locations[source]
        for target, value in scan.out[source].items():
            ti, target_index = locations[target]
            entries.setdefault((si, ti), []).append((source_index, target_index, value))
    coefficients = {}
    for (si, ti), values in entries.items():
        _poll(check)
        _, matrices = factor_coefficients(values, len(blocks[si]), len(blocks[ti]),
                                           check=check)
        coefficients[si, ti] = matrices
        stats['blocks'] += 1
        stats['entries'] += len(values)
        stats['input_terms'] += sum(value.bit_count() for _, _, value in values)
        stats['rank'] += len(matrices)
        stats['coordinate_terms'] += sum(c.bit_count() for a in matrices for c in a)
    return coefficients


def _inverse(columns, check):
    if columns == _identity(len(columns)):
        return list(columns)
    pivots = {}
    for index, original in enumerate(columns):
        _poll(check)
        column, coefficient = original, 1 << index
        while column:
            _poll(check)
            pivot = column.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = column, coefficient
                break
            row, change = pivots[pivot]
            column ^= row
            coefficient ^= change
        else:
            return None
    result = []
    for index in range(len(columns)):
        _poll(check)
        column, coefficient = 1 << index, 0
        while column:
            row, change = pivots[column.bit_length() - 1]
            column ^= row
            coefficient ^= change
        result.append(coefficient)
    return result


def _multiply(left, right, check):
    result = []
    for column in right:
        _poll(check)
        result.append(_apply(left, column))
    return result


def _identity(size):
    return [1 << i for i in range(size)]


def _forest(blocks, coefficients, check, stats):
    """Return roots and mutually inverse transports from each chosen root."""
    parents = list(range(len(blocks)))
    adjacency = [[] for _ in blocks]

    def root(index):
        while parents[index] != index:
            parents[index] = parents[parents[index]]
            index = parents[index]
        return index

    for (si, ti), matrices in coefficients.items():
        _poll(check)
        if len(blocks[si]) != len(blocks[ti]) or root(si) == root(ti):
            continue
        for matrix in matrices:
            inverse = _inverse(matrix, check)
            if inverse is None:
                continue
            adjacency[si].append((ti, matrix, inverse))
            adjacency[ti].append((si, inverse, matrix))
            parents[root(ti)] = root(si)
            stats['forest_edges'] += 1
            break
    roots, changes, inverses = {}, {}, {}
    for start, block in enumerate(blocks):
        if start in roots:
            continue
        roots[start] = start
        changes[start] = inverses[start] = _identity(len(block))
        pending = [start]
        while pending:
            source = pending.pop()
            _poll(check)
            for target, matrix, inverse in adjacency[source]:
                if target in roots:
                    continue
                roots[target] = start
                changes[target] = _multiply(matrix, changes[source], check)
                inverses[target] = _multiply(inverses[source], inverse, check)
                pending.append(target)
    return roots, changes, inverses


def _equations(matrix, source_size, target_size, source_offset, target_offset, check):
    """Rows of Y A + A X=0 in row-major packed matrix unknowns."""
    row_seeds = [0] * target_size
    for source, column in enumerate(matrix):
        _poll(check)
        while column:
            bit = column & -column
            row_seeds[bit.bit_length() - 1] ^= 1 << (source * source_size)
            column ^= bit
    for target, seed in enumerate(row_seeds):
        _poll(check)
        left_offset = target_offset + target * target_size
        for source, column in enumerate(matrix):
            row = (column << left_offset) ^ (seed << (source_offset + source))
            if row:
                yield row


def _transport_basis(basis, blocks, variables, roots, offsets, changes, inverses, check):
    from .corner_split import canonical_binary_span
    count = sum(len(blocks[root]) ** 2 for root in offsets)
    lifts = [0] * count
    for index, block in enumerate(blocks):
        _poll(check)
        size, root = len(block), roots[index]
        original = variables[block[0], block[0]]
        reduced = offsets[root]
        if changes[index] == _identity(size):
            for position in range(size * size):
                lifts[reduced + position] |= 1 << (original + position)
            continue
        inverse_rows = [sum(((column >> row) & 1) << col
                            for col, column in enumerate(inverses[index]))
                        for row in range(size)]
        # S E_(a,b) S^-1 is the outer product of column a of S and row b of S^-1.
        for row_index, column in enumerate(changes[index]):
            _poll(check)
            for col_index, inverse_row in enumerate(inverse_rows):
                outer, remaining = 0, column
                while remaining:
                    bit = remaining & -remaining
                    outer |= inverse_row << (original + (bit.bit_length() - 1) * size)
                    remaining ^= bit
                lifts[reduced + row_index * size + col_index] |= outer
    result = []
    for vector in basis:
        _poll(check)
        full = 0
        while vector:
            bit = vector & -vector
            full ^= lifts[bit.bit_length() - 1]
            vector ^= bit
        result.append(full)
    return canonical_binary_span(result, check=check or (lambda: None))


def coefficient_endomorphism_basis(scan, group, blocks, variables, *, mode='span',
                                   check=None, stats=None):
    """Complete canonical commutant using coefficient spans, optionally a forest.

    The caller first applies the original object/variable caps and verifies
    the grading partition.  ``blocks`` and ``variables`` must have the scalar
    solver's block-contiguous, row-major ordering.  ``stats`` receives local
    operation counts, not cumulative or cached estimates.
    """
    from .scalar_split import binary_nullspace
    validate_mode(mode)
    if mode == 'direct':
        raise ValueError('the direct comparator is implemented by scalar_split')
    local = {key: 0 for key in STAT_KEYS}
    local['original_variables'] = len(variables)
    coefficients = _typed_coefficients(scan, group, blocks, check, local)
    if mode == 'forest':
        roots, changes, inverses = _forest(blocks, coefficients, check, local)
    else:
        roots = {index: index for index in range(len(blocks))}
        changes = inverses = None
    identities = {index: changes[index] == _identity(len(block))
                  for index, block in enumerate(blocks)} if changes is not None else {}
    offsets, count = {}, 0
    for index, block in enumerate(blocks):
        if roots[index] == index:
            offsets[index] = count
            count += len(block) ** 2
    local['reduced_variables'] = count
    equations = []
    for (si, ti), matrices in coefficients.items():
        for matrix in matrices:
            _poll(check)
            if mode == 'forest' and local['forest_edges']:
                if not identities[si]:
                    matrix = _multiply(matrix, changes[si], check)
                if not identities[ti]:
                    matrix = _multiply(inverses[ti], matrix, check)
            equations.extend(_equations(matrix, len(blocks[si]), len(blocks[ti]),
                offsets[roots[si]], offsets[roots[ti]], check))
    local['equations'] = len(equations)
    basis = binary_nullspace(equations, count, check)
    if local['forest_edges']:
        local['transported_vectors'] = len(basis)
        basis = _transport_basis(basis, blocks, variables, roots, offsets,
                                 changes, inverses, check)
    if stats is not None:
        stats.update(local)
    _poll(check)
    return basis, len(equations)
