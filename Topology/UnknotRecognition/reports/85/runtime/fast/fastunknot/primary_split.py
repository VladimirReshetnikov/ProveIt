"""Polynomial idempotents for a typed binary chain endomorphism.

The Frobenius fixed space in F2[t]/(m) is Berlekamp's algebra.  Its
dimension is the number of distinct irreducible factors of m, including
when m has repeated factors.  A nonconstant fixed polynomial gives an
idempotent p(Q), without factoring m or extending the coefficient field.

This module only produces scalar block matrices.  The caller must check
their types, commutation with the whole differential, and the transformed
cross terms.  A primary Q can have no polynomial projector even when its
ambient chain complex decomposes; a negative result is never conclusive.
"""
from __future__ import annotations

from .barcode_scan import _apply


def _poll(check):
    if check is not None:
        check()


def _validated_blocks(columns):
    matrices = [list(matrix) for matrix in columns]
    if not matrices or not any(matrices):
        raise ValueError('at least one nonempty binary matrix block is required')
    for matrix in matrices:
        bound = 1 << len(matrix)
        if any(type(column) is not int or not 0 <= column < bound for column in matrix):
            raise ValueError('matrix columns must be nonnegative packed binary vectors')
    return matrices


def _pack(matrices):
    packed, offset = 0, 0
    for matrix in matrices:
        size = len(matrix)
        for column in matrix:
            packed |= column << offset
            offset += size
    return packed


def _unpack(packed, sizes):
    matrices, offset = [], 0
    for size in sizes:
        mask = (1 << size) - 1
        matrices.append([(packed >> (offset + size * col)) & mask for col in range(size)])
        offset += size * size
    return matrices


def _multiply(left, right, check=None):
    result = []
    for lhs, rhs in zip(left, right):
        _poll(check)
        block = []
        for index, column in enumerate(rhs):
            if not index & 31:
                _poll(check)
            block.append(_apply(lhs, column))
        result.append(block)
    return result


def _relation(value, coefficient, pivots, check=None):
    steps = 0
    while value:
        if not steps & 63:
            _poll(check)
        steps += 1
        pivot = value.bit_length() - 1
        if pivot not in pivots:
            pivots[pivot] = value, coefficient
            return None
        row, change = pivots[pivot]
        value ^= row
        coefficient ^= change
    return coefficient


def _minimal_data(matrices, check=None):
    """First dependence of I,Q,...,Q^d, with faithful packed powers."""
    current = [[1 << col for col in range(len(block))] for block in matrices]
    pivots, powers = {}, []
    dimension = sum(map(len, matrices))
    for exponent in range(dimension + 1):
        _poll(check)
        packed = _pack(current)
        relation = _relation(packed, 1 << exponent, pivots, check)
        if relation is not None:
            if not relation >> exponent == 1:
                raise ArithmeticError('minimal-polynomial relation is not monic')
            return relation, powers
        powers.append(packed)
        current = _multiply(matrices, current, check)
    raise ArithmeticError('Cayley-Hamilton bound failed')


def minimal_polynomial(columns, *, check=None):
    """Minimal polynomial of a direct sum, encoded by binary coefficients."""
    _poll(check)
    result, _ = _minimal_data(_validated_blocks(columns), check)
    _poll(check)
    return result


def polynomial_remainder(value, modulus):
    """Remainder in F2[t]; the two arguments are coefficient bit masks."""
    if type(value) is not int or value < 0 or type(modulus) is not int or modulus < 2:
        raise ValueError('require a nonnegative polynomial and a nonconstant modulus')
    degree = modulus.bit_length() - 1
    while value and value.bit_length() - 1 >= degree:
        value ^= modulus << (value.bit_length() - 1 - degree)
    return value


def berlekamp_basis(modulus, *, check=None):
    """Basis of {p: deg(p)<deg(m), p^2=p mod m}, with repeated factors allowed."""
    if type(modulus) is not int or modulus < 2:
        raise ValueError('the modulus must be a nonconstant binary polynomial')
    degree = modulus.bit_length() - 1
    pivots, basis = {}, []
    for exponent in range(degree):
        _poll(check)
        column = polynomial_remainder((1 << (2 * exponent)) ^ (1 << exponent), modulus)
        relation = _relation(column, 1 << exponent, pivots, check)
        if relation is not None:
            basis.append(relation)
    _poll(check)
    return basis


def evaluate_polynomial(columns, polynomial, *, check=None):
    """Evaluate a coefficient-bit-mask polynomial by independent Horner steps."""
    if type(polynomial) is not int or polynomial < 0:
        raise ValueError('the polynomial must be a nonnegative integer')
    matrices = _validated_blocks(columns)
    result = [[0] * len(block) for block in matrices]
    for exponent in reversed(range(polynomial.bit_length())):
        _poll(check)
        result = _multiply(matrices, result, check)
        if polynomial >> exponent & 1:
            for block in result:
                for index in range(len(block)):
                    block[index] ^= 1 << index
    _poll(check)
    return result


def primary_projector(columns, *, check=None):
    """Return a nontrivial polynomial projector and evidence, or (None, evidence).

    The first dependence supplies the actual minimal polynomial; a mere
    annihilating polynomial would not justify the claimed negative result.
    For the positive result, idempotence and nontriviality are checked again
    on the actual matrices.  O(B^4) elementary binary operations and O(B^3)
    bits suffice for B total scalar dimensions using the elementary methods
    here.  Scanner-side component and variable caps must be applied first.
    """
    _poll(check)
    matrices = _validated_blocks(columns)
    modulus, powers = _minimal_data(matrices, check)
    fixed = berlekamp_basis(modulus, check=check)
    evidence = dict(minimal_polynomial=modulus, minimal_degree=len(powers),
                    berlekamp_dimension=len(fixed), projector_polynomial=None)
    polynomial = next((value for value in fixed if value not in (0, 1)), None)
    if polynomial is None:
        _poll(check)
        return None, evidence
    packed = 0
    for index, power in enumerate(powers):
        if polynomial >> index & 1:
            packed ^= power
    projector = _unpack(packed, list(map(len, matrices)))
    identity = [[1 << col for col in range(len(block))] for block in matrices]
    if not packed or projector == identity or _multiply(projector, projector, check) != projector:
        raise ArithmeticError('the polynomial did not give a nontrivial idempotent')
    evidence['projector_polynomial'] = polynomial
    _poll(check)
    return projector, evidence


def verify_primary_projector(candidate, projector, evidence, *, check=None):
    """Verify a positive polynomial-projector certificate without rediscovery.

    Horner evaluation is separate from discovery's packed power basis.
    This verifies an annihilating polynomial, the displayed idempotent, and
    its nontriviality.  It does not certify that the polynomial is minimal
    or that berlekamp_dimension is accurate; neither is needed to accept a
    split.  Types, differential commutation and conjugation are checked by
    the surrounding scalar-split verifier.
    """
    _poll(check)
    matrices = _validated_blocks(candidate)
    claimed = _validated_blocks(projector)
    if list(map(len, matrices)) != list(map(len, claimed)):
        raise ValueError('candidate and projector blocks must have the same sizes')
    modulus, polynomial = evidence['minimal_polynomial'], evidence['projector_polynomial']
    if type(modulus) is not int or modulus < 2:
        raise ValueError('invalid annihilating polynomial')
    degree = modulus.bit_length() - 1
    if degree > sum(map(len, matrices)) or evidence['minimal_degree'] != degree:
        raise ValueError('invalid polynomial-degree bound')
    if type(polynomial) is not int or not 1 < polynomial < 1 << degree:
        raise ValueError('the projector polynomial must be nonconstant and reduced')
    zero = [[0] * len(block) for block in matrices]
    identity = [[1 << col for col in range(len(block))] for block in matrices]
    square = sum(((polynomial >> index) & 1) << (2 * index) for index in range(degree))
    if polynomial_remainder(square ^ polynomial, modulus):
        raise ArithmeticError('the polynomial is not Frobenius fixed')
    if evaluate_polynomial(matrices, modulus, check=check) != zero:
        raise ArithmeticError('the displayed polynomial does not annihilate the candidate')
    if evaluate_polynomial(matrices, polynomial, check=check) != claimed:
        raise ArithmeticError('the displayed projector is not p(Q)')
    if claimed in (zero, identity) or _multiply(claimed, claimed, check) != claimed:
        raise ArithmeticError('the displayed matrix is not a nontrivial idempotent')
    _poll(check)
    return True
