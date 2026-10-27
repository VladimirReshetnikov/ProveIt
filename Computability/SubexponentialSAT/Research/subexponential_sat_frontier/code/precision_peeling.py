#!/usr/bin/env python3
"""Exact precision peeling for a homogeneous cyclic tensor contraction.

This implements an arithmetic primitive, not a SAT solver.  A scaled matrix
is supplied by its canonical entries modulo 2**precision and an explicit
power of two dividing every entry.  The input residues are divided before
they are reduced to the smaller output precision.  No nonunit is inverted.

The same identity applies to any multilinear tensor contraction over a
commutative ring, provided known powers are removed from the appropriate
target tensors before any information-losing reduction.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Sequence

Matrix = tuple[tuple[int, ...], ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


@dataclass(frozen=True)
class ScaledMatrix:
    entries: Matrix
    valuation: int

    def normalized(self, input_precision: int, output_precision: int) -> Matrix:
        """Recover the normalized tensor at Q, requiring Q+v <= P.

        Input entries are frozen canonical P-bit representatives.  In a
        recursive implementation the returned Q-bit representatives must
        themselves be frozen; later operations may not re-evaluate their
        unfrozen high-precision formula.
        """
        require(input_precision >= 1 and output_precision >= 1,
                "precisions must be positive")
        require(self.valuation >= 0, "valuation must be nonnegative")
        require(output_precision + self.valuation <= input_precision,
                "insufficient precision before exact division")
        modulus = 1 << input_precision
        divisor = 1 << self.valuation
        mask = (1 << output_precision) - 1
        for row in self.entries:
            for value in row:
                require(0 <= value < modulus, "input is not a canonical residue")
                require(value % divisor == 0, "promised tensor valuation fails")
        return tuple(tuple((value >> self.valuation) & mask for value in row)
                     for row in self.entries)


def matmul(a: Matrix, b: Matrix, precision: int) -> Matrix:
    require(precision >= 1, "precision must be positive")
    require(bool(a) and bool(b) and bool(a[0]) and bool(b[0]), "empty matrix")
    require(all(len(row) == len(a[0]) for row in a), "ragged left matrix")
    require(all(len(row) == len(b[0]) for row in b), "ragged right matrix")
    require(len(a[0]) == len(b), "matrix dimensions do not match")
    mask = (1 << precision) - 1
    columns = tuple(zip(*b))
    return tuple(tuple(sum(x*y for x, y in zip(row, column)) & mask
                       for column in columns) for row in a)


def cycle_trace(matrices: Sequence[Matrix], precision: int) -> int:
    require(bool(matrices), "need at least one matrix")
    value = matrices[0]
    for matrix in matrices[1:]:
        value = matmul(value, matrix, precision)
    require(len(value) == len(value[0]), "cyclic contraction does not close")
    return sum(value[j][j] for j in range(len(value))) & ((1 << precision) - 1)


def full_precision_cycle(matrices: Sequence[ScaledMatrix], precision: int) -> int:
    return cycle_trace([matrix.entries for matrix in matrices], precision)


def peeled_cycle(matrices: Sequence[ScaledMatrix], precision: int) -> int:
    require(precision >= 1, "precision must be positive")
    require(bool(matrices), "need at least one matrix")
    require(all(matrix.valuation >= 0 for matrix in matrices),
            "valuation must be nonnegative")
    valuation = sum(matrix.valuation for matrix in matrices)
    if valuation >= precision:
        return 0
    residual = precision - valuation
    normalized = [matrix.normalized(precision, residual) for matrix in matrices]
    return cycle_trace(normalized, residual) << valuation


def fraction_v2(value: Fraction) -> int:
    require(value != 0, "zero has no finite valuation")
    numerator, denominator = abs(value.numerator), value.denominator
    return ((numerator & -numerator).bit_length()
            - (denominator & -denominator).bit_length())


def residue(value: Fraction, precision: int) -> int:
    require(value.denominator & 1 == 1, "nonintegral rational at 2")
    modulus = 1 << precision
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def actual_cauchy_ldu(a: int = 3):
    """Independent exact LDU of an actual permissible i=0 packet subblock.

    At t=1, zeta=1, T=1+2**(a+1), slots x=2k,y=2j give
      W[k,j] = A/(T+2*(k-j)), A=C(T)/C'(0), C(X)=prod_{h=-L}^{L-1}(X-h).
    This is the actual-domain block identified in round2/actual_domain.tex.
    The pivots have weights a+1+4b-2*popcount(b).  Elimination provides an
    independent decomposition; no earlier packet's executable code is used.
    """
    require(1 <= a <= 5, "small exact verification kernel only")
    size, length = 1 << (a-1), 1 << a
    t = 1 + (1 << (a+1))
    prefactor = Fraction(1)
    for h in range(-length, length):
        prefactor *= t-h
        if h:
            prefactor /= -h
    original = [[prefactor / (t+2*(i-j)) for j in range(size)]
                for i in range(size)]
    work = [row[:] for row in original]
    lower = [[Fraction(int(i == j)) for j in range(size)] for i in range(size)]
    upper = [[Fraction(int(i == j)) for j in range(size)] for i in range(size)]
    pivots = []
    for k in range(size):
        pivot = work[k][k]
        pivots.append(pivot)
        for i in range(k+1, size):
            lower[i][k] = work[i][k] / pivot
        for j in range(k+1, size):
            upper[k][j] = work[k][j] / pivot
        for i in range(k+1, size):
            for j in range(k+1, size):
                work[i][j] -= lower[i][k]*pivot*upper[k][j]
    weights = [a+1+4*b-2*b.bit_count() for b in range(size)]
    for k, pivot in enumerate(pivots):
        require(fraction_v2(pivot) == weights[k], "actual Smith pivot mismatch")
    target = [[lower[i][k]*pivots[k] for i in range(size)] for k in range(size)]
    source = [row[:] for row in upper]
    for i in range(size):
        for j in range(size):
            recovered = sum(target[k][i]*source[k][j] for k in range(size))
            require(recovered == original[i][j], "exact LDU reconstruction failed")
    return original, target, source, weights


def cauchy_cycle_checks(a: int = 3, groups: int = 3,
                       precisions: Sequence[int] = (8, 13, 20, 32, 50, 80)) -> dict:
    original, target, source, weights = actual_cauchy_ldu(a)
    size = len(original)
    local = [[((7*g+5*j+3) % 13)-6 for j in range(size)] for g in range(groups)]
    direct = Fraction(0)
    for slots in product(range(size), repeat=groups):
        term = Fraction(1)
        for g in range(groups):
            term *= local[g][slots[g]]*original[slots[g]][slots[(g+1) % groups]]
        direct += term
    factors = [[[sum(Fraction(local[g][x])*source[left][x]*target[right][x]
                     for x in range(size)) for right in range(size)]
                for left in range(size)] for g in range(groups)]
    checks = []
    for precision in precisions:
        modulus = 1 << precision
        baseline = 0
        peeled = 0
        tuples = 0
        residual_charge = 0
        for modes in product(range(size), repeat=groups):
            valuation = sum(weights[mode] for mode in modes)
            if valuation >= precision:
                continue
            tuples += 1
            q = precision-valuation
            residual_charge += q
            old, new = 1, 1
            for g in range(groups):
                factor = factors[g][modes[g-1]][modes[g]]
                old = old * residue(factor, precision) % modulus
                # Exact division BEFORE reduction to the residual precision.
                normalized = factor / (1 << weights[modes[g]])
                new = new * residue(normalized, q) % (1 << q)
            baseline = (baseline+old) % modulus
            peeled = (peeled+(new << valuation)) % modulus
        expected = residue(direct, precision)
        require(baseline == peeled == expected,
                "Cauchy mode sum disagrees with independent original-kernel sum")
        checks.append({"precision": precision, "retained_tuples": tuples,
                       "full_precision_charge": precision*tuples,
                       "residual_precision_charge": residual_charge,
                       "residue": expected})
    return {"a": a, "groups": groups, "mode_weights": weights, "checks": checks}


def residual_precision_inventory(precision: int, families: int = 1,
                                 offset: int = 1) -> dict:
    """Exact colored-partition work model, not a runtime prediction.

    One mode family has weights offset+4b-2*popcount(b), b>=0.
    Multiplicity of every weight is `families`.  Tuples have nonnegative
    exponents and total weight < precision.  Modes of larger weight cannot
    participate and are safely omitted.
    """
    require(precision >= 1 and families >= 1 and offset >= 1, "invalid inventory")
    counts = [0]*precision
    counts[0] = 1
    b = 0
    while True:
        weight = offset+4*b-2*b.bit_count()
        if weight >= precision:
            break
        for _ in range(families):
            for budget in range(weight, precision):
                counts[budget] += counts[budget-weight]
        b += 1
    total = sum(counts)
    residual = sum((precision-weight)*count for weight, count in enumerate(counts))
    square = sum((precision-weight)**2*count for weight, count in enumerate(counts))
    cumulative = 0
    independently_summed = 0
    for count in counts:
        cumulative += count
        independently_summed += cumulative
    require(residual == independently_summed, "residual work identity failed")
    return {"precision": precision, "families": families, "offset": offset,
            "retained_tuples": str(total), "mean_residual_precision": residual/total,
            "linear_charge_ratio": residual/(precision*total),
            "quadratic_charge_ratio": square/(precision*precision*total),
            "residual_charge_exact": str(residual)}
