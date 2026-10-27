"""Exact incremental conditional expectations for collision packing.

This matches the balanced-packing prototype's full trace and tie breaking.
It is a kernel, not a SAT solver. All arithmetic uses the standard library.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

@dataclass(frozen=True)
class Step:
    vertex: int
    before: Fraction
    candidates: tuple[Fraction, ...]
    choice: int
    after: Fraction

@dataclass(frozen=True)
class LabelingResult:
    column_labels: tuple[int, ...]
    cell_loads: tuple[tuple[int, ...], ...]
    initial_potential: Fraction
    final_potential: Fraction
    threshold: int
    steps: tuple[Step, ...]

    @property
    def maximum_load(self) -> int:
        return max((load for row in self.cell_loads for load in row), default=0)


def _validate(weights: Sequence[Sequence[int]], groups: int, z: Fraction,
              threshold: int):
    if not isinstance(groups, int) or groups < 1 or len(weights) != groups:
        raise ValueError('Require exactly groups weight rows')
    columns = len(weights[0])
    if any(len(row) != columns for row in weights):
        raise ValueError('Weight rows must have equal lengths')
    if any(not isinstance(w, int) or w < 0 for row in weights for w in row):
        raise ValueError('Weights must be nonnegative integers')
    z = Fraction(z)
    if z <= 1 or not isinstance(threshold, int) or threshold < 0:
        raise ValueError('Require z > 1 and a nonnegative integer threshold')
    return tuple(tuple(row) for row in weights), columns, z


def derandomize_incremental(weights, groups, z, threshold):
    """Rational sufficient statistics; output includes every candidate potential."""
    weights, columns, z = _validate(weights, groups, z, threshold)
    values = {w: z ** w for row in weights for w in row}
    factors = {w: (groups - 1 + p) / groups for w, p in values.items()}
    unassigned = []
    for row in weights:
        value = Fraction(1)
        for w in row:
            if w:
                value *= factors[w]
        unassigned.append(value)
    powers = [[Fraction(1)] * groups for _ in range(groups)]
    sums = [Fraction(groups)] * groups
    cells = [[0] * groups for _ in range(groups)]
    normalization = z ** threshold
    current_raw = groups * sum(unassigned, Fraction(0))
    initial = current_raw / normalization
    labels, history = [], []
    for vertex in range(columns):
        base = current_raw
        scores = [Fraction(0)] * groups
        affected = []
        for row in range(groups):
            w = weights[row][vertex]
            if not w:
                continue
            previous = unassigned[row]
            unassigned[row] = previous / factors[w]
            base += (unassigned[row] - previous) * sums[row]
            coefficient = unassigned[row] * (values[w] - 1)
            for label in range(groups):
                scores[label] += coefficient * powers[row][label]
            affected.append((row, w))
        candidates_raw = [base + score for score in scores]
        if sum(candidates_raw, Fraction(0)) != groups * current_raw:
            raise ArithmeticError('Conditional expectation identity failed')
        choice = min(range(groups), key=lambda label: (candidates_raw[label], label))
        following = candidates_raw[choice]
        if following > current_raw:
            raise ArithmeticError('Potential increased')
        candidates = tuple(value / normalization for value in candidates_raw)
        history.append(Step(vertex, current_raw / normalization, candidates,
                            choice, following / normalization))
        for row, w in affected:
            old = powers[row][choice]
            powers[row][choice] *= values[w]
            sums[row] += powers[row][choice] - old
            cells[row][choice] += w
        labels.append(choice)
        current_raw = following
    final = current_raw / normalization
    if initial < 1 and any(load >= threshold for row in cells for load in row):
        raise ArithmeticError('Strict potential certificate failed')
    return LabelingResult(tuple(labels), tuple(tuple(row) for row in cells),
                          initial, final, threshold, tuple(history))


def derandomize_integer(weights, groups, z, threshold):
    """Common-denominator integer scores; output includes the identical full trace.

    Write z=a/b, W_r=sum_v w[r][v], W=max_r W_r, q=remaining columns.
    A_r=b**(W-W_r)*product_unassigned((g-1)*b**w+a**w).
    H[r][h]=a**load[r][h]*b**(assigned_weight_r-load[r][h]).
    The raw potential is sum(A_r H[r][h])/(g**q*b**W).
    Candidate decisions can therefore be performed entirely with integers.
    """
    weights, columns, z = _validate(weights, groups, z, threshold)
    a, b = z.numerator, z.denominator
    unique = {w for row in weights for w in row}
    a_pow = {w: a ** w for w in unique}
    b_pow = {w: b ** w for w in unique}
    factor = {w: (groups - 1) * b_pow[w] + a_pow[w] for w in unique}
    row_weights = [sum(row) for row in weights]
    max_weight = max(row_weights, default=0)
    scales = []
    for row, total in zip(weights, row_weights):
        value = b ** (max_weight - total)
        for w in row:
            value *= factor[w]
        scales.append(value)
    homogeneous = [[1] * groups for _ in range(groups)]
    sums = [groups] * groups
    cells = [[0] * groups for _ in range(groups)]
    numerator = groups * sum(scales)
    denominator = groups ** columns * b ** max_weight
    normalizer_num, normalizer_den = b ** threshold, a ** threshold

    def potential(num, den):
        return Fraction(num * normalizer_num, den * normalizer_den)

    initial = potential(numerator, denominator)
    history, labels = [], []
    for vertex in range(columns):
        base = 0
        scores = [0] * groups
        affected = []
        for row in range(groups):
            w = weights[row][vertex]
            scales[row], remainder = divmod(scales[row], factor[w])
            if remainder:
                raise ArithmeticError('An exact product division failed')
            base += scales[row] * b_pow[w] * sums[row]
            if w:
                coefficient = scales[row] * (a_pow[w] - b_pow[w])
                for label in range(groups):
                    scores[label] += coefficient * homogeneous[row][label]
                affected.append((row, w))
        candidates_raw = [base + score for score in scores]
        if sum(candidates_raw) != numerator:
            raise ArithmeticError('Homogeneous averaging identity failed')
        choice = min(range(groups), key=lambda label: (candidates_raw[label], label))
        next_numerator = candidates_raw[choice]
        next_denominator, remainder = divmod(denominator, groups)
        if remainder:
            raise ArithmeticError('A common denominator division failed')
        if groups * next_numerator > numerator:
            raise ArithmeticError('Potential increased')
        candidates = tuple(potential(value, next_denominator) for value in candidates_raw)
        history.append(Step(vertex, potential(numerator, denominator), candidates,
                            choice, potential(next_numerator, next_denominator)))
        for row, w in affected:
            old = homogeneous[row][choice]
            for label in range(groups):
                homogeneous[row][label] *= b_pow[w]
            homogeneous[row][choice] = old * a_pow[w]
            sums[row] = sums[row] * b_pow[w] + old * (a_pow[w] - b_pow[w])
            cells[row][choice] += w
        labels.append(choice)
        numerator, denominator = next_numerator, next_denominator
    final = potential(numerator, denominator)
    if initial < 1 and any(load >= threshold for row in cells for load in row):
        raise ArithmeticError('Strict potential certificate failed')
    return LabelingResult(tuple(labels), tuple(tuple(row) for row in cells),
                          initial, final, threshold, tuple(history))
