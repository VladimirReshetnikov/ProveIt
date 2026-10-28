#!/usr/bin/env python3
"""Exact projective roots-of-unity extraction for multiplicities one and two.

This is a packet-entry kernel, not a SAT solver.  It uses the existing
coefficient ring, provided that a cubic root satisfying w*w+w+1=0 is available
at working precision.  No field extension is silently allocated.  A canonical
root is supplied for the ring with defining polynomial U^2+U+1.

The homogeneous target's smallest positive exponent is fixed projectively.
Every other exponent b uses b+1 roots.  Only powers of two in the averaging
denominator require extra precision; factorial denominators disappear.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import prod

from baseline_packet_extraction import RingSpec, _validate
from streamed_coefficients import gray_changes


@dataclass(frozen=True)
class ProjectiveResult:
    coefficient: tuple[int, ...]
    input_precision: int
    working_precision: int
    denominator_valuation: int
    evaluation_count: int
    homogenized_exponents: tuple[int, ...]
    pivot_axis: int | None
    method: str
    affine_initializations: int
    affine_updates: int
    ring_multiplications: int
    full_grid_count: int


def coefficient_projective_12(forms, beta, p: int,
                             ring=RingSpec((1, 1, 1), 1), *, cube_root=None):
    """Extract a coefficient when every positive homogenized exponent is 1 or 2.

    Input entries are fixed at precision p.  If m nonpivot exponents are one,
    computations use p+m bits and the final numerator is divided by 2**m.
    There are product(b+1)/(1+min_positive_b) evaluations.  Root validation is
    performed at the augmented precision, so a root known only modulo 2**p
    must first be lifted by the caller.  The input root is never treated as an
    invertible power of two.  All coefficients of the quotient ring are kept.
    """
    canonical = _validate(forms, beta, p, ring)
    R = len(forms)
    if sum(beta) > R:
        return ProjectiveResult(ring.zero, p, p, 0, 0, (), None,
                                "projective-12", 0, 0, 0, 0)
    b = (R - sum(beta), *beta)
    if R == 0:
        return ProjectiveResult(ring.one, p, p, 0, 1, b, None,
                                "projective-12", 0, 0, 0, 1)
    active = tuple(j for j, bj in enumerate(b) if bj)
    if any(b[j] not in (1, 2) for j in active):
        raise ValueError("positive homogenized exponents must be one or two")
    pivot = min(active, key=lambda j: (b[j], j))
    axes = tuple(j for j in active if j != pivot)
    loss = sum(b[j] == 1 for j in axes)
    precision = p + loss
    modulus = 1 << precision
    minus_one = ring.scale(-1, ring.one, modulus)

    if any(b[j] == 2 for j in axes):
        if cube_root is None:
            if ring.f != (1, 1, 1):
                raise ValueError("supply a cubic root at working precision for this ring")
            cube_root = (0, 1) + (0,) * (ring.dimension - 2)
        omega = ring.canonical(cube_root, modulus)
        omega2 = ring.multiply(omega, omega, modulus)
        if ring.add(ring.add(omega2, omega, modulus), ring.one, modulus) != ring.zero:
            raise ValueError("cube root does not satisfy U^2+U+1 at working precision")
    else:
        omega = omega2 = ring.zero

    nodes = tuple((ring.one, minus_one) if b[j] == 1
                  else (ring.one, omega, omega2) for j in axes)
    row_values = []
    initializations = updates = multiplies = 0
    for row in canonical:
        value = row[pivot]
        for j in axes:
            value = ring.add(value, row[j], modulus)
            initializations += 1
        row_values.append(value)

    # Precompute each adjacent node difference times each row coefficient.
    # Storage is O(R times number_of_axes), bounded by a constant times input.
    deltas = []
    for j, axis_nodes in zip(axes, nodes):
        axis_deltas = []
        for old in range(len(axis_nodes)-1):
            difference = ring.add(axis_nodes[old+1],
                                  ring.scale(-1, axis_nodes[old], modulus), modulus)
            column = []
            for row in canonical:
                column.append(ring.multiply(row[j], difference, modulus))
                multiplies += 1
            axis_deltas.append(tuple(column))
        deltas.append(tuple(axis_deltas))

    gamma = [0] * len(axes)
    weight = ring.one  # x_j**(-b_j)=x_j for order b_j+1.
    numerator = ring.zero
    evaluations = 0

    def accumulate():
        nonlocal numerator, evaluations, multiplies
        value = weight
        for row_value in row_values:
            value = ring.multiply(value, row_value, modulus)
            multiplies += 1
        numerator = ring.add(numerator, value, modulus)
        evaluations += 1

    accumulate()
    for axis, step in gray_changes(tuple(b[j] for j in axes)):
        old = gamma[axis]
        new = old + step
        increment = deltas[axis][min(old, new)]
        for row_index, delta in enumerate(increment):
            if step < 0:
                delta = ring.scale(-1, delta, modulus)
            row_values[row_index] = ring.add(row_values[row_index], delta, modulus)
            updates += 1
        if b[axes[axis]] == 1:
            weight = ring.scale(-1, weight, modulus)
        else:
            weight = ring.multiply(weight, omega if step > 0 else omega2, modulus)
            multiplies += 1
        gamma[axis] = new
        accumulate()

    full_grid = prod(b[j]+1 for j in active)
    if evaluations != full_grid // (b[pivot]+1):
        raise ArithmeticError("incorrect projective evaluation count")
    two_power = 1 << loss
    if any(a % two_power for a in numerator):
        raise ArithmeticError("root-filter numerator is not exactly divisible")
    odd_part = 3 ** sum(b[j] == 2 for j in axes)
    output_modulus = 1 << p
    odd_inverse = pow(odd_part, -1, output_modulus)
    coefficient = tuple(((a >> loss) * odd_inverse) % output_modulus for a in numerator)
    return ProjectiveResult(coefficient, p, precision, loss, evaluations, b, pivot,
                            "projective-12", initializations, updates, multiplies, full_grid)


if __name__ == "__main__":
    from dataclasses import asdict
    import json
    example = [[(1, 0), (1, 0), (1, 0)]] * 6
    print(json.dumps(asdict(coefficient_projective_12(example, (2, 2), 8)), indent=2))
