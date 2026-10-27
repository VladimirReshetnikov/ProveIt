#!/usr/bin/env python3
"""Exact Gray-streamed and antipodal coefficient extraction.

This replaces the local packet-entry primitive, not the complete SAT solver.
The ring and baseline are the unmodified implementation at ProveIt commit
ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06, supplied alongside this module.
Only one evaluation point and R row values are retained at a time.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import comb, factorial, prod
from typing import Sequence

from baseline_packet_extraction import RingSpec, _validate, v2_factorial


@dataclass(frozen=True)
class StreamedResult:
    coefficient: tuple[int, ...]
    input_precision: int
    working_precision: int
    denominator_valuation: int
    evaluation_count: int
    homogenized_exponents: tuple[int, ...]
    method: str
    affine_initializations: int
    affine_updates: int
    ring_multiplications: int
    full_grid_count: int


def gray_changes(limits: Sequence[int]):
    """Yield (coordinate, signed unit change) for a reflected product grid.

    The first point, all zero, is implicit. limits are inclusive upper bounds.
    Empty and all-singleton grids therefore yield no changes.
    """
    digits = [0] * len(limits)
    directions = [1] * len(limits)
    while True:
        for index, bound in enumerate(limits):
            following = digits[index] + directions[index]
            if 0 <= following <= bound:
                step = directions[index]
                digits[index] = following
                yield index, step
                break
            directions[index] = -directions[index]
        else:
            return


def _antipodal_boxes(exponents):
    """Boxes containing exactly one point from each nonzero antipodal pair.

    A box is (start, inclusive limits) in the original gamma coordinates.
    For odd beta_j, use its lower half and all other coordinates. If every
    beta is even, first noncentral coordinate determines disjoint boxes.
    """
    odd = next((j for j, b in enumerate(exponents) if b % 2), None)
    if odd is not None:
        limits = list(exponents)
        limits[odd] = (exponents[odd] - 1) // 2
        yield (0,) * len(exponents), tuple(limits)
        return
    for j, b in enumerate(exponents):
        if not b:
            continue
        start = tuple(exponents[k] // 2 if k < j else 0
                      for k in range(len(exponents)))
        limits = tuple(0 if k < j else b // 2 - 1 if k == j
                       else exponents[k] for k in range(len(exponents)))
        yield start, limits


def coefficient_streamed(forms, beta, p: int, ring=RingSpec(), *,
                         antipodal: bool = False) -> StreamedResult:
    """Return [Z**beta] product(forms) modulo 2**p in polynomial space.

    Gray: G grid points, precision p+sum v2(beta_i!).
    Antipodal: floor(G/2) grid points, precision p+O-1+sum v2(beta_i!).
    Here O is the sum of the odd homogenized exponents. Even exponents use
    unit-step centered grids; odd exponents use step-two centered grids.
    Here beta_0=R-sum(beta), and G=product(beta_i+1), including beta_0.
    Homogeneous degree zero and impossible targets are handled separately.
    """
    canonical = _validate(forms, beta, p, ring)
    R = len(forms)
    method = "antipodal-gray" if antipodal else "gray"
    if sum(beta) > R:
        return StreamedResult(ring.zero, p, p, 0, 0, (), method, 0, 0, 0, 0)
    exponents = (R - sum(beta), *beta)
    if R == 0:
        return StreamedResult(ring.one, p, p, 0, 1, exponents,
                              method, 0, 0, 0, 1)
    nu = sum(v2_factorial(b) for b in exponents)
    odd_mass = sum(b for b in exponents if b % 2)
    valuation = nu + (odd_mass - 1 if antipodal else 0)
    precision = p + valuation
    modulus = 1 << precision
    active = tuple(j for j, b in enumerate(exponents) if b)
    betas = tuple(exponents[j] for j in active)
    rows = tuple(tuple(row[j] for j in active) for row in canonical)
    full_grid = prod(b + 1 for b in betas)
    boxes = (_antipodal_boxes(betas) if antipodal else
             iter([((0,) * len(betas), betas)]))
    numerator = ring.zero
    initializations = updates = evaluations = multiplications = 0
    step_multipliers = tuple(2 if antipodal and b % 2 else 1 for b in betas)
    for start, limits in boxes:
        gamma = list(start)
        coordinates = [h*g-h*b//2 if antipodal else g
                       for g,b,h in zip(gamma,betas,step_multipliers)]
        row_values = []
        for row in rows:
            value = ring.zero
            for coordinate, coefficient in zip(coordinates, row):
                if coordinate:
                    value = ring.add(value, ring.scale(coordinate, coefficient, modulus), modulus)
                    initializations += 1
            row_values.append(value)
        positive_weight = prod(comb(b, g) for b, g in zip(betas, gamma))
        sign = -1 if (R - sum(gamma)) % 2 else 1

        def accumulate():
            nonlocal numerator, evaluations, multiplications
            value = ring.one
            for row_value in row_values:
                value = ring.multiply(value, row_value, modulus)
                multiplications += 1
            numerator = ring.add(numerator, ring.scale(sign * positive_weight, value, modulus), modulus)
            evaluations += 1

        accumulate()
        for index, step in gray_changes(limits):
            old = gamma[index]
            new = old + step
            # This is division in Z, before passing weights to the ring.
            # No even residue is inverted.
            if step == 1:
                quotient, remainder = divmod(positive_weight * (betas[index] - old), new)
            else:
                quotient, remainder = divmod(positive_weight * old, betas[index] - old + 1)
            if remainder:
                raise ArithmeticError("binomial weight update was not exact")
            positive_weight = quotient
            gamma[index] = new
            sign = -sign
            change = step_multipliers[index] * step
            for row_index, row in enumerate(rows):
                row_values[row_index] = ring.add(row_values[row_index],
                    ring.scale(change, row[index], modulus), modulus)
                updates += 1
            accumulate()
    expected = full_grid // 2 if antipodal else full_grid
    if evaluations != expected:
        raise ArithmeticError("unexpected streamed evaluation count")
    divisor = 1 << valuation
    if any(a % divisor for a in numerator):
        raise ArithmeticError("polarization numerator is not exactly divisible")
    output_modulus = 1 << p
    odd_part = prod(factorial(b) for b in exponents) >> nu
    odd_inverse = pow(odd_part, -1, output_modulus)
    answer = tuple(((a >> valuation) * odd_inverse) % output_modulus for a in numerator)
    return StreamedResult(answer, p, precision, valuation, evaluations, exponents,
        method, initializations, updates, multiplications, full_grid)


def coefficient_gray(forms, beta, p, ring=RingSpec()):
    return coefficient_streamed(forms, beta, p, ring, antipodal=False)


def coefficient_antipodal_gray(forms, beta, p, ring=RingSpec()):
    return coefficient_streamed(forms, beta, p, ring, antipodal=True)


if __name__ == "__main__":
    from dataclasses import asdict
    import json
    example = [[(1,), (1,)]] * 8
    print(json.dumps(asdict(coefficient_antipodal_gray(example, (4,), 12)), indent=2))
