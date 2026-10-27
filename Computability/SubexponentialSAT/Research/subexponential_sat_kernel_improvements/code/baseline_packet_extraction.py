#!/usr/bin/env python3
"""Polynomial-space coefficient extraction for a product of affine forms.

The coefficient ring is
    (Z / 2**p Z)[U,V] / (f(U), V**ell),
where f is any monic integral polynomial.  Irreducibility is not needed
by this subroutine.  The scalar ring is the default (f(U)=U, ell=1).

This is an exact reference implementation of the finite-difference
subroutine, not an implementation or empirical validation of the full
OpenAI SAT/tensor-contraction algorithm.

Each affine form is a sequence [constant, coefficient_of_Z1, ...].
Each coefficient is a tuple in the basis U**i V**j, with U index varying
fastest.  Input coordinates are canonically reduced modulo 2**p before
lifting to the extra precision required for exact division.

No table indexed by the exponential evaluation grid is stored.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from math import comb, factorial, prod
from typing import Sequence


Element = tuple[int, ...]
AffineForm = Sequence[Element]


@dataclass(frozen=True)
class RingSpec:
    """Monic f in increasing coefficient order, and truncation order ell."""

    f: tuple[int, ...] = (0, 1)
    ell: int = 1

    def __post_init__(self) -> None:
        if len(self.f) < 2 or self.f[-1] != 1 or self.ell < 1:
            raise ValueError("f must be monic of positive degree; ell must be positive")

    @property
    def degree(self) -> int:
        return len(self.f) - 1

    @property
    def dimension(self) -> int:
        return self.degree * self.ell

    @property
    def zero(self) -> Element:
        return (0,) * self.dimension

    @property
    def one(self) -> Element:
        return (1,) + (0,) * (self.dimension - 1)

    def canonical(self, x: Sequence[int], modulus: int) -> Element:
        if len(x) != self.dimension:
            raise ValueError("incorrect number of coefficient-ring coordinates")
        return tuple(a % modulus for a in x)

    def add(self, x: Element, y: Element, modulus: int) -> Element:
        return tuple((a + b) % modulus for a, b in zip(x, y))

    def scale(self, scalar: int, x: Element, modulus: int) -> Element:
        return tuple((scalar * a) % modulus for a in x)

    def multiply(self, x: Element, y: Element, modulus: int) -> Element:
        e = self.degree
        # First convolve U and V, truncating V immediately.
        temporary = [[0] * (2 * e - 1) for _ in range(self.ell)]
        for j in range(self.ell):
            for h in range(self.ell - j):
                out = temporary[j + h]
                for i in range(e):
                    xi = x[j * e + i]
                    if xi:
                        for k in range(e):
                            out[i + k] += xi * y[h * e + k]
        # Reduce U^e = -sum_{i<e} f_i U^i, separately for every V coefficient.
        answer = []
        for row in temporary:
            for power in range(2 * e - 2, e - 1, -1):
                value = row[power]
                if value:
                    for i in range(e):
                        row[power - e + i] -= value * self.f[i]
            answer.extend(value % modulus for value in row[:e])
        return tuple(answer)


@dataclass(frozen=True)
class ExtractionResult:
    coefficient: Element
    input_precision: int
    working_precision: int
    denominator_valuation: int
    evaluation_count: int
    homogenized_exponents: tuple[int, ...]


def v2_factorial(n: int) -> int:
    """Legendre's formula v_2(n!) = n - popcount(n)."""
    if n < 0:
        raise ValueError("negative factorial argument")
    return n - n.bit_count()


def _validate(forms: Sequence[AffineForm], beta: Sequence[int], p: int,
              ring: RingSpec) -> tuple[tuple[Element, ...], ...]:
    if p < 1 or any(b < 0 or not isinstance(b, int) for b in beta):
        raise ValueError("p must be positive and target exponents nonnegative integers")
    if any(len(form) != len(beta) + 1 for form in forms):
        raise ValueError("each form needs a constant and one coefficient per target mode")
    modulus = 1 << p
    return tuple(tuple(ring.canonical(a, modulus) for a in form) for form in forms)


def coefficient_finite_difference(
    forms: Sequence[AffineForm], beta: Sequence[int], p: int,
    ring: RingSpec = RingSpec(),
) -> ExtractionResult:
    """Return [Z**beta] product(forms) modulo 2**p, using polynomial space.

    For R forms, homogenization adds exponent beta_0 = R-sum(beta).
    The evaluation grid has exactly product(beta_i+1) points including
    beta_0; this is at most 2**R.  If sum(beta)>R the coefficient is zero.
    All ring computations stream through one grid point at a time.
    """
    canonical_forms = _validate(forms, beta, p, ring)
    R = len(forms)
    if sum(beta) > R:
        return ExtractionResult(ring.zero, p, p, 0, 0, ())
    exponents = (R - sum(beta), *beta)
    denominator = prod(factorial(b) for b in exponents)
    valuation = sum(v2_factorial(b) for b in exponents)
    assert valuation <= R
    precision = p + valuation
    modulus = 1 << precision
    numerator = ring.zero
    evaluation_count = 0
    # Input coefficients remain their original canonical representatives.
    # Computing a different lift of a previously created tensor is unnecessary.
    for gamma in product(*(range(b + 1) for b in exponents)):
        value = ring.one
        for form in canonical_forms:
            affine_value = ring.zero
            for coordinate, coefficient in zip(gamma, form):
                if coordinate:
                    affine_value = ring.add(
                        affine_value, ring.scale(coordinate, coefficient, modulus), modulus
                    )
            value = ring.multiply(value, affine_value, modulus)
        weight = prod(comb(b, g) for b, g in zip(exponents, gamma))
        if (R - sum(gamma)) & 1:
            weight = -weight
        numerator = ring.add(numerator, ring.scale(weight, value, modulus), modulus)
        evaluation_count += 1
    expected_count = prod(b + 1 for b in exponents)
    assert evaluation_count == expected_count <= (1 << R)
    power_of_two = 1 << valuation
    if any(a % power_of_two for a in numerator):
        raise ArithmeticError("finite-difference numerator is not exactly divisible")
    output_modulus = 1 << p
    odd_part = denominator >> valuation
    inverse_odd = pow(odd_part, -1, output_modulus)
    answer = tuple(((a >> valuation) * inverse_odd) % output_modulus for a in numerator)
    return ExtractionResult(answer, p, precision, valuation,
                            evaluation_count, tuple(exponents))


def coefficient_reference(
    forms: Sequence[AffineForm], beta: Sequence[int], p: int,
    ring: RingSpec = RingSpec(),
) -> Element:
    """Independent direct polynomial multiplication, for small verification only.

    This reference stores the whole target exponent box.  It is deliberately
    not the polynomial-space algorithm delivered above.
    """
    canonical_forms = _validate(forms, beta, p, ring)
    if sum(beta) > len(forms):
        return ring.zero
    modulus = 1 << p
    zero_exponent = (0,) * len(beta)
    coefficients = {zero_exponent: ring.one}
    for form in canonical_forms:
        result: dict[tuple[int, ...], Element] = {}
        for exponent, value in coefficients.items():
            term = ring.multiply(value, form[0], modulus)
            result[exponent] = ring.add(result.get(exponent, ring.zero), term, modulus)
            for j in range(len(beta)):
                if exponent[j] < beta[j]:
                    bumped = list(exponent)
                    bumped[j] += 1
                    key = tuple(bumped)
                    term = ring.multiply(value, form[j + 1], modulus)
                    result[key] = ring.add(result.get(key, ring.zero), term, modulus)
        coefficients = result
    return coefficients.get(tuple(beta), ring.zero)


if __name__ == "__main__":
    forms = [[(1,), (1,)]] * 4
    result = coefficient_finite_difference(forms, (2,), 3)
    print("Coefficient of Z^2 in (1+Z)^4 modulo 8:", result.coefficient[0])
    print("Input / working precision:", result.input_precision, result.working_precision)
    print("Grid evaluations:", result.evaluation_count)
