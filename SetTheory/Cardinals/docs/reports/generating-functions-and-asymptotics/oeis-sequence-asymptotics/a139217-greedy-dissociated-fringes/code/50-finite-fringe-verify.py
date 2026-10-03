#!/usr/bin/env python3
"""Exact verification for the A139217/A139218 finite-fringe report.

The program represents

    E(A) = {sum(delta_i * a_i) : delta_i in {0,1,2}}

as the support bits of one Python integer.  If bit j is set, j lies in E(A).
No floating-point arithmetic is used.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Iterable


@dataclass(frozen=True)
class Case:
    name: str
    modulus: int
    residue: int
    fringe: frozenset[int]
    oeis_terms: tuple[int, ...]
    formula: Callable[[int], int]
    recurrence_start: int


def formula_a139217(n: int) -> int:
    if n == 1:
        return 1
    if n == 2:
        return 4
    return 3 * 2 ** (n - 2) + (1 if n % 3 in (0, 1) else -2)


def formula_a139218(n: int) -> int:
    if n <= 3:
        return (0, 2, 5, 8)[n]
    periodic = {
        0: Fraction(-25, 7),
        1: Fraction(20, 7),
        2: Fraction(5, 7),
    }[n % 3]
    value = Fraction(39, 56) * 2**n + periodic
    assert value.denominator == 1
    return value.numerator


CASES = (
    Case(
        name="A139217",
        modulus=3,
        residue=1,
        fringe=frozenset({3}),
        oeis_terms=(1, 4, 7, 13, 22, 49, 97, 190, 385, 769, 1534, 3073, 6145, 12286),
        formula=formula_a139217,
        recurrence_start=6,
    ),
    Case(
        name="A139218",
        modulus=3,
        residue=2,
        fringe=frozenset({1, 3, 6, 11}),
        oeis_terms=(2, 5, 8, 14, 23, 41, 92, 179, 353, 716, 1427, 2849, 5708, 11411),
        formula=formula_a139218,
        recurrence_start=7,
    ),
)


def add_digit(bits: int, value: int) -> int:
    """Multiply the support polynomial by 1+x^value+x^(2*value)."""
    return bits | (bits << value) | (bits << (2 * value))


def set_bits(value: int) -> Iterable[int]:
    """Yield positions of set bits from low to high."""
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


def missing_support(bits: int, total: int) -> list[int]:
    full = (1 << (2 * total + 1)) - 1
    return list(set_bits((~bits) & full))


def next_greedy(bits: int, total: int, modulus: int, residue: int) -> int:
    """Return the least positive admissible integer in one residue class.

    Positive x <= total is admissible exactly when total+x is missing from E.
    Every x > total is automatically admissible because the signed difference
    set lies in [-total,total].
    """
    if total == 0:
        step = residue % modulus
        return step if step else modulus

    lower_mask = (1 << (total + 1)) - 1
    full_mask = (1 << (2 * total + 1)) - 1
    high_mask = full_mask ^ lower_mask  # indices total+1,...,2*total
    high_holes = (~bits) & high_mask

    candidates: list[int] = []
    for index in set_bits(high_holes):
        x = index - total
        if x % modulus == residue % modulus:
            candidates.append(x)

    step = (residue - total) % modulus
    if step == 0:
        step = modulus
    candidates.append(total + step)
    return min(candidates)


def expected_holes(total: int, fringe: frozenset[int]) -> list[int]:
    return sorted(fringe | {2 * total - h for h in fringe})


def verify_case(case: Case, terms: int = 22) -> None:
    bits = 1  # E(empty)={0}
    total = 0
    generated: list[int] = []

    for n in range(1, terms + 1):
        value = next_greedy(bits, total, case.modulus, case.residue)
        generated.append(value)
        assert value == case.formula(n), (case.name, n, value, case.formula(n))

        bits = add_digit(bits, value)
        total += value

        if n >= 3:
            actual = missing_support(bits, total)
            expected = expected_holes(total, case.fringe)
            assert actual == expected, (case.name, n, actual, expected)

    assert tuple(generated[: len(case.oeis_terms)]) == case.oeis_terms

    for n in range(case.recurrence_start, terms + 1):
        assert generated[n - 1] == (
            generated[n - 2] + generated[n - 3] + 2 * generated[n - 4]
        )

    print(
        f"{case.name}: verified {terms} greedy terms, published prefix, "
        f"closed form, recurrence, and exact fringe {sorted(case.fringe)}."
    )
    print(f"  a({terms})={generated[-1]}, S({terms})={total}, support width={2*total+1}")


def verify_generating_functions(terms: int = 30) -> None:
    numerators = {
        "A139217": {1: 1, 2: 3, 3: 2, 5: -6},
        "A139218": {1: 2, 2: 3, 3: 1, 4: -3, 5: -9, 6: -12},
    }
    formulas = {case.name: case.formula for case in CASES}

    for name, numerator in numerators.items():
        coefficients = [0] * (terms + 1)
        for n in range(terms + 1):
            value = numerator.get(n, 0)
            if n >= 1:
                value += coefficients[n - 1]
            if n >= 2:
                value += coefficients[n - 2]
            if n >= 3:
                value += 2 * coefficients[n - 3]
            coefficients[n] = value
        for n in range(1, terms + 1):
            assert coefficients[n] == formulas[name](n), (name, n)
        print(f"{name}: rational generating function checked through x^{terms}.")


def main() -> None:
    for case in CASES:
        verify_case(case)
    verify_generating_functions()
    print("All exact checks passed.")


if __name__ == "__main__":
    main()
