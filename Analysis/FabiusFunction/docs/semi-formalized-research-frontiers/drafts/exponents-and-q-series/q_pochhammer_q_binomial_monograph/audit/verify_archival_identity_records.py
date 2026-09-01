#!/usr/bin/env python3
"""Exact finite QC for fifteen archival q-series identity records.

The records are the formulas transcribed in the historical
q_series_proof_article.tex at lines 2209--2344: Bailey modulus 9,
Dyson modulus 27, Rogers modulus 14, Rogers--Selberg, Jackson--Slater,
and Fine's eta/Lambert identity.  Both sides are independently expanded in
Z[[q]]/(q^101) and all coefficients from q^0 through q^100 are compared.

This script is a transcription and regression check, not an infinite proof.
Agreement of 101 coefficients cannot establish any of the displayed
identities as an identity of formal power series.
"""

from __future__ import annotations

import sys
from collections import Counter
from dataclasses import dataclass
from typing import Callable, Iterable, Sequence


MAX_DEGREE = 100
COEFFICIENTS_PER_IDENTITY = MAX_DEGREE + 1

Series = list[int]


@dataclass(frozen=True)
class Pochhammer:
    """A finite or truncated infinite product (sign*q^start; q^step)_count.

    plus=False denotes factors 1-q^m.  plus=True denotes factors 1+q^m,
    equivalently a q-Pochhammer parameter -q^start.  A count of None means
    the infinite product, truncated only after its factor exponent exceeds
    MAX_DEGREE.
    """

    start: int
    step: int
    count: int | None
    plus: bool = False

    def exponents(self) -> Iterable[int]:
        if self.start <= 0 or self.step <= 0:
            raise ValueError(f"invalid q-Pochhammer progression: {self}")
        if self.count is None:
            exponent = self.start
            while exponent <= MAX_DEGREE:
                yield exponent
                exponent += self.step
            return
        if self.count < 0:
            raise ValueError(f"negative q-Pochhammer length: {self}")
        for index in range(self.count):
            exponent = self.start + self.step * index
            if exponent > MAX_DEGREE:
                break
            yield exponent


@dataclass(frozen=True)
class IdentityRecord:
    family: str
    name: str
    left: Series
    right: Series


def zero() -> Series:
    return [0] * (MAX_DEGREE + 1)


def one() -> Series:
    result = zero()
    result[0] = 1
    return result


def multiply_binomial(series: Series, exponent: int, coefficient: int) -> None:
    """Multiply in place by 1 + coefficient*q^exponent."""

    if exponent > MAX_DEGREE:
        return
    for degree in range(MAX_DEGREE - exponent, -1, -1):
        series[degree + exponent] += coefficient * series[degree]


def divide_binomial(series: Series, exponent: int, coefficient: int) -> None:
    """Divide in place by 1 + coefficient*q^exponent in truncated Z[[q]]."""

    if exponent > MAX_DEGREE:
        return
    for degree in range(exponent, MAX_DEGREE + 1):
        series[degree] -= coefficient * series[degree - exponent]


def multiply_pochhammer(series: Series, product: Pochhammer) -> None:
    coefficient = 1 if product.plus else -1
    for exponent in product.exponents():
        multiply_binomial(series, exponent, coefficient)


def divide_pochhammer(series: Series, product: Pochhammer) -> None:
    coefficient = 1 if product.plus else -1
    for exponent in product.exponents():
        divide_binomial(series, exponent, coefficient)


def add_shifted(target: Series, source: Sequence[int], shift: int) -> None:
    for degree, coefficient in enumerate(source[: MAX_DEGREE + 1 - shift]):
        target[degree + shift] += coefficient


def product_ratio(
    numerators: Sequence[Pochhammer],
    denominators: Sequence[Pochhammer],
) -> Series:
    """Expand an independently specified product quotient."""

    result = one()
    for product in numerators:
        multiply_pochhammer(result, product)
    for product in denominators:
        divide_pochhammer(result, product)
    return result


def unilateral_sum(
    exponent: Callable[[int], int],
    numerators: Callable[[int], Sequence[Pochhammer]],
    denominators: Callable[[int], Sequence[Pochhammer]],
    *,
    start: int = 0,
    initial_one: bool = False,
) -> Series:
    """Expand a unilateral sum whose nth summand has constant-one quotient."""

    result = one() if initial_one else zero()
    n = start
    while True:
        shift = exponent(n)
        if shift > MAX_DEGREE:
            break
        term = one()
        for product in numerators(n):
            multiply_pochhammer(term, product)
        for product in denominators(n):
            divide_pochhammer(term, product)
        add_shifted(result, term, shift)
        n += 1
    return result


def infinite_minus(*progressions: tuple[int, int]) -> list[Pochhammer]:
    return [Pochhammer(start, step, None) for start, step in progressions]


def archival_records() -> list[IdentityRecord]:
    """Construct both sides of all fifteen donor formulas independently."""

    records: list[IdentityRecord] = []

    # Bailey's modulus-9 trio.
    records.append(
        IdentityRecord(
            "Bailey modulus 9",
            "B9.1",
            unilateral_sum(
                lambda n: 3 * n * n,
                lambda n: [Pochhammer(1, 1, 3 * n)],
                lambda n: [
                    Pochhammer(3, 3, n),
                    Pochhammer(3, 3, 2 * n),
                ],
            ),
            product_ratio(
                infinite_minus((4, 9), (5, 9), (9, 9)),
                infinite_minus((3, 3)),
            ),
        )
    )
    records.append(
        IdentityRecord(
            "Bailey modulus 9",
            "B9.2",
            unilateral_sum(
                lambda n: 3 * n * n + 3 * n,
                lambda n: [
                    Pochhammer(1, 1, 3 * n),
                    Pochhammer(3 * n + 2, 1, 1),
                ],
                lambda n: [
                    Pochhammer(3, 3, n),
                    Pochhammer(3, 3, 2 * n + 1),
                ],
            ),
            product_ratio(
                infinite_minus((2, 9), (7, 9), (9, 9)),
                infinite_minus((3, 3)),
            ),
        )
    )
    records.append(
        IdentityRecord(
            "Bailey modulus 9",
            "B9.3",
            unilateral_sum(
                lambda n: 3 * n * n + 3 * n,
                lambda n: [Pochhammer(1, 1, 3 * n + 1)],
                lambda n: [
                    Pochhammer(3, 3, n),
                    Pochhammer(3, 3, 2 * n + 1),
                ],
            ),
            product_ratio(
                infinite_minus((1, 9), (8, 9), (9, 9)),
                infinite_minus((3, 3)),
            ),
        )
    )

    # Dyson's modulus-27 quartet.
    records.append(
        IdentityRecord(
            "Dyson modulus 27",
            "D27.1",
            unilateral_sum(
                lambda n: n * n,
                lambda n: [Pochhammer(3, 3, n - 1)],
                lambda n: [
                    Pochhammer(1, 1, n),
                    Pochhammer(1, 1, 2 * n - 1),
                ],
                start=1,
                initial_one=True,
            ),
            product_ratio(
                infinite_minus((12, 27), (15, 27), (27, 27)),
                infinite_minus((1, 1)),
            ),
        )
    )
    records.append(
        IdentityRecord(
            "Dyson modulus 27",
            "D27.2",
            unilateral_sum(
                lambda n: n * n + n,
                lambda n: [Pochhammer(3, 3, n)],
                lambda n: [
                    Pochhammer(1, 1, n),
                    Pochhammer(1, 1, 2 * n + 1),
                ],
            ),
            product_ratio(
                infinite_minus((9, 9)),
                infinite_minus((1, 1)),
            ),
        )
    )
    records.append(
        IdentityRecord(
            "Dyson modulus 27",
            "D27.3",
            unilateral_sum(
                lambda n: n * n + 2 * n,
                lambda n: [Pochhammer(3, 3, n)],
                lambda n: [
                    Pochhammer(1, 1, n),
                    Pochhammer(1, 1, 2 * n + 2),
                ],
            ),
            product_ratio(
                infinite_minus((6, 27), (21, 27), (27, 27)),
                infinite_minus((1, 1)),
            ),
        )
    )
    records.append(
        IdentityRecord(
            "Dyson modulus 27",
            "D27.4",
            unilateral_sum(
                lambda n: n * n + 3 * n,
                lambda n: [Pochhammer(3, 3, n)],
                lambda n: [
                    Pochhammer(1, 1, n),
                    Pochhammer(1, 1, 2 * n + 2),
                ],
            ),
            product_ratio(
                infinite_minus((3, 27), (24, 27), (27, 27)),
                infinite_minus((1, 1)),
            ),
        )
    )

    # Rogers's modulus-14 trio.
    records.append(
        IdentityRecord(
            "Rogers modulus 14",
            "R14.1",
            unilateral_sum(
                lambda n: n * n,
                lambda _n: [],
                lambda n: [
                    Pochhammer(1, 1, n),
                    Pochhammer(1, 2, n),
                ],
            ),
            product_ratio(
                infinite_minus((6, 14), (8, 14), (14, 14)),
                infinite_minus((1, 1)),
            ),
        )
    )
    records.append(
        IdentityRecord(
            "Rogers modulus 14",
            "R14.2",
            unilateral_sum(
                lambda n: n * n + n,
                lambda _n: [],
                lambda n: [
                    Pochhammer(1, 1, n),
                    Pochhammer(1, 2, n + 1),
                ],
            ),
            product_ratio(
                infinite_minus((4, 14), (10, 14), (14, 14)),
                infinite_minus((1, 1)),
            ),
        )
    )
    records.append(
        IdentityRecord(
            "Rogers modulus 14",
            "R14.3",
            unilateral_sum(
                lambda n: n * n + 2 * n,
                lambda _n: [],
                lambda n: [
                    Pochhammer(1, 1, n),
                    Pochhammer(1, 2, n + 1),
                ],
            ),
            product_ratio(
                infinite_minus((2, 14), (12, 14), (14, 14)),
                infinite_minus((1, 1)),
            ),
        )
    )

    # Rogers--Selberg trio.
    records.append(
        IdentityRecord(
            "Rogers--Selberg",
            "RS.1",
            unilateral_sum(
                lambda n: 2 * n * n,
                lambda _n: [],
                lambda n: [
                    Pochhammer(2, 2, n),
                    Pochhammer(1, 1, 2 * n, plus=True),
                ],
            ),
            product_ratio(
                infinite_minus((3, 7), (4, 7), (7, 7)),
                infinite_minus((2, 2)),
            ),
        )
    )
    records.append(
        IdentityRecord(
            "Rogers--Selberg",
            "RS.2",
            unilateral_sum(
                lambda n: 2 * n * n + 2 * n,
                lambda _n: [],
                lambda n: [
                    Pochhammer(2, 2, n),
                    Pochhammer(1, 1, 2 * n, plus=True),
                ],
            ),
            product_ratio(
                infinite_minus((2, 7), (5, 7), (7, 7)),
                infinite_minus((2, 2)),
            ),
        )
    )
    records.append(
        IdentityRecord(
            "Rogers--Selberg",
            "RS.3",
            unilateral_sum(
                lambda n: 2 * n * n + 2 * n,
                lambda _n: [],
                lambda n: [
                    Pochhammer(2, 2, n),
                    Pochhammer(1, 1, 2 * n + 1, plus=True),
                ],
            ),
            product_ratio(
                infinite_minus((1, 7), (6, 7), (7, 7)),
                infinite_minus((2, 2)),
            ),
        )
    )

    # Jackson--Slater's mixed-modulus record.
    records.append(
        IdentityRecord(
            "Jackson--Slater",
            "JS",
            unilateral_sum(
                lambda n: 2 * n * n,
                lambda _n: [],
                lambda n: [Pochhammer(1, 1, 2 * n)],
            ),
            product_ratio(
                infinite_minus(
                    (1, 8),
                    (7, 8),
                    (8, 8),
                    (6, 16),
                    (10, 16),
                ),
                infinite_minus((1, 1)),
            ),
        )
    )

    # Fine's eta-quotient/Lambert record.
    fine_product = product_ratio(
        infinite_minus((2, 2), (3, 3), (8, 8), (12, 12)),
        infinite_minus((1, 1), (24, 24)),
    )
    fine_lambert = one()
    for k in range(1, MAX_DEGREE + 1):
        term = one()
        multiply_binomial(term, 4 * k, 1)
        multiply_binomial(term, 6 * k, 1)
        divide_binomial(term, 12 * k, 1)
        add_shifted(fine_lambert, term, k)
    records.append(
        IdentityRecord(
            "Fine eta/Lambert",
            "F",
            fine_product,
            fine_lambert,
        )
    )

    return records


EXPECTED_FAMILIES = (
    ("Bailey modulus 9", 3),
    ("Dyson modulus 27", 4),
    ("Rogers modulus 14", 3),
    ("Rogers--Selberg", 3),
    ("Jackson--Slater", 1),
    ("Fine eta/Lambert", 1),
)


def main() -> int:
    records = archival_records()
    family_counts = Counter(record.family for record in records)
    expected_counts = dict(EXPECTED_FAMILIES)

    if family_counts != Counter(expected_counts):
        print(
            f"FAIL: identity inventory is {dict(family_counts)!r}, "
            f"expected {expected_counts!r}",
            file=sys.stderr,
        )
        return 1

    for record in records:
        for degree, (left, right) in enumerate(zip(record.left, record.right)):
            if left != right:
                print(
                    f"FAIL: {record.name} differs at q^{degree}: "
                    f"left={left}, right={right}",
                    file=sys.stderr,
                )
                print(
                    "Finite QC found a discrepancy; no infinite identity "
                    "claim is made.",
                    file=sys.stderr,
                )
                return 1

    for family, expected in EXPECTED_FAMILIES:
        comparisons = expected * COEFFICIENTS_PER_IDENTITY
        noun = "identity" if expected == 1 else "identities"
        print(
            f"{family}: {expected} {noun}, "
            f"{comparisons} coefficient comparisons"
        )

    identity_count = len(records)
    comparison_count = identity_count * COEFFICIENTS_PER_IDENTITY
    if identity_count != 15 or comparison_count != 1515:
        print(
            f"FAIL: aggregate count is {identity_count} identities / "
            f"{comparison_count} comparisons",
            file=sys.stderr,
        )
        return 1

    print(
        "PASS: 15 identities / 1515 exact coefficient comparisons "
        "through q^100"
    )
    print(
        "FINITE QC ONLY: agreement through q^100 guards the transcription; "
        "it is not a proof of any infinite identity."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
