#!/usr/bin/env python3
"""Exact finite checks for Section 'Structural limits'.

Standard library only. Run from any directory:
    python3 code/check_structures.py

The script checks algebraic identities and finite enumeration independently.
It does not test a SAT solver or replace the asymptotic counting proof.
It writes no files; its JSON result can be redirected to results/.
"""
from __future__ import annotations

import itertools
import json
import math
import random
from fractions import Fraction
from typing import Callable, Sequence


Matrix = list[list[int]]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def kron(left: Matrix, right: Matrix) -> Matrix:
    """Kronecker product, without using the closed-form pairing formula."""
    return [
        [a * b for a in left_row for b in right_row]
        for left_row in left
        for right_row in right
    ]


def tensor_power(matrix: Matrix, exponent: int) -> Matrix:
    result = [[1]]
    for _ in range(exponent):
        result = kron(result, matrix)
    return result


def pairing_matrix(n: int) -> Matrix:
    """Independent formula using the union of two bitmask supports."""
    return [
        [1 << (n - (s | t).bit_count()) for t in range(1 << n)]
        for s in range(1 << n)
    ]


def direct_boolean_pairing(n: int) -> Matrix:
    """Count assignments satisfying both positive-unit-clause formulas."""
    size = 1 << n
    return [
        [
            sum((x & s) == s and (x & t) == t for x in range(size))
            for t in range(size)
        ]
        for s in range(size)
    ]


def verify_inverse(matrix: Matrix, inverse: Matrix, modulus: int | None) -> None:
    size = len(matrix)
    require(len(inverse) == size, "Inverse dimension mismatch")
    require(all(len(row) == size for row in matrix + inverse), "Nonsquare matrix")
    for row in range(size):
        for col in range(size):
            product = sum(matrix[row][k] * inverse[k][col] for k in range(size))
            expected = int(row == col)
            if modulus is not None:
                product %= modulus
                expected %= modulus
            require(product == expected, f"Inverse failure at {(row, col, modulus)}")


def integer_determinant(matrix: Matrix) -> int:
    """Bareiss elimination with exact divisibility checks."""
    if not matrix:
        return 1
    work = [row[:] for row in matrix]
    size = len(work)
    previous = 1
    sign = 1
    for k in range(size - 1):
        pivot_row = next((r for r in range(k, size) if work[r][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            work[k], work[pivot_row] = work[pivot_row], work[k]
            sign = -sign
        pivot = work[k][k]
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                numerator = work[i][j] * pivot - work[i][k] * work[k][j]
                quotient, remainder = divmod(numerator, previous)
                require(remainder == 0, "Bareiss division was not exact")
                work[i][j] = quotient
        for i in range(k + 1, size):
            work[i][k] = 0
        previous = pivot
    return sign * work[-1][-1]


def assignment_formula(n: int, mask: int) -> tuple[int, ...]:
    """Unit clauses encoded as signed variable numbers 1,...,n."""
    return tuple(i + 1 if mask & (1 << i) else -(i + 1) for i in range(n))


def units_satisfied(literals: Sequence[int], assignment: int) -> bool:
    return all(
        bool(assignment & (1 << (abs(literal) - 1))) == (literal > 0)
        for literal in literals
    )


def direct_decision_matrix(n: int) -> Matrix:
    formulas = [assignment_formula(n, mask) for mask in range(1 << n)]
    return [
        [
            int(any(units_satisfied(first + second, x) for x in range(1 << n)))
            for second in formulas
        ]
        for first in formulas
    ]


def bounded_arrays_dp(capacities: Sequence[int], budget: int) -> int:
    """Count arrays by a generating-function convolution."""
    require(budget >= 0 and all(cap >= 0 for cap in capacities), "Negative input")
    coefficients = [1] + [0] * budget
    for cap in capacities:
        updated = [0] * (budget + 1)
        for degree, count in enumerate(coefficients):
            for value in range(min(cap, budget - degree) + 1):
                updated[degree + value] += count
        coefficients = updated
    return sum(coefficients)


def bounded_arrays_bruteforce(capacities: Sequence[int], budget: int) -> int:
    return sum(
        sum(values) <= budget
        for values in itertools.product(*(range(cap + 1) for cap in capacities))
    )


def verify_array_count(capacities: Sequence[int], budget: int, claimed: int) -> None:
    exact = bounded_arrays_bruteforce(capacities, budget)
    require(claimed == exact, f"Incorrect array count: {capacities}, {budget}")
    active = sum(cap > 0 for cap in capacities)
    bounds = (
        (budget + 1) ** active,
        math.comb(budget + active, active),
        math.prod(cap + 1 for cap in capacities),
    )
    require(all(exact <= bound for bound in bounds), "An array bound failed")


def expect_rejection(action: Callable[[], None], label: str) -> dict[str, object]:
    try:
        action()
    except AssertionError:
        return {"label": label, "rejected": True}
    raise AssertionError(f"Corruption control was accepted: {label}")


def main() -> None:
    base = [[2, 1], [1, 1]]
    inverse_base = [[1, -1], [-1, 2]]
    moduli: tuple[int | None, ...] = (None, 2, 3, 5, 101)
    inverse_checks = 0
    determinant_checks = 0
    direct_count_checks = 0
    decision_checks = 0

    for n in range(7):
        matrix = pairing_matrix(n)
        require(matrix == tensor_power(base, n), f"Kronecker mismatch for n={n}")
        inverse = tensor_power(inverse_base, n)
        for modulus in moduli:
            verify_inverse(matrix, inverse, modulus)
            inverse_checks += 1
        if n <= 5:
            require(integer_determinant(matrix) == 1, f"Determinant failure at n={n}")
            determinant_checks += 1
            require(matrix == direct_boolean_pairing(n), f"Boolean count failure at n={n}")
            direct_count_checks += 1
        if n <= 4:
            expected = [[int(i == j) for j in range(1 << n)] for i in range(1 << n)]
            require(direct_decision_matrix(n) == expected, f"Decision identity failure at n={n}")
            decision_checks += 1

    array_checks = 0
    for length in range(5):
        for capacities in itertools.product(range(3), repeat=length):
            for budget in range(9):
                verify_array_count(
                    capacities, budget, bounded_arrays_dp(capacities, budget)
                )
                array_checks += 1

    random_source = random.Random(20261026)
    for _ in range(64):
        capacities = tuple(
            random_source.randrange(4) for _ in range(random_source.randrange(1, 8))
        )
        budget = random_source.randrange(sum(capacities) + 3)
        verify_array_count(capacities, budget, bounded_arrays_dp(capacities, budget))
        array_checks += 1

    stars_and_bars_checks = 0
    for length in range(6):
        for budget in range(7):
            capacities = (budget,) * length
            count = bounded_arrays_bruteforce(capacities, budget)
            require(count == math.comb(budget + length, length), "Composition identity failed")
            require(count == bounded_arrays_dp(capacities, budget), "DP identity failed")
            stars_and_bars_checks += 1

    # Direct finite witness for the 0/1-array subfamily of the corollary.
    binary_subfamily_checks = 0
    for count in range(13):
        observed = bounded_arrays_bruteforce((1,) * count, count)
        require(observed == 1 << count, "Binary-array subfamily count failed")
        binary_subfamily_checks += 1

    # This verifies an exact parameter inequality, not the asymptotic graph theorem.
    delta = Fraction(1, 10)
    d = 4
    counting_reserve = d * (1 - 2 * delta) - 3
    require(counting_reserve == Fraction(1, 5), "Graph-counting reserve changed")

    original = pairing_matrix(3)
    correct_inverse = tensor_power(inverse_base, 3)
    corrupt_matrix = [row[:] for row in original]
    corrupt_matrix[2][5] += 1
    corrupt_inverse = [row[:] for row in correct_inverse]
    corrupt_inverse[0][0] += 1
    controls = [
        expect_rejection(
            lambda: verify_inverse(corrupt_matrix, correct_inverse, None),
            "altered integer pairing entry",
        ),
        expect_rejection(
            lambda: verify_inverse(original, corrupt_inverse, 2),
            "altered inverse over characteristic two",
        ),
        expect_rejection(
            lambda: verify_inverse(original, corrupt_inverse, 101),
            "altered inverse over odd characteristic",
        ),
        expect_rejection(
            lambda: verify_array_count((2, 1, 3, 0), 4, bounded_arrays_dp((2, 1, 3, 0), 4) + 1),
            "array total increased by one",
        ),
    ]

    print(json.dumps(
        {
            "status": "PASS",
            "scope": "exact finite algebra and enumeration; no SAT solver benchmark",
            "pairing_dimensions": [1 << n for n in range(7)],
            "inverse_checks": inverse_checks,
            "coefficient_rings": ["integers", "F_2", "F_3", "F_5", "F_101"],
            "integer_determinant_checks": determinant_checks,
            "direct_boolean_count_checks": direct_count_checks,
            "direct_decision_identity_checks": decision_checks,
            "capacity_array_checks": array_checks,
            "stars_and_bars_checks": stars_and_bars_checks,
            "binary_subfamily_checks": binary_subfamily_checks,
            "graph_parameter_reserve": str(counting_reserve),
            "corruption_controls": controls,
            "asymptotic_graph_theorem": "proved in text; not established by finite checks",
        },
        indent=2,
        sort_keys=True,
    ))


if __name__ == "__main__":
    main()

