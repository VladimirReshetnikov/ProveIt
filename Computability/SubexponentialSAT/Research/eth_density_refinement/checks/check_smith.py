#!/usr/bin/env python3
"""Exact small checks of the Cauchy-block Smith valuation lemma.

No floating-point arithmetic and no third-party dependencies are used.
The finite checks supplement, and do not replace, the proof in the report.
"""
from fractions import Fraction
from itertools import combinations
from math import factorial


def valuation_two_integer(value):
    if value == 0:
        return None
    value = abs(value)
    return (value & -value).bit_length() - 1


def valuation_two(value):
    value = Fraction(value)
    if value == 0:
        return None
    return valuation_two_integer(value.numerator) - valuation_two_integer(value.denominator)


def determinant(matrix):
    matrix = [[Fraction(value) for value in row] for row in matrix]
    size = len(matrix)
    result = Fraction(1)
    for col in range(size):
        pivot = next((row for row in range(col, size) if matrix[row][col]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
            result = -result
        scale = matrix[col][col]
        result *= scale
        for row in range(col + 1, size):
            ratio = matrix[row][col] / scale
            for index in range(col + 1, size):
                matrix[row][index] -= ratio * matrix[col][index]
            matrix[row][col] = Fraction(0)
    return result


def expected_determinantal_valuation(order):
    return order * (order - 1) + 2 * sum(
        valuation_two_integer(factorial(index)) for index in range(order)
    )


def verify(max_size=6, odd_parameters=(1, 3, -5, 9)):
    minor_count = 0
    matrix_count = 0
    for size in range(1, max_size + 1):
        for odd in odd_parameters:
            assert odd % 2
            matrix = [[Fraction(1, odd + 2 * row - 2 * col)
                       for col in range(size)] for row in range(size)]
            previous = 0
            for order in range(1, size + 1):
                observed_minimum = None
                for rows in combinations(range(size), order):
                    for cols in combinations(range(size), order):
                        minor = [[matrix[row][col] for col in cols] for row in rows]
                        value = valuation_two(determinant(minor))
                        assert value is not None
                        expected = expected_determinantal_valuation(order)
                        assert value >= expected, (size, odd, rows, cols, value, expected)
                        observed_minimum = value if observed_minimum is None else min(value, observed_minimum)
                        minor_count += 1
                assert observed_minimum == expected_determinantal_valuation(order)
                index = order - 1
                invariant = observed_minimum - previous
                assert invariant == 2 * index + 2 * valuation_two_integer(factorial(index))
                assert invariant == 4 * index - 2 * index.bit_count()
                previous = observed_minimum
            matrix_count += 1
    return {"matrices_checked": matrix_count, "minors_checked": minor_count,
            "maximum_matrix_size": max_size, "status": "passed"}


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2))
