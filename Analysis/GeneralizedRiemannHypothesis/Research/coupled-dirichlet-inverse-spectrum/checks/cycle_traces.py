"""Verify the principal-minor identities of the signed-cycle example over Z."""

from itertools import combinations
import json

from sympy import zeros


def cycle_matrix(size, closing_sign):
    matrix = zeros(size)
    for vertex in range(size - 1):
        matrix[vertex, vertex + 1] = matrix[vertex + 1, vertex] = 1
    matrix[size - 1, 0] = matrix[0, size - 1] = closing_sign
    return matrix


def check_cycle(size):
    positive = cycle_matrix(size, 1)
    negative = cycle_matrix(size, -1)
    proper_count = 0
    for order in range(size):
        for subset in combinations(range(size), order):
            assert positive.extract(subset, subset).det() == negative.extract(subset, subset).det()
            proper_count += 1
    difference = int(positive.det() - negative.det())
    assert difference == 4 * (-1) ** (size - 1)
    return {
        "vertices": size,
        "proper_minors_equal": proper_count,
        "full_determinant_difference": difference,
        "first_nonconstant_log_coefficient_order": size + 1,
    }


if __name__ == "__main__":
    print(json.dumps([check_cycle(size) for size in range(3, 9)], indent=2))
