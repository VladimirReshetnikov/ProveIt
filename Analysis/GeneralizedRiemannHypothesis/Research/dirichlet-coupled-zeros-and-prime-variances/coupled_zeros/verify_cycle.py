#!/usr/bin/env python3
"""Check the four-cycle identity over Z and the numerical prime-witness bounds."""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import isqrt


def cycle_laplacian(weights):
    n = len(weights)
    matrix = [[0 for _ in weights] for _ in weights]
    for i, weight in enumerate(weights):
        j = (i + 1) % n
        matrix[i][i] += weight
        matrix[j][j] += weight
        matrix[i][j] -= weight
        matrix[j][i] -= weight
    return matrix


def principal_minor(matrix, indices):
    result = 0
    for order in permutations(indices):
        inversions = sum(x > y for i, x in enumerate(order) for y in order[i + 1:])
        product = (-1) ** inversions
        for row, col in zip(indices, order):
            product *= matrix[row][col]
        result += product
    return result


def check_determinant():
    a = cycle_laplacian([1, 2, 1, 2])
    b = cycle_laplacian([2, 1, 2, 1])
    # Coefficient of a square-free monomial is the complementary principal minor.
    difference = {}
    for size in range(5):
        for monomial in combinations(range(4), size):
            subset = tuple(i for i in range(4) if i not in monomial)
            coefficient = principal_minor(a, subset) - principal_minor(b, subset)
            if coefficient:
                difference[monomial] = coefficient
    assert difference == {(0, 1): 3, (0, 3): -3, (1, 2): -3, (2, 3): 3}
    assert all(a[i][j] == b[(i+1) % 4][(j+1) % 4] for i in range(4) for j in range(4))
    print("Verified all 16 coefficients: p_A(y)-p_B(y)=3(y1-y3)(y2-y4).")


def log_interval(x, n=72):
    z = (x - 1) / (x + 1)
    lo = 2 * sum(z ** (2*k + 1) / (2*k + 1) for k in range(n))
    return lo, lo + 2 * z**(2*n + 1) / ((2*n + 1)*(1-z*z))


def atan_interval(x, n=20):
    partial = sum((-1)**k * x**(2*k+1) / (2*k+1) for k in range(n))
    next_partial = partial + (-1)**n * x**(2*n+1) / (2*n+1)
    return min(partial, next_partial), max(partial, next_partial)


def check_prime_witness():
    log7, _ = log_interval(F(7))
    lo, hi = log_interval(F(4, 3))
    scale = 10**15
    sqrt7_upper = F(isqrt(7 * scale**2) + 1, scale)
    atan5 = atan_interval(F(1, 5))
    atan239 = atan_interval(F(1, 239))
    pi_upper = 16 * atan5[1] - 4 * atan239[0]  # Machin's formula.
    first = (2*log7/sqrt7_upper + lo)/(4*pi_upper)
    second = (2*log7/sqrt7_upper - hi)/(4*pi_upper)
    assert first > F(1399, 10000) and second > F(941, 10000)
    print("Certified the directional rates above 0.1399 and 0.0941 using rational bounds.")


if __name__ == "__main__":
    check_determinant()
    check_prime_witness()
