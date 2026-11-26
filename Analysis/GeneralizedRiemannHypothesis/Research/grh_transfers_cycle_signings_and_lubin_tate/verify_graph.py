#!/usr/bin/env python3
"""Exact certificate for the signed square of a cycle. Requires only Python 3."""
from collections import Counter
from fractions import Fraction
from itertools import permutations

THRESHOLD = Fraction(1397, 500)
PERIOD = (1, 1, -1, 1, -1, -1, 1, -1)
LENGTH = 27


def symbol(word):
    return "".join("+" if sign == 1 else "-" for sign in word)


def period_windows(length):
    return {
        tuple(PERIOD[(start + step) % 8] for step in range(length))
        for start in range(8)
    }


def extend_block(block, sign):
    """Boundary Schur block of T*I - adjacency, after adjoining a vertex."""
    a, b, c = block
    assert a > 0
    return c - b*b/a, -1 + b*sign/a, THRESHOLD - 1/a


def positive(block):
    a, b, c = block
    return a > 0 and a*c > b*b


def schur_test():
    initial = (THRESHOLD, Fraction(-1), THRESHOLD)
    frontier = {(): (initial, initial)}
    counts = [len(frontier)]
    for length in range(1, LENGTH + 1):
        children = {}
        for word, (minus, plus) in frontier.items():
            for sign in (1, -1):
                left = extend_block(minus, sign)
                right = extend_block(plus, -sign)
                if positive(left) and positive(right):
                    children[word + (sign,)] = left, right
        frontier = children
        counts.append(len(frontier))
        if length == 19:
            alternating = {tuple(phase*(-1)**j for j in range(19)) for phase in (-1, 1)}
            assert set(frontier) == period_windows(19) | alternating
            assert len({word[:-1] for word in frontier}) == len(frontier)
    assert set(frontier) == period_windows(LENGTH)
    assert len(period_windows(LENGTH-1)) == len(PERIOD)
    return counts, set(frontier)


def bareiss(matrix):
    """Determinant by integer, fraction-free elimination with exact division."""
    a = [row.copy() for row in matrix]
    result_sign = 1
    previous = 1
    for k in range(len(a)-1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k+1, len(a)) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            result_sign *= -1
        pivot_value = a[k][k]
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                numerator = a[i][j]*pivot_value - a[i][k]*a[k][j]
                a[i][j], rest = divmod(numerator, previous)
                assert rest == 0
        previous = pivot_value
    return result_sign*a[-1][-1]


def integer_path_matrix(word, side):
    """Integer-scaled T*I + side*A with the actual signed edges."""
    n = len(word) + 2
    a = [[0]*n for _ in range(n)]
    for i in range(n):
        a[i][i] = THRESHOLD.numerator
    adjacent = side*THRESHOLD.denominator
    for i in range(n-1):
        a[i][i+1] = a[i+1][i] = adjacent
    for i, sign in enumerate(word):
        a[i][i+2] = a[i+2][i] = adjacent*sign
    return a


def independent_test():
    # The parent passed Sylvester's test. Only the two new leading minors remain.
    frontier = {()}
    assert all(bareiss(integer_path_matrix((), side)) > 0 for side in (-1, 1))
    counts = [len(frontier)]
    for length in range(1, LENGTH+1):
        children = set()
        for parent in frontier:
            for sign in (-1, 1):
                word = parent + (sign,)
                if all(bareiss(integer_path_matrix(word, side)) > 0
                       for side in (-1, 1)):
                    children.add(word)
        frontier = children
        counts.append(len(frontier))
    return counts, frontier


def verify_floquet():
    # Each nonzero entry of xI-H(z) is a monomial c*x^a*z^b.
    entries = {(i, i): (1, 1, 0) for i in range(8)}
    for i in range(8):
        for step, sign in ((1, 1), (2, PERIOD[i])):
            j, wrap = (i+step) % 8, (i+step) // 8
            entries[i, j] = (-sign, 0, wrap)
            entries[j, i] = (-sign, 0, -wrap)
    det = Counter()
    for perm in permutations(range(8)):
        if any((i, j) not in entries for i, j in enumerate(perm)):
            continue
        inversions = sum(perm[i] > perm[j] for i in range(8) for j in range(i+1,8))
        c, x_power, z_power = (-1)**inversions, 0, 0
        for i, j in enumerate(perm):
            sign, dx, dz = entries[i, j]
            c *= sign
            x_power += dx
            z_power += dz
        det[x_power, z_power] += c
    expected = {(8,0):1, (6,0):-16, (4,0):80, (4,1):-2, (4,-1):-2,
                (2,0):-128, (2,1):16, (2,-1):16, (0,0):40,
                (0,1):-13, (0,-1):-13, (0,2):1, (0,-2):1}
    assert {term: coef for term,coef in det.items() if coef} == expected
    # F(2) < T equivalently (T^2-4)^2-10 > sqrt(20), all squarings positive.
    h = THRESHOLD**2 - 4
    k = h*h - 10
    assert h > 0 and k > 0 and k*k > 20
    # For n=26,28,30, the antiperiodic alternating pattern has radius < T.
    # Its radius is largest at n=30. Use pi > 3.14 and cos(v) <= 1-v^2/2+v^4/24.
    v = Fraction(157,1500)
    cos_upper = lambda x: 1 - x*x/2 + x**4/24
    assert 4*(cos_upper(v)**2 + cos_upper(2*v)**2) < THRESHOLD**2
    return expected


def main():
    counts, words = schur_test()
    independent_counts, independent_words = independent_test()
    assert counts == independent_counts and words == independent_words
    verify_floquet()
    print("Boundary Schur and direct integer determinant checks agree.")
    print("Admissible counts (lengths 0 through 27):", *counts)
    print("Length 19: eight period-eight windows and two alternating windows, unique overlaps.")
    print("27-sign windows:")
    for word in sorted(words, key=symbol):
        print(symbol(word))
    print("All 8 overlap prefixes distinct; Floquet determinant and threshold verified.")


if __name__ == "__main__":
    main()
