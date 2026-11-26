#!/usr/bin/env python3
"""Check sharp jet cutoffs for the multiplicative Lubin–Tate group over Z_2.

All computations use exact integers. The rank tests include all higher-degree
monomials that could affect any observed branch coefficient. No packages needed.
"""
from itertools import combinations
from math import comb


def contact(left, right):
    """Return 2^v_2(left-right) for distinct integer labels."""
    difference = abs(left - right)
    return difference & -difference


def cutoffs(labels):
    return [1 + sum(contact(b, c) for c in labels if c != b) for b in labels]


def polynomial_product(left, right, mask):
    """Multiply two bit-encoded polynomials modulo 2 and truncate."""
    product = 0
    while right:
        if right & 1:
            product ^= left
        left = (left << 1) & mask
        right >>= 1
    return product


def rank(columns):
    pivots = {}
    for column in columns:
        while column:
            pivot = column.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = column
                break
            column ^= pivots[pivot]
    return len(pivots)


def lost_jet_dimension(labels, depths):
    """Return the dimension of the low-jet ambiguity under these observations."""
    d = len(labels)
    maximum = max(depths)
    # Evaluation sends a degree >= maximum monomial to zero since u_b(0)=0.
    powers = []
    for b, depth in zip(labels, depths):
        mask = (1 << depth) - 1
        branch = sum((comb(b, j) % 2) << j for j in range(1, min(b + 1, depth)))
        row = [1 & mask]
        for _ in range(maximum - 1):
            row.append(polynomial_product(row[-1], branch, mask))
        powers.append(row)
    low, high = [], []
    for degree in range(maximum):
        for j in range(degree + 1):
            i = degree - j
            column = 0
            for depth, row in zip(depths, powers):
                column = (column << depth) | ((row[j] << i) & ((1 << depth) - 1))
            (low if degree < d else high).append(column)
    return d * (d + 1) // 2 - rank(low + high) + rank(high)


def check_integral_pair(r):
    # At b=2 the group endomorphism equals delta=2X+X².  In (Z/2^r)((X)),
    # the truncated geometric expansion for 1/delta has pole order r+1.
    modulus = 1 << r
    t = r + 1
    h = [0] * r
    for j in range(r):
        h[t - 2 - j] = pow(-2, j, modulus)
    product = [0] * (t + 1)
    for j, coefficient in enumerate(h):
        product[j + 1] = (product[j + 1] + 2 * coefficient) % modulus
        product[j + 2] = (product[j + 2] + coefficient) % modulus
    assert h[0] != 0 and product == [0] * t + [1]


def main():
    # Direct finite search for the optimal digit counts for directions in [0,7].
    for d in range(1, 9):
        optimum = min(max(cutoffs(row)) for row in combinations(range(8), d))
        assert optimum == 1 + sum(contact(j, 0) for j in range(1, d))
    print('Minimax cutoff verified for all 255 nonempty subsets of {0,...,7}.')
    examples = [(0,), (0, 1, 5), (0, 2, 6, 8), tuple(range(8)), tuple(range(0, 16, 2))]
    for labels in examples:
        depths = cutoffs(labels)
        assert lost_jet_dimension(labels, depths) == 0
        for index in range(len(depths)):
            insufficient = list(depths)
            insufficient[index] -= 1
            assert lost_jet_dimension(labels, insufficient) > 0
        print(f'B={labels}: exact branch depths {depths}')
    for r in range(1, 17):
        check_integral_pair(r)
    print('Integral sharpness witness verified modulo 2^r for 1 <= r <= 16.')


if __name__ == '__main__':
    main()
