#!/usr/bin/env python3
"""Exact degree vectors from the proved formulas (not a symbolic composer).

Examples:
  python code/degrees.py 20
  python code/degrees.py 20 --shear-degree 2
  python code/degrees.py 20 --shear-degree 2 --characteristic 3

The shear degree is the ACTUAL degree over the coefficient field; omit it
for the zero shear.  The characteristic must be zero or prime.
"""
from __future__ import annotations
import argparse
import json
from typing import Sequence


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def multiply(a: Sequence[Sequence[int]], b: Sequence[Sequence[int]]) -> list[list[int]]:
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def power_vector(a: list[list[int]], n: int, v: list[int]) -> list[int]:
    """Binary matrix powering applied directly to a column vector."""
    col = [[x] for x in v]
    while n:
        if n & 1:
            col = multiply(a, col)
        n >>= 1
        if n:
            a = multiply(a, a)
    return [row[0] for row in col]


def degree_vector(n: int, shear_degree: int | None = None,
                  characteristic: int = 0) -> list[int]:
    if n < 0:
        raise ValueError('Iteration count must be nonnegative.')
    if shear_degree is not None and shear_degree < 0:
        raise ValueError('A nonzero shear has degree at least zero.')
    if characteristic != 0 and not is_prime(characteristic):
        raise ValueError('Characteristic must be zero or a prime number.')
    if n == 0:
        return [1, 1, 1]
    m = shear_degree
    if characteristic == 3:
        if m is None:
            a = 7 * 4**(n - 1)
        elif m == 0:
            a = 8 * 4**(n - 1)
        else:
            k = m + 3
            # Exact integer form of the inhomogeneous recurrence.
            a = (2*m + 8) * k**(n - 1) + (m + 5) * (k**(n - 1) - 1) // (k - 1)
        return [a, 1, a - 3]
    matrix = ([[3, 3, 1], [3, 2, 1], [3, 0, 1]] if m is None else
              [[m+3, m+5, 0], [m+3, m+4, 0], [m+3, m+2, 0]])
    return power_vector(matrix, n, [1, 1, 1])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('iterations', type=int)
    parser.add_argument('--shear-degree', type=int, default=None)
    parser.add_argument('--characteristic', type=int, default=0)
    args = parser.parse_args()
    try:
        vector = degree_vector(args.iterations, args.shear_degree, args.characteristic)
    except ValueError as exc:
        parser.error(str(exc))
    print(json.dumps({'iterations': args.iterations,
                      'shear_degree': args.shear_degree,
                      'characteristic': args.characteristic,
                      'coordinate_degrees': vector,
                      'total_degree': max(vector)}, indent=2))


if __name__ == '__main__':
    main()
