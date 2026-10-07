#!/usr/bin/env python3
"""Exact finite continued exponentials; standard-library integer/Fraction arithmetic.

The list entries are n! [x^n] F(x), not ordinary power-series coefficients.
The defining recurrence is derived by differentiating exp(depth*x*child).
"""
from fractions import Fraction
from math import comb

MAX_DEGREE = 200
MAX_HEIGHT = 200


def need(condition, message):
    if not condition:
        raise ValueError(message)


def index(value, maximum, label):
    need(type(value) is int and 0 <= value <= maximum, label + ' outside exact domain')


def finite_tower(height, degree, shift=1):
    """n! coefficients of height cutoff h, with factors shift,...,shift+h-1."""
    index(height, MAX_HEIGHT, 'height')
    index(degree, MAX_DEGREE, 'degree')
    need(type(shift) in (int, Fraction) and shift > 0, 'shift must be positive exact rational')
    child = [1] + [0] * degree
    choose = [[comb(n, k) for k in range(n+1)] for n in range(degree)]
    for level in range(height-1, -1, -1):
        depth = shift + level
        parent = [1]
        for n in range(1, degree+1):
            parent.append(depth * sum(k * choose[n-1][k-1] * child[k-1]
                                      * parent[n-k] for k in range(1, n+1)))
        child = parent
    return child


def coefficients(degree):
    """Triangular, stabilized coefficients of the infinite formal tower.

    This is a faster truncation of the defining recurrence, not an independent
    combinatorial verification. Independence comes from prufer.py/profiles.py.
    """
    index(degree, MAX_DEGREE, 'degree')
    child = [1]
    choose = [[comb(n, k) for k in range(n+1)] for n in range(degree)]
    for depth in range(degree, 0, -1):
        parent = [1]
        for n in range(1, degree-depth+2):
            parent.append(depth * sum(k * choose[n-1][k-1] * child[k-1]
                                      * parent[n-k] for k in range(1, n+1)))
        child = parent
    return child


def height_weights(degree):
    """Table indexed by degree n then exact height h."""
    index(degree, MAX_DEGREE, 'degree')
    previous = [1] + [0] * degree
    weights = [[0] * (degree+1) for _ in range(degree+1)]
    weights[0][0] = 1
    for height in range(1, degree+1):
        current = finite_tower(height, degree)
        for n in range(degree+1):
            weights[n][height] = current[n] - previous[n]
        previous = current
    return weights
