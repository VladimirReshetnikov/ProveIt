#!/usr/bin/env python3
"""Exact three-input arithmetic generator; no Turing-machine size claim.

Seven total projections compute the prefix-closed optimal support extracted
from the Source149 certificate. The nine yielded objects are native rho8 codes.
"""
from math import isqrt


def pair(a, b):
    if type(a) is not int or type(b) is not int or a < 0 or b < 0:
        raise ValueError('natural-number arguments required')
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    if type(n) is not int or n < 0:
        raise ValueError('natural-number argument required')
    diagonal = (isqrt(8 * n + 1) - 1) // 2
    right = n - diagonal * (diagonal + 1) // 2
    return diagonal - right, right


def left(n):
    return unpair(n // 4)[0]


def right(n):
    return unpair(n // 4)[1]


def implication(a, b):
    return 4 * pair(a, b)


def rho8(a, b, c, u):
    return implication(implication(implication(c, u), a),
                       implication(implication(a, c), implication(b, c)))


def fourth_arguments(a):
    if type(a) is not int or a < 0:
        raise ValueError('natural-number argument required')
    u0 = a
    u1 = left(u0)
    u2 = right(u0)
    u3 = left(u1)
    u4 = right(u2)
    u5 = right(u3)
    u6 = right(u4)
    u7 = right(u5)
    return (0, u0, u1, u2, u3, u4, u5, u6, u7)


def axiom_codes(a, b, c):
    return tuple(rho8(a, b, c, u) for u in fourth_arguments(a))
