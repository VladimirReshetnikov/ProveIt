#!/usr/bin/env python3
"""Independent positive level-composition sum, using rational arithmetic.

For a composition d_1+...+d_h=n and d_0=1 the weight divided by n!
 is product_i (i*d_(i-1))**d_i / d_i! . This is separate from the
finite-tower exponential recurrence and from Pruefer-tree enumeration.
"""
from fractions import Fraction
from math import factorial

MAX_N = 14


def need(condition, message):
    if not condition:
        raise ValueError(message)


def compositions(n):
    need(type(n) is int and 0 <= n <= MAX_N, 'composition domain n=0..14')
    if n == 0:
        yield ()
        return
    for first in range(1, n+1):
        for rest in compositions(n-first):
            yield (first,) + rest


def height_weights(n):
    need(type(n) is int and 0 <= n <= MAX_N, 'profile domain n=0..14')
    result = [Fraction(0)] * (n+1)
    for composition in compositions(n):
        previous = 1
        weight = Fraction(factorial(n))
        for level, population in enumerate(composition, 1):
            weight *= Fraction((level * previous)**population, factorial(population))
            previous = population
        need(weight.denominator == 1, 'nonintegral labelled profile weight')
        result[len(composition)] += weight
    need(all(v.denominator == 1 for v in result), 'nonintegral height total')
    return [v.numerator for v in result]
