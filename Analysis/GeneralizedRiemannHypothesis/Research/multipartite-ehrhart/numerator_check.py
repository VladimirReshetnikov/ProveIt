#!/usr/bin/env python3
"""Exact change in the real-root count on deleting the 85th edge in dimension 169."""
from fractions import Fraction
from math import comb, gcd


def primitive(p):
    while p and not p[-1]:
        p.pop()
    if not p:
        return p
    g = gcd(*p)
    return [a // g for a in p]


def negative_remainder(p, q):
    """Primitive negative Euclidean remainder, scaled only by positive constants."""
    p = p.copy()
    while len(p) >= len(q):
        a, b = p[-1], q[-1]
        g = gcd(a, b)
        factor = a // g * (1 if b > 0 else -1)
        offset = len(p) - len(q)
        p = [t * (abs(b) // g) for t in p]
        for i, value in enumerate(q):
            p[i + offset] -= factor * value
        p = primitive(p)
    return [-u for u in p]


def sturm(p):
    q = primitive([i * p[i] for i in range(1, len(p))])
    seq = [p]
    while q:
        seq.append(q)
        p, q = q, negative_remainder(p, q)
    if len(seq[-1]) != 1:
        raise ArithmeticError("Repeated roots require a squarefree decomposition.")
    return seq


def variations(values):
    signs = [1 if a > 0 else -1 for a in values if a != 0]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def main():
    for matching_size, expected in [(84, 84), (85, 82)]:
        coefficients = [comb(2*j, j) * comb(169, 2*j) for j in range(85)]
        coefficients[1] -= 2*matching_size
        seq = sturm(coefficients)
        neg_inf = variations(s[-1] * (-1)**(len(s)-1) for s in seq)
        pos_inf = variations(s[-1] for s in seq)
        count = neg_inf - pos_inf
        if count != expected:
            raise ArithmeticError((matching_size, count))
        print(f"d=169, M={matching_size}: Sturm variations at -inf,+inf = "
              f"({neg_inf},{pos_inf}); {count} real and {84-count} nonreal gamma roots.")
    x = Fraction(-1, 218)
    p = first = second = 0
    for coefficient in reversed(coefficients):
        p, first, second = p*x + coefficient, first*x + p, second*x + 2*first
    if not -13348 < first*first - p*second < -13347:
        raise ArithmeticError("Laguerre inequality certificate disagrees.")
    print("The exact Laguerre expression at -1/218 lies between -13348 and -13347.")


if __name__ == "__main__":
    main()
