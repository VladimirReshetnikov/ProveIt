#!/usr/bin/env python3
"""Compute one-variable Alexander data of a closed braid. Requires SymPy.

Usage: python alexander_braids.py [number-of-strands [signed generators ...]]
For example, 3 1 -2 1 -2 is the figure-eight knot. Positive generators
are downward left-over-right. Without arguments, run the finite checks.
"""
from itertools import combinations
from math import gcd
import sys

import sympy as sp

t = sp.Symbol("t")


def braid_matrix(strands, word):
    """Linear map on the initial segment colors, acting on columns."""
    if strands < 1:
        raise ValueError("strand count must be positive")
    rows = list(sp.eye(strands).tolist())
    for generator in word:
        i = abs(generator) - 1
        if not 0 <= i < strands - 1:
            raise ValueError("generator index out of range")
        left, right = rows[i], rows[i + 1]
        if generator > 0:
            rows[i] = [sp.expand((1 - t) * a + t * b) for a, b in zip(left, right)]
            rows[i + 1] = left
        else:
            rows[i] = right
            rows[i + 1] = [sp.expand(a / t + (1 - 1 / t) * b) for a, b in zip(left, right)]
    return sp.Matrix(rows)


def clear_monomial(value):
    """Choose the integral polynomial in a nonzero Laurent shift class with low degree 0."""
    terms = sp.expand(value)
    if terms == 0:
        return sp.Poly(0, t, domain=sp.ZZ)
    lo = min(term.as_powers_dict().get(t, 0) for term in sp.Add.make_args(terms))
    return sp.Poly(sp.expand(terms * t ** -lo), t, domain=sp.ZZ)


def first_minor_gcd(matrix):
    """Gcd of all (columns - 1)-minors in Z[t,t^-1], including content."""
    size = matrix.cols - 1
    if size == 0:
        return sp.Integer(1)
    primitive_gcd = None
    content = 0
    for rows in combinations(range(matrix.rows), size):
        for columns in combinations(range(matrix.cols), size):
            determinant = matrix.extract(rows, columns).det()
            polynomial = clear_monomial(determinant)
            if polynomial.is_zero:
                continue
            scalar, primitive = polynomial.primitive()
            content = gcd(content, int(scalar))
            primitive_gcd = primitive if primitive_gcd is None else sp.gcd(primitive_gcd, primitive)
    if primitive_gcd is None:
        return sp.Integer(0)
    answer = sp.Poly(content * primitive_gcd, t)
    # Value +1 at t=1 for knots; positive leading coefficient if the value is zero.
    value_at_one = answer.eval(1)
    change_sign = value_at_one < 0 or (value_at_one == 0 and answer.LC() < 0)
    return (-answer if change_sign else answer).as_expr()


def alexander(strands, word):
    return first_minor_gcd(braid_matrix(strands, word) - sp.eye(strands))


def checks():
    assert alexander(1, []) == 1
    assert alexander(2, []) == 0
    assert alexander(3, [1, 1, 1]) == 0  # Trefoil split from an extra circle.
    assert first_minor_gcd(sp.Matrix([[6 * (1 - t), 0], [0, 9 * (t - 1) / t]])) == 3 * t - 3
    for strand in (1, 2):
        assert braid_matrix(3, [strand, -strand]) == sp.eye(3)
        assert braid_matrix(3, [-strand, strand]) == sp.eye(3)
    assert braid_matrix(3, [1, 2, 1]) == braid_matrix(3, [2, 1, 2])
    for crossings in range(1, 10):
        series = sum((-t) ** j for j in range(crossings))
        result = alexander(2, [1] * crossings)
        assert sp.expand(result - series) == 0 or sp.expand(result + series) == 0
        assert abs(result.subs(t, -1)) == crossings
        assert alexander(2, [-1] * crossings) == result
    assert alexander(2, [1, 1, 1]) == t ** 2 - t + 1
    figure_eight = [1, -2, 1, -2]
    assert alexander(3, figure_eight) == -t ** 2 + 3 * t - 1
    assert alexander(3, [-g for g in figure_eight]) == -t ** 2 + 3 * t - 1
    # Both Markov stabilizations of a two-braid: direct checks of the presentation.
    for crossing in (2, -2):
        assert alexander(3, [1, 1, 1, crossing]) == t ** 2 - t + 1
    print("Passed first-minor gcd, integral content, split diagrams, braid relations,")
    print("two-strand closures and mirrors through nine crossings, trefoil stabilizations,")
    print("and the figure-eight and its mirror.")


if __name__ == "__main__":
    if len(sys.argv) == 1:
        checks()
    else:
        count = int(sys.argv[1])
        braid = tuple(map(int, sys.argv[2:]))
        presentation = braid_matrix(count, braid) - sp.eye(count)
        print("Closure matrix")
        print(presentation)
        print("Alexander polynomial")
        print(first_minor_gcd(presentation))
