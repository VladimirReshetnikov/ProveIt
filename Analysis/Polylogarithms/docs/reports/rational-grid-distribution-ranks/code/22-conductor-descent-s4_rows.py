"""Exact imaginary Gaussian depth-two law presentation.

The rows are formal shuffle/stuffle consequences of products of two
single polylogarithms, with single-value products and tails suppressed.
All weight-one boundary instantiations are included in this deliberately
specified formal vocabulary. A row-space obstruction does not disprove
an identity between the evaluated constants.
"""
from __future__ import annotations
from math import comb
from typing import Callable, Iterable
import sympy as sp

Term = tuple[int, int, int, int, int]  # coefficient, a, b, c, d
Variable = tuple[int, int, int, int]   # Im Li_(a,b)(i**c, i**d)


def build(weight: int, distribution: bool = True) -> tuple[
        list[Variable], sp.Matrix, list[tuple], Callable[[Iterable[Term]], list]]:
    """Return variables, integer matrix, row descriptions, term-to-row map.

    Canonical conjugation signs encode x(-c,-d) = -x(c,d).
    Colors fixed by conjugation have zero imaginary component.
    Distribution rows use the degree-two root filter; at level four their
    imaginary components vanish after conjugation, but they are generated
    explicitly so that this fact remains checkable.
    """
    if not isinstance(weight, int) or weight < 2:
        raise ValueError("weight must be an integer >= 2")

    def canonical(c: int, d: int) -> tuple[tuple[int, int] | None, int]:
        c %= 4
        d %= 4
        if c in (0, 2) and d in (0, 2):
            return None, 0
        pair, conjugate = (c, d), ((-c) % 4, (-d) % 4)
        return (pair, 1) if pair < conjugate else (conjugate, -1)

    colors = sorted({pair for c in range(4) for d in range(4)
                     if (pair := canonical(c, d)[0]) is not None})
    variables = [(a, weight-a, c, d)
                 for a in range(1, weight) for c, d in colors]
    index = {x: j for j, x in enumerate(variables)}

    def row(terms: Iterable[Term]) -> list:
        result = [sp.S.Zero] * len(variables)
        for coefficient, a, b, c, d in terms:
            if a < 1 or b < 1 or a+b != weight:
                raise ValueError("each term must have positive indices of the given weight")
            pair, sign = canonical(c, d)
            if sign:
                result[index[(a, b, *pair)]] += sign * sp.sympify(coefficient)
        return result

    rows, descriptions = [], []
    for p in range(1, weight):
        q = weight-p
        for c in range(4):
            for d in range(4):
                r = row([(1, p, q, c, d), (1, q, p, d, c)])
                if any(r):
                    rows.append(r)
                    descriptions.append(('stuffle', p, q, c, d))
                terms = [(comb(q-1+j, j), q+j, p-j, d, c-d)
                         for j in range(p)]
                terms += [(comb(p-1+j, j), p+j, q-j, c, d-c)
                          for j in range(q)]
                r = row(terms)
                if any(r):
                    rows.append(r)
                    descriptions.append(('shuffle', p, q, c, d))
    if distribution:
        for a in range(1, weight):
            b = weight-a
            for c in range(2):
                for d in range(2):
                    terms = [(2**(weight-2), a, b, c+2*j, d+2*k)
                             for j in range(2) for k in range(2)]
                    terms.append((-1, a, b, 2*c, 2*d))
                    r = row(terms)
                    if any(r):
                        rows.append(r)
                        descriptions.append(('distribution', a, b, c, d))
    return variables, sp.Matrix(rows), descriptions, row
