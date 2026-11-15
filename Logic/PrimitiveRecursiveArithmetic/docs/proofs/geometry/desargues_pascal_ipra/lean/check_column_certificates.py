#!/usr/bin/env python3
"""Exact symbolic check of the six generic determinant column identities.

No random sampling or floating point is used. Variables 0..35 denote a
generic 6x6 matrix; variables 36..41 are the six conic coefficients.
This is supplementary arithmetic checking, not a Lean or iPRA proof checker.
"""

from itertools import permutations
import json


def add(a, b):
    out = dict(a)
    for term, coeff in b.items():
        value = out.get(term, 0) + coeff
        if value:
            out[term] = value
        else:
            out.pop(term, None)
    return out


def scale(a, n):
    return {term: coeff * n for term, coeff in a.items() if coeff * n}


def mul(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            term = tuple(sorted(m + n))
            out[term] = out.get(term, 0) + c * d
    return {term: coeff for term, coeff in out.items() if coeff}


def var(i):
    return {(i,): 1}


def det6(matrix):
    out = {}
    for p in permutations(range(6)):
        parity = sum(p[i] > p[j] for i in range(6) for j in range(i + 1, 6))
        term = {(): (-1) ** parity}
        for i in range(6):
            term = mul(term, matrix[i][p[i]])
        out = add(out, term)
    return out


def main():
    matrix = [[var(6 * i + j) for j in range(6)] for i in range(6)]
    coeffs = [var(36 + j) for j in range(6)]
    base = det6(matrix)
    assert len(base) == 720
    combinations = []
    for i in range(6):
        row_sum = {}
        for k in range(6):
            row_sum = add(row_sum, mul(matrix[i][k], coeffs[k]))
        combinations.append(row_sum)
    checks = []
    for j in range(6):
        changed = [row.copy() for row in matrix]
        for i in range(6):
            changed[i][j] = combinations[i]
        lhs = det6(changed)
        rhs = mul(coeffs[j], base)
        assert lhs == rhs, f"Column identity {j} failed"
        checks.append({"column": j, "normalized_terms": len(lhs), "passed": True})
    print(json.dumps({"method": "exact sparse integer polynomial normalization",
                      "variables": 42, "degree": 7, "checks": checks}, indent=2))


if __name__ == "__main__":
    main()
