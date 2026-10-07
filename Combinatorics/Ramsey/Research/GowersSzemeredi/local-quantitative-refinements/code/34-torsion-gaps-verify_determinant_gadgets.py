"""Exact regression checks for the construction in gowers_cube_structure.tex.

These finite checks verify signs, row encoding, dimensions, Smith factors,
and unit cofactors; the universal and asymptotic theorems are proved in
the accompanying gowers_cube_structure.tex. Requires SymPy (tested with version 1.14.0
on Python 3.12.14). Run from any directory with
    python3 /path/to/code/verify_determinant_gadgets.py
"""

from itertools import product
from random import Random
import json
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


def nonunit_smith(a):
    diagonal = smith_normal_form(sp.Matrix(a), domain=sp.ZZ)
    return [abs(int(diagonal[i, i])) for i in range(len(a))
            if abs(int(diagonal[i, i])) != 1]


def det(a):
    """Integer Bareiss determinant, including row-pivot signs."""
    a = [list(map(int, row)) for row in a]
    n = len(a)
    if not n:
        return 1
    sign = 1
    previous = 1
    for k in range(n - 1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        d = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * d - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = d
    return sign * a[-1][-1]


def convert_row(a, i):
    n = len(a)
    z = a[i]
    assert set(z) <= {-2, -1, 0, 1}
    u = [int(x < 0) for x in z]
    v = [int(x == -2) for x in z]
    w = [int(x == 1) for x in z]
    out = [[1, 0] + u, [0, 1] + v]
    for j in range(n):
        out.append(([1, 1] + w) if j == i else ([0, 0] + a[j]))
    return out


def encode_first_row(a, max_abs):
    n = len(a)
    b = max_abs.bit_length()  # ceil(log2(max_abs+1)), exact integer form
    assert b >= 1
    assert all(abs(x) <= max_abs for x in a[0])
    out = [[0] * (n + b - 1) for _ in range(n + b - 1)]
    for i in range(b - 1):
        out[i][i] = 1
        out[i + 1][i] = -2
    for i in range(b):
        for j, value in enumerate(a[0]):
            sign = 1 if value >= 0 else -1
            out[i][b - 1 + j] = sign * ((abs(value) >> (b - i - 1)) & 1)
    for i in range(1, n):
        out[b + i - 1][b - 1:] = a[i]
    assert det(out) == det(a)
    for i in range(b):
        old_det = det(out)
        out = convert_row(out, 3 * i)
        assert det(out) == old_det
    assert len(out) == n + 3 * b - 1
    assert all(x in (0, 1) for row in out for x in row)
    assert nonunit_smith(out) == nonunit_smith(a)
    return out


def compose(m, u_index, v_index, t, h):
    m_dim = len(m)
    assert det(m) == 1
    inverse = sp.Matrix(m).inv()
    alpha = -int(inverse[u_index, v_index])
    base = abs(alpha)
    assert base > 1
    assert abs(h) < base ** t
    digits = []
    remaining = abs(h)
    for j in range(t):
        d = remaining % base
        remaining //= base
        digits.append((1 if h >= 0 else -1) * ((-1 if alpha > 0 else 1) ** j) * d)
    n = t + (t - 1) * m_dim
    out = [[0] * n for _ in range(n)]
    out[0][:t] = digits
    for i in range(1, t):
        out[i][i] = 1
        start = t + (i - 1) * m_dim
        out[i][start + u_index] = 1
        out[start + v_index][i - 1] = 1
        for r in range(m_dim):
            for c in range(m_dim):
                out[start + r][start + c] = m[r][c]
    assert det(out) == h
    out = encode_first_row(out, base - 1)
    expected = (t - 1) * (m_dim + 1) + 3 * (base - 1).bit_length()
    assert len(out) == expected
    assert det(out) == h
    assert nonunit_smith(out) == ([] if abs(h) == 1 else [abs(h)])
    omitted = 3 * (base - 1).bit_length() - 1
    unit_minor = [[x for j, x in enumerate(row) if j != omitted]
                  for i, row in enumerate(out) if i != omitted]
    assert det(unit_minor) == 1
    return out, alpha


def main():
    rng = Random(20261006)
    row_cases = 0
    for n in range(2, 6):
        for bound in (1, 2, 3, 4, 5, 7, 8, 15, 16):
            for _ in range(4):
                a = [[rng.randrange(-bound, bound + 1) for _ in range(n)]]
                a += [[rng.randrange(2) for _ in range(n)] for _ in range(n - 1)]
                encode_first_row(a, bound)
                row_cases += 1
    m4 = [[0, 0, 0, 1], [0, 0, 1, 1],
          [0, 1, 0, 1], [1, 1, 1, 0]]
    m5 = [row + [0] for row in m4] + [[1, 0, 0, 1, 1]]
    composition_cases = []
    for m, u, v, t in ((m4, 0, 0, 2), (m4, 0, 0, 3),
                       (m5, 4, 0, 2), (m5, 4, 0, 3)):
        alpha = -int(sp.Matrix(m).inv()[u, v])
        total = abs(alpha) ** t
        for h in range(-total + 1, total):
            out, checked_alpha = compose(m, u, v, t, h)
            assert checked_alpha == alpha
        composition_cases.append({"alpha": alpha, "digits": t,
                                  "range": [-total + 1, total - 1],
                                  "order": len(out), "cases": 2 * total - 1})
    result = {"row_encoding_cases": row_cases,
              "composition_cases": composition_cases,
              "total_composition_cases": sum(x["cases"] for x in composition_cases),
              "status": "All exact determinant, Smith-factor, unit-cofactor, binary-entry, dimension, and sign checks passed."}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
