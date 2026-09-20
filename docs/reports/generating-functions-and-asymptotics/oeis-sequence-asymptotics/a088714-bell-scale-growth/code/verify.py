#!/usr/bin/env python3
"""Finite exact-arithmetic implementation audits; not a substitute for the proof."""
from __future__ import annotations
from math import comb
from pathlib import Path
from coefficients import coefficients, read_coefficients

ROOT = Path(__file__).resolve().parent.parent


def mul(a: list[int], b: list[int], degree: int) -> list[int]:
    """Multiply polynomials, truncating after x^degree."""
    out = [0] * (degree + 1)
    for i, x in enumerate(a[:degree + 1]):
        if x:
            for j, y in enumerate(b[:degree + 1 - i]):
                out[i + j] += x * y
    return out


def compose(a: list[int], b: list[int], degree: int) -> list[int]:
    """Horner composition, for an inner series of constant coefficient zero."""
    if b[0] != 0:
        raise ValueError("The inner series must have constant coefficient zero")
    out = [0] * (degree + 1)
    for coefficient in reversed(a[:degree + 1]):
        out = mul(out, b, degree)
        out[0] += coefficient
    return out


def stirling_rows(n_max: int) -> list[list[int]]:
    rows = [[1]]
    for n in range(n_max):
        row = [0] * (n + 2)
        for j, v in enumerate(rows[-1]):
            row[j] += j * v
            row[j + 1] += v
        rows.append(row)
    return rows


def main() -> None:
    supplied = read_coefficients(ROOT / "data" / "coefficients.txt")
    known = [1, 1, 3, 13, 69, 419, 2809, 20353, 157199, 1281993,
             10963825, 97828031, 907177801, 8716049417, 86553001779,
             886573220093, 9351927111901, 101447092428243,
             1130357986741545, 12923637003161409, 151479552582252239]
    assert supplied[:len(known)] == known
    print("PASS: initial OEIS terms, n = 0..20.")

    n_check = min(400, len(supplied) - 1)
    own = coefficients(n_check)
    assert own == supplied[:n_check + 1]
    print(f"PASS: independent Python recomputation agrees with supplied GMP data, n = 0..{n_check}.")

    degree = 40
    a = supplied[:degree + 1]
    b = [0] + a[:degree]
    composed = compose(a, b, degree)
    product = mul(mul(a, a, degree), composed, degree)
    rhs = [1] + product[:degree]
    assert rhs == a
    inverse = ([0, 1] + [-v for v in a])[:degree + 1]
    identity = [0, 1] + [0] * (degree - 1)
    assert compose(b, inverse, degree) == identity
    assert compose(inverse, b, degree) == identity
    assert compose(inverse, inverse, degree) == [
        inverse[j] - (inverse[j - 1] if j else 0)
        for j in range(degree + 1)
    ]
    print(f"PASS: defining functional equation, both inverse compositions, and f(f(x))=(1-x)f(x), through degree {degree}.")

    limit = 80
    rows = stirling_rows(max(limit, 150))
    # Polynomial coefficients for E[(1+X)^n] and E[(2+X)^n].
    m1 = [[sum(comb(n, j) * rows[j][r] for j in range(r, n + 1))
           for r in range(n + 1)] for n in range(limit + 1)]
    m2 = [[sum(comb(n, j) * 2 ** (n - j) * rows[j][r]
                   for j in range(r, n + 1))
           for r in range(n + 1)] for n in range(limit + 1)]
    previous_h: list[int] | None = None
    for n in range(1, limit + 1):
        s = [0] * n
        for i in range(n):
            for p, u in enumerate(m1[i]):
                for q, v in enumerate(m2[n - 1 - i]):
                    s[p + q] += u * v
        d = [(r + 1) * rows[n][r + 1] for r in range(n)]
        h = [0] * (n + 1)
        for r in range(n):
            h[r] += 2 * d[r]
            h[r + 1] += d[r] - s[r]
        assert all(v >= 0 for v in h)
        if previous_h is not None:
            # Twice the H recurrence: avoids rational arithmetic.
            old_n = n - 1
            rhs2 = [0] * (n + 1)
            for j, value in enumerate(previous_h):
                rhs2[j] += (j + 2) * value
                rhs2[j + 1] += 2 * value
            for j in range(old_n + 1):
                sj = rows[old_n][j]
                sj1 = rows[old_n][j + 1] if j + 1 <= old_n else 0
                k2 = (j - 1) * (j - 4) * sj + j * (j + 1) * sj1
                rhs2[j] += k2
                if old_n >= 4:
                    assert k2 >= 0
            assert rhs2 == [2 * v for v in h]
        previous_h = h
    print(f"PASS: H_n coefficient positivity and exact H recurrence, n = 1..{limit}; K_n positivity, n = 4..{limit-1}.")

    bound_limit = min(150, len(supplied) - 1)
    for n in range(1, bound_limit + 1):
        assert max(h ** (n + 1 - h) for h in range(1, n + 2)) <= supplied[n]
        for lam in (1, 2, 5, 10, 20):
            derivative = sum(j * rows[n][j] * lam ** (j - 1) for j in range(1, n + 1))
            assert supplied[n] * lam ** n <= (lam + 2) ** n * derivative
    print(f"PASS: lower bound and Touchard upper bound for lambda=1,2,5,10,20, n = 1..{bound_limit}.")
    print(f"Supplied exact data range: n = 0..{len(supplied)-1}.")
    print("All finite audits passed. All-index claims are justified by the written proof.")


if __name__ == "__main__":
    main()
