#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

These checks are not proofs of the infinite-dimensional or arbitrary-support
results.  In particular, a finite rectangular test is not an injective,
nonsurjective finite-dimensional endomorphism.

Run: python code/verify.py
Requires: Python 3.10+ and SymPy.
"""
from __future__ import annotations

import random
import sys
from collections import defaultdict
from fractions import Fraction
from typing import Callable

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install SymPy before running these checks.") from exc

CHECKS = 0
GROUPS: list[tuple[str, int]] = []
RNG = random.Random(20260922)
Exponent = tuple[Fraction, Fraction]
ZERO_EXP: Exponent = (Fraction(0), Fraction(0))


def check(condition: bool, description: str) -> None:
    global CHECKS
    CHECKS += 1
    if not condition:
        raise AssertionError(f"Check {CHECKS} failed: {description}")


def matrix_zero(a: sp.MatrixBase) -> bool:
    return all(sp.cancel(x) == 0 for x in a)


def run_group(name: str, fn: Callable[[], None]) -> None:
    before = CHECKS
    fn()
    GROUPS.append((name, CHECKS - before))
    print(f"PASS  {name}: {CHECKS - before} exact assertions")


def exp_add(a: Exponent, b: Exponent) -> Exponent:
    return (a[0] + b[0], a[1] + b[1])


def random_entry() -> sp.Expr:
    return sp.Rational(RNG.randint(-3, 3), RNG.randint(1, 3)) + sp.I * sp.Rational(
        RNG.randint(-2, 2), RNG.randint(1, 3)
    )


def random_matrix(rows: int, columns: int) -> sp.Matrix:
    return sp.Matrix(rows, columns, lambda _i, _j: random_entry())


def normalize(series: dict[Exponent, sp.MatrixBase]) -> dict[Exponent, sp.Matrix]:
    return {e: sp.simplify(m) for e, m in series.items() if not matrix_zero(m)}


def multiply(
    left: dict[Exponent, sp.MatrixBase], right: dict[Exponent, sp.MatrixBase]
) -> dict[Exponent, sp.Matrix]:
    if not left or not right:
        return {}
    rows = next(iter(left.values())).rows
    columns = next(iter(right.values())).cols
    out: dict[Exponent, sp.Matrix] = {}
    for a, ma in left.items():
        for b, mb in right.items():
            e = exp_add(a, b)
            out[e] = out.get(e, sp.zeros(rows, columns)) + ma * mb
    return normalize(out)


def star(series: dict[Exponent, sp.MatrixBase]) -> dict[Exponent, sp.Matrix]:
    return {e: m.conjugate().T for e, m in series.items()}


def inner(
    x: dict[Exponent, sp.MatrixBase], y: dict[Exponent, sp.MatrixBase]
) -> dict[Exponent, sp.Matrix]:
    # Linear in x, conjugate-linear in y, as in the article.
    return multiply(star(y), x)


def same(
    a: dict[Exponent, sp.MatrixBase], b: dict[Exponent, sp.MatrixBase]
) -> bool:
    keys = a.keys() | b.keys()
    for e in keys:
        if e not in a:
            if not matrix_zero(b[e]):
                return False
        elif e not in b:
            if not matrix_zero(a[e]):
                return False
        elif not matrix_zero(a[e] - b[e]):
            return False
    return True


def finite_hahn_checks() -> None:
    # Lexicographic order includes positive exponents with negative components.
    op_support = [(-1, 2), (0, -2), (0, 1), (1, -3)]
    vector_support = [(-1, -1), (0, 0), (0, 2)]
    convert = lambda e: (Fraction(e[0], 2), Fraction(e[1], 3))
    for _ in range(8):
        a = normalize({convert(e): random_matrix(2, 2) for e in op_support})
        b = normalize({convert(e): random_matrix(2, 2) for e in op_support[:3]})
        x = normalize({convert(e): random_matrix(2, 1) for e in vector_support})
        y = normalize({convert(e): random_matrix(2, 1) for e in vector_support[1:]})
        check(same(inner(multiply(a, x), y), inner(x, multiply(star(a), y))),
              "Hahn adjoint identity with a linear-first inner product")
        check(same(multiply(multiply(a, b), x), multiply(a, multiply(b, x))),
              "finite Hahn associativity")
        check(same(star(multiply(a, b)), multiply(star(b), star(a))),
              "coefficientwise involution reverses products")
        xx = inner(x, x)
        delta = min(x)
        check(min(xx) == exp_add(delta, delta), "inner-product leading valuation")
        expected = (x[delta].conjugate().T * x[delta])[0]
        check(sp.simplify(xx[min(xx)][0] - expected) == 0 and bool(expected > 0),
              "positive ordinary leading coefficient")


def noncommutative_neumann() -> None:
    e1 = sp.Matrix([[0, 1], [2, -1]])
    e2 = sp.Matrix([[1, 2], [0, 3]])
    check(not matrix_zero(e1 * e2 - e2 * e1), "test coefficients really do not commute")
    nmax = 12
    f = [sp.eye(2)]
    for n in range(1, nmax + 1):
        f.append(-e1 * f[n - 1] - (e2 * f[n - 2] if n >= 2 else sp.zeros(2)))
    for n in range(1, nmax + 1):
        left = f[n] + e1 * f[n - 1] + (e2 * f[n - 2] if n >= 2 else sp.zeros(2))
        right = f[n] + f[n - 1] * e1 + (f[n - 2] * e2 if n >= 2 else sp.zeros(2))
        check(matrix_zero(left), f"left Neumann inverse, coefficient {n}")
        check(matrix_zero(right), f"right Neumann inverse, coefficient {n}")


def isolated_resolvent() -> None:
    t = sp.Symbol("t")
    epsilon = t + t**2
    p = sp.diag(1, 1, 0, 0)
    q = sp.eye(4) - p
    t_op = sp.diag(1, 1, 3, 5)
    b = sp.diag(0, 0, sp.Rational(1, 2), sp.Rational(1, 4))
    a = t_op - (1 + epsilon) * sp.eye(4)
    for nmax in range(7):
        r = -p / epsilon
        for n in range(nmax + 1):
            r += epsilon**n * b ** (n + 1)
        expected = sp.eye(4) - epsilon ** (nmax + 1) * b ** (nmax + 1) * q
        check(matrix_zero(a * r - expected), "isolated-point left resolvent remainder")
        check(matrix_zero(r * a - expected), "isolated-point right resolvent remainder")
        check(matrix_zero(a * (-p / epsilon) - p), "exact inversion on isolated eigenspace")


def rectangular_complement() -> None:
    # V=C^2 -> Y=C^3 is a finite analogue of an injective range splitting.
    t = sp.Symbol("t")
    s = sp.Matrix([[1, 0], [0, 1], [0, 0]])
    u = sp.Matrix([[1, 0, 0], [0, 1, 0]])
    e = t * sp.Matrix([[1, 2], [0, 1], [3, 4]]) + t**2 * sp.Matrix(
        [[0, 1], [-1, 0], [2, -2]]
    )
    a = s + e
    r = (sp.eye(2) + u * e).inv()
    left = r * u
    projection = sp.eye(3) - a * left
    w = sp.Matrix([0, 0, 1])
    check(matrix_zero(u * s - sp.eye(2)), "US=I in rectangular analogue")
    check(matrix_zero(left * a - sp.eye(2)), "LA=I in rectangular analogue")
    check(matrix_zero(u * projection), "U Pi=0")
    check(matrix_zero(projection * a), "Pi A=0")
    check(matrix_zero(projection * w - w), "Pi fixes the complement")
    check(matrix_zero(projection**2 - projection), "Pi is idempotent")
    check(matrix_zero(a * left + projection - sp.eye(3)), "exact splitting identity")


def finite_diagonal_sections() -> None:
    t = sp.Symbol("t", real=True)
    for n in range(1, 13):
        a = sp.Rational(1, n) - sp.I * t
        c = sp.Rational(1, n*n) + t*t
        check(sp.expand(sp.conjugate(a) * a - c) == 0, "A* A = D^2+t^2I")
        for kmax in (0, 1, 3, 6):
            solution = sum((-1)**k * n**(2*k) * t**(2*k) for k in range(kmax + 1))
            remainder = (-1)**kmax * n**(2*kmax) * t**(2*kmax + 2)
            check(sp.expand(c * solution - sp.Rational(1, n*n) - remainder) == 0,
                  "finite positive-regularizer solution remainder")
            resolvent = sum(sp.I**k * n**(k+1) * t**k for k in range(kmax + 1))
            check(sp.expand(a * resolvent - 1 + (sp.I*n*t)**(kmax+1)) == 0,
                  "finite imaginary-shift resolvent remainder")
    for n in (1, 2, 5, 10, 25):
        ones = sp.ones(n, 1)
        check((ones.T * ones)[0] == n, "constant finite solution has norm squared N")


def backward_shift_check() -> None:
    t = sp.Symbol("t")
    for nmax in range(1, 13):
        b = sp.zeros(nmax + 1)
        for j in range(1, nmax + 1):
            b[j - 1, j] = 1
        x = sp.Matrix([t**j for j in range(nmax + 1)])
        remainder = sp.zeros(nmax + 1, 1)
        remainder[nmax] = -t**(nmax + 1)
        check(matrix_zero(b*x - t*x - remainder), "truncated backward-shift exact residual")


def main() -> None:
    print("Finite exact checks for Infinitesimal Spectral Thickening")
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}; seed 20260922")
    print("No numerical tolerances; no infinite-dimensional verification claimed.\n")
    run_group("Finite Hahn convolution, adjoints and positivity", finite_hahn_checks)
    run_group("Noncommutative Neumann inversion", noncommutative_neumann)
    run_group("Isolated spectral-point resolvent", isolated_resolvent)
    run_group("Rectangular complement-splitting analogue", rectangular_complement)
    run_group("Finite diagonal sections and exact remainders", finite_diagonal_sections)
    run_group("Backward-shift residual", backward_shift_check)
    print(f"\nALL PASSED: {CHECKS} exact assertions in {len(GROUPS)} groups.")
    print("The Baire, full Hahn-support, spectral, cokernel and completeness proofs")
    print("remain mathematical proofs in article.tex, not conclusions of these tests.")


if __name__ == "__main__":
    main()
