#!/usr/bin/env python3
"""Exact finite algebra checks for Nonabelian Support Obstructions.

These computations do NOT verify an infinite well-ordering argument, the
analytic existence theorems, or the research novelty of any statement.
Run from any working directory: python path/to/code/verify.py
Requires Python >= 3.10 and SymPy.
"""
from __future__ import annotations

from fractions import Fraction
import platform
from typing import Mapping

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

CHECKS = 0
u, z = sp.symbols("u z")


def check(condition: bool, description: str) -> None:
    global CHECKS
    if not condition:
        raise AssertionError(description)
    CHECKS += 1


def expand_matrix(matrix: sp.MatrixBase) -> sp.Matrix:
    return sp.Matrix(matrix).applyfunc(sp.expand)


def equal_matrix(left: sp.MatrixBase, right: sp.MatrixBase, description: str) -> None:
    check(left.shape == right.shape, description + " (shape)")
    check(all(sp.cancel(value) == 0 for value in left - right), description)


def unit(size: int, row: int, column: int) -> sp.Matrix:
    result = sp.zeros(size)
    result[row - 1, column - 1] = 1
    return result


def rank_three() -> None:
    x, y = sp.symbols("x y")
    eye = sp.eye(3)
    e12, e23, e13 = unit(3, 1, 2), unit(3, 2, 3), unit(3, 1, 3)
    g = eye + x / u * e12 + y * e23
    p = eye + x / u * e12 - x * y / u * e13
    h = eye + y * e23
    equal_matrix(p * h, g, "rank-three polar times regular equals input")
    check(g.det() == 1, "rank-three determinant is one")
    repaired = g + x * y / u * e13
    equal_matrix((eye + x / u * e12) * h, repaired, "repair removes hidden polar term")
    nilpotent = g - eye
    equal_matrix(nilpotent ** 3, sp.zeros(3), "rank-three nilpotence")
    logarithm = nilpotent - nilpotent ** 2 / 2
    check(sp.expand(logarithm[0, 2]) == -x * y / (2 * u), "matrix-log half coefficient")
    naive = eye + x / u * e12 - x * y / (2 * u) * e13
    check(sp.cancel((naive - p)[0, 2]) == x * y / (2 * u), "naive polar logarithm is incorrect")
    print("PASS: rank-three factorization, determinant, repair, and logarithm diagnostic")


def chain_examples() -> None:
    a = sp.symbols("a")
    for rank in range(3, 11):
        constants = sp.symbols(f"c2:{rank}")
        c = sp.zeros(rank)
        for j in range(2, rank):
            c += constants[j - 2] * unit(rank, j, j + 1)
        eye = sp.eye(rank)
        h = eye + c
        h_inverse = sp.zeros(rank)
        for k in range(rank):
            h_inverse += (-c) ** k
        equal_matrix(h * h_inverse, eye, f"rank {rank} chain inverse")
        g = eye + c + a * unit(rank, 1, 2)
        polar = eye.copy()
        product = sp.Integer(1)
        for k in range(2, rank + 1):
            if k >= 3:
                product *= constants[k - 3]
            polar += (-1) ** (k - 2) * a * product * unit(rank, 1, k)
        equal_matrix(polar * h, g, f"rank {rank} chain factorization")
        equal_matrix((polar - eye) ** 2, sp.zeros(rank), f"rank {rank} row-one square zero")
        check(g.det() == 1, f"rank {rank} chain determinant")
    for rank in range(4, 13):
        for n in range(2, 26):
            exponents = {2: Fraction(1) - Fraction(1, n)}
            exponents.update({j: Fraction(1) for j in range(3, rank - 1)})
            exponents[rank - 1] = Fraction(2, n)
            total = Fraction(1)
            for k in range(3, rank + 1):
                total += exponents[k - 1]
                expected = (Fraction(k - 1) - Fraction(1, n)
                            if k < rank else Fraction(rank - 2) + Fraction(1, n))
                check(total == expected, f"exponent formula rank {rank}, n {n}, entry 1{k}")
                if k < rank:
                    check(expected < Fraction(k - 1) - Fraction(1, n + 1),
                          "finite lower-support monotonicity illustration")
                else:
                    check(expected > Fraction(rank - 2) + Fraction(1, n + 1),
                          "finite terminal-support monotonicity illustration")
    print("PASS: chain identities for ranks 3--10; exponent formulas for ranks 4--12, n=2--25")


Series = dict[Fraction, sp.Matrix]


def generated_exponents(generators: set[Fraction], cutoff: Fraction) -> list[Fraction]:
    if not generators or any(g <= 0 for g in generators):
        raise ValueError("A nonempty finite set of positive rational generators is required")
    reached = {Fraction(0)}
    frontier = [Fraction(0)]
    while frontier:
        base = frontier.pop()
        for generator in generators:
            new = base + generator
            if new <= cutoff and new not in reached:
                reached.add(new)
                frontier.append(new)
    return sorted(reached)


def coefficient(series: Mapping[Fraction, sp.Matrix], exponent: Fraction, size: int) -> sp.Matrix:
    return series.get(exponent, sp.zeros(size))


def product_series(left: Series, right: Series, cutoff: Fraction, size: int) -> Series:
    answer: Series = {}
    for a, first in left.items():
        for b, second in right.items():
            exponent = a + b
            if exponent <= cutoff:
                answer[exponent] = answer.get(exponent, sp.zeros(size)) + first * second
    return {exponent: expand_matrix(matrix) for exponent, matrix in answer.items()}


def negative_part(value: sp.Expr) -> sp.Expr:
    answer = sp.Integer(0)
    for term in sp.Add.make_args(sp.expand(value)):
        power = term.as_powers_dict().get(u, sp.Integer(0))
        if not power.is_Integer:
            raise ValueError(f"Expected a Laurent polynomial in u, got {term}")
        if power < 0:
            answer += term
    return sp.expand(answer)


def factor_series(g: Series, exponents: list[Fraction], size: int) -> tuple[Series, Series]:
    p: Series = {Fraction(0): sp.eye(size)}
    h: Series = {Fraction(0): sp.eye(size)}
    for gamma in exponents[1:]:
        residual = coefficient(g, gamma, size).copy()
        for eta in exponents[1:]:
            if eta >= gamma:
                break
            theta = gamma - eta
            if theta in h:
                residual -= coefficient(p, eta, size) * h[theta]
        residual = expand_matrix(residual)
        polar = residual.applyfunc(negative_part)
        p[gamma] = polar
        h[gamma] = expand_matrix(residual - polar)
    return p, h


def equal_series(left: Series, right: Series, exponents: list[Fraction], size: int, label: str) -> None:
    for exponent in exponents:
        equal_matrix(coefficient(left, exponent, size), coefficient(right, exponent, size),
                     f"{label}: exponent {exponent}")


def rational_recursion() -> None:
    half, third = Fraction(1, 2), Fraction(2, 3)
    cutoff = Fraction(3)
    exponents = generated_exponents({half, third}, cutoff)
    size = 2
    g: Series = {
        Fraction(0): sp.eye(size),
        half: sp.Matrix([[u, 1/u], [1/u**2, -u]]),
        third: sp.Matrix([[1/u + u**2, 1], [u, -1/u]]),
        half + third: sp.Matrix([[2/u, u**2], [0, -u]]),
    }
    p, h = factor_series(g, exponents, size)
    equal_series(product_series(p, h, cutoff, size), g, exponents, size, "local recursion product")
    for gamma in exponents[1:]:
        equal_matrix(p[gamma].applyfunc(negative_part), p[gamma], "polar output is negative Laurent")
        equal_matrix(h[gamma].applyfunc(negative_part), sp.zeros(size), "regular output is holomorphic")
    q: Series = {
        Fraction(0): sp.eye(size),
        half: sp.Matrix([[1, u], [0, 0]]),
        third: sp.Matrix([[0, 0], [u**2, 1]]),
    }
    gauged = product_series(g, q, cutoff, size)
    p_gauged, h_gauged = factor_series(gauged, exponents, size)
    equal_series(p_gauged, p, exponents, size, "holomorphic right-gauge invariance")
    equal_series(h_gauged, product_series(h, q, cutoff, size), exponents, size,
                 "right gauge multiplies regular factor")
    inverse: Series = {Fraction(0): sp.eye(size)}
    for gamma in exponents[1:]:
        value = sp.zeros(size)
        for eta in exponents[1:]:
            if eta > gamma:
                break
            if gamma - eta in inverse:
                value -= coefficient(g, eta, size) * inverse[gamma - eta]
        inverse[gamma] = expand_matrix(value)
    identity: Series = {Fraction(0): sp.eye(size)}
    equal_series(product_series(g, inverse, cutoff, size), identity, exponents, size, "right inverse")
    equal_series(product_series(inverse, g, cutoff, size), identity, exponents, size, "left inverse")
    print(f"PASS: noncommuting rational-exponent recursion through {cutoff}, "
          f"{len(exponents)} exponents including zero; local gauges and two-sided inverse")


def finite_punctures() -> None:
    x = sp.symbols("x")
    centres = (2, 3, 5, 7)
    local_constants = sp.symbols("y2 y3 y5 y7")
    eye = sp.eye(3)
    e12, e23, e13 = unit(3, 1, 2), unit(3, 2, 3), unit(3, 1, 3)
    polars = {
        n: eye + x / (z-n) * e12 - x * y / (z-n) * e13
        for n, y in zip(centres, local_constants)
    }
    f = eye.copy()
    for polar in polars.values():
        f += polar - eye
    f_inverse = 2 * eye - f  # row-one square-zero algebra
    equal_matrix(f * f_inverse, eye, "finite central inverse")
    for n, y in zip(centres, local_constants):
        p = polars[n]
        h = eye + y * e23
        q = (2 * eye - p) * f
        q = q.applyfunc(sp.cancel)
        q_at_centre = q.applyfunc(lambda value: value.subs(z, n))
        check(not any(value.has(sp.zoo, sp.nan, sp.oo, -sp.oo) for value in q_at_centre),
              f"finite disk gauge extends at centre {n}")
        b = (eye - y * e23) * q
        b_inverse = (2 * eye - q) * h
        equal_matrix(b * b_inverse, eye, f"finite disk gauge inverse at {n}")
        g = eye + x / (z-n) * e12 + y * e23
        equal_matrix(f * b_inverse, g, f"finite-puncture splitting at {n}")
    print("PASS: exact four-puncture splitting and extension of every local frame")


def main() -> None:
    print("Nonabelian Support Obstructions: exact finite algebra verification")
    print(f"Python {platform.python_version()}; SymPy {sp.__version__}")
    print("No floating-point arithmetic is used in the checked identities.")
    rank_three()
    chain_examples()
    rational_recursion()
    finite_punctures()
    print(f"SUCCESS: {CHECKS} exact checks passed.")
    print("Finite checks are not proofs of the infinite support or analytic existence theorems.")


if __name__ == "__main__":
    main()
