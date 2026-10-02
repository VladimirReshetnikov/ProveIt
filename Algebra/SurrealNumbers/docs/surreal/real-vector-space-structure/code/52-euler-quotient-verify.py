#!/usr/bin/env python3
"""Exact finite checks accompanying 'Surreal Numbers as a Real Vector Space'.

Python 3.10+; standard library only. No floating-point arithmetic is used.
These tests verify finite algebraic identities and selected truncations, NOT
infinite Hahn support admissibility, cardinal dimension, class recursion,
spherical completeness, or historical novelty. See the mathematical proofs.

Run from any working directory:
    python code/verify.py
The report is written to ../data/verification.json relative to this file.
"""
from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path
from typing import Callable, Iterable

Series = dict[F, F]
Matrix = list[list[F]]
RESULTS: list[dict[str, object]] = []


def record(name: str, condition: bool, **details: object) -> None:
    """Fail immediately on a false claim, without depending on Python assert."""
    if not condition:
        raise AssertionError(f"Verification failed: {name}; {details}")
    RESULTS.append({"name": name, "passed": True, **details})


def series(items: Iterable[tuple[F | int, F | int]]) -> Series:
    out: Series = {}
    for exponent, coefficient in items:
        e, c = F(exponent), F(coefficient)
        out[e] = out.get(e, F(0)) + c
    return {e: c for e, c in out.items() if c}


def add(x: Series, y: Series) -> Series:
    return series([*x.items(), *y.items()])


def scale(a: F | int, x: Series) -> Series:
    return series((e, F(a) * c) for e, c in x.items())


def diagonal(x: Series, weight: Callable[[F], F]) -> Series:
    return series((e, weight(e) * c) for e, c in x.items())


def mul(x: Series, y: Series) -> Series:
    return series((e + f, c * d) for e, c in x.items() for f, d in y.items())


def rref(matrix: Matrix) -> tuple[Matrix, list[int]]:
    """Exact reduced row echelon form. Columns must already be in scale order."""
    if not matrix:
        return [], []
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("The matrix must be rectangular")
    a = [[F(x) for x in row] for row in matrix]
    pivots: list[int] = []
    row_index = 0
    for col in range(width):
        pivot = next((i for i in range(row_index, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row_index], a[pivot] = a[pivot], a[row_index]
        multiplier = a[row_index][col]
        a[row_index] = [x / multiplier for x in a[row_index]]
        for i in range(len(a)):
            if i != row_index and a[i][col]:
                multiplier = a[i][col]
                a[i] = [u - multiplier * v for u, v in zip(a[i], a[row_index])]
        pivots.append(col)
        row_index += 1
        if row_index == len(a):
            break
    return [row for row in a if any(row)], pivots


def determinant(matrix: Matrix) -> F:
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("Determinant needs a square matrix")
    a = [[F(x) for x in row] for row in matrix]
    value = F(1)
    for col in range(n):
        pivot = next((i for i in range(col, n) if a[i][col]), None)
        if pivot is None:
            return F(0)
        if pivot != col:
            a[pivot], a[col] = a[col], a[pivot]
            value = -value
        diagonal_entry = a[col][col]
        value *= diagonal_entry
        for i in range(col + 1, n):
            factor = a[i][col] / diagonal_entry
            for j in range(col + 1, n):
                a[i][j] -= factor * a[col][j]
            a[i][col] = F(0)
    return value


def finite_echelon_check() -> None:
    # Exact prefixes of a=sum(t^n), b=sum((n+1)t^n).
    nterms = 18
    a = [F(1) for _ in range(nterms)]
    b = [F(n + 1) for n in range(nterms)]
    rows, pivots = rref([a, b])
    expected = [[2 * u - v for u, v in zip(a, b)],
                [v - u for u, v in zip(a, b)]]
    record("reduced Hahn basis: geometric/derivative example",
           rows == expected and pivots == [0, 1], prefix_terms=nterms)
    changed = [[3 * u + 5 * v for u, v in zip(a, b)],
               [7 * u + 2 * v for u, v in zip(a, b)],
               [u + v for u, v in zip(a, b)]]
    record("canonical echelon basis invariant under changed generators",
           rref(changed) == (rows, pivots))
    for u, v in [(F(3, 7), F(-5, 9)), (F(0), F(2)), (F(9), F(0))]:
        x = [u * p + v * q for p, q in zip(a, b)]
        reconstructed = [sum(x[pivots[i]] * rows[i][j]
                             for i in range(len(rows))) for j in range(nterms)]
        record(f"pivot coefficient reconstruction ({u}, {v})", reconstructed == x)


def vandermonde_checks() -> None:
    bases = [F(1, 3), F(1), F(2), F(5, 2)]
    for start in [0, 1, 7, 20]:
        matrix = [[r ** n for r in bases] for n in range(start, start + len(bases))]
        expected = F(1)
        for r in bases:
            expected *= r ** start
        for j in range(len(bases)):
            for i in range(j):
                expected *= bases[j] - bases[i]
        actual = determinant(matrix)
        record(f"eventual Vandermonde determinant at N={start}",
               actual == expected and actual != 0, determinant=str(actual))
    # Selected finite minors for the exponential-polynomial independence proof.
    columns = [(r, k) for r in [F(1), F(2), F(3)] for k in range(3)]
    for start in [0, 4, 11]:
        matrix = [[F(n) ** k * r ** n for r, k in columns]
                  for n in range(start, start + len(columns))]
        value = determinant(matrix)
        record(f"exponential-polynomial minor at N={start}", value != 0,
               rows=len(columns), determinant=str(value))


def euler_checks() -> None:
    p = lambda e: (e - 2) ** 2 * (e + 1)
    x = series([(F(-3), 2), (-1, 7), (0, 3), (F(1, 2), -5), (2, 11), (3, 4)])
    pd = lambda z: diagonal(z, p)
    gp = lambda z: diagonal(z, lambda e: 1 / p(e) if p(e) else F(0))
    nonresonant = series((e, c) for e, c in x.items() if p(e))
    record("polynomial Green identity p(D) G_p = I - P_res", pd(gp(x)) == nonresonant)
    record("polynomial Green identity G_p p(D) = I - P_res", gp(pd(x)) == nonresonant)
    roots = [e for e in x if not p(e)]
    record("multiple polynomial root contributes only one coordinate",
           sorted(roots) == [F(-1), F(2)], kernel_dimension=2, cokernel_dimension=2)
    # The article's explicit resonant solution, checked at 24 coefficients.
    z = series((n, 2 ** n) for n in range(24))
    solution = series((n, F(2 ** n, n - 2)) for n in range(24) if n != 2)
    record("explicit solution (D-2)y = (1-2t)^-1 - 4t^2: finite prefix",
           diagonal(solution, lambda e: e - 2) == add(z, {F(2): F(-4)}),
           prefix_terms=24)
    y = series([(-2, 2), (F(1, 3), 5), (2, -1)])
    d = lambda z: diagonal(z, lambda e: e)
    record("Euler Leibniz identity on exact finite Hahn polynomials",
           d(mul(x, y)) == add(mul(d(x), y), mul(x, d(y))))
    # Coefficient-cokernel decomposition underlying automatic strongness.
    for gamma in list(x) + [F(8, 3)]:
        correction = series((e, c / (e - gamma)) for e, c in x.items() if e != gamma)
        split = add({gamma: x.get(gamma, F(0))},
                    diagonal(correction, lambda e: e - gamma))
        record(f"Euler cokernel decomposition at gamma={gamma}", split == x)


def commutant_checks() -> None:
    eigenvalues = [F(-2), F(-1, 2), F(0), F(2), F(7, 3)]
    n = len(eigenvalues)
    # On the matrix-unit basis E_ij, [D,E_ij]=(lambda_i-lambda_j)E_ij.
    commutator = [[F(0) for _ in range(n * n)] for _ in range(n * n)]
    for i in range(n):
        for j in range(n):
            commutator[n * i + j][n * i + j] = eigenvalues[i] - eigenvalues[j]
    _, pivots = rref(commutator)
    kernel_units = [(i, j) for i in range(n) for j in range(n)
                    if eigenvalues[i] == eigenvalues[j]]
    record("finite Euler commutant consists of diagonal matrix units",
           len(pivots) == n * n - n and kernel_units == [(i, i) for i in range(n)],
           dimension=n, warning="finite analogue, not the proof of the infinite theorem")


def symmetry_checks() -> None:
    x = series([(-2, 3), (0, -7), (1, 4), (3, 5)])
    gamma, delta = F(1), F(4)
    def reweight(z: Series, a: F) -> Series:
        return add(z, {gamma: (a - 1) * z.get(gamma, F(0))})
    for a in [F(1, 2), F(2), F(7)]:
        image = reweight(x, a)
        record(f"positive coordinate reweighting inverse a={a}",
               reweight(image, 1 / a) == x)
        record(f"positive coordinate reweighting preserves leading sign a={a}",
               min(image) == min(x) and image[min(image)] * x[min(x)] > 0)
    def shear(z: Series, a: F) -> Series:
        return add(z, {delta: a * z.get(gamma, F(0))})
    record("higher-coordinate shear has stated inverse", shear(shear(x, F(1)), F(-1)) == x)
    record("higher-coordinate shear preserves leading coefficient",
           shear(x, F(1))[min(x)] == x[min(x)])
    orbit = [[F(1), a] for a in [F(1, 2), F(2), F(7)]]
    record("three distinct projective reweighting lines have rank two",
           len(rref(orbit)[0]) == 2 and
           all(determinant([orbit[i], orbit[j]]) != 0 for i in range(3) for j in range(i)))


def bounded_support_checks() -> None:
    def gamma(n: int) -> F:
        if n < 1:
            raise ValueError("The index must be positive")
        return -(F(1, n) + F(1, n + 1)) / 2
    exponents = [gamma(n) for n in range(1, 201)]
    record("bounded support witness has required reciprocal intervals: finite sample",
           all(-F(1, n) < gamma(n) < -F(1, n + 1) for n in range(1, 201)) and
           all(a < b < 0 for a, b in zip(exponents, exponents[1:])), sample_terms=200)
    columns = [(r, k) for r in [F(1), F(2), F(3)] for k in range(2)]
    for start in [1, 4, 12]:
        matrix = [[gamma(n) ** k * r ** n for r, k in columns]
                  for n in range(start, start + len(columns))]
        value = determinant(matrix)
        record(f"bounded-exponent rational-module witness minor at N={start}",
               value != 0, determinant=str(value),
               warning="finite sample; all-orders independence is proved in the article")
    # D inverse example: D(-sum n*t^(-1/n)) = sum t^(-1/n).
    nterms = 50
    witness = series((-F(1, n), 1) for n in range(1, nterms + 1))
    primitive = series((-F(1, n), -n) for n in range(1, nterms + 1))
    record("bounded-tail Euler inverse identity: finite prefix",
           diagonal(primitive, lambda e: e) == witness, prefix_terms=nterms)


def main() -> None:
    finite_echelon_check()
    vandermonde_checks()
    euler_checks()
    commutant_checks()
    symmetry_checks()
    bounded_support_checks()
    report = {
        "article": "Surreal Numbers as a Real Vector Space",
        "arithmetic": "fractions.Fraction; no floating point",
        "status": "passed",
        "number_of_checks": len(RESULTS),
        "checks": RESULTS,
        "not_verified_by_this_program": [
            "Infinite Hahn support well-ordering and strong summability",
            "Spherical completeness and nonexistence of valuation Hamel bases",
            "Continuum or proper-class dimension and global-choice constructions",
            "Automatic coefficientwise form of arbitrary infinite-dimensional commutants",
            "Infinite rational-module independence and nonsplitting",
            "Historical novelty or completeness of the literature/repository audit",
            "Any Lean, Mizar, or other proof-assistant verification"
        ]
    }
    target = Path(__file__).resolve().parents[1] / "data" / "verification.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(RESULTS)} exact finite checks")
    print(f"Report: {target}")
    print("The infinite mathematical results require the article's proofs.")


if __name__ == "__main__":
    main()
