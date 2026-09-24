#!/usr/bin/env python3
"""Independent, exact checks for the Hankel--Somos-6 research note.

Moments are computed from their quadratic generating equation, and ALL Hankel
values are computed as determinants. The asserted Somos identity is never used
to generate the values that test it. Python 3.10+; standard library only.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import platform
import random
import time
from fractions import Fraction
from pathlib import Path
from typing import Sequence, TypeAlias

Number: TypeAlias = int | Fraction


def determinant(matrix: Sequence[Sequence[Number]]) -> Number:
    """Bareiss elimination, with row pivoting and exact division checks."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("The matrix must be square")
    if n == 0:
        return 1
    if any(not isinstance(value, (int, Fraction)) for row in matrix for value in row):
        raise TypeError("Use integers or Fraction values, not floating-point entries")
    a = [list(row) for row in matrix]
    previous: Number = 1
    sign = 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot_row = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot_row is None:
                return 0
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                if isinstance(numerator, int) and isinstance(previous, int):
                    value, remainder = divmod(numerator, previous)
                    if remainder:
                        raise ArithmeticError("Nonexact Bareiss division")
                    a[i][j] = value
                else:
                    a[i][j] = Fraction(numerator) / previous
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def determinant_leibniz(matrix: Sequence[Sequence[int]]) -> int:
    """Independent reference implementation, used only for very small matrices."""
    n = len(matrix)
    total = 0
    for permutation in itertools.permutations(range(n)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(n) for j in range(i + 1, n))
        term = -1 if inversions % 2 else 1
        for i, j in enumerate(permutation):
            term *= matrix[i][j]
        total += term
    return total


def quadratic_moments(nmax: int, numerator: Sequence[Number],
                      denominator: Sequence[Number],
                      quadratic: Sequence[Number]) -> list[Number]:
    """Coefficients of D(x)F(x)=N(x)+B(x)F(x)^2, with D(0)=N(0)=1.

B must have no constant or linear term, so each new coefficient depends only
on previous coefficients. No numerical approximation is performed.
"""
    if nmax < 0:
        raise ValueError("nmax must be nonnegative")
    if not numerator or not denominator or numerator[0] != 1 or denominator[0] != 1:
        raise ValueError("Both constant terms must be 1")
    if any(not isinstance(value, (int, Fraction))
           for seq in (numerator, denominator, quadratic) for value in seq):
        raise TypeError("Use integers or Fraction values, not floating-point coefficients")
    if any(quadratic[:2]):
        raise ValueError("The quadratic term must be divisible by x^2")
    coefficients: list[Number] = []
    convolutions: list[Number] = []
    for n in range(nmax + 1):
        value = numerator[n] if n < len(numerator) else 0
        for j in range(1, min(n + 1, len(denominator))):
            value -= denominator[j] * coefficients[n - j]
        for j in range(2, min(n + 1, len(quadratic))):
            value += quadratic[j] * convolutions[n - j]
        coefficients.append(value)
        convolutions.append(sum(coefficients[j] * coefficients[n - j]
                                for j in range(n + 1)))
    return coefficients


def tree_moments(r: int, s: int, t: int, nmax: int) -> list[int]:
    """Independent expansion of G=1+W(x)G+t*x^3*G^2 from the tree grammar."""
    g = [1]
    for n in range(1,nmax+1):
        value = 0
        for length in range(1,n+1):
            colors = 1 if length == 1 else r+2 if length == 2 else r+s+2
            value += colors*g[n-length]
        if n >= 3:
            value += t*sum(g[j]*g[n-3-j] for j in range(n-2))
        g.append(value)
    return g


def family(u: Number, R: Number, B: Number, t: Number,
           nmax: int) -> tuple[list[Number], Number, Number]:
    """The four-parameter family, with R=b+u^2 and B=c+t."""
    moments = quadratic_moments(
        nmax, [1, -u], [1, -2*u, u*u-R, t-B], [0, 0, 0, t, -u*t])
    alpha = t*t*R*R
    gamma = t**3 * (B*(B+u*R)**2 + t*R**3)
    return moments, alpha, gamma


def universal(a: Number, b: Number, c: Number, p: Number, k: Number,
              lam: Number, mu: Number, nmax: int
              ) -> tuple[list[Number], Number, Number]:
    """The polynomial seven-parameter deformation used in the proof."""
    ell1 = a*p+k-lam*p
    ell0 = a*k-a*lam*p+b*p-k*lam+lam*lam*p-mu*p+p*p
    v = ell1*mu+ell0*lam-c*p-b*k-2*p*k
    m = ell0*mu-c*k-k*k
    moments = quadratic_moments(
        nmax, [1, lam, mu], [1, a, b+2*p, c+2*k],
        [0, 0, p, ell1, ell0])
    return moments, v*v, m**3-a*v*m*m+b*v*v*m-c*v**3


def hankels(moments: Sequence[Number], nmax: int) -> list[Number]:
    if nmax < 0 or (nmax and len(moments) < 2*nmax-1):
        raise ValueError("Insufficient moments or invalid size")
    return [determinant([[moments[i+j] for j in range(n)] for i in range(n)])
            for n in range(nmax+1)]


def check_case(moments: Sequence[Number], alpha: Number, gamma: Number,
               nmax: int, label: object) -> tuple[list[Number], int]:
    h = hankels(moments, nmax)
    for n in range(6, nmax+1):
        residual = h[n]*h[n-6]-alpha*h[n-1]*h[n-5]-gamma*h[n-3]**2
        if residual != 0:
            raise AssertionError(f"Nonzero residual: {label=}, {n=}, {residual=}")
    return h, max(0, nmax-5)


def run_suite(output: Path, quick: bool = False) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    rng = random.Random(20260919)
    determinant_checks = 0
    for n in range(7):
        for _ in range(12):
            matrix = [[rng.randint(-2, 2) for _ in range(n)] for _ in range(n)]
            if determinant(matrix) != determinant_leibniz(matrix):
                raise AssertionError("The determinant implementations disagree")
            determinant_checks += 1

    records: list[dict] = []
    residuals = 0
    zero_cases = 0
    zero_determinants = 0
    maxsize = 10 if quick else 14
    original_range = range(-1, 2) if quick else range(-3, 4)
    general_range = range(-1, 2) if quick else range(-2, 3)

    def save_case(group: str, pars: Sequence[Number], values: tuple,
                  size: int) -> None:
        nonlocal residuals, zero_cases, zero_determinants
        moments, alpha, gamma = values
        h, checks = check_case(moments, alpha, gamma, size, (group, pars))
        residuals += checks
        zeros = [n for n in range(2, len(h)) if h[n] == 0]
        zero_determinants += len(zeros)
        zero_cases += bool(zeros)
        records.append({"group": group, "parameters": [str(x) for x in pars],
                        "max_size": size, "checks": checks,
                        "zero_indices": zeros, "alpha": str(alpha),
                        "gamma": str(gamma), "last_hankel": str(h[-1])})

    for r, s, t in itertools.product(original_range, repeat=3):
        values = family(1,r+2,s+t,t,2*maxsize-2)
        if values[0] != tree_moments(r,s,t,2*maxsize-2):
            raise AssertionError("Independent moment recurrences disagree")
        save_case("Barry", (r,s,t), values, maxsize)
    for pars in itertools.product(general_range, repeat=4):
        save_case("four_parameter", pars, family(*pars,2*maxsize-2), maxsize)
    for _ in range(16 if quick else 128):
        pars = tuple(rng.randint(-4,4) for _ in range(7))
        save_case("universal", pars, universal(*pars,2*maxsize-2), maxsize)
    for _ in range(4 if quick else 16):
        pars = tuple(rng.randint(-3,3) for _ in range(7))
        size = 14 if quick else 24
        save_case("stress", pars, universal(*pars,2*size-2), size)
    for _ in range(4 if quick else 16):
        pars = tuple(Fraction(rng.randint(-3,3),rng.randint(1,3)) for _ in range(4))
        save_case("rational", pars, family(*pars,18), 10)

    # The all-nonsingular specialization in the proof.
    moments, _, _ = universal(0,-3,0,1,0,0,-1,46)
    catalan_h = hankels(moments,24)
    if catalan_h != [1]*25:
        raise AssertionError("Catalan specialization failed")

    examples = {}
    for r,s,t in [(0,0,1),(1,1,1),(-3,-2,1),(-2,-2,1),(2,2,2)]:
        moments, alpha, gamma = family(1,r+2,s+t,t,38)
        h, _ = check_case(moments,alpha,gamma,20,(r,s,t))
        key = f"r={r},s={s},t={t}"
        examples[key] = {"moments": moments,"hankels":h,"alpha":alpha,"gamma":gamma}
        path = output / f"example_r{r}_s{s}_t{t}.csv"
        with path.open("w", newline="", encoding="utf-8") as stream:
            writer = csv.writer(stream)
            writer.writerow(["n","g_n","H_n (n by n, H_0=1)"])
            for n,g in enumerate(moments):
                writer.writerow([n,g,h[n] if n < len(h) else ""])

    summary = {
        "status":"PASS", "seed":20260919, "python":platform.python_version(),
        "mode":"quick" if quick else "full",
        "determinant_cross_checks":determinant_checks,
        "original_moment_cross_checks":len(original_range)**3,
        "parameter_cases":len(records), "recurrence_residuals":residuals,
        "groups":{group:sum(rec["group"]==group for rec in records)
                  for group in ["Barry","four_parameter","universal","stress","rational"]},
        "cases_with_zero_hankels":zero_cases,
        "zero_hankels_in_test_cases":zero_determinants,
        "catalan_hankels_checked":len(catalan_h),
        "max_hankel_size_in_suite":max(rec["max_size"] for rec in records),
        "additional_examples":len(examples),
        "example_recurrence_residuals":len(examples)*15,
        "elapsed_seconds":round(time.perf_counter()-started,3),
        "method":"Every H_n evaluated independently by exact determinant elimination",
        "interpretation":"Finite checks support, but do not replace, the proof."
    }
    (output/"verification_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    (output/"verification_cases.json").write_text(json.dumps(records,indent=2)+"\n")
    (output/"examples.json").write_text(json.dumps(examples,indent=2)+"\n")
    print(json.dumps(summary,indent=2))
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    output = args.output or (Path(__file__).resolve().parents[1]/"data")
    if args.quick and args.output is None:
        output = output/"quick_run"
    run_suite(output,args.quick)


if __name__ == "__main__":
    main()
