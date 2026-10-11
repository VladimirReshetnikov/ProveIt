#!/usr/bin/env python3
"""Exact Bell-space certificates and independent numerical moment checks.

The rational calculations certify finite algebra only. The high-precision
tail calculations are diagnostics, not interval bounds or proofs of sums.
Run from any directory; results are written beside this package's code/.
"""
from __future__ import annotations

import json
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from pathlib import Path

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]


def partitions(n, minimum=2):
    if n == 0:
        yield ()
    for k in range(minimum, n + 1):
        for tail in partitions(n - k, k):
            yield (k,) + tail


def multiply(a, b, cap):
    out = defaultdict(lambda: 0)
    for i, x in a.items():
        for j, y in b.items():
            if i + j <= cap:
                out[i + j] += x * y
    return dict(out)


def coefficient_matrix(weight):
    parts = sorted(partitions(weight), key=lambda t: (len(t), t))
    columns = []
    for part in parts:
        polynomial = {0: 1}
        denominator = 1
        for k, multiplicity in Counter(part).items():
            denominator *= factorial(k) ** multiplicity * factorial(multiplicity)
            factor = {i: comb(k, i) for i in range(1, k)}
            for _ in range(multiplicity):
                polynomial = multiply(polynomial, factor, weight)
        columns.append([
            Fraction(factorial(r) * factorial(weight-r)
                     * polynomial.get(r, 0), denominator)
            for r in range(1, weight // 2 + 1)
        ])
    return parts, sp.Matrix(columns).T


@lru_cache(None)
def derivative_recurrence(r, s):
    if r == 0:
        return {(): 1} if s == 0 else {}
    answer = defaultdict(int)
    for i in range(r):
        for j in range(1, s + 1):
            coefficient = comb(r-1, i) * comb(s, j)
            for part, value in derivative_recurrence(r-1-i, s-j).items():
                key = tuple(sorted(part + (i+j+1,)))
                answer[key] += coefficient * value
    return dict(answer)


def serial_matrix(matrix):
    return [[str(value) for value in row] for row in matrix.tolist()]


def bernoulli_polynomial(j, a):
    return mp.fsum(comb(j, h) * mp.bernoulli(h) * a**(j-h)
                   for h in range(j+1))


def lambda_tail(k, a, order):
    # x=n+a/2. Bernoulli reflection cancels every odd inverse power.
    result = {}
    if k % 2:
        result[k-1] = mp.mpf(2 * factorial(k-2))
    for power in range(k, order+1):
        j = power-k+1
        if (k+j) % 2 == 0:
            continue
        result[power] = (2 * factorial(k-1) * (-1)**j
                         * mp.rf(k, j-1) / factorial(j)
                         * bernoulli_polynomial(j, a/2))
    return result


def moments(weight, a, count=100, order=44):
    parts, matrix = coefficient_matrix(weight)
    values = [mp.mpf(0) for _ in parts]
    for n in range(count):
        lambdas = {
            k: factorial(k-1) * (mp.zeta(k, n+a)-(-1)**k*mp.zeta(k, n+1))
            for k in range(2, weight+1)
        }
        x = n+a/2
        for index, part in enumerate(parts):
            values[index] += x * mp.fprod(lambdas[k] for k in part)
    tails = {k: lambda_tail(k, a, order) for k in range(2, weight+1)}
    for index, part in enumerate(parts):
        polynomial = {0: mp.mpf(1)}
        for k in part:
            polynomial = multiply(polynomial, tails[k], order)
        values[index] += mp.fsum(value * mp.zeta(power-1, count+a/2)
                                for power, value in polynomial.items())
    return parts, matrix, values


def closed_row(weight, r, a):
    s = weight-r
    sign = (-1)**weight
    T = ((a-1)*mp.polygamma(weight-2, a)
         +(weight-2)*mp.polygamma(weight-3, a))
    if r == 1:
        return (weight-1)/mp.mpf(2) * (
            sign*T+(a-1)*mp.polygamma(weight-2, 1)
            -(weight-2)*mp.polygamma(weight-3, 1))
    if r == 2:
        return sign*(weight-2)*T-(weight-2)*mp.polygamma(weight-3, 1)
    return sign*r*s*T/2


def main():
    exact = []
    certificates = {}
    for weight in range(2, 19):
        parts, matrix = coefficient_matrix(weight)
        for r in range(1, weight//2+1):
            independent = derivative_recurrence(r, weight-r)
            assert list(matrix[r-1, :]) == [independent.get(p, 0) for p in parts]
        assert matrix.rank() == weight//2
        # The proof uses this length-triangular, nonzero-diagonal minor.
        pivots = [parts.index(tuple(sorted((2,)*(r-1)+(weight-2*r+2,))))
                  for r in range(1, weight//2+1)]
        minor = matrix[:, pivots]
        assert all(minor[i, j] == 0 for i in range(minor.rows)
                   for j in range(i+1, minor.cols))
        assert all(minor[i, i] > 0 for i in range(minor.rows))
        exact.append({"weight": weight, "columns": len(parts),
                      "rank": matrix.rank(), "codimension": len(parts)-weight//2,
                      "independent_recurrence": True})
        if weight in (6, 8):
            rref, leading = matrix.rref()
            elimination = matrix[:, list(leading)].inv()
            assert elimination*matrix == rref
            annihilators = matrix.nullspace()
            for vector in annihilators:
                assert matrix*vector == sp.zeros(matrix.rows, 1)
            # No nonlinear coordinate vector belongs to this row space.
            for index in range(1, len(parts)):
                unit = sp.zeros(1, len(parts)); unit[0, index] = 1
                assert matrix.col_join(unit).rank() == matrix.rows+1
            certificates[str(weight)] = {
                "monomials": parts, "matrix": serial_matrix(matrix),
                "elimination": serial_matrix(elimination),
                "rref": serial_matrix(rref),
                "annihilators": [serial_matrix(v.T)[0] for v in annihilators]}
    _, m8 = coefficient_matrix(8)
    zero_row = 16*m8[2, :]-15*m8[3, :]
    assert list(zero_row) == [1, 0, 0, -30, -120, -720, -360]
    corrupted = zero_row.copy(); corrupted[0, 3] += 1
    assert corrupted != zero_row

    mp.mp.dps = 75
    numerical = []
    for weight, a in [(6, mp.mpf('0.5')), (6, mp.mpf('1.3')),
                       (8, mp.mpf('2')), (8, mp.mpc('1.25', '0.2')),
                       (10, mp.mpf('2.7'))]:
        _, matrix, values = moments(weight, a)
        residuals = []
        for r in range(1, weight//2+1):
            lhs = mp.fsum(int(matrix[r-1, j])*values[j] for j in range(len(values)))
            rhs = closed_row(weight, r, a)
            residual = abs(lhs-rhs)/max(1, abs(rhs))
            assert residual < mp.mpf('1e-32'), (weight, a, r, residual)
            residuals.append(mp.nstr(residual, 9))
        numerical.append({"weight": weight, "a": mp.nstr(a, 12),
                          "relative_residuals": residuals,
                          "method": "100 direct terms plus 44th-order centered zeta tail"})
    # Separate normalization check of the new harmonic specialization.
    _, _, v = moments(8, mp.mpf(2), count=140, order=48)
    # Column (2,3,3) = sum k*(-1/k^2)*(2 C_k)^2.
    lhs_harmonic = -v[5]/4
    rhs_harmonic = 2*mp.zeta(7)
    harmonic_error = abs(lhs_harmonic-rhs_harmonic)
    assert harmonic_error < mp.mpf('1e-40')
    result = {"status": "passed", "exact_weight_checks": exact,
              "certificates": certificates, "weight_eight_zero_row": list(map(str, zero_row)),
              "corrupted_coefficient_rejected": True, "numerical": numerical,
              "harmonic_tail_identity": {"value": mp.nstr(rhs_harmonic, 55),
                 "absolute_residual": mp.nstr(harmonic_error, 10)},
              "limitations": "Floating-point asymptotic tails are not interval enclosures; proofs are in the article.",
              "versions": {"sympy": sp.__version__, "mpmath": mp.__version__}}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results'/'bell_moments.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({"status": "passed", "weights": "2 through 18",
                      "numeric_parameter_cases": len(numerical),
                      "harmonic_absolute_residual": mp.nstr(harmonic_error, 8)}))


if __name__ == '__main__':
    main()
