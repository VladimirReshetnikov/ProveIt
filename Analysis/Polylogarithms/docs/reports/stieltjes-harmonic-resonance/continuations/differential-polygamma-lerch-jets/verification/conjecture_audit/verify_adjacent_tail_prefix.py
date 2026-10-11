#!/usr/bin/env python3
"""Independent exact checks for the adjacent even-tail prefix theorem.

This script does not import source-package code or perform period recognition.
The all-b theorem is proved in adjacent_tail_prefix.tex. These finite checks
audit its normalization, determinant, and reconstruction formula.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path


def bernoulli_table(n: int) -> list[F]:
    """Bernoulli numbers with B_1=-1/2, from the defining recurrence."""
    values = [F(1)]
    for m in range(1, n + 1):
        values.append(-sum(F(comb(m + 1, k)) * values[k]
                           for k in range(m)) / (m + 1))
    return values


def determinant(matrix: list[list[F]]) -> F:
    a = [[F(x) for x in row] for row in matrix]
    n = len(a)
    result = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        result *= a[j][j]
        for i in range(j + 1, n):
            multiplier = a[i][j] / a[j][j]
            for k in range(j + 1, n):
                a[i][k] -= multiplier * a[j][k]
            a[i][j] = F(0)
    return result


def binomial_term(top: int, lower: int) -> F:
    return F(comb(top, lower), top) if 2 <= lower <= top else F(0)


def source_entry(p: int, q: int, j: int, k: int, bern: list[F]) -> F:
    """Direct transcription of tr:Aentries, including omitted lower zero."""
    d = 2 * j + 1
    e = d - p - q + 2 * k + 1
    if e < 0:
        return F(0)
    return bern[e] * (binomial_term(d - q + 1, p - 2 * k)
                      + binomial_term(d - p + 1, q - 2 * k))


def alpha(n: int, bern: list[F]) -> F:
    return 2 * abs(bern[2 * n]) / factorial(2 * n)


def d(r: int) -> int:
    """Coefficient d_(r+1) in the article."""
    return 4 * (2 * r + 1) ** 2


def w(r: int, s: int, bern: list[F]) -> F:
    return alpha(r + 1 - s, bern) * (
        2 * r * (2 * r + 1) + (2 * s * (2 * s - 1) if s >= 2 else 0))


def rho_table(n: int, bern: list[F]) -> list[F]:
    rho = [F(0), F(1)]
    for r in range(1, n):
        rho.append(sum(w(r, s, bern) * rho[s]
                       for s in range(1, r + 1)) / d(r))
    return rho


def odd_double_factorial(n: int) -> int:
    result = 1
    for k in range(1, n + 1, 2):
        result *= k
    return result


def reconstruct(blocks: list[F], bern: list[F], rho: list[F]) -> list[F]:
    """Recover coordinates v from blocks M v by the explicit recurrence."""
    b = len(blocks)
    ys = [F(0)] + [F(2 * (-1) ** (r - 1), factorial(2 * r - 1))
                    * blocks[r - 1] for r in range(1, b + 1)]
    eta = [F(0), F(0)]
    for r in range(1, b):
        eta.append((ys[r] + sum(w(r, s, bern) * eta[s]
                               for s in range(1, r + 1))) / d(r))
    first = -(ys[b] + sum(w(b, s, bern) * eta[s]
                         for s in range(1, b + 1))) / (d(b) * rho[b + 1])
    rs = [F(0)] + [rho[s] * first + eta[s] for s in range(1, b + 1)]
    return [(-1) ** (b - k) * factorial(2 * b - 2 * k) * rs[b - k]
            for k in range(b)]


def bernoulli_half(n: int, bern: list[F]) -> F:
    return (F(2) ** (1 - n) - 1) * bern[n]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-b', type=int, default=18)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('adjacent_tail_results.json'))
    args = parser.parse_args()
    max_b = args.max_b
    assert max_b >= 6
    bern = bernoulli_table(max(4 * max_b, 32))
    rho = rho_table(max_b + 1, bern)
    checks = 0
    assert bern[:5] == [F(1), -F(1, 2), F(1, 6), F(0), -F(1, 30)]
    checks += 1
    for n in range(1, max_b + 1):
        assert alpha(n, bern) > 0
        assert rho[n + 1] > 0
        checks += 2
    assert rho[1:6] == [F(1), F(1, 36), F(11, 5400),
                        F(113, 705600), F(2509, 190512000)]
    checks += 1
    records = []
    corruption_rejected = False
    for b in range(2, max_b + 1):
        p, q = 2 * b - 2, 2 * b
        matrix = [[source_entry(p, q, b + r - 1, k, bern)
                   for k in range(b)] for r in range(1, b + 1)]
        actual = determinant(matrix)
        expected = ((-1) ** (b * (b - 1) // 2)
                    * F(odd_double_factorial(2 * b + 1) ** 2, factorial(b))
                    * rho[b + 1])
        assert actual == expected != 0
        checks += 1
        # Check every entry in the independent differential/rotation matrix.
        for r in range(1, b + 1):
            for s in range(1, b + 1):
                Hrs = F(d(r)) if s == r + 1 else (-w(r, s, bern) if s <= r else F(0))
                lhs = Hrs * F((-1) ** s, factorial(2 * s))
                rhs = F(2 * (-1) ** (r - 1), factorial(2 * r - 1)) * matrix[r - 1][b - s]
                assert lhs == rhs
                checks += 1
        # Exact reconstruction of every coordinate basis vector.
        if b <= 10:
            for k in range(b):
                recovered = reconstruct([row[k] for row in matrix], bern, rho)
                assert recovered == [F(int(j == k)) for j in range(b)]
                checks += b
        last_block = [F(0)] * (b - 1) + [F(1)]
        lambda_last = reconstruct(last_block, bern, rho)[0]
        top_weight = (4 * b - 1) * lambda_last
        expected_top = F(b * (4 * b - 1), (2 * b + 1) ** 2) * rho[b] / rho[b + 1]
        assert top_weight == expected_top > 0
        checks += 1
        # Independent determinant of the complete first-q moment matrix.
        if b <= 5:
            blocks = [[F(int(r == k)) if k < b else F(0)
                       for k in range(2 * b)] for r in range(b)]
            blocks += [[F(0)] * b + row for row in matrix]
            moment_matrix = []
            for r in range(2 * b):
                moment_matrix.append([
                    sum(F(comb(2 * r, 2 * j), 2 * j + 1)
                        * bernoulli_half(2 * r - 2 * j, bern) * blocks[j][k]
                        for j in range(r + 1)) for k in range(2 * b)])
            assert determinant(moment_matrix) == expected / odd_double_factorial(4 * b - 1)
            checks += 1
        if b == 4:
            corrupt = [row[:] for row in matrix]
            corrupt[0][0] += 1
            corruption_rejected = determinant(corrupt) != expected
            assert corruption_rejected
            checks += 1
        records.append({'p': p, 'q': q, 'late_determinant': str(actual),
                        'rho_b_plus_1': str(rho[b + 1]),
                        'complete_determinant': str(expected / odd_double_factorial(4 * b - 1))})
    # Symbolic cot differentiation is separate from the Bernoulli-entry route.
    import sympy as sp
    x = sp.symbols('x')
    symbolic_checks = 0
    for b in range(2, 7):
        cot = sp.cot(x / 2).series(x, 0, 2 * b + 1).removeO()
        for s in range(1, b + 1):
            R = x ** (2 * s)
            derivative = sp.expand((sp.diff(R, x, 2) - sp.diff(R, x, 2).subs(x, 0))
                                   * cot + sp.diff(R * cot, x, 2))
            for r in range(1, b + 1):
                value = F(d(r)) if s == r + 1 else (-w(r, s, bern) if s <= r else F(0))
                assert derivative.coeff(x, 2 * r - 1) == sp.Rational(value.numerator, value.denominator)
                symbolic_checks += 1
    # The displayed (p,q)=(4,6) rational moment identity and subtraction.
    m46 = sp.Matrix([[sp.Rational(source_entry(4, 6, j, k, bern))
                     for k in range(3)] for j in range(3, 6)])
    inverse46 = sp.Matrix([[-28, 180, 264], [136, 288, -120],
                           [948, -864, 360]]) / 339
    assert m46.inv() == inverse46
    inverse_bernoulli = sp.Matrix([
        [sp.binomial(2 * j + 1, 2 * r) * sp.Rational(1, 2) ** (2 * (j - r))
         if r <= j else 0 for r in range(6)] for j in range(3, 6)])
    weights46 = [67, 15516, 324320, 1434496, 1601280, 371712]
    assert (inverse46 * inverse_bernoulli).row(0) == sp.Matrix([weights46]) / 43392
    polynomial46 = sum(weight * x ** (2 * r) for r, weight in enumerate(weights46))
    asymptotic46 = sp.Rational(1, 15) * x ** -8 - sp.Rational(7, 60) * x ** -10
    product46 = sp.expand(polynomial46 * asymptotic46)
    nonnegative46 = sum(term for term in sp.Add.make_args(product46)
                        if term.as_powers_dict().get(x, 0) >= 0)
    assert nonnegative46 == sp.Rational(123904, 5) * x ** 2 + sp.Rational(316928, 5)
    checks += 3
    # Independent rational-function telescoping certificate for the ordinary sum.
    N, a4, a6 = sp.symbols('N a4 a6')
    K = -3584 * N ** 7 + 23040 * N ** 9 + 33792 * N ** 11
    P4 = 128 * N * (N + 1) * (44 * N ** 4 + 88 * N ** 3 + 67 * N ** 2 + 23 * N - 14)
    P6 = 128 * N ** 3 * (N + 1) ** 3 * (33 * N ** 2 + 33 * N - 14)
    R0 = -sp.Rational(74624, 15) * N ** 3 + 4928 * N ** 2 - sp.Rational(244288, 15) * N
    primitive = K * a4 * a6 + P4 * a4 + P6 * a6 + R0
    previous = primitive.subs({N: N - 1, a4: a4 + N ** -4, a6: a6 + N ** -6}, simultaneous=True)
    target_difference = (polynomial46.subs(x, N - sp.Rational(1, 2))
                         * (a4 + N ** -4) * (a6 + N ** -6)
                         - sp.Rational(123904, 5) * (N - sp.Rational(1, 2)) ** 2
                         - sp.Rational(316928, 5))
    assert sp.cancel(primitive - previous - target_difference) == 0
    expansion4 = N ** -3 / 3 - N ** -4 / 2 + N ** -5 / 3
    expansion6 = N ** -5 / 5 - N ** -6 / 2 + N ** -7 / 2
    expanded_primitive = sp.expand(primitive.subs({a4: expansion4, a6: expansion6}))
    nonnegative_primitive = sum(term for term in sp.Add.make_args(expanded_primitive)
                                if term.as_powers_dict().get(N, 0) >= 0)
    assert nonnegative_primitive == -21696
    assert [sp.expand(expr).coeff(N, 0) for expr in
            (K * expansion4 * expansion6, P4 * expansion4, P6 * expansion6)] == [-20224, -448, -1024]
    checks += 3
    # Optional general-gap factorization; no all-gap nonvanishing claim.
    gap_records = []
    for b in range(2, 9):
        for c in range(1, b):
            def aa(s):
                return F(factorial(2 * s), factorial(2 * s - 2 * c)) if s > c else F(0)
            def bb(s):
                return F(factorial(2 * s - 1), factorial(2 * s - 2 * c - 1))
            def dd(s):
                return 2 * (aa(s) + bb(s))
            fundamental = {s: [F(int(s == j)) for j in range(1, c + 1)]
                           for s in range(1, c + 1)}
            for s in range(c + 1, b + c + 1):
                fundamental[s] = [sum(alpha(s - u, bern) * (bb(s) + aa(u))
                                      * fundamental[u][j] for u in range(1, s)) / dd(s)
                                  for j in range(c)]
            boundary = [fundamental[b + i] for i in range(1, c + 1)]
            boundary_det = determinant(boundary)
            source = [[source_entry(2 * (b - c), 2 * b, b + r - 1, k, bern)
                       for k in range(b)] for r in range(1, b + 1)]
            factor = F((-1) ** (b * (b - 1) // 2), 4 ** b * factorial(b))
            for s in range(c + 1, b + c + 1):
                factor *= dd(s)
            assert determinant(source) == factor * boundary_det
            checks += 1
            gap_records.append({'b': b, 'c': c, 'boundary_determinant': str(boundary_det)})
    selected_signs = {(row['b'], row['c']): F(row['boundary_determinant'])
                      for row in gap_records}
    assert selected_signs[6, 3] < 0 < selected_signs[7, 3]
    checks += 1
    result = {
        'scope': 'Finite exact audit of an all-order proof; no numerical independence claim.',
        'all_order_result': 'Optimal first-q formal rank for p=q-2, every even q>=4.',
        'general_unequal_conjecture_solved': False,
        'rational_assertions': checks,
        'independent_symbolic_derivative_assertions': symbolic_checks,
        'max_b': max_b,
        'corruption_control_rejected': corruption_rejected,
        'records': records,
        'general_gap_factorization_checks': gap_records,
        'versions': {'sympy': sp.__version__},
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('records', 'general_gap_factorization_checks')}, indent=2))
    print(f'Results: {args.output}')


if __name__ == '__main__':
    main()
