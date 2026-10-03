#!/usr/bin/env python3
"""Exact symbolic checks for the Conjecture 17 proof package.

The verifier uses only exact SymPy polynomial/rational arithmetic.  It checks
finite ranges; the all-index result rests on the proofs in article.tex.
"""
from __future__ import annotations

import argparse
import json
import platform
import time
from fractions import Fraction
from itertools import combinations
from math import comb, factorial, prod
from pathlib import Path

import sympy as sp

T = sp.symbols("t")
N = sp.symbols("n", integer=True, nonnegative=True)


def beta(m: int, r: int) -> sp.Rational:
    if not (0 <= r <= m):
        raise ValueError((m, r))
    num = prod(factorial(j) for j in range(r))
    den = prod(factorial(j) for j in range(m - r, m))
    return sp.Rational(num, den)


def collision_sign(k: int) -> int:
    """Correct reciprocity sign epsilon_k."""
    a = k // 2
    b = (k - 1) // 2
    return -1 if (k - 1 + a + a * b) % 2 else 1


def denominator_D(k: int) -> sp.Expr:
    a = k // 2
    b = (k - 1) // 2
    return (1 - T) ** a * (1 - T**2) ** (a * b)


def confluent_group_numerators(k: int, n: int) -> list[sp.Expr]:
    """Grouped Laplace numerators N_{k,q}(n,t) in the confluent bialternant."""
    if k < 1 or n < 0:
        raise ValueError((k, n))
    a = k // 2
    b = (k - 1) // 2
    if a == 0:
        return [sp.Integer(1)]
    K = k
    A = a
    C = b + 1

    # Rows are normalized x-derivatives at 1, t, t^2.
    rows: list[tuple[int, int, int]] = []
    for cluster, (multiplicity, weight) in enumerate(((a, 0), (1, 1), (b, 2))):
        for derivative_order in range(multiplicity):
            rows.append((cluster, derivative_order, weight))

    exponents = list(range(C)) + list(range(n + C, n + K))
    matrix = sp.zeros(K, K)
    for i, (_cluster, h, weight) in enumerate(rows):
        for j, exponent in enumerate(exponents):
            matrix[i, j] = (
                sp.binomial(exponent, h) * T ** (weight * (exponent - h))
                if exponent >= h
                else 0
            )

    high_columns = list(range(C, K))
    low_columns = list(range(C))
    high_column_sum = sum(j + 1 for j in high_columns)
    grouped = [sp.Integer(0) for _ in range(k)]

    for chosen_tuple in combinations(range(K), A):
        chosen = list(chosen_tuple)
        chosen_set = set(chosen)
        complement = [i for i in range(K) if i not in chosen_set]
        r2 = sum(rows[i][0] == 1 for i in chosen)
        r3 = sum(rows[i][0] == 2 for i in chosen)
        q = r2 + 2 * r3
        laplace_sign = (-1) ** (sum(i + 1 for i in chosen) + high_column_sum)
        high_minor = matrix.extract(chosen, high_columns).det(method="domain-ge")
        low_minor = matrix.extract(complement, low_columns).det(method="domain-ge")
        grouped[q] += laplace_sign * high_minor * low_minor

    return [sp.expand(value) for value in grouped]


def c_values_at_n(k: int, n: int) -> list[sp.Expr]:
    """Compute c_{k,q}(n,t) from the grouped confluent determinants."""
    if k == 1:
        return [sp.Integer(1)]
    a = k // 2
    b = (k - 1) // 2
    grouped = confluent_group_numerators(k, n)
    values: list[sp.Expr] = []
    for q, numerator in enumerate(grouped):
        Bq = q * (q + 1) // 2
        exponent = q * n + Bq + b
        quotient = sp.cancel(numerator / (T**exponent * (T - 1) ** b))
        value = sp.cancel((-1) ** (q + a + a * b) * quotient)
        if sp.denom(value) != 1:
            raise AssertionError(f"non-polynomial c for k={k}, q={q}, n={n}: {value}")
        values.append(sp.Poly(sp.expand(value), T).as_expr())
    return values


def interpolate_c_family(k: int) -> list[sp.Expr]:
    """Recover each c_{k,q}(n,t) from d_q+1 exact integer-width values."""
    dmax = max((q * (k - 1 - q)) // 2 for q in range(k))
    table = [c_values_at_n(k, n) for n in range(dmax + 1)]
    result: list[sp.Expr] = []
    for q in range(k):
        dq = (q * (k - 1 - q)) // 2
        polynomial = sp.interpolate([(n, table[n][q]) for n in range(dq + 1)], N)
        result.append(sp.expand(polynomial))
    return result


def complete_homogeneous(alphabet: list[sp.Expr], maximum: int) -> list[sp.Expr]:
    h = [sp.Integer(1)] + [sp.Integer(0)] * maximum
    for x in alphabet:
        for j in range(1, maximum + 1):
            h[j] = sp.expand(h[j] + x * h[j - 1])
    return h


def schur_rectangle(k: int, n: int) -> sp.Expr:
    a = k // 2
    b = (k - 1) // 2
    if a == 0:
        return sp.Integer(1)
    alphabet = [sp.Integer(1)] * a + [T] + [T**2] * b
    h = complete_homogeneous(alphabet, n + a)
    matrix = [
        [h[n - i + j] if n - i + j >= 0 else sp.Integer(0) for j in range(a)]
        for i in range(a)
    ]
    return sp.Poly(sp.Matrix(matrix).det(method="domain-ge"), T).as_expr()


def source_moment(r: int) -> sp.Expr:
    if r == 0:
        return sp.Integer(1)
    return sp.expand(
        sum(
            comb((r - 1) // 2, (j - 1) // 2)
            * comb(r // 2, j // 2)
            * T ** (j - 1)
            for j in range(1, r + 1)
        )
    )


def source_hankel(k: int, n: int) -> sp.Expr:
    if n == 0:
        return sp.Integer(1)
    moments = [source_moment(r) for r in range(k + 2 * n - 1)]
    matrix = [[moments[k + i + j] for j in range(n)] for i in range(n)]
    return sp.Poly(sp.Matrix(matrix).det(method="domain-ge"), T).as_expr()


def assert_zero(expr: sp.Expr, context: str) -> None:
    if sp.cancel(expr) != 0:
        raise AssertionError(f"{context}: {sp.factor(expr)}")


def run(output: Path) -> dict:
    started = time.monotonic()
    record: dict = {
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "arithmetic": "exact symbolic polynomial/rational arithmetic",
        "scope": "finite verification only; all-index claims depend on article proofs",
        "checks": {},
    }

    families: dict[int, list[sp.Expr]] = {}
    polynomial_cases = 0
    interpolation_cases = 0
    reciprocity_cases = 0
    leading_cases = 0
    reconstruction_cases = 0
    integrality_cases = 0

    for k in range(1, 9):
        family = interpolate_c_family(k)
        families[k] = family
        eps = collision_sign(k)

        for q, cq in enumerate(family):
            rq = q * (k - 1 - q)
            dq = rq // 2
            poly_n = sp.Poly(cq, N)
            poly_t = sp.Poly(cq, T)
            if poly_n.degree() != dq:
                raise AssertionError(("n-degree", k, q, poly_n.degree(), dq))
            if poly_t.degree() != rq:
                raise AssertionError(("t-degree", k, q, poly_t.degree(), rq))
            polynomial_cases += 1
            interpolation_cases += dq + 1

            paired = family[k - 1 - q]
            assert_zero(
                paired - eps * T**rq * cq.subs(T, 1 / T),
                f"reciprocity k={k}, q={q}",
            )
            reciprocity_cases += 1

            h = q // 2
            if q % 2 == 0:
                predicted = (
                    beta(k // 2, k // 2 - h)
                    * beta((k - 1) // 2, h)
                    * (1 - T**2) ** dq
                )
            else:
                predicted = (
                    (-1) ** h
                    * beta(k // 2, k // 2 - h - 1)
                    * beta((k - 1) // 2, h)
                    * (1 + T if k % 2 else 1)
                    * (1 - T**2) ** dq
                )
            assert_zero(poly_n.LC() - predicted, f"leading coefficient k={k}, q={q}")
            leading_cases += 1

        # Check widths used for interpolation and two fresh widths.
        dmax = max((q * (k - 1 - q)) // 2 for q in range(k))
        widths = list(range(dmax + 1)) + [dmax + 1, dmax + 3]
        Dk = denominator_D(k)
        for n in widths:
            direct = c_values_at_n(k, n)
            for q in range(k):
                assert_zero(direct[q] - family[q].subs(N, n), f"interpolation k={k},q={q},n={n}")
                coeffs = sp.Poly(direct[q], T).all_coeffs()
                if any(not coefficient.is_Integer for coefficient in coeffs):
                    raise AssertionError(("integrality", k, q, n, coeffs))
                integrality_cases += 1

            numerator = sum(
                (-1) ** q
                * family[q].subs(N, n)
                * T ** (q * n + q * (q + 1) // 2)
                for q in range(k)
            )
            assert_zero(Dk * schur_rectangle(k, n) - numerator, f"Schur reconstruction k={k},n={n}")
            reconstruction_cases += 1

    # Independent bridge to the original Hankel determinant for manageable sizes.
    hankel_cases = 0
    for k in range(1, 7):
        for n in range(0, 6):
            C = n * (n - 1) // 2
            expected = (-1) ** (k * C) * T**C * schur_rectangle(k, n)
            assert_zero(source_hankel(k, n) - expected, f"source Hankel bridge k={k},n={n}")
            hankel_cases += 1

    # The sign printed in Cigler's equation (83) fails already at k=5,q=2.
    c52 = families[5][2]
    corrected_residual = sp.cancel(c52 - T**4 * c52.subs(T, 1 / T))
    printed_residual = sp.cancel(c52 + T**4 * c52.subs(T, 1 / T))
    assert_zero(corrected_residual, "corrected k=5 central reciprocity")
    if printed_residual == 0:
        raise AssertionError("printed sign unexpectedly passed at k=5,q=2")

    record["checks"] = {
        "polynomial_bidegrees": {"cases": polynomial_cases, "k": [1, 8]},
        "interpolation_input_values": {"cases": interpolation_cases},
        "corrected_reciprocity": {"cases": reciprocity_cases, "k": [1, 8]},
        "explicit_n_leading_coefficients": {"cases": leading_cases, "k": [1, 8]},
        "fresh_width_reconstruction": {"cases": reconstruction_cases, "k": [1, 8]},
        "integer_t_coefficients_at_integer_widths": {"cases": integrality_cases},
        "original_hankel_to_schur_bridge": {"cases": hankel_cases, "k": [1, 6], "n": [0, 5]},
        "printed_sign_counterexample": {
            "k": 5,
            "q": 2,
            "printed_residual_nonzero": str(sp.factor(printed_residual)),
            "corrected_residual": "0",
        },
    }

    record["sample_polynomials"] = {
        "c_4_1": str(sp.factor(families[4][1])),
        "c_4_2": str(sp.factor(families[4][2])),
        "c_5_1": str(sp.factor(families[5][1])),
        "c_5_2": str(sp.factor(families[5][2])),
        "c_5_3": str(sp.factor(families[5][3])),
        "c_6_2": str(sp.factor(families[6][2])),
    }
    record["elapsed_seconds"] = round(time.monotonic() - started, 3)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("data/verification.json"))
    args = parser.parse_args()
    record = run(args.output)
    print(json.dumps(record["checks"], indent=2, sort_keys=True))
    print(f"elapsed_seconds={record['elapsed_seconds']}")


if __name__ == "__main__":
    main()
