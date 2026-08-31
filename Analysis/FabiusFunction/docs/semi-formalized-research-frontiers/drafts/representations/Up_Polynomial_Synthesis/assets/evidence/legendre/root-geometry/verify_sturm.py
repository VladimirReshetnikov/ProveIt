"""Verify the deconvolved-Legendre root counts in exact rational arithmetic."""

from __future__ import annotations

from functools import lru_cache
from pathlib import Path

import sympy as sp


X = sp.Symbol("x")
HERE = Path(__file__).resolve().parent


def cumulants(max_degree: int) -> list[sp.Rational]:
    result = [sp.Rational(0)] * (max_degree + 1)
    for n in range(2, max_degree + 1, 2):
        r = n // 2
        result[n] = sp.bernoulli(n) / (
            sp.Rational(n) * (1 - sp.Rational(1, 4) ** r)
        )
    return result


@lru_cache(maxsize=None)
def reciprocal_coefficients(max_degree: int) -> tuple[sp.Rational, ...]:
    kap = cumulants(max_degree)
    gamma = [sp.Rational(0)] * (max_degree + 1)
    gamma[0] = sp.Rational(1)
    for n in range(1, max_degree + 1):
        gamma[n] = sp.simplify(
            -sum(
                sp.binomial(n - 1, r - 1) * kap[r] * gamma[n - r]
                for r in range(1, n + 1)
            )
        )
    return tuple(gamma)


def q_polynomial(n: int) -> sp.Poly:
    gamma = reciprocal_coefficients(n)
    source = sp.legendre(n, X)
    value = sp.expand(
        sum(
            gamma[j] * sp.diff(source, X, j) / sp.factorial(j)
            for j in range(n + 1)
        )
    )
    return sp.Poly(value, X, domain=sp.QQ)


def variations(signs: list[int]) -> int:
    return sum(a * b < 0 for a, b in zip(signs, signs[1:]))


def main() -> None:
    expected_nonreal = {
        1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0, 8: 0, 9: 0,
        10: 0, 11: 0, 12: 4, 13: 4, 14: 4, 15: 8, 16: 8,
        17: 8, 18: 8, 19: 12, 20: 12,
    }
    rows: list[tuple[int, int, int]] = []
    polynomials = {n: q_polynomial(n) for n in range(1, 21)}
    for n, poly in polynomials.items():
        real = int(poly.count_roots(-sp.oo, sp.oo))
        nonreal = n - real
        assert nonreal == expected_nonreal[n], (n, real, nonreal)
        rows.append((n, real, nonreal))

    chain = [sp.Poly(p, X, domain=sp.QQ) for p in sp.sturm(polynomials[12].as_expr(), X)]
    degree_signs = [(p.degree(), int(sp.sign(p.LC()))) for p in chain]
    expected_degree_signs = [
        (12, 1), (11, 1), (10, 1), (9, 1), (8, 1), (7, 1), (6, 1),
        (5, 1), (4, -1), (3, 1), (2, 1), (1, 1), (0, 1),
    ]
    assert degree_signs == expected_degree_signs
    plus = [sign for _, sign in degree_signs]
    minus = [sign if degree % 2 == 0 else -sign for degree, sign in degree_signs]
    assert variations(minus) == 10
    assert variations(plus) == 2

    expected_csv = ["n,exact_real_root_count,exact_nonreal_root_count"]
    expected_csv.extend(",".join(map(str, row)) for row in rows)
    actual_csv = HERE.joinpath("sturm_real_root_counts.csv").read_text(
        encoding="utf-8"
    ).strip().splitlines()
    assert actual_csv == expected_csv

    certificate = HERE.joinpath("Q12_sturm_certificate.txt").read_text(
        encoding="utf-8"
    )
    assert repr(degree_signs) in certificate
    assert "variations=10" in certificate
    assert "variations=2" in certificate
    print("verified exact Sturm counts for Q_1 through Q_20; Q_12 has 8 real roots")


if __name__ == "__main__":
    main()
