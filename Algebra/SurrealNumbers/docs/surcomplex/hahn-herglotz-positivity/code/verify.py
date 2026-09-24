#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

These checks are not proofs of the infinite or transfinite theorems.
Epsilon is a formal symbol; no numerical substitute for an infinitesimal is used.
Run: python verify.py
Requires Python 3.10+ and SymPy (tested with 1.14.0).
"""
from __future__ import annotations

from itertools import product
import platform
import sympy as sp


def require_zero(expr: sp.Expr, description: str) -> None:
    """Raise a useful exception when an exact rational identity fails."""
    reduced = sp.cancel(sp.expand(expr))
    if reduced != 0:
        raise AssertionError(f"{description}: nonzero remainder {reduced}")


def lex_nonnegative(values: tuple[int, ...]) -> bool:
    for value in values:
        if value:
            return value > 0
    return True


def direct_set_positivity(levels: tuple[tuple[int, ...], ...]) -> bool:
    atoms = len(levels[0])
    for mask in range(1 << atoms):
        masses = tuple(
            sum(row[a] for a in range(atoms) if mask & (1 << a))
            for row in levels
        )
        if not lex_nonnegative(masses):
            return False
    return True


def finite_null_ideal_criterion(levels: tuple[tuple[int, ...], ...]) -> bool:
    atoms = len(levels[0])
    for gamma, row in enumerate(levels):
        for mask in range(1 << atoms):
            selected = [a for a in range(atoms) if mask & (1 << a)]
            earlier_variations_vanish = all(
                sum(abs(levels[beta][a]) for a in selected) == 0
                for beta in range(gamma)
            )
            if earlier_variations_vanish:
                if sum(max(-row[a], 0) for a in selected) != 0:
                    return False
    return True


def main() -> None:
    print("EXACT FINITE VERIFICATION REPORT")
    print(f"Python {platform.python_version()}; SymPy {sp.__version__}")
    print("Formal epsilon throughout. No numerical positivity sampling.")
    print()
    e, z, x = sp.symbols("epsilon z x")
    n = sp.symbols("n", integer=True, nonnegative=True)

    for N in range(9):
        size = N + 1
        T = (1 + e) * sp.eye(size) - e * sp.ones(size)
        ones = sp.ones(size, 1)
        assert T * ones == (1 - N * e) * ones
        for j in range(1, size):
            v = sp.zeros(size, 1)
            v[0] = -1
            v[j] = 1
            assert T * v == (1 + e) * v
        require_zero(T.det(method="domain-ge") - (1 + e) ** N * (1 - N * e),
                     f"Toeplitz determinant N={N}")
    print("PASS: Toeplitz determinant and eigenspace identities, N=0,...,8.")

    H = 1 - 2 * e * z / (1 - z)
    require_zero(H.subs(z, 1 - e) - (-1 + 2 * e), "negative-atom boundary value")
    s0 = -e / (1 - (1 + e) * z)
    require_zero((H - 1) / (z * (H + 1)) - s0, "Cayley quotient")
    sn = -e / (1 - n * e - (1 - (n - 1) * e) * z)
    an = -e / (1 - n * e)
    snext = -e / (1 - (n + 1) * e - (1 - n * e) * z)
    require_zero((sn - an) / (z * (1 - an * sn)) - snext,
                 "symbolic Schur recurrence")
    require_zero(sn.subs(z, 0) - an, "Schur parameter")
    print("PASS: Cayley quotient and Schur recursion with symbolic integer n.")
    print("PASS: H_epsilon(1-epsilon) = -1 + 2 epsilon.")

    gf_n2 = z * sp.diff(z * sp.diff(1 / (1 - z), z), z)
    require_zero(gf_n2 - z * (1 + z) / (1 - z) ** 3, "n^2 generating function")
    er = sp.symbols("epsilon_real", real=True)
    boundary = 1 - (1 + sp.I) * er
    H2_boundary = 1 + 2 * er * boundary * (1 + boundary) / (1 - boundary) ** 3
    real_part = sp.simplify(sp.re(sp.expand_complex(H2_boundary)))
    require_zero(real_part - (2 - er ** -2), "n^2 boundary real part")
    require_zero(boundary * sp.conjugate(boundary) - (1 - 2 * er + 2 * er ** 2),
                 "internal disk norm square")
    require_zero(1 - (1 + e / 2) ** 2 - (-e - e ** 2 / 4), "negative T_1")
    print("PASS: n^2 generating function; Re H_2(1-(1+i)e) = 2-e^(-2).")
    print("PASS: internal norm square and halo-positive negative T_1 identity.")

    theta = sp.symbols("theta", real=True)
    for order_half in range(1, 5):
        value = (-1) ** order_half * sp.diff(sp.exp(-sp.I * n * theta),
                                             theta, 2 * order_half).subs(theta, 0)
        require_zero(value - n ** (2 * order_half), "distribution Fourier coefficient")
    print("PASS: Fourier coefficients of (-1)^m delta^(2m), m=1,...,4.")

    for M in range(2, 13):
        w1 = (1 - (M - 1) * e) / M
        wother = (1 + e) / M
        require_zero(w1 + (M - 1) * wother - 1, "quadrature mass")
        assert w1.subs(e, 0) == sp.Rational(1, M)
        assert wother.subs(e, 0) == sp.Rational(1, M)
        cyclotomic = sp.cyclotomic_poly(M, x)
        for k in range(M):
            root_sum = sum(x ** ((j * k) % M) for j in range(M))
            root_sum_value = sp.rem(root_sum, cyclotomic, x)
            expected_sum = M if k == 0 else 0
            require_zero(root_sum_value - expected_sum, "root-of-unity sum")
            moment = (1 + e) * root_sum_value / M - e
            require_zero(moment - (1 if k == 0 else -e), "quadrature moment")
    print("PASS: positive-leading quadrature weights and exact Fourier moments, M=2,...,12.")

    for N in range(9):
        kernel = sp.expand(sum(x ** j for j in range(N + 1))
                           * sum(x ** (-j) for j in range(N + 1)) / (N + 1))
        expected = sum((1 - sp.Rational(abs(k), N + 1)) * x ** k
                       for k in range(-N, N + 1))
        require_zero(kernel - expected, "Fejer kernel identity")
        density = sp.expand(1 + e - e * kernel)
        require_zero(density.coeff(x, 0) - 1, "Fejer density mass")
        for k in range(1, N + 1):
            require_zero(density.coeff(x, k) + e * (1 - sp.Rational(k, N + 1)),
                         "Fejer density Fourier moment")
    print("PASS: Fejer kernel expansion and fixed-Haar density moments, N=0,...,8.")

    checked = positive = 0
    for entries in product((-1, 0, 1), repeat=9):
        levels = tuple(tuple(entries[3 * g:3 * g + 3]) for g in range(3))
        direct = direct_set_positivity(levels)
        criterion = finite_null_ideal_criterion(levels)
        if direct != criterion:
            raise AssertionError(f"Null-ideal mismatch: {levels}")
        checked += 1
        positive += int(direct)
    assert checked == 3 ** 9
    assert positive == 14 ** 3
    print(f"PASS: finite null-ideal equivalence for all {checked:,} three-level, three-atom arrays.")
    print(f"      Exactly {positive:,} arrays are positive on every subset.")
    print()
    print("All implemented checks passed.")
    print("Not checked by this program: arbitrary support, Borel measure uniqueness,")
    print("Hahn summability, analytic minimum principles, transfinite induction,")
    print("or theorem validity at all sizes. See the article's proofs for these.")


if __name__ == "__main__":
    main()
