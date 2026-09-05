#!/usr/bin/env python3
"""Exact experiments for repeated signed Thue--Morse summation.

This companion program validates the formulas proved in
``thue_morse_diagonal_polynomials.tex`` and generates the figure used there.
All arithmetic used for identities is exact (Python integers and SymPy
rationals).  Floating-point numbers are used only when plotting normalized
profiles.

Mathematical notation used by the script
----------------------------------------

* epsilon(q) = (-1)^(binary digit sum of q), the signed Thue--Morse sequence.
* E(z) = sum epsilon(q) z^q = product_{j>=0} (1-z^(2^j)).
* s(n,k) is the table in the prompt, with n,k >= 0.
* r = k-n-1 is the diagonal offset from the first nonzero diagonal.
* D_r(x) is the polynomial satisfying s(n,n+1+r) = D_r(n):

      D_r(x) = sum_{q=0}^{floor(r/2)} epsilon(q)
               * binomial(2*x+r-2*q-1, r-2*q).

The row profile in one dyadic block of length L=2^(2*n+1) is the coefficient
list of

      B_n(z) = z^(n+1) product_{j=1}^{2*n} (1+z+...+z^(2^j-1)).

The full row is obtained by multiplying consecutive blocks by epsilon(q).

Run this file directly.  It will:
  1. verify the diagonal formula against the original weighted recurrence;
  2. verify the ruler-function recurrence for D_r;
  3. verify all stated block, symmetry, complement, plateau, sum, and
     distinct-value laws for several rows;
  4. mirror the Wolfram Language ``sFast`` decision tree and compare it with
     exact signed blocks over several complete periods;
  5. verify the exact criterion for nonnegative half-integer roots;
  6. generate ``row_profiles.pdf`` and ``row_profiles.png``;
  7. write a human-readable ``verification_report.txt``.

Dependencies: Python 3.10+, SymPy, and Matplotlib.
"""

from __future__ import annotations

from collections import Counter
from functools import lru_cache
from pathlib import Path
from math import comb
from typing import Iterable, List, Sequence

import matplotlib.pyplot as plt
import sympy as sp


HERE = Path(__file__).resolve().parent
X = sp.symbols("x")


def tm_sign(q: int) -> int:
    """Return epsilon_q = (-1)^(number of 1-bits of q), for q >= 0."""

    if q < 0:
        raise ValueError("tm_sign is defined only for nonnegative integers")
    return -1 if q.bit_count() % 2 else 1


def tm_sign_extended(q: int) -> int:
    """Return epsilon_q for q >= 0 and 0 for q < 0.

    The zero extension is convenient in finite-difference formulas such as
    D_r(-a/2) = sum_j (-1)^j binomial(a-1,j) epsilon_{r-j}.
    """

    return 0 if q < 0 else tm_sign(q)


@lru_cache(maxsize=None)
def diagonal_polynomial(r: int) -> sp.Expr:
    """Return the exact polynomial D_r(x) in expanded form.

    We use rising factorials rather than asking SymPy to infer polynomiality
    from generalized binomial coefficients:

        binomial(2*x+m-1,m) = rising_factorial(2*x,m)/m!.
    """

    if r < 0:
        return sp.Integer(0)
    terms = []
    for q in range(r // 2 + 1):
        m = r - 2 * q
        terms.append(
            tm_sign(q) * sp.rf(2 * X, m) / sp.factorial(m)
        )
    return sp.expand(sum(terms, sp.Integer(0)))


def diagonal_polynomials_by_ruler(max_r: int, x: sp.Expr = X) -> List[sp.Expr]:
    """Construct D_0,...,D_max_r by the ruler-function recurrence.

    If nu_2(m) denotes the exponent of 2 in m, then

        r D_r(x) = sum_{m=1}^r (2*x+2-2^(nu_2(m)+1)) D_{r-m}(x).
    """

    if max_r < 0:
        return []
    ds = [sp.Integer(1)]
    for r in range(1, max_r + 1):
        total = sp.Integer(0)
        for m in range(1, r + 1):
            nu2 = (m & -m).bit_length() - 1
            c_m = 2 * x + 2 - 2 ** (nu2 + 1)
            total += c_m * ds[r - m]
        ds.append(sp.expand(total / r))
    return ds


def diagonal_value(r: int, n: int) -> int:
    """Evaluate D_r(n) with integers only, without constructing a polynomial."""

    if r < 0:
        return 0
    if n < 0:
        raise ValueError("n must be nonnegative")
    total = 0
    for q in range(r // 2 + 1):
        m = r - 2 * q
        if m == 0:
            binomial_value = 1
        elif n == 0:
            binomial_value = 0
        else:
            # binomial(2*n+m-1,m)
            binomial_value = comb(2 * n + m - 1, m)
        total += tm_sign(q) * binomial_value
    return total


def iterated_prefix_value(h: int, r: int) -> int:
    """Return the h-fold inclusive prefix S_r^(h) exactly.

    The convolution formula is

        S_r^(h) = sum_{j=0}^r binomial(r-j+h-1,h-1) epsilon_j,  h >= 1.

    At h=0 the value is epsilon_r.
    """

    if h < 0 or r < 0:
        raise ValueError("h and r must be nonnegative")
    if h == 0:
        return tm_sign(r)
    return sum(
        comb(r - j + h - 1, h - 1) * tm_sign(j)
        for j in range(r + 1)
    )


def exclusive_prefix_value(k: int) -> int:
    """Return sum_{j=0}^{k-1} epsilon_j, the n=0 row."""

    if k < 0:
        raise ValueError("k must be nonnegative")
    return sum(tm_sign(j) for j in range(k))


def recurrence_table(max_n: int, max_k: int) -> List[List[int]]:
    """Build the table from the weighted recurrence in O(max_n*max_k).

    The direct recurrence is

        s(n,k) = sum_{j=0}^{k-1} (k-j) s(n-1,j).

    Prefix sums of s(n-1,j) and j*s(n-1,j) turn each inner sum into O(1):

        s(n,k) = k*sum_{j<k}s(n-1,j) - sum_{j<k}j*s(n-1,j).
    """

    if max_n < 0 or max_k < 0:
        raise ValueError("bounds must be nonnegative")

    rows: List[List[int]] = [
        [exclusive_prefix_value(k) for k in range(max_k + 1)]
    ]
    for n in range(1, max_n + 1):
        previous = rows[-1]
        prefix = [0] * (max_k + 2)
        weighted_prefix = [0] * (max_k + 2)
        for j, value in enumerate(previous):
            prefix[j + 1] = prefix[j] + value
            weighted_prefix[j + 1] = weighted_prefix[j] + j * value
        row = [0] * (max_k + 1)
        for k in range(max_k + 1):
            row[k] = k * prefix[k] - weighted_prefix[k]
        rows.append(row)
    return rows


def convolve_with_ones(coefficients: Sequence[int], width: int) -> List[int]:
    """Convolve an integer sequence with ``width`` consecutive ones.

    A sliding window makes this linear in the output length rather than
    quadratic.  This is the exact coefficient update for multiplication by
    1+z+...+z^(width-1).
    """

    if width <= 0:
        raise ValueError("width must be positive")
    output_length = len(coefficients) + width - 1
    output = [0] * output_length
    running = 0
    for i in range(output_length):
        if i < len(coefficients):
            running += coefficients[i]
        if i - width >= 0 and i - width < len(coefficients):
            running -= coefficients[i - width]
        output[i] = running
    return output


@lru_cache(maxsize=None)
def iterated_prefix_block(h: int) -> tuple[int, ...]:
    """Return one length-2^h coefficient block for the h-fold prefix."""

    if h < 1:
        raise ValueError("h must be at least 1")
    length = 2**h
    coefficients: List[int] = [1]
    for j in range(h):
        coefficients = convolve_with_ones(coefficients, 2**j)
    return tuple(coefficients + [0] * (length - len(coefficients)))


def verify_general_iterated_prefix_blocks(max_h: int = 8) -> None:
    """Verify the finite-block theorem for every summation order h tested."""

    for h in range(1, max_h + 1):
        block = iterated_prefix_block(h)
        length = 2**h
        degree = length - h - 1
        maximum = 2 ** ((h - 1) * (h - 2) // 2)
        plateau = list(range(length // 2 - h, length // 2))

        assert all(block[a] > 0 for a in range(degree + 1)), h
        assert all(block[a] == 0 for a in range(degree + 1, length)), h
        assert all(block[a] == block[degree - a] for a in range(degree + 1)), h
        assert [a for a, value in enumerate(block) if value == maximum] == plateau, h
        assert sum(block) == 2 ** (h * (h - 1) // 2), h

        counts = Counter(block)
        assert counts[0] == h, h
        assert counts[maximum] == h, h
        assert all(count == 2 for value, count in counts.items() if value not in (0, maximum)), h
        assert len(counts) == 2 ** (h - 1) - h + 2, h

        d = length // 2 - h
        for a in range(d):
            assert block[a] + block[d - 1 - a] == maximum, (h, a)

        # Check several signed blocks against the direct convolution formula.
        for q in range(4):
            for a in range(length):
                r = q * length + a
                assert iterated_prefix_value(h, r) == tm_sign(q) * block[a], (h, q, a)


@lru_cache(maxsize=None)
def row_block(n: int) -> tuple[int, ...]:
    """Return the nonnegative profile b_{n,a}, 0 <= a < 2^(2*n+1)."""

    if n < 0:
        raise ValueError("n must be nonnegative")
    length = 2 ** (2 * n + 1)
    coefficients: List[int] = [1]
    for j in range(1, 2 * n + 1):
        coefficients = convolve_with_ones(coefficients, 2**j)
    shifted = [0] * (n + 1) + coefficients
    if len(shifted) > length:
        raise AssertionError("derived profile has unexpectedly large degree")
    return tuple(shifted + [0] * (length - len(shifted)))


def table_value_by_block(n: int, k: int) -> int:
    """Return s(n,k) from the exact signed-block factorization."""

    if n < 0 or k < 0:
        raise ValueError("n and k must be nonnegative")
    length = 2 ** (2 * n + 1)
    block_index, residue = divmod(k, length)
    return tm_sign(block_index) * row_block(n)[residue]


@lru_cache(maxsize=None)
def row_core_fast(n: int, residue: int) -> int:
    """Evaluate one residue of the first row block by symmetry reduction.

    This is a literal Python analogue of ``rowCoreValue`` in the companion
    Wolfram Language file.  The order of the cases is important: terminal
    zeros and the central plateau are fixed before reflection or complement
    can map a residue to itself.  Every remaining residue is reduced to the
    first quarter and then evaluated by the exact diagonal sum.
    """

    if n < 0 or residue < 0:
        raise ValueError("n and residue must be nonnegative")

    length = 2 ** (2 * n + 1)
    maximum = 2 ** (n * (2 * n - 1))
    residue %= length

    if residue <= n or residue >= length - n:
        return 0
    if length // 2 - n <= residue <= length // 2 + n:
        return maximum
    if residue > length // 2:
        return row_core_fast(n, length - residue)
    if n >= 1 and residue == length // 4:
        return maximum // 2
    if n >= 1 and residue > length // 4:
        return maximum - row_core_fast(n, length // 2 - residue)

    # Here residue is in the first quarter and strictly after the initial
    # zero run.  Its diagonal offset is r=residue-n-1.
    return diagonal_value(residue - n - 1, n)


def table_value_fast(n: int, k: int) -> int:
    """Return s(n,k) by the same hybrid strategy used by WL ``sFast``."""

    if n < 0 or k < 0:
        raise ValueError("n and k must be nonnegative")
    length = 2 ** (2 * n + 1)
    block_index, residue = divmod(k, length)
    return tm_sign(block_index) * row_core_fast(n, residue)


def verify_hybrid_evaluator(max_n: int = 5, block_count: int = 3) -> None:
    """Compare the hybrid evaluator with exact blocks over whole periods."""

    for n in range(max_n + 1):
        length = 2 ** (2 * n + 1)
        block = row_block(n)

        # First verify every residue of the positive block.
        for residue, expected in enumerate(block):
            assert row_core_fast(n, residue) == expected, (
                n,
                residue,
                row_core_fast(n, residue),
                expected,
            )

        # Then verify the signed repetition over several whole blocks.
        for k in range(block_count * length):
            block_index, residue = divmod(k, length)
            expected = tm_sign(block_index) * block[residue]
            assert table_value_fast(n, k) == expected, (
                n,
                k,
                table_value_fast(n, k),
                expected,
            )


def nonnegative_half_root_condition(r: int, m: int) -> bool:
    """Test whether D_r(m/2)=0 by the exact residue criterion.

    Put h=m+1 and L=2^h.  The value vanishes exactly when the residue of r
    lies in the terminal h positions of a block:

        r mod L in {L-h, ..., L-1}.
    """

    if r < 0 or m < 0:
        raise ValueError("r and m must be nonnegative")
    h = m + 1
    length = 2**h
    return r % length >= length - h


def generalized_binomial_polynomial_value(r: int, x_value: sp.Rational) -> int:
    """Evaluate D_r at a half-integer exactly and return a Python integer."""

    value = sp.simplify(diagonal_polynomial(r).subs(X, x_value))
    if not value.is_Integer:
        raise AssertionError(f"expected an integer, obtained {value}")
    return int(value)


def verify_diagonal_formula(max_n: int = 6, max_k: int = 180) -> None:
    """Compare D_{k-n-1}(n) with the original recurrence table."""

    table = recurrence_table(max_n, max_k)
    for n in range(max_n + 1):
        for k in range(max_k + 1):
            predicted = 0 if k <= n else diagonal_value(k - n - 1, n)
            assert table[n][k] == predicted, (n, k, table[n][k], predicted)
            assert table[n][k] == table_value_by_block(n, k), (
                n,
                k,
                table[n][k],
                table_value_by_block(n, k),
            )


def verify_ruler_recurrence(max_r: int = 30) -> None:
    """Compare direct and ruler-recurrence constructions of D_r."""

    via_ruler = diagonal_polynomials_by_ruler(max_r)
    for r in range(max_r + 1):
        assert sp.expand(via_ruler[r] - diagonal_polynomial(r)) == 0, r


def verify_half_step_and_derivative(max_r: int = 20) -> None:
    """Check two structural recurrences symbolically."""

    ds = [diagonal_polynomial(r) for r in range(max_r + 1)]
    for r in range(1, max_r + 1):
        half_step = sp.expand(ds[r] - ds[r].subs(X, X - sp.Rational(1, 2)) - ds[r - 1])
        assert half_step == 0, ("half-step", r, half_step)
        derivative_rhs = 2 * sum(ds[r - j] / sp.Integer(j) for j in range(1, r + 1))
        derivative_error = sp.expand(sp.diff(ds[r], X) - derivative_rhs)
        assert derivative_error == 0, ("derivative", r, derivative_error)


def verify_row_geometry(max_n: int = 6) -> None:
    """Verify the complete finite-block geometry stated in the article."""

    for n in range(max_n + 1):
        block = row_block(n)
        length = 2 ** (2 * n + 1)
        maximum = 2 ** sp.binomial(2 * n, 2)
        maximum = int(maximum)

        # Support and circular mirror symmetry.
        for a, value in enumerate(block):
            should_be_zero = a <= n or a >= length - n
            assert (value == 0) == should_be_zero, (n, a, value)
        for a in range(1, length):
            assert block[a] == block[length - a], (n, a)

        # Complement law on the first half; n=0 also satisfies it directly.
        for a in range(length // 2 + 1):
            assert block[a] + block[length // 2 - a] == maximum, (n, a)

        # Exact plateau and maximum.
        plateau = range(length // 2 - n, length // 2 + n + 1)
        assert all(block[a] == maximum for a in plateau), n
        assert [a for a, value in enumerate(block) if value == maximum] == list(plateau), n

        # Strict ramps outside the zero and maximum plateaux.
        for a in range(n + 2, length // 2 - n + 1):
            assert block[a] > block[a - 1], (n, a)
        for a in range(length // 2 + n + 1, length - n):
            assert block[a] < block[a - 1], (n, a)

        # Sum, multiplicities, and number of distinct values.
        assert sum(block) == 2 ** (n * (2 * n + 1)), n
        counts = Counter(block)
        assert counts[0] == 2 * n + 1, n
        assert counts[maximum] == 2 * n + 1, n
        assert all(count == 2 for value, count in counts.items() if value not in (0, maximum)), n
        assert len(counts) == 2 ** (2 * n) - 2 * n + 1, n


def verify_half_integer_roots(max_r: int = 45, max_m: int = 10) -> None:
    """Check the exact nonnegative half-integer root criterion."""

    for r in range(max_r + 1):
        polynomial = diagonal_polynomial(r)
        for m in range(max_m + 1):
            value = sp.simplify(polynomial.subs(X, sp.Rational(m, 2)))
            assert (value == 0) == nonnegative_half_root_condition(r, m), (
                r,
                m,
                value,
            )


def verify_negative_half_integer_formula(max_r: int = 30, max_a: int = 10) -> None:
    """Check D_r(-a/2) as a finite backward difference of epsilon."""

    for r in range(max_r + 1):
        polynomial = diagonal_polynomial(r)
        for a in range(1, max_a + 1):
            lhs = sp.simplify(polynomial.subs(X, -sp.Rational(a, 2)))
            rhs = sum(
                (-1) ** j * sp.binomial(a - 1, j) * tm_sign_extended(r - j)
                for j in range(a)
            )
            assert lhs == rhs, (r, a, lhs, rhs)

    # Two explicit valuation criteria discussed in the article.
    for r in range(1, max_r + 1):
        value_at_minus_one = sp.simplify(diagonal_polynomial(r).subs(X, -1))
        nu2_r = (r & -r).bit_length() - 1
        assert (value_at_minus_one == 0) == (nu2_r % 2 == 1), r
    for r in range(3, max_r + 1):
        value_at_minus_two = sp.simplify(diagonal_polynomial(r).subs(X, -2))
        nu2_r_minus_one = ((r - 1) & -(r - 1)).bit_length() - 1
        assert (value_at_minus_two == 0) == (nu2_r_minus_one % 2 == 1), r


def make_row_profile_plot(max_n: int = 5) -> None:
    """Plot normalized first-block profiles for n=1,...,max_n.

    No colors or styles are fixed explicitly; Matplotlib's default cycle is
    used.  The output illustrates the exact finite profiles whose normalized
    polygonal interpolants are connected to the Fabius function in the repo.
    """

    figure, axis = plt.subplots(figsize=(8.0, 4.8))
    for n in range(1, max_n + 1):
        block = row_block(n)
        length = len(block)
        maximum = 2 ** (n * (2 * n - 1))
        horizontal = [a / length for a in range(length)]
        vertical = [value / maximum for value in block]
        axis.plot(horizontal, vertical, linewidth=1.15, label=f"n={n}")
    axis.set_xlabel(r"normalized residue $a/2^{2n+1}$")
    axis.set_ylabel(r"normalized block value $b_{n,a}/2^{\binom{2n}{2}}$")
    axis.set_title("Normalized first positive blocks of the table")
    axis.grid(True, linewidth=0.4, alpha=0.45)
    axis.legend()
    figure.tight_layout()
    figure.savefig(HERE / "row_profiles.pdf", bbox_inches="tight")
    figure.savefig(HERE / "row_profiles.png", dpi=180, bbox_inches="tight")
    plt.close(figure)


def write_report(max_polynomial: int = 15) -> None:
    """Write a compact report with checks and initial factorizations."""

    lines = [
        "Exact verification report for repeated signed Thue--Morse summation",
        "=" * 74,
        "",
        "All assertions below were checked with exact integer/rational arithmetic.",
        "",
        "Checks completed:",
        "  * weighted recurrence = diagonal polynomial = signed block formula",
        "  * direct diagonal formula = ruler-function recurrence",
        "  * half-step and differential recurrences",
        "  * arbitrary-order finite-block theorem and signed block law",
        "  * hybrid arbitrary-entry evaluator = exact signed block lookup",
        "  * support, mirror, complement, plateau, sum, and multiplicities",
        "  * nonnegative half-integer root criterion",
        "  * negative half-integer finite-difference formula",
        "",
        "Initial diagonal polynomials D_r(x) in factored form:",
    ]
    for r in range(max_polynomial + 1):
        lines.append(f"D_{r}(x) = {sp.sstr(sp.factor(diagonal_polynomial(r)))}")
    lines.extend(
        [
            "",
            "Interpretation: s(n,n+1+r)=D_r(n).",
            "The user-facing diagonal d=k-n is therefore P_d(n)=D_{d-1}(n).",
            "",
        ]
    )
    (HERE / "verification_report.txt").write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    """Run all exact checks and generate the companion outputs."""

    verify_diagonal_formula()
    verify_ruler_recurrence()
    verify_half_step_and_derivative()
    verify_general_iterated_prefix_blocks()
    verify_row_geometry()
    verify_hybrid_evaluator()
    verify_half_integer_roots()
    verify_negative_half_integer_formula()
    make_row_profile_plot()
    write_report()
    print("All exact checks passed.")
    print(f"Wrote {HERE / 'row_profiles.pdf'}")
    print(f"Wrote {HERE / 'row_profiles.png'}")
    print(f"Wrote {HERE / 'verification_report.txt'}")


if __name__ == "__main__":
    main()
