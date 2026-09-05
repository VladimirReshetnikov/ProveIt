#!/usr/bin/env python3
"""Exact experiments for diagonal polynomials in iterated Thue--Morse sums.

The article defines

    epsilon(q) = (-1) ** popcount(q),
    D_m(x) = [z^m] T(z^2) / (1-z)^(2x),
    T(z) = product_{j>=0} (1-z^(2^j)).

For an integer row n and original column k,

    s(n,k) = 0                              if k <= n,
    s(n,k) = D_{k-n-1}(n)                  if k > n.

This script performs exact symbolic and integer checks of the formulas in the
article.  It deliberately uses only exact SymPy arithmetic; no floating-point
recognition is used anywhere.

Typical use:

    python diagonal_polynomials.py --max-degree 12 --verify

The verification bounds are intentionally modest so that the script runs
quickly on ordinary hardware.  Increase them in ``run_verification`` when a
larger experimental sweep is desired.
"""

from __future__ import annotations

import argparse
import math
from functools import lru_cache
from typing import Iterable

import sympy as sp

X = sp.Symbol("x")


def thue_morse_sign(n: int) -> int:
    """Return epsilon_n = (-1)^popcount(n) for n >= 0."""
    if n < 0:
        raise ValueError("the Thue--Morse index must be nonnegative")
    return -1 if n.bit_count() & 1 else 1


def rising_two_x(p: int, x: sp.Expr = X) -> sp.Expr:
    """Return (2*x)^(overline p), with the empty product equal to 1."""
    if p < 0:
        raise ValueError("the rising-factorial order must be nonnegative")
    return sp.rf(2 * x, p)


@lru_cache(maxsize=None)
def diagonal_polynomial(m: int) -> sp.Expr:
    r"""Return the exact polynomial D_m(x).

    The finite rising-factorial formula is

        D_m(x) = sum_{q=0}^{floor(m/2)} epsilon_q
                 (2*x)^(overline{m-2q}) / (m-2q)!.

    This is generally faster and more stable than interpolating values of the
    original recursively defined two-dimensional table.
    """
    if m < 0:
        return sp.Integer(0)
    terms: list[sp.Expr] = []
    for q in range(m // 2 + 1):
        p = m - 2 * q
        terms.append(
            thue_morse_sign(q) * rising_two_x(p) / sp.factorial(p)
        )
    return sp.Poly(sum(terms), X, domain=sp.QQ).as_expr()


def diagonal_value(m: int, n: int) -> int:
    r"""Evaluate D_m(n) by the finite generalized-binomial formula.

        D_m(n) = sum_q epsilon_q binomial(2n+m-2q-1, m-2q).

    SymPy correctly interprets binomial(-1, 0)=1, so the formula also covers
    n=0 without a special case.
    """
    if m < 0:
        return 0
    if n < 0:
        raise ValueError("this evaluator expects a nonnegative integer row")
    value = sp.Integer(0)
    for q in range(m // 2 + 1):
        p = m - 2 * q
        value += thue_morse_sign(q) * sp.binomial(2 * n + p - 1, p)
    return int(value)


def diagonal_value_block_reduced(m: int, n: int) -> int:
    r"""Evaluate D_m(n) after the exact Thue--Morse block reduction.

    Let B=2^(2n+1).  The finite-product factorization gives

        D_m(n) = epsilon_floor(m/B) D_(m mod B)(n).

    This is useful when m is enormous but n is small.  It reduces the direct
    binomial sum to fewer than B/2 terms, independently of the magnitude of m.
    """
    if m < 0:
        return 0
    if n < 0:
        raise ValueError("the row must be nonnegative")
    block = 1 << (2 * n + 1)
    q, r = divmod(m, block)
    return thue_morse_sign(q) * diagonal_value(r, n)


@lru_cache(maxsize=None)
def thue_morse_prefix_moments(length: int, max_degree: int) -> tuple[int, ...]:
    r"""Return M_d(length)=sum_{q < length} epsilon_q q^d for 0<=d<=max_degree.

    Pairing q=2u and q=2u+1 gives the divide-and-conquer recurrences

        M_d(2N)   = -sum_{j<d} binomial(d,j) 2^j M_j(N),
        M_d(2N+1) = M_d(2N) + epsilon_N (2N)^d.

    The recursion has depth O(log length) and computes the whole moment vector
    in O(max_degree^2 log length) exact arithmetic operations.
    """
    if length < 0 or max_degree < 0:
        raise ValueError("length and max_degree must be nonnegative")
    if length == 0:
        return tuple(0 for _ in range(max_degree + 1))

    half = length // 2
    lower = thue_morse_prefix_moments(half, max_degree)
    paired: list[int] = []
    for degree in range(max_degree + 1):
        value = -sum(
            math.comb(degree, j) * (2 ** j) * lower[j]
            for j in range(degree)
        )
        paired.append(value)

    if length & 1:
        sign = thue_morse_sign(half)
        for degree in range(max_degree + 1):
            paired[degree] += sign * ((2 * half) ** degree)

    return tuple(paired)


def diagonal_value_by_moments(m: int, n: int) -> int:
    r"""Evaluate D_m(n) in time polynomial in n and logarithmic in m.

    For n>=1, write the generalized binomial in the direct formula as the
    degree-(2n-1) polynomial

        binomial(2n+m-2q-1, 2n-1) = sum_d c_d q^d.

    Then D_m(n)=sum_d c_d M_d(floor(m/2)+1), where M_d is computed by
    ``thue_morse_prefix_moments``.  This avoids a loop with O(m) summands.
    """
    if m < 0:
        return 0
    if n < 0:
        raise ValueError("the row must be nonnegative")
    if n == 0:
        return thue_morse_sign(m // 2) if m % 2 == 0 else 0

    degree = 2 * n - 1
    q = sp.Symbol("q")
    p = m - 2 * q
    kernel = sp.prod(p + j for j in range(1, 2 * n)) / math.factorial(degree)
    kernel_poly = sp.Poly(sp.expand(kernel), q, domain=sp.QQ)
    moments = thue_morse_prefix_moments(m // 2 + 1, degree)
    value = sum(kernel_poly.nth(d) * moments[d] for d in range(degree + 1))
    if value.q != 1:
        raise ArithmeticError("an integer-valued formula produced a noninteger")
    return int(value)


def diagonal_value_hybrid(m: int, n: int, direct_cutoff: int = 128) -> int:
    """Block-reduce m, then choose a short sum or the moment algorithm."""
    if m < 0:
        return 0
    if n < 0 or direct_cutoff < 0:
        raise ValueError("n and direct_cutoff must be nonnegative")
    block = 1 << (2 * n + 1)
    q, r = divmod(m, block)
    core = (
        diagonal_value(r, n)
        if r <= direct_cutoff
        else diagonal_value_by_moments(r, n)
    )
    return thue_morse_sign(q) * core


@lru_cache(maxsize=None)
def diagonal_polynomial_newton(m: int) -> sp.Expr:
    r"""Generate D_m(x) from the 2-adic Newton--Bell recurrence.

    Put

        lambda_r(x) = 2x + 2 - 2^(v_2(r)+1).

    Then D_0=1 and

        m D_m = sum_{r=1}^m lambda_r D_{m-r}.
    """
    if m < 0:
        return sp.Integer(0)
    if m == 0:
        return sp.Integer(1)
    total = sp.Integer(0)
    for r in range(1, m + 1):
        valuation = (r & -r).bit_length() - 1
        lam = 2 * X + 2 - 2 ** (valuation + 1)
        total += lam * diagonal_polynomial_newton(m - r)
    return sp.Poly(total / m, X, domain=sp.QQ).as_expr()


def iterated_prefix_row(order: int, last_index: int) -> list[int]:
    """Compute S^(order)(0..last_index) by literal inclusive prefix sums."""
    if order < 0 or last_index < 0:
        raise ValueError("order and last_index must be nonnegative")
    row = [thue_morse_sign(j) for j in range(last_index + 1)]
    for _ in range(order):
        running = 0
        next_row: list[int] = []
        for value in row:
            running += value
            next_row.append(running)
        row = next_row
    return row


def s_from_definition(n: int, k: int) -> int:
    """Literal reference implementation of the user's s(n,k)."""
    if n < 0 or k < 0:
        raise ValueError("n and k must be nonnegative")
    if k <= n:
        return 0
    prefix_index = k - n - 1
    return iterated_prefix_row(2 * n + 1, prefix_index)[prefix_index]


def expected_common_denominator(m: int) -> int:
    r"""Return the theorem's exact common denominator of D_m.

        den(D_m) = m! / 2^min(v_2(m!), ceil(m/2)).
    """
    factorial = math.factorial(m)
    v2_factorial = 0
    t = factorial
    while t and t % 2 == 0:
        v2_factorial += 1
        t //= 2
    c = (m + 1) // 2
    return factorial // (2 ** min(v2_factorial, c))


def actual_common_denominator(poly: sp.Expr) -> int:
    """Least common multiple of the reduced coefficient denominators."""
    denominators = [int(c.q) for c in sp.Poly(poly, X, domain=sp.QQ).all_coeffs()]
    return math.lcm(*denominators) if denominators else 1


def nonnegative_half_root_predicted(m: int, a: int) -> bool:
    r"""Test the exact residue criterion for D_m(a/2)=0.

    With B=2^(a+1), the root occurs exactly when m mod B is one of the final
    a+1 residues B-a-1,...,B-1.
    """
    if m < 0 or a < 0:
        raise ValueError("m and a must be nonnegative")
    block = 1 << (a + 1)
    return (m % block) >= block - a - 1


def negative_half_value(m: int, b: int) -> int:
    r"""Evaluate D_m(-b/2) by the finite binomial/Thue--Morse formula.

        D_m(-b/2) = sum_{0<=j<=min(b,m), j == m (mod 2)}
                      (-1)^j binomial(b,j) epsilon_((m-j)/2).
    """
    if m < 0 or b < 0:
        raise ValueError("m and b must be nonnegative")
    total = 0
    for j in range(min(b, m) + 1):
        if (m - j) % 2 == 0:
            total += (
                (-1) ** j
                * math.comb(b, j)
                * thue_morse_sign((m - j) // 2)
            )
    return total


def scan_negative_strict_half_roots(max_odd_b: int, max_m: int) -> list[tuple[int, int]]:
    r"""Search for zeros D_m(-b/2) with odd b (strict negative halves).

    The article records the conjecture that this list is always empty.  This
    function is only an exact finite experiment; it is not used as a proof.
    """
    if max_odd_b < 1 or max_m < 0:
        raise ValueError("max_odd_b must be positive and max_m nonnegative")
    zeros: list[tuple[int, int]] = []
    for b in range(1, max_odd_b + 1, 2):
        for m in range(max_m + 1):
            if negative_half_value(m, b) == 0:
                zeros.append((b, m))
    return zeros


def primitive_normalization(m: int) -> sp.Poly:
    r"""Return Q_m(x)=m! D_m(x)/2^ceil(m/2), a primitive Z[x] polynomial."""
    c = (m + 1) // 2
    expr = sp.factorial(m) * diagonal_polynomial(m) / (2 ** c)
    return sp.Poly(expr, X, domain=sp.ZZ)


def print_polynomials(max_degree: int) -> None:
    """Print factored diagonal polynomials and their exact denominators."""
    for m in range(max_degree + 1):
        poly = diagonal_polynomial(m)
        print(
            f"D_{m}(x) = {sp.factor(poly)}"
            f"    [common denominator {actual_common_denominator(poly)}]"
        )


def run_verification(max_degree: int) -> None:
    """Run a collection of exact regression checks from the article."""
    symbolic_bound = max(max_degree, 10)

    # Closed form versus Newton--Bell generation.
    for m in range(symbolic_bound + 1):
        assert sp.expand(diagonal_polynomial(m) - diagonal_polynomial_newton(m)) == 0

    # The Sheffer lowering law: D_m(x)-D_m(x-1/2)=D_(m-1)(x).
    for m in range(1, symbolic_bound + 1):
        lhs = diagonal_polynomial(m) - diagonal_polynomial(m).subs(X, X - sp.Rational(1, 2))
        assert sp.expand(lhs - diagonal_polynomial(m - 1)) == 0

    # Direct formula versus literal repeated prefix summation.  Build each
    # literal row once instead of recomputing all lower prefixes for every k.
    for n in range(5):
        largest_k = 34
        largest_prefix_index = largest_k - n - 1
        literal = iterated_prefix_row(2 * n + 1, largest_prefix_index)
        for k in range(0, largest_k + 1):
            if k <= n:
                observed = 0
            else:
                observed = literal[k - n - 1]
            expected = 0 if k <= n else diagonal_value(k - n - 1, n)
            assert observed == expected

    # Block reduction in the diagonal offset m.  A sparse collection of edge,
    # center, and multi-block samples avoids spending most of the run time on
    # enormous generalized binomial sums while still exercising every case.
    for n in range(5):
        block = 1 << (2 * n + 1)
        residues = {0, 1, 2, n, n + 1, block // 4, block // 2, block - n - 2, block - 1}
        samples = {q * block + r for q in range(5) for r in residues if 0 <= r < block}
        for m in sorted(samples):
            direct = diagonal_value(m, n)
            assert direct == diagonal_value_block_reduced(m, n)
            assert direct == diagonal_value_by_moments(m, n)
            assert direct == diagonal_value_hybrid(m, n, direct_cutoff=16)

    # Additional moderately large offsets exercise the logarithmic-time
    # prefix-moment recursion without making the literal direct sum dominant.
    for n, m in [(2, 10_003), (5, 1_000_007), (10, 10**9 + 7)]:
        assert diagonal_value_hybrid(m, n, direct_cutoff=16) == \
            diagonal_value_hybrid(m + (1 << (2 * n + 1)), n, direct_cutoff=16) * \
            thue_morse_sign(1)

    # Exact common-denominator and primitive-content theorems.
    for m in range(symbolic_bound + 1):
        assert actual_common_denominator(diagonal_polynomial(m)) == expected_common_denominator(m)
        primitive = primitive_normalization(m)
        content, _ = sp.polys.polytools.primitive(primitive)
        assert abs(int(content)) == 1

    # Exact nonnegative half-integer zero criterion.
    for m in range(symbolic_bound + 1):
        for a in range(0, 12):
            value = diagonal_polynomial(m).subs(X, sp.Rational(a, 2))
            assert (value == 0) == nonnegative_half_root_predicted(m, a)

    # Negative half-grid evaluation formula.
    for m in range(symbolic_bound + 1):
        for b in range(0, 12):
            value = diagonal_polynomial(m).subs(X, -sp.Rational(b, 2))
            assert value == negative_half_value(m, b)

    print(
        "All exact checks passed: closed forms, Newton recurrence, half-step "
        "lowering, repeated sums, block reduction, logarithmic-time moment evaluation, denominators, and half-grid values."
    )


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-degree",
        type=int,
        default=10,
        help="largest D_m to print (default: 10)",
    )
    parser.add_argument(
        "--verify",
        action="store_true",
        help="run exact symbolic and integer regression checks",
    )
    parser.add_argument(
        "--scan-negative-half",
        action="store_true",
        help="scan the article's strict-negative-half-root conjecture",
    )
    parser.add_argument(
        "--scan-max-b",
        type=int,
        default=63,
        help="largest odd b in the conjecture scan (default: 63)",
    )
    parser.add_argument(
        "--scan-max-m",
        type=int,
        default=10_000,
        help="largest diagonal m in the conjecture scan (default: 10000)",
    )
    return parser.parse_args(argv)


def main() -> None:
    args = parse_args()
    if args.max_degree < 0:
        raise SystemExit("--max-degree must be nonnegative")
    print_polynomials(args.max_degree)
    if args.verify:
        run_verification(args.max_degree)
    if args.scan_negative_half:
        zeros = scan_negative_strict_half_roots(args.scan_max_b, args.scan_max_m)
        print(
            f"Strict-negative-half scan through odd b <= {args.scan_max_b} "
            f"and m <= {args.scan_max_m}: {len(zeros)} zero(s)."
        )
        if zeros:
            print(zeros[:50])


if __name__ == "__main__":
    main()
