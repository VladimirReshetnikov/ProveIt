#!/usr/bin/env python3
"""Exact experiments for dyadic extrapolation of Rvachev up-function splines.

This file accompanies the article
    "Exact quarter-base extrapolation for dyadic samples of the
     Rvachev up-function spline prefixes".

The user-defined approximation is

    up_n(x) = F^{-1}[ product_{k=0}^n sinc(pi*t/2^k) ](x).

With the Fourier convention used in the article, up_n is the convolution of
n+1 centered uniform densities.  For |x| <= 1 it equals the centered Fabius
spline S_n(1-|x|), where

    S_n(y) = 1/(2^(n(n-1)/2) n!)
             sum_{r>=0} eps_r (2^n y - 1/2 - r)_+^n,

and eps_r = (-1)^(binary digit sum of r).  At rational y this formula is
computed exactly with fractions.Fraction.

For a reduced dyadic a = 1-|x| = m/2^s, set d=floor(s/2) and Q=1/4.  The
article proves that, for all n >= s,

    up_n(x) = L + A_1 Q^n + ... + A_d Q^(d*n),
    L = up(x).

Hence d+1 consecutive exact values determine L and all A_r.  The closed
q-binomial extraction formula is

    L = 1/(Q;Q)_d * sum_{j=0}^d (-1)^j Q^(j(j+1)/2)
                          [d choose j]_Q up_{N+d-j}(x).

Everything below uses only Python's standard library and exact rational
arithmetic.  No floating-point value is used in any assertion.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import factorial
from typing import Iterable, List, Sequence, Tuple


Q_QUARTER = Fraction(1, 4)


def thue_morse_sign(r: int) -> int:
    """Return eps_r=(-1)^(number of 1-bits of r)."""
    if r < 0:
        raise ValueError("the Thue--Morse index must be nonnegative")
    return -1 if r.bit_count() & 1 else 1


def floor_fraction(value: Fraction) -> int:
    """Exact mathematical floor for a Fraction (also correct when negative)."""
    return value.numerator // value.denominator


def centered_spline(n: int, y: Fraction) -> Fraction:
    """Evaluate the centered spline S_n(y) exactly.

    The summation cutoff is
        N_n(y)=max(0, floor(2^n y + 1/2)).
    For n>0, the term at a knot is zero, so the formula is independent of
    whether one writes the upper endpoint inclusively or exclusively.

    The degree-zero convention is the signed Thue--Morse prefix used in the
    linked ProveIt development.  The demonstrations below use n>=1 except at
    the three trivial depth-zero points.
    """
    if n < 0:
        raise ValueError("spline degree n must be nonnegative")
    y = Fraction(y)
    two_n = 1 << n
    cutoff = max(0, floor_fraction(two_n * y + Fraction(1, 2)))

    if n == 0:
        return Fraction(sum(thue_morse_sign(r) for r in range(cutoff)), 1)

    z = two_n * y - Fraction(1, 2)
    numerator = sum(
        Fraction(thue_morse_sign(r), 1) * (z - r) ** n
        for r in range(cutoff)
    )
    denominator = (1 << (n * (n - 1) // 2)) * factorial(n)
    return numerator / denominator


def up_partial(n: int, x: Fraction) -> Fraction:
    """Evaluate the finite sinc-product inverse transform up_n(x) exactly.

    The finite convolution is even, so evaluating S_n(1-|x|) avoids the much
    longer signed global prefix that S_n(1+x) would use for positive x.
    """
    x = Fraction(x)
    if not -1 <= x <= 1:
        # The truncated convolution actually has smaller support than [-1,1].
        return Fraction(0)
    return centered_spline(n, Fraction(1) - abs(x))


def is_power_of_two(value: int) -> bool:
    """Return True exactly when value is a positive power of two."""
    return value > 0 and value & (value - 1) == 0


def dyadic_depth(value: Fraction) -> int:
    """Return s for a reduced dyadic value with denominator 2^s.

    fractions.Fraction is always reduced, so the denominator itself determines
    the depth.  The values 0 and 1 have denominator 1 and therefore depth 0.
    """
    value = Fraction(value)
    denominator = value.denominator
    if not is_power_of_two(denominator):
        raise ValueError(f"{value} is not dyadic")
    return denominator.bit_length() - 1


def q_pochhammer(a: Fraction, q: Fraction, n: int) -> Fraction:
    """Return the finite q-Pochhammer symbol (a;q)_n exactly."""
    if n < 0:
        raise ValueError("q-Pochhammer length must be nonnegative")
    result = Fraction(1)
    for k in range(n):
        result *= 1 - a * q**k
    return result


def gaussian_binomial(n: int, k: int, q: Fraction) -> Fraction:
    """Return the Gaussian binomial coefficient [n choose k]_q.

    This product formula is sufficient here because q=1/4 is not a root of
    unity, so no denominator vanishes.
    """
    if k < 0 or k > n:
        return Fraction(0)
    return q_pochhammer(q, q, n) / (
        q_pochhammer(q, q, k) * q_pochhammer(q, q, n - k)
    )


def reverse_extraction_weights(
    d: int, q: Fraction = Q_QUARTER
) -> List[Fraction]:
    """Weights w_j for q_{N+d-j}, j=0,...,d.

    They are the coefficients of

        W_d(z) = (q*z;q)_d/(q;q)_d.

    Therefore W_d(1)=1 and W_d(q^{-r})=0 for r=1,...,d, which is exactly the
    constant-preservation / geometric-mode-annihilation property.
    """
    if d < 0:
        raise ValueError("d must be nonnegative")
    denominator = q_pochhammer(q, q, d)
    return [
        (-1) ** j
        * q ** (j * (j + 1) // 2)
        * gaussian_binomial(d, j, q)
        / denominator
        for j in range(d + 1)
    ]


def extract_limit_from_values(
    values_forward: Sequence[Fraction], q: Fraction = Q_QUARTER
) -> Fraction:
    """Extract L from q_N,...,q_{N+d}, supplied in forward order."""
    if not values_forward:
        raise ValueError("at least one sequence value is required")
    d = len(values_forward) - 1
    weights = reverse_extraction_weights(d, q)
    return sum(weights[j] * values_forward[d - j] for j in range(d + 1))


def richardson_extract(
    values_forward: Sequence[Fraction], q: Fraction = Q_QUARTER
) -> Fraction:
    """Same extraction via the triangular Richardson recursion.

    Starting with R_0(N+j)=q_{N+j}, repeatedly apply

        R_r(j) = (R_{r-1}(j+1)-q^r R_{r-1}(j))/(1-q^r).

    After d stages, the sole remaining entry is the exact constant L.
    """
    if not values_forward:
        raise ValueError("at least one sequence value is required")
    row = [Fraction(v) for v in values_forward]
    for r in range(1, len(values_forward)):
        factor = q**r
        row = [
            (row[j + 1] - factor * row[j]) / (1 - factor)
            for j in range(len(row) - 1)
        ]
    return row[0]


def solve_fraction_system(
    matrix: Sequence[Sequence[Fraction]], rhs: Sequence[Fraction]
) -> List[Fraction]:
    """Solve a square linear system over Q by exact Gauss--Jordan elimination."""
    n = len(matrix)
    if n == 0 or len(rhs) != n or any(len(row) != n for row in matrix):
        raise ValueError("matrix must be nonempty and square, with matching rhs")

    augmented = [
        [Fraction(entry) for entry in matrix[i]] + [Fraction(rhs[i])]
        for i in range(n)
    ]

    for column in range(n):
        pivot = next(
            (row for row in range(column, n) if augmented[row][column] != 0),
            None,
        )
        if pivot is None:
            raise ValueError("singular system")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]

        pivot_value = augmented[column][column]
        augmented[column] = [entry / pivot_value for entry in augmented[column]]

        for row in range(n):
            if row == column:
                continue
            multiplier = augmented[row][column]
            if multiplier:
                augmented[row] = [
                    augmented[row][col] - multiplier * augmented[column][col]
                    for col in range(n + 1)
                ]

    return [augmented[i][-1] for i in range(n)]


def recover_tail_coefficients(
    x: Fraction, start_n: int, d: int, q: Fraction = Q_QUARTER
) -> Tuple[Fraction, List[Fraction]]:
    """Recover L,A_1,...,A_d from d+1 consecutive up_n(x) values.

    The exact Vandermonde system is

        up_{start_n+j}(x) = L + sum_{r=1}^d A_r q^(r(start_n+j)).
    """
    values = [up_partial(start_n + j, x) for j in range(d + 1)]
    matrix = [
        [Fraction(1)]
        + [q ** (r * (start_n + j)) for r in range(1, d + 1)]
        for j in range(d + 1)
    ]
    solution = solve_fraction_system(matrix, values)
    return solution[0], solution[1:]


def bernoulli_numbers(max_index: int) -> List[Fraction]:
    """Compute B_0,...,B_max_index by Akiyama--Tanigawa.

    This implementation returns B_1=+1/2.  Only even Bernoulli numbers are used
    below, so the convention at B_1 is irrelevant.
    """
    work = [Fraction(0) for _ in range(max_index + 1)]
    result: List[Fraction] = []
    for m in range(max_index + 1):
        work[m] = Fraction(1, m + 1)
        for j in range(m, 0, -1):
            work[j - 1] = j * (work[j - 1] - work[j])
        result.append(work[0])
    return result


def reciprocal_centered_moments(max_k: int) -> List[Fraction]:
    """Return gamma_0,...,gamma_max_k exactly.

    The article defines

        1/C(T) = sum gamma_k T^(2k)/(2k)!,
        C(T)   = product_{j>=1} sinh(T/2^j)/(T/2^j).

    We use the rational logarithm

        log C(T) = sum_{r>=1}
          2^(2r-1) B_(2r) / (r (2r)! (2^(2r)-1)) * T^(2r),

    then exponentiate -log C as an ordinary series in u=T^2.  If
    A(u)=exp(B(u)), its coefficients obey

        n a_n = sum_{k=1}^n k b_k a_(n-k).
    """
    if max_k < 0:
        raise ValueError("max_k must be nonnegative")
    bernoulli = bernoulli_numbers(2 * max_k)

    log_inverse = [Fraction(0) for _ in range(max_k + 1)]
    for r in range(1, max_k + 1):
        log_c_coefficient = (
            Fraction(2 ** (2 * r - 1))
            * bernoulli[2 * r]
            / (r * factorial(2 * r) * (2 ** (2 * r) - 1))
        )
        log_inverse[r] = -log_c_coefficient

    ordinary = [Fraction(0) for _ in range(max_k + 1)]
    ordinary[0] = Fraction(1)
    for n in range(1, max_k + 1):
        ordinary[n] = sum(
            k * log_inverse[k] * ordinary[n - k]
            for k in range(1, n + 1)
        ) / n

    return [ordinary[k] * factorial(2 * k) for k in range(max_k + 1)]


def parse_fraction(text: str) -> Fraction:
    """Parse an integer, fraction such as -11/16, or finite decimal."""
    try:
        return Fraction(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def format_tail(limit: Fraction, coefficients: Sequence[Fraction]) -> str:
    """Return a readable exact formula L + sum A_r*4^(-rn)."""
    parts = [str(limit)]
    for r, coefficient in enumerate(coefficients, start=1):
        sign = "+" if coefficient >= 0 else "-"
        parts.append(f" {sign} {abs(coefficient)}*4^(-{r}n)")
    return "".join(parts)


def demonstrate_case(
    x: Fraction,
    expected_limit: Fraction | None = None,
    extra_checks: int = 4,
) -> None:
    """Run all exact checks for one dyadic x and print the results."""
    x = Fraction(x)
    if not -1 <= x <= 1:
        raise ValueError("the demonstration expects x in [-1,1]")

    a = Fraction(1) - abs(x)
    s = dyadic_depth(a)
    d = s // 2
    start_n = s

    values = [up_partial(start_n + j, x) for j in range(d + 1)]
    extracted_closed = extract_limit_from_values(values)
    extracted_recursive = richardson_extract(values)
    recovered_limit, coefficients = recover_tail_coefficients(x, start_n, d)

    assert extracted_closed == extracted_recursive == recovered_limit
    if expected_limit is not None:
        assert recovered_limit == expected_limit

    # Verify that the recovered finite geometric tail predicts later splines.
    for n in range(start_n, start_n + d + 1 + extra_checks):
        predicted = recovered_limit + sum(
            coefficients[r - 1] * Q_QUARTER ** (r * n)
            for r in range(1, d + 1)
        )
        actual = up_partial(n, x)
        assert predicted == actual, (n, predicted, actual)

    print("=" * 76)
    print(f"x = {x};  a=1-|x| = {a};  dyadic depth s = {s};  d = {d}")
    for j, value in enumerate(values):
        print(f"up_{start_n + j}(x) = {value}")
    print(f"extracted up(x) = {recovered_limit}")
    print("eventual formula:")
    print(f"  up_n(x) = {format_tail(recovered_limit, coefficients)}  (n >= {s})")
    print("reverse q-binomial weights on up_{N+d},...,up_N:")
    print("  " + ", ".join(str(w) for w in reverse_extraction_weights(d)))
    print(f"verified through n = {start_n + d + extra_checks}")


def exhaustive_self_test(max_depth: int, extra_checks: int = 2) -> None:
    """Check every reduced dyadic ``a=1-|x|`` through a chosen depth.

    This is an empirical verification rather than part of the proof.  For each
    odd numerator m at every depth 1 <= s <= max_depth, it performs three
    independent algebraic consistency checks:

    * the closed q-binomial row and triangular Richardson table agree;
    * a rational Vandermonde solve recovers the same constant;
    * the recovered finite geometric formula predicts several later splines.

    It also checks the two depth-zero endpoints a=0 and a=1.  By symmetry we
    use x=1-a in [0,1]; the same values occur at -x.
    """
    if max_depth < 0:
        raise ValueError("max_depth must be nonnegative")
    if extra_checks < 0:
        raise ValueError("extra_checks must be nonnegative")

    cases = 0

    # The depth-zero values correspond to x=1 and x=0.
    for a in (Fraction(0), Fraction(1)):
        x = 1 - a
        value = up_partial(0, x)
        assert extract_limit_from_values([value]) == value
        cases += 1

    for s in range(1, max_depth + 1):
        denominator = 1 << s
        for m in range(1, denominator, 2):
            a = Fraction(m, denominator)
            x = 1 - a
            d = s // 2
            values = [up_partial(s + j, x) for j in range(d + 1)]

            closed = extract_limit_from_values(values)
            recursive = richardson_extract(values)
            recovered, coefficients = recover_tail_coefficients(x, s, d)
            assert closed == recursive == recovered

            # The theorem predicts that every possible mode is present once
            # s >= 2; checking this catches accidental rank/indexing errors.
            if s >= 2:
                assert all(coefficient != 0 for coefficient in coefficients)

            # Check both later prediction and independence of the starting N.
            last_n = s + d + extra_checks
            for n in range(s, last_n + 1):
                predicted = recovered + sum(
                    coefficients[r - 1] * Q_QUARTER ** (r * n)
                    for r in range(1, d + 1)
                )
                assert predicted == up_partial(n, x)

            shifted_values = [
                up_partial(s + 1 + j, x) for j in range(d + 1)
            ]
            assert extract_limit_from_values(shifted_values) == recovered
            cases += 1

    print(
        f"exhaustive exact self-test passed for {cases} dyadic points "
        f"through reduced depth {max_depth}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Exact quarter-base extrapolation for finite sinc-product "
            "approximations to Rvachev's up-function."
        )
    )
    parser.add_argument(
        "--x",
        type=parse_fraction,
        help=(
            "optional dyadic x in [-1,1], e.g. --x=-11/16; when omitted, "
            "the two article examples are run"
        ),
    )
    parser.add_argument(
        "--extra-checks",
        type=int,
        default=4,
        help="number of later n-values used to verify the recovered tail (default: 4)",
    )
    parser.add_argument(
        "--self-test-max-depth",
        type=int,
        default=0,
        metavar="S",
        help=(
            "after the displayed case(s), exhaustively verify every reduced "
            "dyadic point through denominator depth S; 0 disables this test"
        ),
    )
    args = parser.parse_args()

    print("First reciprocal centered moments gamma_k:")
    print("  " + ", ".join(str(g) for g in reciprocal_centered_moments(5)))

    if args.x is None:
        demonstrate_case(Fraction(-3, 4), Fraction(5, 72), args.extra_checks)
        demonstrate_case(
            Fraction(-11, 16), Fraction(305857, 2073600), args.extra_checks
        )
    else:
        demonstrate_case(args.x, None, args.extra_checks)

    if args.self_test_max_depth:
        exhaustive_self_test(args.self_test_max_depth, min(args.extra_checks, 3))


if __name__ == "__main__":
    main()
