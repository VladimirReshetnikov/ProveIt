#!/usr/bin/env python3
"""Exact experiments for dyadic Rvachev up-function extrapolation.

This program uses only Python's standard library and performs every computation
with ``fractions.Fraction``.  There is no floating-point arithmetic in the
proof checks.

Notation
--------
The user's approximant ``up_n`` is the inverse Fourier transform of

    product_{k=0}^n sinc(pi*t/2^k).

The article also uses ``p_N`` for the prefix containing exactly N factors, so
``up_n = p_{n+1}``.

For a dyadic x=a/2^s in lowest terms, the theorem proved in the accompanying
article states that, for n >= s,

    up_n(x) = up(x) + B_1*Q^n + ... + B_R*Q^(R*n),

where Q=1/4 and R=floor(s/2).  The q-binomial weights recover the constant term
up(x) from any R+1 consecutive values.

The script:
  * evaluates finite sinc-product splines exactly by the Thue--Morse
    truncated-power formula;
  * constructs q-Pochhammer/q-binomial extrapolation weights;
  * solves the exact Vandermonde system for all geometric coefficients;
  * computes the Bernoulli--Bell reciprocal-tail coefficients alpha_r;
  * checks the claimed identities on a collection of dyadic examples and on
    a full denominator grid through a configurable depth.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
from math import factorial
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple


Q = Fraction(1, 4)


def thue_morse_sign(k: int) -> int:
    """Return tau_k=(-1)^(binary digit sum of k)."""

    if k < 0:
        raise ValueError("k must be nonnegative")
    return -1 if k.bit_count() & 1 else 1


@lru_cache(maxsize=None)
def thue_morse_prefix(length: int) -> Tuple[int, ...]:
    """Return tau_0,...,tau_{length-1}; cached for repeated spline calls."""

    if length < 0:
        raise ValueError("length must be nonnegative")
    return tuple(thue_morse_sign(k) for k in range(length))


@lru_cache(maxsize=None)
def finite_prefix_value(number_of_factors: int, x: Fraction) -> Fraction:
    r"""Evaluate p_N(x) exactly, where N=``number_of_factors``.

    The formula is

      p_N(x) = 2^{N(N-1)/2}/(N-1)! *
               sum_{k=0}^{2^N-1} tau_k
               (x + 1 - 2^{-N} - k/2^{N-1})_+^{N-1}.

    At the sample levels used by the theorem (n >= dyadic depth), x is strictly
    inside a knot cell, so no convention for y_+^0 at a knot is needed.
    """

    n = number_of_factors
    x = Fraction(x)
    if n < 1:
        raise ValueError("number_of_factors must be at least 1")

    degree = n - 1

    # At every level used by the theorem, x is the midpoint of a knot cell.
    # Then M=2^(N-1)(x+1) is an integer and the scaled cell formula reduces
    # to one integer sum:
    #
    #   p_N(x) = sum_{k=0}^{M-1} tau_k (2(M-k)-1)^(N-1)
    #            / ((N-1)! 2^(N(N-1)/2)).
    #
    # This branch is dramatically faster than repeated Fraction powers.
    midpoint_coordinate = x + 1
    scaled = midpoint_coordinate * 2 ** (n - 1)
    if scaled.denominator == 1:
        m = scaled.numerator
        upper = max(0, min(m, 2**n))
        integer_sum = sum(
            sign * (2 * (m - k) - 1) ** degree
            for k, sign in enumerate(thue_morse_prefix(upper))
        )
        denominator = factorial(degree) * 2 ** (n * (n - 1) // 2)
        return Fraction(integer_sum, denominator)

    # General rational fallback, retained so the evaluator is useful outside
    # the exact dyadic-midpoint regime as well.
    support_radius = Fraction(2**n - 1, 2**n)  # A_N = 1-2^{-N}
    total = Fraction(0)
    for k, sign in enumerate(thue_morse_prefix(2**n)):
        shifted = x + support_radius - Fraction(k, 2 ** (n - 1))
        if shifted > 0:
            total += sign * shifted**degree
    normalization = Fraction(2 ** (n * (n - 1) // 2), factorial(degree))
    return normalization * total


def up_prefix_value(n: int, x: Fraction) -> Fraction:
    """Evaluate the user's up_n(x), which contains the factors k=0,...,n."""

    if n < 0:
        raise ValueError("n must be nonnegative")
    return finite_prefix_value(n + 1, Fraction(x))


def dyadic_depth(x: Fraction) -> int:
    """Return the least s >= 0 for which 2^s*x is an integer."""

    x = Fraction(x)
    denominator = x.denominator
    if denominator & (denominator - 1):
        raise ValueError(f"{x} is not dyadic")
    return denominator.bit_length() - 1


def q_pochhammer(q: Fraction, m: int) -> Fraction:
    r"""Return (q;q)_m = product_{k=1}^m (1-q^k)."""

    if m < 0:
        raise ValueError("m must be nonnegative")
    value = Fraction(1)
    for k in range(1, m + 1):
        value *= 1 - q**k
    return value


def gaussian_q_binomial(n: int, k: int, q: Fraction) -> Fraction:
    r"""Return the Gaussian binomial [n choose k]_q by q-Pochhammers."""

    if k < 0 or k > n:
        return Fraction(0)
    return q_pochhammer(q, n) / (
        q_pochhammer(q, k) * q_pochhammer(q, n - k)
    )


def extrapolation_weights(order: int, q: Fraction = Q) -> List[Fraction]:
    r"""Return the q-Lagrange weights w_j^(order), j=0,...,order.

    w_j^(R) = (-1)^(R-j) q^((R-j)(R-j+1)/2)
              / ((q;q)_j (q;q)_{R-j}).

    These weights have mass one and annihilate q^{jr} for r=1,...,R.
    """

    if order < 0:
        raise ValueError("order must be nonnegative")
    result: List[Fraction] = []
    for j in range(order + 1):
        exponent = (order - j) * (order - j + 1) // 2
        numerator = (-1) ** (order - j) * q**exponent
        denominator = q_pochhammer(q, j) * q_pochhammer(q, order - j)
        result.append(numerator / denominator)
    return result


def extrapolate_limit(values: Sequence[Fraction], q: Fraction = Q) -> Fraction:
    """Extract the constant term from R+1 geometric samples."""

    order = len(values) - 1
    if order < 0:
        raise ValueError("at least one value is required")
    return sum(
        (weight * Fraction(value) for weight, value in zip(
            extrapolation_weights(order, q), values
        )),
        Fraction(0),
    )


def richardson_table(values: Sequence[Fraction], q: Fraction = Q) -> List[List[Fraction]]:
    r"""Build the triangular recursion A_{m,n}.

      A_{0,n} = value_n,
      A_{m,n} = (A_{m-1,n+1} - q^m A_{m-1,n})/(1-q^m).

    The first entry in row R equals the weighted q-binomial extrapolant of
    order R.
    """

    rows: List[List[Fraction]] = [[Fraction(v) for v in values]]
    for m in range(1, len(values)):
        previous = rows[-1]
        rows.append([
            (previous[j + 1] - q**m * previous[j]) / (1 - q**m)
            for j in range(len(previous) - 1)
        ])
    return rows


def solve_fraction_system(
    matrix: Sequence[Sequence[Fraction]], right_hand_side: Sequence[Fraction]
) -> List[Fraction]:
    """Solve a square linear system over Q by exact Gauss--Jordan elimination."""

    size = len(matrix)
    if size == 0 or len(right_hand_side) != size:
        raise ValueError("the system must be nonempty and square")
    if any(len(row) != size for row in matrix):
        raise ValueError("the coefficient matrix must be square")

    augmented = [
        [Fraction(entry) for entry in row] + [Fraction(rhs)]
        for row, rhs in zip(matrix, right_hand_side)
    ]

    for column in range(size):
        pivot = next(
            (row for row in range(column, size) if augmented[row][column]),
            None,
        )
        if pivot is None:
            raise ValueError("singular linear system")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]

        pivot_value = augmented[column][column]
        augmented[column] = [entry / pivot_value for entry in augmented[column]]

        for row in range(size):
            if row == column:
                continue
            multiplier = augmented[row][column]
            if multiplier:
                augmented[row] = [
                    augmented[row][col] - multiplier * augmented[column][col]
                    for col in range(size + 1)
                ]

    return [augmented[row][-1] for row in range(size)]


def fit_geometric_model(
    x: Fraction, start_n: int | None = None, q: Fraction = Q
) -> List[Fraction]:
    r"""Recover [up(x), B_1,...,B_R] from R+1 exact prefix values.

    The fitted model is

        up_n(x) = up(x) + sum_{r=1}^R B_r q^{r n}.
    """

    x = Fraction(x)
    depth = dyadic_depth(x)
    order = depth // 2
    if start_n is None:
        start_n = depth
    if start_n < depth:
        raise ValueError("the theorem only guarantees the model for start_n >= depth")

    samples = [up_prefix_value(start_n + j, x) for j in range(order + 1)]
    matrix = [
        [Fraction(1)] + [q ** (r * (start_n + j)) for r in range(1, order + 1)]
        for j in range(order + 1)
    ]
    return solve_fraction_system(matrix, samples)


def bernoulli_number(n: int) -> Fraction:
    """Return B_n exactly by the Akiyama--Tanigawa recurrence.

    This implementation uses the B_1=+1/2 convention.  Only even Bernoulli
    numbers are used below, so the B_1 convention is immaterial.
    """

    if n < 0:
        raise ValueError("n must be nonnegative")
    work = [Fraction(0) for _ in range(n + 1)]
    for m in range(n + 1):
        work[m] = Fraction(1, m + 1)
        for j in range(m, 0, -1):
            work[j - 1] = j * (work[j - 1] - work[j])
    return work[0]


def reciprocal_tail_cumulant(k: int) -> Fraction:
    r"""Return c_k for base 2 in Phi(z)=exp(sum_{k>=1} c_k z^k)."""

    if k < 1:
        raise ValueError("k must be positive")
    bernoulli = bernoulli_number(2 * k)
    numerator = (-1) ** (k + 1) * 2 ** (2 * k - 1) * bernoulli
    denominator = k * factorial(2 * k) * (4**k - 1)
    return numerator / denominator


def reciprocal_tail_alphas(max_order: int) -> List[Fraction]:
    r"""Return alpha_0,...,alpha_max_order by the exact Bell recurrence.

      alpha_0=1,
      r alpha_r = sum_{k=1}^r k c_k alpha_{r-k}.
    """

    if max_order < 0:
        raise ValueError("max_order must be nonnegative")
    alpha = [Fraction(1)]
    for r in range(1, max_order + 1):
        value = sum(
            (k * reciprocal_tail_cumulant(k) * alpha[r - k]
             for k in range(1, r + 1)),
            Fraction(0),
        ) / r
        alpha.append(value)
    return alpha


def inferred_even_derivatives(coefficients: Sequence[Fraction]) -> List[Fraction]:
    r"""Infer up^(2r)(x) from fitted B_r and the theoretical alpha_r.

    Since B_r=(-1)^r alpha_r 4^{-r} up^(2r)(x),

        up^(2r)(x)=(-1)^r 4^r B_r/alpha_r.
    """

    order = len(coefficients) - 1
    alpha = reciprocal_tail_alphas(order)
    return [
        (-1) ** r * 4**r * Fraction(coefficients[r]) / alpha[r]
        for r in range(1, order + 1)
    ]


def format_fraction(value: Fraction) -> str:
    """Format a rational compactly for the text report."""

    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def format_model(x: Fraction, coefficients: Sequence[Fraction], start_n: int) -> str:
    """Format the recovered exact model in a human-readable line."""

    parts = [format_fraction(coefficients[0])]
    for r, coefficient in enumerate(coefficients[1:], start=1):
        sign = "+" if coefficient >= 0 else "-"
        magnitude = abs(coefficient)
        base = 4**r
        parts.append(
            f" {sign} ({format_fraction(magnitude)})*({base}^(-n))"
        )
    return f"x={x}: up_n(x) = {''.join(parts)}, n >= {start_n}"


def verify_point(x: Fraction, extra_levels: int = 5) -> Tuple[Fraction, List[Fraction]]:
    """Run all exact checks at one dyadic point and return the fitted data."""

    x = Fraction(x)
    depth = dyadic_depth(x)
    order = depth // 2
    coefficients = fit_geometric_model(x, depth)
    limit_value = coefficients[0]

    # Check the one-line q-binomial formula on several overlapping blocks.
    for start in range(depth, depth + extra_levels + 1):
        block = [up_prefix_value(start + j, x) for j in range(order + 1)]
        extracted = extrapolate_limit(block)
        assert extracted == limit_value, (x, start, extracted, limit_value)

    # Check the complete fitted geometric formula at additional levels.
    for n in range(depth, depth + order + extra_levels + 2):
        predicted = coefficients[0] + sum(
            (coefficients[r] * Q ** (r * n) for r in range(1, order + 1)),
            Fraction(0),
        )
        actual = up_prefix_value(n, x)
        assert predicted == actual, (x, n, predicted, actual)

    # Check the annihilating moments of the q-binomial weights.
    weights = extrapolation_weights(order)
    assert sum(weights, Fraction(0)) == 1
    for r in range(1, order + 1):
        assert sum(
            (weights[j] * Q ** (j * r) for j in range(order + 1)),
            Fraction(0),
        ) == 0

    return limit_value, coefficients


def verification_grid(max_depth: int) -> Iterable[Fraction]:
    """Generate all reduced dyadics in [0,1] through the requested depth."""

    yield Fraction(0)
    yield Fraction(1)
    for depth in range(1, max_depth + 1):
        denominator = 2**depth
        for numerator in range(1, denominator, 2):
            yield Fraction(numerator, denominator)


def build_report(max_depth: int) -> str:
    """Run the exact checks and return a reproducible text report."""

    lines: List[str] = []
    lines.append("Exact dyadic Rvachev extrapolation verification")
    lines.append("=" * 52)
    lines.append("")
    lines.append("Q = 1/4")
    lines.append("")

    lines.append("First reciprocal-tail coefficients alpha_r:")
    alpha = reciprocal_tail_alphas(5)
    for r, value in enumerate(alpha):
        lines.append(f"  alpha_{r} = {format_fraction(value)}")
    lines.append("")

    lines.append("First q-binomial extrapolation filters:")
    for order in range(1, 4):
        weights = extrapolation_weights(order)
        lines.append(
            f"  R={order}: " + ", ".join(format_fraction(w) for w in weights)
        )
    lines.append("")

    examples = [
        Fraction(0),
        Fraction(1, 2),
        Fraction(1, 4),
        Fraction(3, 4),
        Fraction(1, 8),
        Fraction(1, 16),
        Fraction(3, 16),
        Fraction(5, 16),
        Fraction(1, 32),
    ]
    lines.append("Selected exact models:")
    for x in examples:
        _, coefficients = verify_point(x)
        lines.append("  " + format_model(x, coefficients, dyadic_depth(x)))
        derivatives = inferred_even_derivatives(coefficients)
        if derivatives:
            derivative_text = ", ".join(
                f"up^({2*r})={format_fraction(value)}"
                for r, value in enumerate(derivatives, start=1)
            )
            lines.append("      inferred derivatives: " + derivative_text)
    lines.append("")

    count = 0
    for x in verification_grid(max_depth):
        verify_point(x, extra_levels=3)
        # Evenness gives the same test for -x; explicitly verify it too.
        if x:
            verify_point(-x, extra_levels=3)
            count += 2
        else:
            count += 1
    lines.append(
        f"All exact checks passed at {count} signed dyadic points "
        f"of depth <= {max_depth}."
    )
    lines.append("No floating-point arithmetic was used.")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-depth",
        type=int,
        default=6,
        help="verify every signed dyadic point through this denominator depth (default: 6)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="optional path for the text report; stdout is always printed",
    )
    args = parser.parse_args()
    if args.max_depth < 0:
        parser.error("--max-depth must be nonnegative")

    report = build_report(args.max_depth)
    print(report, end="")
    if args.output is not None:
        args.output.write_text(report, encoding="utf-8")


if __name__ == "__main__":
    main()
