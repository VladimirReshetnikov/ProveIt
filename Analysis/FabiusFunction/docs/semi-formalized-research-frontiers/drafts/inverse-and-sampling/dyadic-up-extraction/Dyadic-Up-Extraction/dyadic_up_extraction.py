#!/usr/bin/env python3
"""Exact experiments for dyadic samples of finite Rvachev up splines.

The Fourier transform convention used throughout is

    f_hat(t) = integral_R f(x) exp(-2*pi*i*t*x) dx.

For n >= 0, ``up_n`` is the inverse Fourier transform of

    product_{k=0}^n sinc(pi*t/2^k).

Consequently ``up_n`` is the density of a sum of independent centered
uniform random variables whose widths are 1, 1/2, ..., 1/2^n.  The explicit
inclusion--exclusion formula implemented below is therefore an exact rational
formula at every dyadic argument.

For a reduced dyadic x = a/2^r in [-1,1], the article proves that, for every
n >= r,

    up_n(x) = up(x) + sum_{ell=1}^{floor(r/2)} A_ell(x) * rho**(ell*(n+1)),
    rho = 1/4.

The constant term can be recovered from floor(r/2)+1 consecutive samples by
one quarter-base q-Pochhammer / Gaussian-binomial row.  All routines in this
file use ``fractions.Fraction``; no floating-point approximation is involved.

Typical invocations:

    python dyadic_up_extraction.py
    python dyadic_up_extraction.py --x 1/16
    python dyadic_up_extraction.py --x 3/32 --start 7 --check-through 12

The direct finite-spline evaluator has exponential cost O(2^n), which is
entirely adequate for verification at the modest levels used in the paper.
It is not intended to replace the faster bit-recursive exact evaluators in the
ProveIt corpus.
"""

from __future__ import annotations

import argparse
import math
from fractions import Fraction
from functools import lru_cache
from typing import Iterable, Sequence


RHO = Fraction(1, 4)


def is_power_of_two(n: int) -> bool:
    """Return whether positive integer *n* is a power of two."""

    return n > 0 and (n & (n - 1)) == 0


def parse_fraction(text: str) -> Fraction:
    """Parse an integer, decimal, or ``numerator/denominator`` exactly."""

    try:
        return Fraction(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError(f"not a rational number: {text!r}") from exc


def dyadic_level(x: Fraction) -> int:
    """Return r for a reduced dyadic x=a/2^r.

    ``Fraction`` keeps its argument in lowest terms, so this is simply the
    base-two logarithm of the denominator.  Integers, including 0 and +/-1,
    have level 0.
    """

    x = Fraction(x)
    denominator = x.denominator
    if not is_power_of_two(denominator):
        raise ValueError(f"{x} is not dyadic: denominator {denominator} is not a power of 2")
    return denominator.bit_length() - 1


def positive_part_power(y: Fraction, degree: int) -> Fraction:
    """Return (y_+)^degree for degree >= 1."""

    if degree < 1:
        raise ValueError("positive_part_power is used only for positive degrees")
    return y**degree if y > 0 else Fraction(0)


@lru_cache(maxsize=None)
def up_prefix_value(x: Fraction, n: int) -> Fraction:
    r"""Evaluate the finite sinc-prefix spline ``up_n(x)`` exactly.

    For n >= 1, convolution of n+1 centered boxes gives

      up_n(x) = 2^(n(n+1)/2)/n! *
        sum_{j=0}^{2^(n+1)-1} (-1)^popcount(j)
          (x + 1 - 2^(-n-1) - j/2^n)_+^n.

    At n=0 the inverse transform is the unit-height box on [-1/2,1/2].
    The half-height convention at its two jump points is the symmetric Fourier
    inversion value; it does not affect any later convolution.
    """

    x = Fraction(x)
    if n < 0:
        raise ValueError("n must be nonnegative")

    if n == 0:
        half = Fraction(1, 2)
        if -half < x < half:
            return Fraction(1)
        if x == -half or x == half:
            return Fraction(1, 2)
        return Fraction(0)

    shifted_x = x + 1 - Fraction(1, 2 ** (n + 1))
    alternating_sum = Fraction(0)
    mesh_denominator = 2**n

    for j in range(2 ** (n + 1)):
        argument = shifted_x - Fraction(j, mesh_denominator)
        if argument <= 0:
            # As j increases the argument decreases, so all remaining terms
            # also vanish.  This early exit is useful near the left endpoint.
            break
        sign = -1 if j.bit_count() & 1 else 1
        alternating_sum += sign * argument**n

    normalization = Fraction(2 ** (n * (n + 1) // 2), math.factorial(n))
    return normalization * alternating_sum


def q_pochhammer_self(q: Fraction, n: int) -> Fraction:
    r"""Return (q;q)_n = product_{k=1}^n (1-q^k)."""

    if n < 0:
        raise ValueError("n must be nonnegative")
    product = Fraction(1)
    for k in range(1, n + 1):
        product *= 1 - q**k
    return product


def q_binomial(n: int, k: int, q: Fraction) -> Fraction:
    r"""Return the Gaussian coefficient [n choose k]_q by q-Pochhammers."""

    if k < 0 or k > n:
        return Fraction(0)
    return q_pochhammer_self(q, n) / (
        q_pochhammer_self(q, k) * q_pochhammer_self(q, n - k)
    )


def extraction_weight(order: int, sample_index: int, q: Fraction = RHO) -> Fraction:
    r"""Weight of q_{N+sample_index} in the exact limit-extraction row.

    For 0 <= j <= m,

      lambda_{m,j}(q) =
        (-1)^(m-j) q^binom(m-j+1,2) / ((q;q)_j (q;q)_{m-j}).

    These are the Lagrange cardinal weights for evaluating at zero a
    polynomial known at the geometric nodes 1,q,...,q^m.
    """

    m = order
    j = sample_index
    if not 0 <= j <= m:
        raise ValueError("sample_index must lie between 0 and order")
    exponent = (m - j) * (m - j + 1) // 2
    sign = -1 if (m - j) & 1 else 1
    return Fraction(sign) * q**exponent / (
        q_pochhammer_self(q, j) * q_pochhammer_self(q, m - j)
    )


def extraction_weight_q_binomial(
    order: int, sample_index: int, q: Fraction = RHO
) -> Fraction:
    """Equivalent Gaussian-binomial form of :func:`extraction_weight`."""

    m = order
    j = sample_index
    exponent = (m - j) * (m - j + 1) // 2
    sign = -1 if (m - j) & 1 else 1
    return (
        Fraction(sign)
        * q**exponent
        * q_binomial(m, j, q)
        / q_pochhammer_self(q, m)
    )


def extract_limit_from_samples(
    samples: Sequence[Fraction], q: Fraction = RHO
) -> Fraction:
    """Extract the constant term from m+1 consecutive geometric samples."""

    if not samples:
        raise ValueError("at least one sample is required")
    m = len(samples) - 1
    return sum(
        (extraction_weight(m, j, q) * Fraction(value) for j, value in enumerate(samples)),
        Fraction(0),
    )


@lru_cache(maxsize=None)
def recover_up_value(x: Fraction) -> Fraction:
    """Recover the exact value up(x) at a dyadic x in [-1,1].

    The guaranteed first valid spline level is N=r, where r is the reduced
    dyadic denominator exponent.  The number of correction modes is m=floor(r/2),
    so m+1 samples suffice.
    """

    x = Fraction(x)
    if x < -1 or x > 1:
        return Fraction(0)
    r = dyadic_level(x)
    m = r // 2
    samples = tuple(up_prefix_value(x, r + j) for j in range(m + 1))
    return extract_limit_from_samples(samples)


def polynomial_add(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    """Add coefficient lists in increasing-power order."""

    length = max(len(a), len(b))
    result = [Fraction(0)] * length
    for i, value in enumerate(a):
        result[i] += value
    for i, value in enumerate(b):
        result[i] += value
    return result


def polynomial_scale(a: Sequence[Fraction], scalar: Fraction) -> list[Fraction]:
    """Multiply a polynomial coefficient list by a scalar."""

    return [Fraction(scalar) * value for value in a]


def polynomial_multiply(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    """Multiply coefficient lists in increasing-power order."""

    if not a or not b:
        return []
    result = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, left in enumerate(a):
        for j, right in enumerate(b):
            result[i + j] += left * right
    return result


def interpolate_geometric_polynomial(
    samples: Sequence[Fraction], q: Fraction = RHO
) -> list[Fraction]:
    r"""Interpolate R(z) from R(q^j)=samples[j], 0 <= j <= m.

    The returned list is ``[z^0]R, [z^1]R, ..., [z^m]R``.  It provides not
    only the limiting value R(0), but every decaying-mode coefficient.
    """

    if not samples:
        raise ValueError("at least one sample is required")
    m = len(samples) - 1
    nodes = [q**j for j in range(m + 1)]
    result = [Fraction(0)] * (m + 1)

    for j, value in enumerate(samples):
        numerator = [Fraction(1)]
        denominator = Fraction(1)
        for k, node in enumerate(nodes):
            if k == j:
                continue
            numerator = polynomial_multiply(numerator, [-node, Fraction(1)])
            denominator *= nodes[j] - node
        basis = polynomial_scale(numerator, Fraction(value) / denominator)
        result = polynomial_add(result, basis)

    return result


def recover_mode_coefficients(
    x: Fraction, start: int | None = None, q: Fraction = RHO
) -> tuple[Fraction, list[Fraction], tuple[Fraction, ...]]:
    r"""Recover up(x) and the A_ell in the eventual expansion.

    If N=``start``, interpolation first finds C_ell in

      q_{N+j} = up(x) + sum C_ell * (q^j)^ell.

    Since C_ell=A_ell*q^(ell*(N+1)), the routine rescales them back to the
    normalization used in the theorem.
    """

    x = Fraction(x)
    r = dyadic_level(x)
    m = r // 2
    n0 = r if start is None else start
    if n0 < r:
        raise ValueError(f"the guaranteed model begins at n=r={r}; got start={n0}")

    samples = tuple(up_prefix_value(x, n0 + j) for j in range(m + 1))
    polynomial = interpolate_geometric_polynomial(samples, q)
    limit = polynomial[0]
    mode_coefficients = [
        polynomial[ell] / q ** (ell * (n0 + 1)) for ell in range(1, m + 1)
    ]
    return limit, mode_coefficients, samples


@lru_cache(maxsize=None)
def bernoulli_number(n: int) -> Fraction:
    r"""Return the Bernoulli number B_n with B_1=-1/2.

    Only even Bernoulli numbers enter the up-law cumulants, but the standard
    recurrence is short and keeps the implementation self-contained.
    """

    if n < 0:
        raise ValueError("n must be nonnegative")
    if n == 0:
        return Fraction(1)
    return -sum(
        (Fraction(math.comb(n + 1, k)) * bernoulli_number(k) for k in range(n)),
        Fraction(0),
    ) / Fraction(n + 1)


def up_cumulant(order: int) -> Fraction:
    r"""Return the order-*order* cumulant of the Rvachev up density.

    Odd cumulants vanish.  For order 2m,

      kappa_{2m} = B_{2m}/(2m*(1-4^{-m})).
    """

    if order < 0:
        raise ValueError("order must be nonnegative")
    if order == 0:
        raise ValueError("there is no order-zero cumulant in this convention")
    if order & 1:
        return Fraction(0)
    m = order // 2
    return bernoulli_number(order) / (order * (1 - RHO**m))


@lru_cache(maxsize=None)
def reciprocal_mgf_coefficient(order: int) -> Fraction:
    r"""Return gamma_order in 1/M(z)=sum gamma_j*z^j/j!.

    If kappa_j are the cumulants, reciprocal exponential-series inversion gives

      gamma_0 = 1,
      gamma_n = -sum_{j=1}^n binom(n-1,j-1) kappa_j gamma_{n-j}.
    """

    if order < 0:
        raise ValueError("order must be nonnegative")
    if order == 0:
        return Fraction(1)
    return -sum(
        (
            Fraction(math.comb(order - 1, j - 1))
            * up_cumulant(j)
            * reciprocal_mgf_coefficient(order - j)
            for j in range(1, order + 1)
        ),
        Fraction(0),
    )


def thue_morse_sign(index: int) -> int:
    """Return (-1)^s_2(index)."""

    return -1 if index.bit_count() & 1 else 1


def up_derivative_at_dyadic(x: Fraction, order: int) -> Fraction:
    r"""Evaluate an up derivative at a dyadic point exactly.

    Repeated differentiation of

      up'(x)=2(up(2x+1)-up(2x-1))

    gives the finite Thue--Morse stencil

      up^(m)(x) = 2^binom(m+1,2) sum_{j<2^m} (-1)^s_2(j)
                    up(2^m*x + 2^m-1-2j).

    Every argument is again dyadic, and :func:`recover_up_value` supplies its
    exact rational value.  Terms outside [-1,1] vanish and are skipped.
    """

    x = Fraction(x)
    if order < 0:
        raise ValueError("order must be nonnegative")
    if order == 0:
        return recover_up_value(x)

    total = Fraction(0)
    dilation = 2**order
    for j in range(dilation):
        argument = dilation * x + dilation - 1 - 2 * j
        if -1 <= argument <= 1:
            total += thue_morse_sign(j) * recover_up_value(Fraction(argument))
    return Fraction(2 ** (order * (order + 1) // 2)) * total


def theoretical_mode_coefficients(x: Fraction) -> list[Fraction]:
    r"""Compute A_ell=gamma_{2ell} up^(2ell)(x)/(2ell)! exactly."""

    x = Fraction(x)
    m = dyadic_level(x) // 2
    return [
        reciprocal_mgf_coefficient(2 * ell)
        * up_derivative_at_dyadic(x, 2 * ell)
        / math.factorial(2 * ell)
        for ell in range(1, m + 1)
    ]


def predicted_prefix_value(
    limit: Fraction, modes: Sequence[Fraction], n: int, q: Fraction = RHO
) -> Fraction:
    """Evaluate the finite geometric expansion at spline level n."""

    return Fraction(limit) + sum(
        (Fraction(coefficient) * q ** (ell * (n + 1))
         for ell, coefficient in enumerate(modes, start=1)),
        Fraction(0),
    )


def characteristic_polynomial(order: int, q: Fraction = RHO) -> list[Fraction]:
    r"""Return coefficients of product_{ell=0}^order (z-q^ell)."""

    polynomial = [Fraction(1)]
    for ell in range(order + 1):
        polynomial = polynomial_multiply(polynomial, [-q**ell, Fraction(1)])
    return polynomial


def recurrence_residual(x: Fraction, n: int, q: Fraction = RHO) -> Fraction:
    r"""Check the order-(m+1) recurrence induced by roots 1,q,...,q^m."""

    x = Fraction(x)
    m = dyadic_level(x) // 2
    coefficients = characteristic_polynomial(m, q)
    return sum(
        (coefficients[j] * up_prefix_value(x, n + j)
         for j in range(m + 2)),
        Fraction(0),
    )


def common_integer_row(values: Iterable[Fraction]) -> tuple[list[int], int]:
    """Scale rational row entries to coprime integer numerators / denominator."""

    values = list(values)
    common_denominator = 1
    for value in values:
        common_denominator = math.lcm(common_denominator, value.denominator)
    integers = [int(value * common_denominator) for value in values]
    common_factor = 0
    for value in integers:
        common_factor = math.gcd(common_factor, abs(value))
    common_factor = max(common_factor, 1)
    return [value // common_factor for value in integers], common_denominator // common_factor


def print_fraction_sequence(label: str, values: Sequence[Fraction]) -> None:
    """Pretty-print a sequence of exact rationals."""

    print(f"{label}:")
    for index, value in enumerate(values):
        print(f"  [{index}] {value}")


def run_single_example(x: Fraction, start: int | None, check_through: int | None) -> None:
    """Print a complete exact analysis for one dyadic argument."""

    x = Fraction(x)
    if not -1 <= x <= 1:
        raise ValueError("x must lie in [-1,1]")
    r = dyadic_level(x)
    m = r // 2
    n0 = r if start is None else start
    if n0 < r:
        raise ValueError(f"start must be at least the dyadic level r={r}")

    limit, interpolated_modes, samples = recover_mode_coefficients(x, n0)
    direct_limit = recover_up_value(x)
    theoretical_modes = theoretical_mode_coefficients(x)
    weights = [extraction_weight(m, j) for j in range(m + 1)]
    gaussian_weights = [extraction_weight_q_binomial(m, j) for j in range(m + 1)]
    integer_row, integer_denominator = common_integer_row(weights)

    print(f"x = {x}")
    print(f"reduced dyadic level r = {r}")
    print(f"number of geometric correction modes m = floor(r/2) = {m}")
    print(f"first guaranteed valid level N = {n0}")
    print_fraction_sequence("consecutive spline samples q_(N+j)", samples)
    print_fraction_sequence("q-Pochhammer extraction weights", weights)
    print(f"same row as integers: {integer_row} / {integer_denominator}")
    print(f"extracted up(x) = {limit}")
    print(f"independent default-start extraction = {direct_limit}")
    print(f"weight formulas agree with Gaussian-binomial form: {weights == gaussian_weights}")
    print_fraction_sequence("interpolated A_ell", interpolated_modes)
    print_fraction_sequence("derivative/deconvolution A_ell", theoretical_modes)
    print(f"the two coefficient constructions agree: {interpolated_modes == theoretical_modes}")

    last = check_through if check_through is not None else n0 + max(4, m + 2)
    print("eventual-expansion and recurrence checks:")
    for n in range(n0, last + 1):
        actual = up_prefix_value(x, n)
        predicted = predicted_prefix_value(limit, interpolated_modes, n)
        residual = recurrence_residual(x, n)
        print(
            f"  n={n:2d}: q_n={actual}; model residual={actual-predicted}; "
            f"recurrence residual={residual}"
        )


def run_default_suite() -> None:
    """Run the exact examples tabulated in the accompanying article."""

    examples = [
        Fraction(1, 4),
        Fraction(1, 8),
        Fraction(1, 16),
        Fraction(3, 16),
        Fraction(1, 32),
        Fraction(5, 32),
    ]

    print("Exact dyadic up-spline extraction suite")
    print("=======================================")
    print()
    for x in examples:
        r = dyadic_level(x)
        m = r // 2
        limit, modes, samples = recover_mode_coefficients(x, r)
        weights = [extraction_weight(m, j) for j in range(m + 1)]
        row, denominator = common_integer_row(weights)
        print(f"x={x:>5}; r={r}; m={m}; up(x)={limit}")
        print(f"  samples n={r}..{r+m}: {', '.join(str(v) for v in samples)}")
        print(f"  extraction row: {row}/{denominator}")
        print(f"  modes A_ell: {', '.join(str(v) for v in modes) if modes else '(none)'}")
        assert modes == theoretical_mode_coefficients(x)
        for n in range(r, r + 4):
            assert up_prefix_value(x, n) == predicted_prefix_value(limit, modes, n)
            assert recurrence_residual(x, n) == 0
        print("  exact checks: PASS")
        print()

    print("First reciprocal-mgf coefficients gamma_(2 ell)")
    print("------------------------------------------------")
    for ell in range(0, 7):
        order = 2 * ell
        gamma = reciprocal_mgf_coefficient(order)
        ordinary = gamma / math.factorial(order)
        print(f"gamma_{order} = {gamma}; gamma_{order}/{order}! = {ordinary}")

    print()
    print("Quarter-base extraction rows")
    print("----------------------------")
    for m in range(0, 6):
        weights = [extraction_weight(m, j) for j in range(m + 1)]
        row, denominator = common_integer_row(weights)
        print(f"m={m}: {row}/{denominator}")


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--x",
        type=parse_fraction,
        help="a dyadic rational in [-1,1]; omit to run the article's full suite",
    )
    parser.add_argument(
        "--start",
        type=int,
        help="first spline level N (default: the reduced dyadic level r)",
    )
    parser.add_argument(
        "--check-through",
        type=int,
        help="last spline level printed in the verification table",
    )
    return parser


def main() -> None:
    args = build_argument_parser().parse_args()
    if args.x is None:
        run_default_suite()
    else:
        run_single_example(args.x, args.start, args.check_through)


if __name__ == "__main__":
    main()
