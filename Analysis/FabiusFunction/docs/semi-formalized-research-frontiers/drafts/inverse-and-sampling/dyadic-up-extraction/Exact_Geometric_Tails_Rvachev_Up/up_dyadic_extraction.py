#!/usr/bin/env python3
"""Exact dyadic extraction for finite-sinc approximants to Rvachev's up-function.

This companion program implements the formulas proved in
``up_dyadic_extraction.tex`` using only Python's standard library.  Every
quantity is represented by ``fractions.Fraction``; no floating-point arithmetic
is used in the theorem checks.

Fourier normalization
---------------------
We use

    hat f(t) = integral_R f(x) exp(-2*pi*i*x*t) dx,
    sinc(z)  = sin(z)/z.

The user-indexed finite approximant ``up_n`` has transform

    product_{k=0}^n sinc(pi*t/2^k).

Thus ``up_n`` contains n+1 box factors and is a spline of degree n.  This is
one index lower than conventions in which ``p_N`` denotes the product of the
first N factors: up_n = p_{n+1}.

Main exact extraction formula
-----------------------------
Let x be an interior dyadic rational, let m be the least nonnegative integer
such that 2^m*x is integral, put d=floor(m/2), and rho=1/4.  For any N >= m,

    up(x) = sum_{i=0}^d w[d,i] * up_{N+i}(x),

where

    w[d,i] = (-1)^(d-i) rho^((d-i)(d-i+1)/2)
             / ((rho;rho)_i (rho;rho)_{d-i}).

The program also computes the Bell--Bernoulli coefficients in the exact law

    up_n(x) = sum_{j=0}^d (-1)^j a_j 4^(-j(n+1)) up^(2j)(x),

and verifies this identity over a configurable finite set of dyadic points.

Typical commands
----------------

    python up_dyadic_extraction.py --examples
    python up_dyadic_extraction.py --verify-level 7
    python up_dyadic_extraction.py --x 1/16

The direct truncated-power evaluator costs O(2^n) rational terms and is meant
as a transparent verification method.  Production code can replace it with
any exact finite-spline evaluator; the q-Pochhammer extraction itself is tiny.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import factorial
from typing import Iterable, Optional, Sequence


RHO = Fraction(1, 4)


def thue_morse_sign(k: int) -> int:
    """Return tau_k = (-1)^s_2(k), where s_2 is binary digit sum."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    # Kernighan's loop keeps the script compatible with Python 3.9, where
    # int.bit_count() is not yet available.
    parity = 0
    while k:
        parity ^= 1
        k &= k - 1
    return -1 if parity else 1


def positive_part_power(x: Fraction, degree: int) -> Fraction:
    """Return (x_+)^degree, with the right-continuous degree-zero convention.

    The only discontinuous approximant is up_0.  Values used by the main
    theorem have N >= m and are continuous except for the harmless x=0 case.
    For the canonical symmetric Fourier value at a jump, use a half-sum
    separately; the exact extraction routine deliberately starts at N >= m.
    """
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    if x <= 0:
        return Fraction(0)
    return Fraction(1) if degree == 0 else x**degree


@lru_cache(maxsize=None)
def finite_up(n: int, x: Fraction) -> Fraction:
    r"""Evaluate the user-indexed spline up_n(x) exactly.

    The exact truncated-power formula is

      up_n(x) = 2^{n(n+1)/2}/n! * sum_{k=0}^{2^{n+1}-1}
                tau_k (x + A_n - k/2^n)_+^n,

    where A_n = 1 - 2^{-n-1}.  Rational x therefore gives a rational result.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    x = Fraction(x)
    degree = n
    support_radius = Fraction((1 << (n + 1)) - 1, 1 << (n + 1))
    mesh = Fraction(1, 1 << n)
    coefficient = Fraction(1 << (n * (n + 1) // 2), factorial(n))

    # Terms after the active cell vanish.  Restricting the loop can be much
    # faster near the left endpoint while preserving the literal formula.
    scaled = (x + support_radius) / mesh
    if scaled <= 0:
        return Fraction(0)
    max_k = min((1 << (n + 1)) - 1, (scaled.numerator - 1) // scaled.denominator)

    total = Fraction(0)
    for k in range(max_k + 1):
        argument = x + support_radius - k * mesh
        total += thue_morse_sign(k) * positive_part_power(argument, degree)
    return coefficient * total


def is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0


def dyadic_level(x: Fraction) -> int:
    """Return the least m >= 0 for which 2^m*x is an integer."""
    x = Fraction(x)
    if not is_power_of_two(x.denominator):
        raise ValueError(f"{x} is not dyadic")
    return x.denominator.bit_length() - 1


def earliest_proved_stage(m: int) -> int:
    """Return the earliest convention-free stage proved in the article.

    The centered-cell theorem starts at n=m.  At odd levels m>=3, the knot
    averaging argument proves the same law already at n=m-1.  For m=1 we
    deliberately return 1 because up_0 is discontinuous and its endpoint
    value depends on the representative chosen for the rectangle.
    """
    if m < 0:
        raise ValueError("m must be nonnegative")
    return m - 1 if (m >= 3 and (m & 1)) else m


def q_pochhammer(q: Fraction, n: int) -> Fraction:
    """Return (q;q)_n = product_{k=1}^n (1-q^k)."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    result = Fraction(1)
    for k in range(1, n + 1):
        result *= 1 - q**k
    return result


def gaussian_q_binomial(n: int, k: int, q: Fraction) -> Fraction:
    r"""Return the Gaussian coefficient [n choose k]_q at rational q."""
    if k < 0 or k > n:
        return Fraction(0)
    return q_pochhammer(q, n) / (q_pochhammer(q, k) * q_pochhammer(q, n - k))


def extraction_weights(d: int, rho: Fraction = RHO) -> list[Fraction]:
    r"""Return the d+1 exact weights that extract the constant geometric mode.

    They satisfy

      sum_i w_i = 1,
      sum_i w_i rho^{j i} = 0  for 1 <= j <= d.
    """
    if d < 0:
        raise ValueError("d must be nonnegative")
    result: list[Fraction] = []
    for i in range(d + 1):
        triangular = (d - i) * (d - i + 1) // 2
        numerator = (-1 if ((d - i) & 1) else 1) * rho**triangular
        denominator = q_pochhammer(rho, i) * q_pochhammer(rho, d - i)
        result.append(numerator / denominator)
    return result


def extract_constant_mode(samples: Sequence[Fraction], rho: Fraction = RHO) -> Fraction:
    """Extract L from samples f_i=L+sum_{j=1}^d C_j rho^{ji}."""
    if not samples:
        raise ValueError("at least one sample is required")
    d = len(samples) - 1
    return sum(w * Fraction(value) for w, value in zip(extraction_weights(d, rho), samples))


@lru_cache(maxsize=None)
def exact_up(x: Fraction, start: Optional[int] = None) -> Fraction:
    """Compute up(x) for dyadic x using the q-Pochhammer extraction theorem."""
    x = Fraction(x)
    if x <= -1 or x >= 1:
        return Fraction(0)
    m = dyadic_level(x)
    d = m // 2
    n0 = m if start is None else start
    if n0 < earliest_proved_stage(m):
        raise ValueError(
            f"the proved extraction law requires start >= {earliest_proved_stage(m)} "
            f"for dyadic level {m}"
        )
    samples = [finite_up(n0 + i, x) for i in range(d + 1)]
    return extract_constant_mode(samples)


def bernoulli_number(n: int) -> Fraction:
    """Return B_n exactly by the Akiyama--Tanigawa triangular algorithm.

    This implementation has B_1=+1/2; only even Bernoulli numbers are used.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    row = [Fraction(0)] * (n + 1)
    for m in range(n + 1):
        row[m] = Fraction(1, m + 1)
        for j in range(m, 0, -1):
            row[j - 1] = j * (row[j - 1] - row[j])
    return row[0]


def reciprocal_sinc_coefficients(count: int) -> list[Fraction]:
    r"""Return a_0,...,a_{count-1} in

      1/Phi(z) = sum_{j>=0} a_j (2*pi*z)^{2j}.

    If

      alpha_j = |B_{2j}|/[2j (2j)! (1-2^{-2j})],

    then exp(sum_{j>=1} alpha_j t^j)=sum_{m>=0} a_m t^m and

      m a_m = sum_{j=1}^m j alpha_j a_{m-j}.
    """
    if count < 1:
        raise ValueError("count must be positive")
    alpha = [Fraction(0)] * count
    for j in range(1, count):
        alpha[j] = abs(bernoulli_number(2 * j)) / (
            2 * j * factorial(2 * j) * (1 - Fraction(1, 2) ** (2 * j))
        )

    a = [Fraction(0)] * count
    a[0] = Fraction(1)
    for m in range(1, count):
        a[m] = sum(j * alpha[j] * a[m - j] for j in range(1, m + 1)) / m
    return a


def up_derivative(order: int, x: Fraction) -> Fraction:
    r"""Evaluate up^{(order)}(x) at a dyadic point exactly.

    Repeated differentiation of

      up'(x)=2(up(2x+1)-up(2x-1))

    gives

      up^{(r)}(x)=2^{r(r+1)/2} sum_{k<2^r} tau_k
                  up(2^r*x+2^r-1-2k).
    """
    if order < 0:
        raise ValueError("order must be nonnegative")
    x = Fraction(x)
    if order == 0:
        return exact_up(x)
    coefficient = 1 << (order * (order + 1) // 2)
    total = Fraction(0)
    scale = 1 << order
    for k in range(scale):
        argument = scale * x + scale - 1 - 2 * k
        total += thue_morse_sign(k) * exact_up(Fraction(argument))
    return coefficient * total


def predicted_finite_up(n: int, x: Fraction) -> Fraction:
    """Evaluate the exact finite geometric law from up and its even jet."""
    x = Fraction(x)
    m = dyadic_level(x)
    if n < earliest_proved_stage(m):
        raise ValueError(
            f"the proved exact law requires n >= {earliest_proved_stage(m)} "
            f"for dyadic level {m}"
        )
    d = m // 2
    a = reciprocal_sinc_coefficients(d + 1)
    return sum(
        (-1 if (j & 1) else 1)
        * a[j]
        * Fraction(1, 4) ** (j * (n + 1))
        * up_derivative(2 * j, x)
        for j in range(d + 1)
    )


@dataclass(frozen=True)
class Example:
    x: Fraction
    start: int
    label: str


def format_fraction(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def print_examples() -> None:
    examples = [
        Example(Fraction(1, 4), 2, "one geometric mode"),
        Example(Fraction(1, 8), 2, "odd binary level; one-stage sharpening"),
        Example(Fraction(1, 16), 4, "two geometric modes"),
    ]
    print("Exact extraction examples\n")
    for example in examples:
        x = example.x
        m = dyadic_level(x)
        d = m // 2
        samples = [finite_up(example.start + i, x) for i in range(d + 1)]
        value = extract_constant_mode(samples)
        print(f"x = {format_fraction(x)} ({example.label}), m={m}, d={d}")
        for i, sample in enumerate(samples):
            print(f"  q_{example.start + i} = {format_fraction(sample)}")
        print(f"  up(x) = {format_fraction(value)}")
        print(f"  weights = {[format_fraction(w) for w in extraction_weights(d)]}")
        print()


def verify(max_level: int, extra_stages: int = 3) -> None:
    """Exhaustively verify the exact law for all reduced dyadics to max_level."""
    if max_level < 0:
        raise ValueError("max_level must be nonnegative")
    checked_points = 0
    checked_identities = 0

    # x=0 is the sole interior point of exact level zero.
    levels: Iterable[tuple[int, list[Fraction]]] = [(0, [Fraction(0)])]
    dynamic_levels = []
    for m in range(1, max_level + 1):
        denominator = 1 << m
        points = [Fraction(p, denominator) for p in range(-denominator + 1, denominator, 2)]
        dynamic_levels.append((m, points))
    levels = list(levels) + dynamic_levels

    for m, points in levels:
        d = m // 2
        weights = extraction_weights(d)
        # Check the defining Vandermonde annihilation identities once per level.
        assert sum(weights) == 1
        for j in range(1, d + 1):
            assert sum(weights[i] * RHO ** (j * i) for i in range(d + 1)) == 0

        for x in points:
            checked_points += 1
            # The q-Pochhammer extraction must be invariant under sliding the
            # sample window once the guaranteed onset N=m has been reached.
            reference = exact_up(x)
            for n0 in range(m, m + extra_stages + 1):
                samples = [finite_up(n0 + i, x) for i in range(d + 1)]
                assert extract_constant_mode(samples) == reference
                checked_identities += 1

            # Verify the stronger Bell--Bernoulli differential formula at
            # several consecutive stages.
            for n in range(m, m + extra_stages + 1):
                direct = finite_up(n, x)
                predicted = predicted_finite_up(n, x)
                assert direct == predicted, (m, x, n, direct, predicted)
                checked_identities += 1

            # At odd levels m>=3, verify the additional knot-stage identity
            # n=m-1 and the extraction window beginning there.
            if m >= 3 and (m & 1):
                early = m - 1
                early_samples = [finite_up(early + i, x) for i in range(d + 1)]
                assert extract_constant_mode(early_samples) == reference
                assert finite_up(early, x) == predicted_finite_up(early, x)
                checked_identities += 2

    print(
        f"Verified {checked_identities} exact identities at {checked_points} "
        f"interior dyadic points through binary level {max_level}."
    )
    print("All arithmetic was rational; no tolerance was used.")


def parse_fraction(text: str) -> Fraction:
    try:
        return Fraction(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def inspect_point(x: Fraction, start: Optional[int] = None) -> None:
    x = Fraction(x)
    if not (-1 <= x <= 1):
        raise ValueError("x must lie in [-1,1]")
    if abs(x) == 1:
        print(f"up({format_fraction(x)}) = 0 (endpoint)")
        return
    m = dyadic_level(x)
    d = m // 2
    n0 = m if start is None else start
    if n0 < earliest_proved_stage(m):
        raise ValueError(
            f"--start must be at least {earliest_proved_stage(m)} for this point"
        )
    samples = [finite_up(n0 + i, x) for i in range(d + 1)]
    weights = extraction_weights(d)
    value = extract_constant_mode(samples)

    print(f"x={format_fraction(x)}, exact dyadic level m={m}, d=floor(m/2)={d}")
    print(f"using q_{n0},...,q_{n0+d}")
    for i, (sample, weight) in enumerate(zip(samples, weights)):
        print(
            f"  q_{n0+i}={format_fraction(sample):>24}   "
            f"weight={format_fraction(weight)}"
        )
    print(f"up(x)={format_fraction(value)}")
    if d:
        print("even derivatives and geometric coefficients C_j in q_n=up(x)+sum C_j*4^(-jn):")
        a = reciprocal_sinc_coefficients(d + 1)
        for j in range(1, d + 1):
            derivative = up_derivative(2 * j, x)
            coefficient = (-1 if (j & 1) else 1) * a[j] * RHO**j * derivative
            print(
                f"  j={j}: up^({2*j})(x)={format_fraction(derivative)}, "
                f"C_{j}={format_fraction(coefficient)}"
            )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--examples", action="store_true", help="print the article's exact examples")
    parser.add_argument(
        "--verify-level",
        type=int,
        metavar="M",
        help="verify all reduced interior dyadics of exact level at most M",
    )
    parser.add_argument("--x", type=parse_fraction, help="inspect one dyadic point, e.g. 1/16")
    parser.add_argument("--start", type=int, help="first finite stage N for --x (default: m)")
    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    requested = False
    if args.examples:
        requested = True
        print_examples()
    if args.verify_level is not None:
        requested = True
        verify(args.verify_level)
    if args.x is not None:
        requested = True
        inspect_point(args.x, args.start)
    if not requested:
        parser.print_help()


if __name__ == "__main__":
    main()
