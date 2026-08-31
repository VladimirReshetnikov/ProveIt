#!/usr/bin/env python3
"""Reproducible experiments for the inverse-Fabius computability report.

The proof in the accompanying report is exact and does not depend on floating
point experiments.  This script illustrates three of its constructive pieces:

1. exact rational evaluation of the centered finite Thue--Morse spline S_N;
2. the certified uniform estimate |S_N(x) - F(x)| <= 2^(-N);
3. the elementary lower and upper bounds on F(2^(-r)) that squeeze the
   binary inverse-continuity modulus to r^2/2 + r log_2(r) + O(r).

All core calculations use fractions.Fraction.  Consequently the printed spline
values, errors against the three exact dyadic values included below, and the
finite-spline interval-mass check are exact rational computations.  Decimal
columns are only human-readable renderings of those exact values.

The naive spline formula has 2^N summands.  That is entirely adequate for the
small verification orders used here, but it is intentionally *not* presented
as an efficient production evaluator.  The ProveIt repository contains much
better exact dyadic recurrences and primitive-recursive natural-number code.

Run:
    python inverse_fabius_computability_experiments.py

Optional:
    python inverse_fabius_computability_experiments.py --max-r 20 --order 10
"""

from __future__ import annotations

import argparse
import math
from fractions import Fraction
from typing import Iterable, Tuple


def thue_morse_sign(j: int) -> int:
    """Return (-1)^(s_2(j)), where s_2 is binary digit sum."""

    if j < 0:
        raise ValueError("j must be nonnegative")
    return -1 if j.bit_count() & 1 else 1


def positive_part(x: Fraction) -> Fraction:
    """Exact positive part max(x, 0)."""

    return x if x > 0 else Fraction(0)


def centered_fabius_spline(order: int, x: Fraction) -> Fraction:
    r"""Evaluate the centered order-``order`` Fabius spline exactly.

    Let X_N = sum_{k=1}^N 2^{-k} U_k with independent U_k uniform on [0,1].
    The centered truncation is Q_N = X_N + 2^{-N-1}.  Its CDF is

        S_N(x) = 2^{N(N+1)/2}/N! * sum_{j=0}^{2^N-1}
                 (-1)^{s_2(j)}
                 (x - (2j+1)/2^{N+1})_+^N.

    Every operation is rational when x is rational.  The infinite Fabius CDF
    F satisfies the rigorous all-real estimate

        |S_N(x) - F(x)| <= 2^{-N}.

    The estimate follows because the omitted random tail differs from its mean
    by at most 2^{-N-1}, while every finite CDF has density bounded by 2.
    """

    if order <= 0:
        raise ValueError("order must be positive")

    x = Fraction(x)
    denominator = 1 << (order + 1)
    coefficient = Fraction(1 << (order * (order + 1) // 2), math.factorial(order))

    total = Fraction(0)
    # Terms with breakpoint >= x vanish.  The simple loop is kept explicit to
    # make the inclusion--exclusion/Thue--Morse structure easy to inspect.
    for j in range(1 << order):
        displacement = x - Fraction(2 * j + 1, denominator)
        if displacement > 0:
            total += thue_morse_sign(j) * displacement**order
    return coefficient * total


def centered_spline_interval(order: int, x: Fraction) -> Tuple[Fraction, Fraction]:
    """Return a certified interval containing F(x).

    The interval is obtained directly from |S_N(x)-F(x)| <= 2^{-N} and is
    clipped to the CDF range [0,1].
    """

    approximation = centered_fabius_spline(order, x)
    error = Fraction(1, 1 << order)
    return max(Fraction(0), approximation - error), min(Fraction(1), approximation + error)


def elementary_endpoint_lower_bound(r: int) -> Fraction:
    r"""Return the report's explicit lower bound Delta_r <= F(2^{-r}).

    Put m=r+1.  Restrict the first m independent uniforms by

        U_k <= 2^{k-r-1}/m,  k=1,...,m.

    Their weighted contribution is then at most 2^{-r-1}; the entire remaining
    tail is at most another 2^{-r-1}.  The probability of this box event is

        Delta_r = 2^{-r(r+1)/2} (r+1)^{-(r+1)}.
    """

    if r < 0:
        raise ValueError("r must be nonnegative")
    denominator = (1 << (r * (r + 1) // 2)) * (r + 1) ** (r + 1)
    return Fraction(1, denominator)


def flatness_endpoint_upper_bound(r: int) -> Fraction:
    r"""Return F(2^{-r}) <= 2^{-r(r-1)/2}/r! for r>=1.

    Iterating F'(x)=2F(2x) gives

        F^{(r)}(x)=2^{r(r+1)/2} F(2^r x) <= 2^{r(r+1)/2}

    on 0<=x<=2^{-r}.  Taylor's integral remainder at the flat endpoint then
    yields F(x)<=2^{r(r+1)/2}x^r/r!, and x=2^{-r} gives this bound.
    """

    if r <= 0:
        raise ValueError("r must be positive")
    denominator = (1 << (r * (r - 1) // 2)) * math.factorial(r)
    return Fraction(1, denominator)


def log2_reciprocal(q: Fraction) -> float:
    """Floating rendering of log_2(1/q) for a positive exact rational q."""

    if q <= 0:
        raise ValueError("q must be positive")
    # Separate numerator and denominator to avoid converting a tiny Fraction
    # to float before taking the logarithm.
    return math.log2(q.denominator) - math.log2(q.numerator)


def print_modulus_table(max_r: int) -> None:
    """Print the rigorous two-sided endpoint/modulus table."""

    print("\nEndpoint mass and binary-modulus bounds")
    print("r | Delta_r (lower) | -log2 Delta_r | flatness upper | -log2 upper")
    print("--+-----------------+---------------+----------------+------------")
    for r in range(1, max_r + 1):
        lower = elementary_endpoint_lower_bound(r)
        upper = flatness_endpoint_upper_bound(r)
        if lower > upper:
            raise AssertionError("the proved lower bound exceeded the proved upper bound")
        print(
            f"{r:2d} | {float(lower):.8e} | {log2_reciprocal(lower):13.6f} | "
            f"{float(upper):.8e} | {log2_reciprocal(upper):10.6f}"
        )


def print_spline_convergence(orders: Iterable[int]) -> None:
    """Compare exact centered splines with three exact Fabius dyadic values."""

    exact_values = {
        Fraction(1, 2): Fraction(1, 2),
        Fraction(1, 4): Fraction(5, 72),
        Fraction(1, 8): Fraction(1, 288),
    }

    print("\nExact centered-spline convergence")
    print("N | x   | S_N(x)                 | |S_N-F|       | certified 2^-N")
    print("--+-----+------------------------+---------------+----------------")
    for order in orders:
        for x, exact in exact_values.items():
            approximation = centered_fabius_spline(order, x)
            actual_error = abs(approximation - exact)
            certified_error = Fraction(1, 1 << order)
            if actual_error > certified_error:
                raise AssertionError("certified centered-spline error was violated")
            print(
                f"{order:2d} | {str(x):3s} | {float(approximation):.16e} | "
                f"{float(actual_error):.8e} | {float(certified_error):.8e}"
            )


def verify_finite_interval_mass(order: int, grid_bits: int, h: Fraction) -> None:
    r"""Check the endpoint-minimum interval-mass law for S_N on a dyadic grid.

    The theorem in the report is analytic and concerns the limiting Fabius CDF:

        min_{0<=x<=1-h} [F(x+h)-F(x)] = F(h).

    The same conclusion holds for every centered finite convolution because
    its density is also symmetric and unimodal.  Here we verify the identity
    exactly on a finite dyadic grid.  This is a consistency check, not the
    proof: the continuous theorem follows by differentiating the interval-mass
    function and using unimodality.
    """

    if not (0 < h <= 1):
        raise ValueError("h must lie in (0,1]")
    denominator = 1 << grid_bits
    h_steps = h * denominator
    if h_steps.denominator != 1:
        raise ValueError("h must lie on the selected dyadic grid")

    endpoint_mass = centered_fabius_spline(order, h) - centered_fabius_spline(order, Fraction(0))
    minimum_mass: Fraction | None = None
    minimizers: list[Fraction] = []

    for i in range(denominator - h_steps.numerator + 1):
        x = Fraction(i, denominator)
        mass = centered_fabius_spline(order, x + h) - centered_fabius_spline(order, x)
        if minimum_mass is None or mass < minimum_mass:
            minimum_mass = mass
            minimizers = [x]
        elif mass == minimum_mass:
            minimizers.append(x)

    if minimum_mass != endpoint_mass:
        raise AssertionError("finite interval-mass minimum was not the endpoint mass")

    reflected_endpoint = Fraction(1) - h
    if Fraction(0) not in minimizers or reflected_endpoint not in minimizers:
        raise AssertionError("the two symmetric endpoints were not both minimizers")

    print("\nFinite-spline interval-mass check")
    print(f"order N          : {order}")
    print(f"grid             : multiples of 2^-{grid_bits}")
    print(f"interval length h: {h}")
    print(f"minimum mass     : {minimum_mass} ~= {float(minimum_mass):.16e}")
    print(f"endpoint mass    : {endpoint_mass} ~= {float(endpoint_mass):.16e}")
    print(f"minimizers       : {', '.join(str(x) for x in minimizers)}")


def print_small_tolerant_bisection_demo(order: int = 12) -> None:
    r"""Demonstrate a certified tolerant comparison at one modest scale.

    The full proof algorithm chooses a target spatial tolerance h=2^{-r}, a
    positive mass threshold Delta_r, and a spline order N so that 2^{-N} is a
    small fraction of Delta_r.  It then compares F(c) with the target y only
    when the certified intervals are disjoint; otherwise the inverse-modulus
    theorem certifies that c is already close enough.

    To keep this script fast, the demonstration uses r=2, hence h=1/4 and
    Delta_2=1/216.  Order 12 has error 2^{-12}<Delta_2/8.  The target y=1/10
    is rational, so its name error is zero in this illustrative run.
    """

    r = 2
    h = Fraction(1, 1 << r)
    delta = elementary_endpoint_lower_bound(r)
    spline_error = Fraction(1, 1 << order)
    if not spline_error < delta / 8:
        raise ValueError("increase order: the demonstration needs 2^-N < Delta_2/8")

    y = Fraction(1, 10)
    left, right = Fraction(0), Fraction(1)
    transcript: list[str] = []

    # Four steps are enough to make the bracket width 1/16 < h even if the
    # near-target branch is never taken.
    for step in range(4):
        c = (left + right) / 2
        s = centered_fabius_spline(order, c)
        f_lo, f_hi = max(Fraction(0), s - spline_error), min(Fraction(1), s + spline_error)

        if f_lo > y:
            right = c
            decision = "inverse lies left"
        elif f_hi < y:
            left = c
            decision = "inverse lies right"
        else:
            # In the general proof this branch is triggered by a symmetric
            # approximate-difference test and the Delta_r inverse modulus.
            decision = "comparison unresolved; modulus says midpoint is close"
            left = max(Fraction(0), c - h)
            right = min(Fraction(1), c + h)
            transcript.append(
                f"step {step}: c={c}, F(c) in [{f_lo}, {f_hi}], {decision}"
            )
            break

        transcript.append(f"step {step}: c={c}, F(c) in [{f_lo}, {f_hi}], {decision}")

    print("\nCertified comparison/bisection demonstration")
    for line in transcript:
        print(line)
    print(f"final containing interval: [{left}, {right}]")
    print(f"width                    : {right-left} ~= {float(right-left):.8e}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-r", type=int, default=12, help="largest endpoint scale in the modulus table")
    parser.add_argument("--order", type=int, default=8, help="finite spline order for the interval-mass grid check")
    parser.add_argument("--grid-bits", type=int, default=8, help="dyadic grid denominator exponent")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.max_r < 1:
        raise SystemExit("--max-r must be positive")
    if args.order <= 0:
        raise SystemExit("--order must be positive")
    if args.grid_bits < 3:
        raise SystemExit("--grid-bits must be at least 3")

    print_modulus_table(args.max_r)
    print_spline_convergence((4, 8, 12))
    verify_finite_interval_mass(args.order, args.grid_bits, Fraction(1, 8))
    print_small_tolerant_bisection_demo(order=12)


if __name__ == "__main__":
    main()
