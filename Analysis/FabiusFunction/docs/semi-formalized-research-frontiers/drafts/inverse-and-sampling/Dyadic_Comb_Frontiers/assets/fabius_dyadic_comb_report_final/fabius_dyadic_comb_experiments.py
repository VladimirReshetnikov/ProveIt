#!/usr/bin/env python3
"""Exact and high-precision experiments for dyadic-comb sums.

This script accompanies the report

    Dyadic-Comb Quadrature for the Fabius and Rvachev Functions

and is intentionally self-contained.  Exact arithmetic uses only Python's
standard library.  The optional fractional-power experiments use ``mpmath``.

Main identities checked by the program
--------------------------------------

1. Rvachev shifted-comb exactness.  If h = 2^{-m}, then

       h * sum_k (h(k+theta))^p up(h(k+theta))

   equals the p-th moment of ``up`` for every p <= m and every shift theta.
   The code tests dyadic shifts exactly (other shifts would require a
   non-dyadic point evaluator).

2. Fabius right-comb stabilization.  For p in N_0 and
   m >= tau(p), where tau(0)=0 and tau(p)=2*ceil(p/2) for p>=1,

       h * sum_{a=0}^{2^m} (a h)^p F(a h)
       = [h^{p+1} B_{p+1}(2^m+1) - d_{p+1}] / (p+1).

3. n-fold prefix sums.  Repeated discrete summation produces the binomial
   Cauchy kernel, and at full support the result reduces to finitely many
   exact moments / stabilized Fabius combs.

4. Fractional absolute powers.  The corrected values

       h * sum_{k != 0} |kh|^alpha up(kh)
       - 2*zeta(-alpha)*h^{alpha+1}

   rapidly stabilize as m grows.  This illustrates the singular
   Euler--Maclaurin theorem proved in the report.

The implementation of F(a/2^m) is the exact Thue--Morse/moment formula from
Arias de Reyna and the ProveIt exposition.  It is quadratic in 2^m; depths up
to about 10--12 are appropriate for exact experiments on a typical machine.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from typing import Iterable, List, Sequence, Tuple

try:
    import mpmath as mp  # type: ignore
except ImportError:  # pragma: no cover - optional dependency
    mp = None


def thue_morse_sign(n: int) -> int:
    """Return epsilon_n = (-1)^{s_2(n)}."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return -1 if n.bit_count() & 1 else 1


@lru_cache(maxsize=None)
def centered_moments_c(n_max: int) -> Tuple[Fraction, ...]:
    """Return c_0,...,c_n_max, where c_n = int x^(2n) up(x) dx.

    The recurrence is

      (2n+1)(2^(2n)-1)c_n = sum_{k<n} binom(2n+1,2k)c_k.
    """
    if n_max < 0:
        raise ValueError("n_max must be nonnegative")
    c: List[Fraction] = [Fraction(1)]
    for n in range(1, n_max + 1):
        numerator = sum(Fraction(comb(2 * n + 1, 2 * k)) * c[k]
                        for k in range(n))
        denominator = (2 * n + 1) * (2 ** (2 * n) - 1)
        c.append(numerator / denominator)
    return tuple(c)


@lru_cache(maxsize=None)
def fabius_law_moments_d(n_max: int) -> Tuple[Fraction, ...]:
    """Return d_r = E[Y^r] for the Fabius probability law on [0,1].

    If X has density up(x) on [-1,1] and Y=(X+1)/2, then

      d_r = 2^{-r} sum_{j=0}^{floor(r/2)} binom(r,2j)c_j.
    """
    if n_max < 0:
        raise ValueError("n_max must be nonnegative")
    c = centered_moments_c(n_max // 2)
    out: List[Fraction] = []
    for r in range(n_max + 1):
        s = sum(Fraction(comb(r, 2 * j)) * c[j]
                for j in range(r // 2 + 1))
        out.append(s / (2 ** r))
    return tuple(out)


@lru_cache(maxsize=None)
def bernoulli_numbers(n_max: int) -> Tuple[Fraction, ...]:
    """Return B_0,...,B_n_max with the convention B_1=-1/2."""
    if n_max < 0:
        raise ValueError("n_max must be nonnegative")
    b: List[Fraction] = [Fraction(1)]
    for n in range(1, n_max + 1):
        s = sum(Fraction(comb(n + 1, k)) * b[k] for k in range(n))
        b.append(-s / (n + 1))
    return tuple(b)


def bernoulli_polynomial(n: int, x: Fraction | int) -> Fraction:
    """Evaluate the Bernoulli polynomial B_n(x) exactly."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    xx = Fraction(x)
    b = bernoulli_numbers(n)
    return sum(Fraction(comb(n, k)) * b[k] * xx ** (n - k)
               for k in range(n + 1))


def power_sum(start: int, stop: int, exponent: int) -> Fraction:
    """Return sum_{a=start}^{stop} a^exponent by Bernoulli polynomials."""
    if exponent < 0:
        raise ValueError("exponent must be nonnegative")
    if stop < start:
        return Fraction(0)
    n = exponent + 1
    return (bernoulli_polynomial(n, stop + 1)
            - bernoulli_polynomial(n, start)) / n


@lru_cache(maxsize=None)
def fabius_level(m: int) -> Tuple[Fraction, ...]:
    """Return all exact values F(a/2^m), 0 <= a <= 2^m.

    Formula:

      F(a/2^m) = 2^{-m(m+1)/2}/m! * sum_{r<a} epsilon_r P_m(2a-2r-1),

      P_m(t) = sum_j binom(m,2j)c_j t^{m-2j}.
    """
    if m < 0:
        raise ValueError("m must be nonnegative")
    if m == 0:
        return (Fraction(0), Fraction(1))

    M = 2 ** m
    c = centered_moments_c(m // 2)
    scale = 2 ** (m * (m + 1) // 2) * factorial(m)

    # P_m is needed only at positive odd arguments 1,3,...,2M-1.
    p_values: List[Fraction] = [Fraction(0)] * (M + 1)
    for delta in range(1, M + 1):
        t = 2 * delta - 1
        p_values[delta] = sum(
            Fraction(comb(m, 2 * j)) * c[j] * t ** (m - 2 * j)
            for j in range(m // 2 + 1)
        )

    eps = [thue_morse_sign(r) for r in range(M)]
    values: List[Fraction] = [Fraction(0)]
    for a in range(1, M + 1):
        convolution = sum(eps[r] * p_values[a - r] for r in range(a))
        values.append(convolution / scale)
    return tuple(values)


def fabius_dyadic(m: int, a: int) -> Fraction:
    """Exact F(a/2^m) for 0 <= a <= 2^m."""
    M = 2 ** m
    if not 0 <= a <= M:
        raise ValueError(f"a must satisfy 0 <= a <= {M}")
    return fabius_level(m)[a]


def up_dyadic(m: int, k: int) -> Fraction:
    """Exact up(k/2^m) on its support."""
    M = 2 ** m
    if abs(k) > M:
        return Fraction(0)
    return fabius_level(m)[M - abs(k)]


def moment_mu(p: int) -> Fraction:
    """Return int x^p up(x) dx exactly for p in N_0."""
    if p < 0:
        raise ValueError("p must be nonnegative")
    if p & 1:
        return Fraction(0)
    return centered_moments_c(p // 2)[p // 2]


def tau(p: int) -> int:
    """Stabilization depth for the Fabius right comb."""
    if p < 0:
        raise ValueError("p must be nonnegative")
    if p == 0:
        return 0
    return p if p % 2 == 0 else p + 1


def fabius_right_comb_direct(m: int, p: int) -> Fraction:
    """Compute R_{m,p}=h sum_{a=0}^{2^m}(ah)^p F(ah) exactly."""
    if p < 0:
        raise ValueError("p must be nonnegative")
    M = 2 ** m
    vals = fabius_level(m)
    return sum(Fraction(a, M) ** p * vals[a] for a in range(M + 1)) / M


def fabius_right_comb_stabilized(m: int, p: int) -> Fraction:
    """Closed form valid when m >= tau(p)."""
    if m < tau(p):
        raise ValueError(f"closed form requires m >= tau(p)={tau(p)}")
    M = 2 ** m
    h = Fraction(1, M)
    d = fabius_law_moments_d(p + 1)[p + 1]
    return (h ** (p + 1) * bernoulli_polynomial(p + 1, M + 1) - d) / (p + 1)


def fabius_right_comb_all_depth(m: int, p: int) -> Fraction:
    """All-depth Bernoulli--Thue--Morse formula for natural p.

    This is the integer specialization of the report's Hurwitz-zeta formula.
    It is slower than direct summation but independently checks the algebraic
    reduction obtained by swapping the point-value and comb sums.
    """
    if p < 0:
        raise ValueError("p must be nonnegative")
    M = 2 ** m
    c = centered_moments_c(m // 2)
    scale = Fraction(1, 2 ** (m * (m + 1) // 2) * factorial(m) * M ** (p + 1))
    total = Fraction(0)
    for r in range(M):
        eps = thue_morse_sign(r)
        for j in range(m // 2 + 1):
            degree = m - 2 * j
            base = Fraction(comb(m, 2 * j)) * c[j]
            for ell in range(degree + 1):
                coeff = (comb(degree, ell) * 2 ** ell
                         * (-2 * r - 1) ** (degree - ell))
                ps = power_sum(r + 1, M, p + ell)
                total += eps * base * coeff * ps
    return scale * total


def rvachev_centered_comb(m: int, p: int) -> Fraction:
    """Exact centered comb h sum_k (kh)^p up(kh)."""
    if p < 0:
        raise ValueError("p must be nonnegative")
    M = 2 ** m
    return sum(Fraction(k, M) ** p * up_dyadic(m, k)
               for k in range(-M, M + 1)) / M


def rvachev_absolute_punctured_comb(m: int, p: int) -> Fraction:
    """Exact punctured absolute comb h sum_{k!=0}|kh|^p up(kh)."""
    if p < 0:
        raise ValueError("p must be nonnegative")
    M = 2 ** m
    return sum(Fraction(abs(k), M) ** p * up_dyadic(m, k)
               for k in range(-M, M + 1) if k != 0) / M


def rvachev_absolute_integer_closed(m: int, p: int) -> Fraction:
    """Closed integer-power formula valid for m >= tau(p).

    A_{m,p} = 2 d_{p+1}/(p+1) + 2 zeta(-p) h^{p+1}.
    Here zeta(-p)=-B_{p+1}/(p+1).
    """
    if m < tau(p):
        raise ValueError(f"closed form requires m >= tau(p)={tau(p)}")
    M = 2 ** m
    d = fabius_law_moments_d(p + 1)[p + 1]
    zeta_negative_p = -bernoulli_numbers(p + 1)[p + 1] / (p + 1)
    return 2 * d / (p + 1) + 2 * zeta_negative_p / M ** (p + 1)


def shifted_rvachev_comb_dyadic(m: int, p: int,
                                theta_numerator: int,
                                theta_bits: int) -> Fraction:
    """Exact shifted comb for theta=theta_numerator/2^theta_bits.

    The grid points have denominator 2^(m+theta_bits), so all up-values are
    available through the exact dyadic evaluator.
    """
    if p < 0 or theta_bits < 0:
        raise ValueError("p and theta_bits must be nonnegative")
    den = 2 ** theta_bits
    s = theta_numerator
    M = 2 ** m
    D = M * den

    # Solve -D <= den*k+s <= D for integer k.
    # ceil((-D-s)/den) = -floor((D+s)/den) for a positive denominator.
    k_min = -((D + s) // den)
    # Correct for unusual (non-normalized) shift numerators as a safeguard.
    while den * k_min + s < -D:
        k_min += 1
    while den * (k_min - 1) + s >= -D:
        k_min -= 1
    k_max = (D - s) // den

    total = Fraction(0)
    level = m + theta_bits
    for k in range(k_min, k_max + 1):
        numerator = den * k + s
        x = Fraction(numerator, D)
        total += x ** p * up_dyadic(level, numerator)
    return total / M


def elementary_symmetric(values: Sequence[Fraction], degree: int) -> Fraction:
    """Elementary symmetric polynomial e_degree(values)."""
    if not 0 <= degree <= len(values):
        return Fraction(0)
    e = [Fraction(1)] + [Fraction(0)] * degree
    for value in values:
        for j in range(degree, 0, -1):
            e[j] += value * e[j - 1]
    return e[degree]


def iterated_up_direct(m: int, p: int, order: int) -> Fraction:
    """n-fold prefix sum of x^p up(x), evaluated at the right support edge."""
    if p < 0 or order < 1:
        raise ValueError("p >= 0 and order >= 1 are required")
    M = 2 ** m
    h = Fraction(1, M)
    return h ** order * sum(
        Fraction(comb(M - j + order - 1, order - 1))
        * Fraction(j, M) ** p * up_dyadic(m, j)
        for j in range(-M, M + 1)
    )


def iterated_up_closed(m: int, p: int, order: int) -> Fraction:
    """Moment formula valid for m >= p+order-1."""
    if p < 0 or order < 1:
        raise ValueError("p >= 0 and order >= 1 are required")
    if m < p + order - 1:
        raise ValueError("requires m >= p+order-1")
    h = Fraction(1, 2 ** m)
    constants = [1 + s * h for s in range(1, order)]
    total = Fraction(0)
    for ell in range(order):
        coeff = ((-1) ** ell
                 * elementary_symmetric(constants, order - 1 - ell))
        total += coeff * moment_mu(p + ell)
    return total / factorial(order - 1)


def iterated_fabius_direct(m: int, p: int, order: int) -> Fraction:
    """n-fold prefix sum of x^p F(x), evaluated at x=1."""
    if p < 0 or order < 1:
        raise ValueError("p >= 0 and order >= 1 are required")
    M = 2 ** m
    h = Fraction(1, M)
    vals = fabius_level(m)
    return h ** order * sum(
        Fraction(comb(M - j + order - 1, order - 1))
        * Fraction(j, M) ** p * vals[j]
        for j in range(M + 1)
    )


def iterated_fabius_closed(m: int, p: int, order: int) -> Fraction:
    """Closed formula valid for m >= tau(p+order-1)."""
    if p < 0 or order < 1:
        raise ValueError("p >= 0 and order >= 1 are required")
    required = tau(p + order - 1)
    if m < required:
        raise ValueError(f"requires m >= {required}")
    h = Fraction(1, 2 ** m)
    constants = [1 + s * h for s in range(1, order)]
    total = Fraction(0)
    for ell in range(order):
        coeff = ((-1) ** ell
                 * elementary_symmetric(constants, order - 1 - ell))
        total += coeff * fabius_right_comb_stabilized(m, p + ell)
    return total / factorial(order - 1)


def fraction_to_mpf(value: Fraction):
    """Convert Fraction to mp.mpf without first rounding through float."""
    if mp is None:  # pragma: no cover
        raise RuntimeError("mpmath is required")
    return mp.mpf(value.numerator) / value.denominator


def fractional_corrected_sequence(alpha: str,
                                  depths: Iterable[int],
                                  precision: int = 60):
    """Return corrected absolute-comb values for a real alpha."""
    if mp is None:
        raise RuntimeError("Install mpmath for fractional-power experiments")
    mp.mp.dps = precision
    a = mp.mpf(alpha)
    rows = []
    for m in depths:
        M = 2 ** m
        vals = fabius_level(m)
        raw = mp.mpf("0")
        # up is even; k=M contributes zero but retaining it is harmless.
        for k in range(1, M + 1):
            up_value = fraction_to_mpf(vals[M - k])
            raw += 2 * (mp.mpf(k) / M) ** a * up_value / M
        correction = 2 * mp.zeta(-a) * mp.power(mp.mpf(1) / M, a + 1)
        rows.append((m, raw, correction, raw - correction))
    return rows


def print_exactness_tables(max_p: int = 10) -> None:
    print("Exact moments c_n and Fabius-law moments d_n")
    print("c:", ", ".join(str(x) for x in centered_moments_c(5)))
    print("d:", ", ".join(str(x) for x in fabius_law_moments_d(10)))
    print()

    print("Fabius right-comb stabilization thresholds")
    print(" p | first tested exact m | predicted tau(p)")
    print("---+----------------------+-----------------")
    for p in range(max_p + 1):
        first = None
        for m in range(0, max(max_p, tau(p)) + 1):
            if fabius_right_comb_direct(m, p) == (
                    (Fraction(1, 2 ** m) ** (p + 1)
                     * bernoulli_polynomial(p + 1, 2 ** m + 1)
                     - fabius_law_moments_d(p + 1)[p + 1]) / (p + 1)):
                first = m
                break
        print(f"{p:2d} | {str(first):>20} | {tau(p):>15}")
    print()

    print("Shifted Rvachev exactness and first-failure superconvergence")
    print("m | theta | exact for 0<=p<=m | p=m+1 error")
    print("--+-------+--------------------+----------------")
    shifts = [(0, 0, "0"), (1, 1, "1/2"), (1, 2, "1/4"), (3, 2, "3/4")]
    for m in range(1, 7):
        for num, bits, label in shifts:
            ok = all(shifted_rvachev_comb_dyadic(m, p, num, bits)
                     == moment_mu(p) for p in range(m + 1))
            error = (shifted_rvachev_comb_dyadic(m, m + 1, num, bits)
                     - moment_mu(m + 1))
            print(f"{m:1d} | {label:>5} | {str(ok):>18} | {error}")
    print()

    print("Independent all-depth Bernoulli--Thue--Morse checks")
    for m, p in [(1, 4), (2, 5), (3, 4), (4, 3)]:
        direct = fabius_right_comb_direct(m, p)
        closed = fabius_right_comb_all_depth(m, p)
        print(f"(m,p)=({m},{p}): direct == all-depth formula -> {direct == closed}")
    print()

    print("Iterated-sum checks")
    cases = [(2, 0, 3), (4, 1, 3), (6, 2, 4)]
    for m, p, order in cases:
        up_ok = (m >= p + order - 1 and
                 iterated_up_direct(m, p, order)
                 == iterated_up_closed(m, p, order))
        f_ok = (m >= tau(p + order - 1) and
                iterated_fabius_direct(m, p, order)
                == iterated_fabius_closed(m, p, order))
        print(f"(m,p,n)=({m},{p},{order}): up={up_ok}, F={f_ok}")


def print_fractional_tables() -> None:
    if mp is None:
        print("\nmpmath is not installed; skipping fractional experiments.")
        return
    print("\nFractional-power corrected sequences")
    for alpha in ("0.5", "1.5", "-0.5", "2.5"):
        print(f"\nalpha={alpha}")
        print("m | raw comb | singular correction | corrected value")
        for m, raw, corr, corrected in fractional_corrected_sequence(
                alpha, range(5, 11), precision=70):
            print(f"{m:2d} | {mp.nstr(raw, 24)} | {mp.nstr(corr, 12)} | "
                  f"{mp.nstr(corrected, 30)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-p", type=int, default=10,
                        help="largest integer power in the threshold table")
    parser.add_argument("--skip-fractional", action="store_true",
                        help="skip mpmath-based fractional experiments")
    args = parser.parse_args()

    print_exactness_tables(args.max_p)
    if not args.skip_fractional:
        print_fractional_tables()


if __name__ == "__main__":
    main()
