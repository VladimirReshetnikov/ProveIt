#!/usr/bin/env python3
"""Exact rational reference programs for the iPRA Stirling manuscript.

All mathematical calculations use integers and fractions.Fraction.
This is executable reference code, NOT a formal iPRA proof or Lean proof.
The manuscript supplies the mathematical proofs of the interval claims.
Every loop has an explicit finite bound; no numerical convergence test or
unbounded search is used. Python's reduced Fraction representation is only
a convenient implementation of the unreduced rational-pair algorithms.
"""

from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
from math import isqrt
from typing import Tuple

Interval = Tuple[F, F]


def dyadic(p: int) -> F:
    """2**(-p), for a nonnegative precision parameter."""
    if p < 0:
        raise ValueError("precision must be nonnegative")
    return F(1, 1 << p)


def bit_length(n: int) -> int:
    """Least b <= n+1 with n < 2**b, including b(0)=0."""
    if n < 0:
        raise ValueError("natural number required")
    return n.bit_length()


def exponent(a: int, b: int) -> int:
    """Largest i <= a with 2**i*b <= a, for a >= b > 0.

    If d=bit_length(a)-bit_length(b), the desired value is d or d-1;
    one exact comparison chooses it. This equals the manuscript's bounded
    scan and avoids iterating up to a potentially enormous numerator.
    """
    if not a >= b > 0:
        raise ValueError("requires a >= b > 0")
    k = a.bit_length() - b.bit_length()
    return k - int((b << k) > a)


@lru_cache(maxsize=None)
def log_series(z: F, terms: int) -> F:
    """2 sum_{0 <= j < terms} z**(2*j+1)/(2*j+1)."""
    if terms < 0:
        raise ValueError("nonnegative term count required")
    z = F(z)
    total, power, square = F(0), z, z * z
    for j in range(terms):
        total += power / (2 * j + 1)
        power *= square
    return 2 * total


def log_series_tail(z: F, terms: int) -> F:
    """Explicit absolute tail bound, valid for abs(z)<1."""
    z = abs(F(z))
    if not 0 <= z < 1 or terms < 0:
        raise ValueError("requires abs(z)<1 and nonnegative term count")
    return 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))


@lru_cache(maxsize=None)
def log_core(q: F, precision: int) -> F:
    """Range-reduced lower logarithm approximant for q>=1."""
    q = F(q)
    if q < 1 or precision < 0:
        raise ValueError("requires q>=1 and nonnegative precision")
    k = exponent(q.numerator, q.denominator)
    y = q / (1 << k)
    terms = precision + k + 4
    return k * log_series(F(1, 3), terms) + log_series((y - 1) / (y + 1), terms)


@lru_cache(maxsize=None)
def log_approx(q: F, precision: int) -> F:
    """Total rational log algorithm; nonpositive inputs return zero."""
    q = F(q)
    if precision < 0:
        raise ValueError("nonnegative precision required")
    if q <= 0:
        return F(0)
    return log_core(q, precision) if q >= 1 else -log_core(1 / q, precision)


@lru_cache(maxsize=None)
def log_interval(q: F, precision: int) -> Interval:
    """Rational log enclosure justified by the finite geometric-tail lemma.

    Unlike log_approx, this interface rejects nonpositive logarithm inputs.
    """
    q = F(q)
    if q <= 0 or precision < 0:
        raise ValueError("requires positive q and nonnegative precision")
    if q < 1:
        low, high = log_interval(1 / q, precision)
        return -high, -low
    k = exponent(q.numerator, q.denominator)
    y = q / (1 << k)
    terms = precision + k + 4
    low = log_core(q, precision)
    tail = k * log_series_tail(F(1, 3), terms)
    tail += log_series_tail((y - 1) / (y + 1), terms)
    return low, low + tail


@lru_cache(maxsize=None)
def pi_approx(precision: int) -> F:
    """4 times finite arctangent sums at 1/2 and 1/3."""
    if precision < 0:
        raise ValueError("nonnegative precision required")
    total, a, b, sign = F(0), F(1, 2), F(1, 3), 1
    for j in range(precision + 4):
        total += sign * (a + b) / (2 * j + 1)
        a /= 4
        b /= 9
        sign = -sign
    return 4 * total


@lru_cache(maxsize=None)
def pi_interval(precision: int) -> Interval:
    """Alternating-series enclosure for the independently defined pi."""
    terms = precision + 4
    value = pi_approx(precision)
    tail = 4 * (F(1, 2) ** (2 * terms + 1) + F(1, 3) ** (2 * terms + 1))
    tail /= 2 * terms + 1
    return (value, value + tail) if terms % 2 == 0 else (value - tail, value)


@lru_cache(maxsize=None)
def stirling_approx(n: int, precision: int) -> F:
    """Q(n,p) from the manuscript, approximating the log remainder."""
    if n < 0 or precision < 0:
        raise ValueError("natural-number arguments required")
    if n == 0:
        return F(0)
    r = precision + bit_length(n) + 4
    return (
        sum((log_approx(F(j), r) for j in range(1, n + 1)), F(0))
        - (F(n) + F(1, 2)) * log_approx(F(n), r)
        + n
        - F(1, 2) * log_approx(2 * pi_approx(r), r)
    )


def stirling_test(n: int, precision: int) -> bool:
    """The concrete finite predicate, with n=0 accepted by convention."""
    if n < 0 or precision < 0:
        raise ValueError("natural-number arguments required")
    if n == 0:
        return True
    q, error = stirling_approx(n, precision), dyadic(precision)
    return F(1, 12 * n + 1) - error <= q <= F(1, 12 * n) + error


@lru_cache(maxsize=None)
def stirling_interval(n: int, precision: int) -> Interval:
    """Independent interval propagation for the actual log remainder.

    The bounds use both endpoints of pi_interval, rather than treating the
    computed pi approximation as the exact constant. This supplies a
    separate numerical validation of Q's advertised approximation budget.
    """
    if n < 1 or precision < 0:
        raise ValueError("requires n>=1 and nonnegative precision")
    r = precision + bit_length(n) + 4
    bounds = [log_interval(F(j), r) for j in range(1, n + 1)]
    low = sum((x[0] for x in bounds), F(0))
    high = sum((x[1] for x in bounds), F(0))
    logn_low, logn_high = bounds[-1]
    coefficient = F(n) + F(1, 2)
    pi_low, pi_high = pi_interval(r)
    logpi_low = log_interval(2 * pi_low, r)[0]
    logpi_high = log_interval(2 * pi_high, r)[1]
    return (
        low - coefficient * logn_high + n - logpi_high / 2,
        high - coefficient * logn_low + n - logpi_low / 2,
    )


def wallis_product(m: int) -> F:
    """W_m=product_{j=1}^m 4*j*j/(4*j*j-1)."""
    if m < 0:
        raise ValueError("natural number required")
    result = F(1)
    for j in range(1, m + 1):
        result *= F(4 * j * j, 4 * j * j - 1)
    return result


def wallis_integrand(k: int, t: F) -> F:
    """F_k(t)=2/(1+t^2)*(2*t/(1+t^2))^k."""
    return 2 / (1 + t * t) * (2 * t / (1 + t * t)) ** k


def wallis_antiderivative(k: int, t: F) -> F:
    """G_k(t)=(1-t^2)/(1+t^2)*(2*t/(1+t^2))^(k-1)."""
    if k < 1:
        raise ValueError("requires k>=1")
    return (1 - t * t) / (1 + t * t) * (2 * t / (1 + t * t)) ** (k - 1)


@lru_cache(maxsize=None)
def wallis_sum(k: int, mesh: int) -> F:
    """I_k(N), the left rational Riemann sum with N terms."""
    if k < 0 or mesh < 1:
        raise ValueError("requires k>=0 and mesh>=1")
    return sum((wallis_integrand(k, F(j, mesh)) for j in range(mesh)), F(0)) / mesh


def wallis_error_constant(m: int) -> int:
    """D_m=16*2^m*(m+1)^2."""
    if m < 0:
        raise ValueError("natural number required")
    return 16 * (1 << m) * (m + 1) ** 2


def factorial(n: int) -> int:
    """Factorial by an explicitly bounded product."""
    if n < 0:
        raise ValueError("natural number required")
    value = 1
    for j in range(1, n + 1):
        value *= j
    return value


@lru_cache(maxsize=None)
def e_approx(precision: int) -> F:
    """E_t=sum_{j=0}^{t+2} 1/j!."""
    if precision < 0:
        raise ValueError("nonnegative precision required")
    total, term = F(1), F(1)
    for j in range(1, precision + 3):
        term /= j
        total += term
    return total


def e_tail(precision: int) -> F:
    """Geometric bound for the positive tail after degree t+2."""
    first = F(1, factorial(precision + 3))
    return first / (1 - F(1, precision + 4))


def sqrt_lower(q: F, precision: int) -> F:
    """floor(sqrt(floor(q*2^(2t))))/2^t.

    Integer isqrt is an exact convenience implementation of a bounded
    integer search; both bounding-square inequalities are checked below.
    """
    q = F(q)
    if q < 0 or precision < 0:
        raise ValueError("nonnegative arguments required")
    scaled = q * (1 << (2 * precision))
    return F(isqrt(scaled.numerator // scaled.denominator), 1 << precision)


@lru_cache(maxsize=None)
def ratio_approx(n: int, precision: int) -> F:
    """Direct rational approximation to n! e^n/(n^n sqrt(2*pi*n))."""
    if n < 0 or precision < 0:
        raise ValueError("natural-number arguments required")
    if n == 0:
        return F(1)
    t = precision + 4 * n + 2
    denominator_root = sqrt_lower(2 * n * pi_approx(t), t)
    return factorial(n) * e_approx(t) ** n / (n ** n * denominator_root)


def ratio_test(n: int, precision: int) -> bool:
    if n < 0 or precision < 0:
        raise ValueError("natural-number arguments required")
    if n == 0:
        return True
    q, error = ratio_approx(n, precision), dyadic(precision)
    return 1 + F(1, 12 * n + 1) - error <= q <= 1 + F(1, 12 * n - 1) + error


@lru_cache(maxsize=None)
def ratio_interval(n: int, precision: int) -> Interval:
    """Independent positive interval propagation for the exact ratio."""
    if n < 1 or precision < 0:
        raise ValueError("requires n>=1 and nonnegative precision")
    t = precision + 4 * n + 2
    pi_low, pi_high = pi_interval(t)
    root_low = sqrt_lower(2 * n * pi_low, t)
    root_high = sqrt_lower(2 * n * pi_high, t) + dyadic(t)
    low_e = e_approx(t)
    high_e = low_e + e_tail(t)
    scale = F(factorial(n), n ** n)
    return scale * low_e ** n / root_high, scale * high_e ** n / root_low


if __name__ == "__main__":
    import argparse
    from decimal import Decimal, localcontext

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("precision", type=int, nargs="?", default=12)
    args = parser.parse_args()
    value = stirling_approx(args.n, args.precision)
    print("Finite rational predicate:", stirling_test(args.n, args.precision))
    with localcontext() as context:
        context.prec = 30
        print("Q(n,p), decimal display only:", Decimal(value.numerator) / Decimal(value.denominator))
