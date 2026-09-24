"""Exact and asymptotic evaluation of OEIS A277280.

Python 3.9+; exact routines use only the standard library.
High-precision routines import mpmath only when called.
See article.tex for proofs, conventions, and error terms.
"""
from __future__ import annotations

from math import factorial, isqrt
from operator import index
from typing import Iterator, Tuple


def _nonnegative_integer(n: int) -> int:
    if isinstance(n, bool):
        raise TypeError("n must be an integer, not bool")
    try:
        n = index(n)
    except TypeError as exc:
        raise TypeError("n must be an integer") from exc
    if n < 0:
        raise ValueError("n must be nonnegative")
    return n


def maximizing_exponent(n: int) -> int:
    """Return the unique d for which [x**d] H_n(x) is maximal.

    H_n denotes the physicists' Hermite polynomial. Signs are respected.
    The formula uses integer square root: no floating-point rounding.
    """
    n = _nonnegative_integer(n)
    k = (2 * n + 6 - isqrt(8 * n + 21)) // 8
    return n - 4 * k


def a277280(n: int) -> int:
    """Compute one term exactly, without constructing H_n."""
    n = _nonnegative_integer(n)
    d = maximizing_exponent(n)
    m = (n - d) // 2
    return (factorial(n) << d) // (factorial(m) * factorial(d))


def iter_terms(last: int) -> Iterator[Tuple[int, int, int]]:
    """Yield (n, maximizing exponent, a(n)) for 0 <= n <= last.

    Each transition uses a bounded number of integer operations. The
    integers themselves grow, so this is not constant bit-time per term.
    Exact division is checked as an implementation invariant.
    """
    last = _nonnegative_integer(last)
    d, m, value = 0, 0, 1
    yield 0, d, value
    for n in range(last):
        if d * (d + 1) < 2 * n + 7:
            numerator = 2 * (n + 1)
            denominator = d + 1
            next_d, next_m = d + 1, m
        else:
            numerator = (n + 1) * d * (d - 1) * (d - 2)
            denominator = 8 * (m + 1) * (m + 2)
            next_d, next_m = d - 3, m + 2
        value, remainder = divmod(value * numerator, denominator)
        if remainder:
            raise ArithmeticError("nonintegral transition: implementation error")
        d, m = next_d, next_m
        yield n + 1, d, value


def ratio_fraction(n: int) -> Tuple[int, int]:
    """Return an exact (not necessarily reduced) fraction a(n+1)/a(n)."""
    n = _nonnegative_integer(n)
    d = maximizing_exponent(n)
    m = (n - d) // 2
    if d * (d + 1) < 2 * n + 7:
        return 2 * (n + 1), d + 1
    return (n + 1) * d * (d - 1) * (d - 2), 8 * (m + 1) * (m + 2)


def correction_polynomials(delta):
    """Return P1, P2, P3 in log(a(n)/L(n)). Uses mpmath numbers."""
    import mpmath as mp
    z = mp.mpf(delta)
    p1 = mp.mpf(41) / 24 - z * z / 2
    p2 = z**3 / 6 - z*z + mp.mpf(47) * z / 24 - mp.mpf(3) / 4
    p3 = (-z**4 / 12 + z**3 / 3 - mp.mpf(35) * z*z / 24
          + mp.mpf(47) * z / 12 - mp.mpf(8719) / 2880)
    return p1, p2, p3


def log_values(n: int, dps: int = 60):
    """Return (log a(n), log L(n), delta_n), evaluated at high precision.

    n must be positive. Guard digits compensate for cancellation between
    log-gamma values. These are numerical evaluations, not interval
    arithmetic certificates.
    """
    import mpmath as mp
    n = _nonnegative_integer(n)
    if n == 0:
        raise ValueError("the asymptotic normalization L(n) requires n >= 1")
    if not isinstance(dps, int) or dps < 15:
        raise ValueError("dps must be an integer >= 15")
    # log_gamma is of order n log n. bit_length avoids converting huge n
    # to a decimal string just to estimate the needed guard precision.
    guards = (n.bit_length() * 30103) // 100000 + 20
    with mp.workdps(dps + guards):
        d = maximizing_exponent(n)
        m = (n - d) // 2
        s = mp.sqrt(2 * n)
        loga = (mp.loggamma(n + 1) - mp.loggamma(m + 1)
                - mp.loggamma(d + 1) + d * mp.log(2))
        logl = (mp.mpf(n) / 2 * (mp.log(2 * n) - 1) + s
                - mp.mpf(1) / 2 - mp.log(mp.pi) / 2 - mp.log(2 * n) / 4)
        delta = d - s + mp.mpf(3) / 2
        return +loga, +logl, +delta


def stirling_log_enclosure(n: int, dps: int = 60):
    """Numerically evaluate the two analytic bounds in article Section 5.

    The underlying formulas are rigorous inequalities; these returned
    mpf approximations do NOT themselves have directed-rounding guarantees.
    n, m, and d must all be positive.
    """
    import mpmath as mp
    n = _nonnegative_integer(n)
    d = maximizing_exponent(n)
    m = (n - d) // 2
    if min(n, m, d) < 1:
        raise ValueError("requires n, (n-d)/2, and d to be positive")
    guards = (n.bit_length() * 30103) // 100000 + 20
    with mp.workdps(dps + guards):
        def stirling(x: int):
            y = mp.mpf(x)
            return (y + mp.mpf('.5')) * mp.log(y) - y + mp.log(2*mp.pi)/2 + 1/(12*y)
        center = stirling(n) - stirling(m) - stirling(d) + d * mp.log(2)
        lower = center - 1 / (360 * mp.mpf(n)**3)
        upper = center + 1 / (360 * mp.mpf(m)**3) + 1 / (360 * mp.mpf(d)**3)
        return +lower, +upper


if __name__ == "__main__":
    import argparse
    import sys
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--log", action="store_true", help="print logarithmic diagnostics")
    args = parser.parse_args()
    if args.log:
        import mpmath as mp
        mp.mp.dps = 50
        la, ll, delta = log_values(args.n)
        print("d =", maximizing_exponent(args.n))
        print("log(a(n)) =", mp.nstr(la, 50))
        print("a(n)/L(n) =", mp.nstr(mp.exp(la-ll), 40))
        print("delta =", mp.nstr(delta, 40))
    else:
        if hasattr(sys, "set_int_max_str_digits"):
            sys.set_int_max_str_digits(0)
        print(a277280(args.n))
