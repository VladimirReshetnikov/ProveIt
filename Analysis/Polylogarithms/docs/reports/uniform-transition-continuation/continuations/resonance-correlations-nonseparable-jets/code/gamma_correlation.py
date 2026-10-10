"""Periodic log-Gamma correlation using an exact convergent expansion.

The accompanying article proves strict convexity of the autocorrelation
and gives the tail estimate returned here. This module requires mpmath.

The analytic tail estimate bounds omitted series terms. It is not an
interval-arithmetic bound on floating-point roundoff. Set mp.mp.dps to
the desired working precision before calling these functions.
"""

from dataclasses import dataclass
from functools import lru_cache
import mpmath as mp


@dataclass(frozen=True)
class Truncation:
    value: object
    tail_bound: object
    reduced_shift: object
    terms: int


@lru_cache(maxsize=8)
def _coefficients(terms, dps):
    with mp.workdps(dps + 12):
        return tuple(
            2 * (mp.harmonic(2*j-2)*mp.zeta(2*j-1)
                 + mp.diff(mp.zeta, 2*j-1)) / (j*(2*j-1))
            for j in range(2, terms+1)
        )


def squared_increment(a, terms=48):
    """Approximate integral_0^1 (logGamma({x+a})-logGamma(x))**2 dx.

    Periodicity and reflection reduce a to [0, 1/2]. The returned value
    truncates after a**(2*terms). In exact arithmetic it lies above the
    target, and value-tail_bound lies below it.
    """
    if not isinstance(terms, int) or terms < 2:
        raise ValueError('terms must be an integer at least 2')
    a = mp.mpf(a)
    if not mp.isfinite(a):
        raise ValueError('a must be finite and real')
    a -= mp.floor(a)
    a = min(a, 1-a)
    if not a:
        return Truncation(mp.mpf('0'), mp.mpf('0'), a, terms)
    dps = mp.mp.dps
    with mp.workdps(dps + 12):
        L = -mp.log(a)
        leading = a*(L*L + 2*L + 2 + mp.pi**2/3)
        quadratic = (2*mp.stieltjes(1) - mp.pi**2/3)*a*a
        table = _coefficients(terms, dps)
        value = leading + quadratic - mp.fsum(
            coeff*a**(2*j) for j, coeff in enumerate(table, 2)
        )
        bound = (2*mp.zeta(3)*(1+mp.log(2*terms+2))/(terms+1)**2
                 *a**(2*terms+2)/(1-a*a))
    return Truncation(+value, +bound, +a, terms)


def centered_correlation_hurwitz(a):
    """Independent Hurwitz-jet formula for the centered correlation."""
    a = mp.mpf(a)
    a -= mp.floor(a)
    if not a:
        return centered_second_moment()
    h = lambda s: mp.zeta(s, a) + mp.zeta(s, 1-a)
    B2 = a*a-a+mp.mpf(1)/6
    return (-mp.diff(h, -1, 2)/2 - mp.diff(h, -1)
            +(1+mp.pi**2/6)*B2)


def centered_second_moment():
    A = mp.euler + mp.log(2*mp.pi)
    return (mp.diff(mp.zeta, 2, 2)-2*A*mp.diff(mp.zeta, 2)
            +(A*A+mp.pi**2/4)*mp.zeta(2))/(2*mp.pi**2)


def maximum_increment():
    """Exact half-shift formula, evaluated at the current precision."""
    q = mp.log(2)
    A = mp.euler + mp.log(2*mp.pi)
    return ((3*mp.diff(mp.zeta, 2, 2)
             +2*(q-3*A)*mp.diff(mp.zeta, 2))/(2*mp.pi**2)
            +A*A/4-A*q/6-q*q/12+mp.pi**2/16)


def autocorrelation(a, terms=48):
    """Return the log-Gamma autocorrelation and its analytic tail bound.

    In exact arithmetic value lies below the target by at most
    tail_bound. This direction is the opposite of squared_increment.
    """
    inc = squared_increment(a, terms)
    value = (mp.log(2*mp.pi)**2/4 + centered_second_moment()
             - inc.value/2)
    return Truncation(value, inc.tail_bound/2, inc.reduced_shift, terms)


def self_check():
    """Check independent identities; these tests do not replace proofs."""
    import json
    mp.mp.dps = 65
    for a in ['0.125', '0.3', '0.5', '0.91', '-0.3']:
        result = squared_increment(a, terms=100)
        exact = 2*(centered_second_moment()
                   - centered_correlation_hurwitz(a))
        error = abs(result.value-exact)
        # This tolerance concerns numerical consistency at 65 dps, not
        # the mathematical proof of the one-sided analytic tail bound.
        if error > mp.mpf('1e-58') + result.tail_bound:
            raise AssertionError((a, error, result.tail_bound))
        print(json.dumps({'shift':a,
                          'increment':mp.nstr(result.value, 45),
                          'absolute_error':mp.nstr(error, 8),
                          'analytic_tail_bound':mp.nstr(result.tail_bound, 8)}))
    half = squared_increment('0.5', terms=100)
    assert abs(half.value-maximum_increment()) < mp.mpf('1e-58')
    zero = squared_increment(0)
    assert zero.value == zero.tail_bound == 0
    print(json.dumps({'maximum_at_half':mp.nstr(maximum_increment(), 50),
                      'status':'passed'}))


if __name__ == '__main__':
    self_check()
