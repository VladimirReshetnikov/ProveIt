#!/usr/bin/env python3
"""Replay exact critical-Euler and harmonic-defect certificates.

Only the Python standard library is used. Every finite calculation is an
outward integer-grid interval. The infinite tail is the proved critical
signed-measure bound, not a numerical estimate. Run from any directory.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb
from pathlib import Path
import json

DIGITS = 210
S = 10 ** DIGITS
ROOT_CHECKS = 0

def ceildiv(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError('positive denominator required')
    return -((-a) // b)

def iroot(n: int, k: int) -> int:
    """Integer Newton proposal, followed by an exact acceptance inequality."""
    if n < 0 or k < 1:
        raise ValueError('nonnegative radicand and positive degree required')
    if n < 2 or k == 1:
        return n
    x = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    while x ** k > n:
        x -= 1
    while (x + 1) ** k <= n:
        x += 1
    assert x ** k <= n < (x + 1) ** k
    return x

@dataclass(frozen=True)
class IV:
    lo: int
    hi: int
    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError('reversed interval')
    def __add__(self, other: IV) -> IV:
        return IV(self.lo + other.lo, self.hi + other.hi)
    def __sub__(self, other: IV) -> IV:
        return IV(self.lo - other.hi, self.hi - other.lo)
    def times(self, k: int) -> IV:
        return IV(self.lo*k, self.hi*k) if k >= 0 else IV(self.hi*k, self.lo*k)
    def divided(self, k: int) -> IV:
        return IV(self.lo // k, ceildiv(self.hi, k))
    def positive_product(self, other: IV) -> IV:
        if self.lo < 0 or other.lo < 0:
            raise ValueError('positive_product requires nonnegative operands')
        return IV(self.lo*other.lo // S, ceildiv(self.hi*other.hi, S))

ZERO = IV(0, 0)

def rational(x: Fraction) -> IV:
    return IV(S*x.numerator // x.denominator,
              ceildiv(S*x.numerator, x.denominator))

@lru_cache(maxsize=None)
def inverse_power(n: int, exponent: Fraction) -> IV:
    global ROOT_CHECKS
    if n < 1 or exponent < 0:
        raise ValueError('n >= 1 and exponent >= 0 required')
    p, q = exponent.numerator, exponent.denominator
    radicand = n**p * S**q
    r = iroot(radicand, q)
    assert r**q <= radicand < (r+1)**q
    ROOT_CHECKS += 1
    if r**q == radicand:
        return IV(S*S // r, ceildiv(S*S, r))
    return IV(S*S // (r+1), ceildiv(S*S, r))

def coefficients(a: Fraction, b: Fraction, last: int) -> list[IV]:
    c = [ZERO, ZERO]
    h = ZERO
    for n in range(2, last+1):
        h = h + inverse_power(n-1, b)
        c.append(h.positive_product(inverse_power(n, a)))
    return c

def euler(c: list[IV], n: int) -> IV:
    """Exact finite binomial-tail formula, avoiding difference-table growth."""
    if n < 1 or 2*n-1 >= len(c):
        raise ValueError('insufficient coefficients')
    tail = (1 << n)
    total = ZERO
    for j in range(n):
        tail -= comb(n, j)
        total = total + c[2*j+1].times(tail if j % 2 == 0 else -tail)
    return total.divided(1 << n)

def decimal_integer(k: int, digits: int) -> str:
    sign = '-' if k < 0 else ''
    k = abs(k)
    if digits == 0:
        return sign + str(k)
    z = str(k).rjust(digits+1, '0')
    return sign + z[:-digits] + '.' + z[-digits:]

def record(v: IV, digits: int = 30) -> dict[str, str]:
    div = 10 ** (DIGITS-digits)
    lo, hi = v.lo // div, ceildiv(v.hi, div)
    return {'lower': decimal_integer(lo, digits),
            'upper': decimal_integer(hi, digits),
            'width_upper': decimal_integer(hi-lo, digits)}

def run() -> dict:
    K = 256
    rows, actual = [], {}
    orders = [Fraction(1, 10), Fraction(1, 4), Fraction(1, 2),
              Fraction(3, 4), Fraction(9, 10)]
    for a in orders:
        b = 1-a
        c = coefficients(a, b, 2*K-1)
        ek = euler(c, K)
        # 0 < E_K - g < (1/a) 2^{-K}.
        tail = ceildiv(S*a.denominator, a.numerator*(1 << K))
        gi = IV(ek.lo-tail, ek.hi)
        rrows = []
        for N in (1, 8, 16, 32, 64, 128):
            en = euler(c, N)
            rv = (en - gi).times(1 << N)
            assert rv.lo > 0
            actual[(a, N)] = rv
            rrows.append({'N': N, **record(rv)})
        # Positive surplus: Q_n = 1/a - c_n - 1/n.
        qseq = [rational(1/a) - c[n] - rational(Fraction(1, n))
                for n in range(1, 19)]
        diff_tests = 0
        cur = qseq
        for depth in range(7):
            for n in range(min(8, len(cur))):
                assert cur[n].lo > 0, (a, depth, n)
                diff_tests += 1
            cur = [cur[j]-cur[j+1] for j in range(len(cur)-1)]
        rows.append({'a': str(a), 'b': str(b), 'g': record(gi),
                     'scaled_errors': rrows,
                     'strict_surplus_difference_tests': diff_tests})
    reversal = actual[(Fraction(1,2),128)] - actual[(Fraction(1,4),128)]
    original = actual[(Fraction(1,4),1)] - actual[(Fraction(1,2),1)]
    assert reversal.lo > 0 and original.lo > 0
    # Simple, human-readable rational separating intervals.
    lo1, hi1 = Fraction('0.084208864068217362453965253610'), Fraction('0.084208864068217362453965253612')
    lo2, hi2 = Fraction('0.084523512538326867477886761599'), Fraction('0.084523512538326867477886761601')
    for a, lo, hi in [(Fraction(1,4),lo1,hi1),(Fraction(1,2),lo2,hi2)]:
        rv = actual[(a,128)]
        assert rv.lo*lo.denominator > lo.numerator*S
        assert rv.hi*hi.denominator < hi.numerator*S
    return {
        'status': 'PASS', 'arithmetic': 'integer outward intervals; no floating point',
        'grid_decimal_digits': DIGITS, 'reference_euler_depth': K,
        'tail_theorem': '0 < E_K-g < (1/a) 2^(-K), critical line only',
        'root_acceptance_inequalities_checked': ROOT_CHECKS,
        'rows': rows,
        'R128_half_minus_quarter': record(reversal),
        'R1_quarter_minus_half': record(original),
        'interpretation': 'R1 decreases, but fixed-depth R128 need not decrease in a.'
    }

if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O: exact acceptance assertions must remain enabled.')
    result = run()
    out = Path(__file__).resolve().parents[1]/'data'/'exact_certificates.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])
    print('Integer-root checks:', result['root_acceptance_inequalities_checked'])
    print('R128(1/2)-R128(1/4):', result['R128_half_minus_quarter'])
    print('Written:', out)
