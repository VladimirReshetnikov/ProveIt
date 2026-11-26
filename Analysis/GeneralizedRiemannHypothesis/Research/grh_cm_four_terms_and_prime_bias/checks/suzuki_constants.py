"""Rational enclosures for the constants and logarithms in the Suzuki checks.

All interval endpoints are integer multiples of 1/SCALE. Only the display of
results uses decimal formatting. Mathematical ingredients are Machin's
identity, the logarithm series and the elementary trapezoid error bound.
"""
from fractions import Fraction
from functools import lru_cache

SCALE = 10**12


def ceil_div(n, d):
    return -((-n) // d)


def two_atanh(a, b):
    """Enclose 2 atanh(a/b) on 0 <= a/b <= 1/3."""
    assert 0 <= 3 * a <= b
    lo = hi = 0
    u, v = a, b
    # After 17 terms the tail <= 2*(1/3)^35/(35*(1-1/9)) < 1/SCALE.
    for j in range(17):
        num = 2 * SCALE * u
        den = (2 * j + 1) * v
        lo += num // den
        hi += ceil_div(num, den)
        u *= a*a
        v *= b*b
    return lo, hi + 1


LOG_TWO = two_atanh(1, 3)


@lru_cache(None)
def log_bounds(n):
    k = n.bit_length() - 1
    base = 1 << k
    lo, hi = two_atanh(n - base, n + base)
    return k*LOG_TWO[0] + lo, k*LOG_TWO[1] + hi


def log_ratio_bounds(n, d):
    """Outward bounds for log(n/d) with n >= d > 0."""
    assert n >= d > 0
    k = n.bit_length() - d.bit_length()
    if n < (d << k):
        k -= 1
    den = d << k
    lo, hi = two_atanh(n - den, n + den)
    return k*LOG_TWO[0] + lo, k*LOG_TWO[1] + hi


def atan_unit_fraction(d):
    """Alternating Taylor sums of consecutive lengths enclose atan(1/d)."""
    s = sum((Fraction((-1)**j, (2*j+1)*d**(2*j+1))
             for j in range(16)), Fraction())
    return s, s + Fraction(1, 33*d**33)


@lru_cache(None)
def constant_bounds():
    lo5, hi5 = atan_unit_fraction(5)
    lo239, hi239 = atan_unit_fraction(239)
    pi_lo = (16*lo5 - 4*hi239)*SCALE
    pi_hi = (16*hi5 - 4*lo239)*SCALE
    pi_lo = pi_lo.numerator // pi_lo.denominator
    pi_hi = ceil_div(pi_hi.numerator, pi_hi.denominator)

    n = 1024
    # Write gamma = H_n - log n - 1/(2n) + E. On each [k,k+1],
    # the trapezoid approximation to integral(1/t) has error in
    # [0, max(2/t^3)/12]. Summing for k>=n gives the E bound below.
    harm_lo = sum(SCALE // j for j in range(1, n+1))
    harm_hi = sum(ceil_div(SCALE, j) for j in range(1, n+1))
    ln_lo, ln_hi = log_bounds(n)
    gamma_lo = harm_lo - ln_hi - ceil_div(SCALE, 2*n)
    error_hi = ceil_div(SCALE, 6*n**3) + ceil_div(SCALE, 12*n**2)
    gamma_hi = harm_hi - ln_lo - SCALE//(2*n) + error_hi

    log4_lo = log_ratio_bounds(4*pi_lo, SCALE)[0]
    log4_hi = log_ratio_bounds(4*pi_hi, SCALE)[1]
    log8_lo = log_ratio_bounds(8*pi_lo, SCALE)[0]
    log8_hi = log_ratio_bounds(8*pi_hi, SCALE)[1]
    b_lo = log8_lo + gamma_lo
    b_hi = log8_hi + gamma_hi
    return {
        "pi": (pi_lo, pi_hi),
        "EulerGamma": (gamma_lo, gamma_hi),
        "B": (b_lo, b_hi),
        "S": (2*SCALE + gamma_lo - log4_hi, 2*SCALE + gamma_hi - log4_lo),
        "c": ((pi_lo + 2*b_lo)//4, ceil_div(pi_hi + 2*b_hi, 4)),
        "logH": log_bounds(3*10**12),
    }


if __name__ == "__main__":
    for name, (lo, hi) in constant_bounds().items():
        print(f"{lo}/{SCALE} <= {name} <= {hi}/{SCALE}")
