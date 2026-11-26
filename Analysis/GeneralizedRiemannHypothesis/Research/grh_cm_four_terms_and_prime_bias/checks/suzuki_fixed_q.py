"""Certify the signs of all cumulative fixed-modulus coefficients up to 9999.

Endpoints below are integers in units of 1/SCALE. Arithmetic is outward
rounded. The logarithm power series has a rational remainder bound.
"""
from functools import lru_cache
from math import isqrt

from suzuki_constants import SCALE, ceil_div, constant_bounds, log_bounds

# These coarser intervals also reproduce the cumulative enclosures in the text.
B_LO = 3_801_380_000_000
B_HI = 3_801_400_000_000
b_lo, b_hi = constant_bounds()["B"]
assert B_LO < b_lo <= b_hi < B_HI


@lru_cache(None)
def factor(n):
    ans = []
    d = 2
    while d*d <= n:
        if n % d == 0:
            power = 1
            while n % d == 0:
                n //= d
                power *= d
            ans.append((d, power))
        d += 1
    if n > 1:
        ans.append((n, n))
    return ans


@lru_cache(None)
def phi(n):
    ans = n
    for p, _ in factor(n):
        ans = ans // p * (p - 1)
    return ans


def order_mod(p, m):
    if m == 1:
        return 1
    f = phi(m)
    for d, _ in factor(f):
        while f % d == 0 and pow(p, f // d, m) == 1:
            f //= d
    return f


def coefficient(q):
    lo = B_LO - log_bounds(q)[1]
    hi = B_HI - log_bounds(q)[0]
    euler_lo = euler_hi = 0
    for p, power in factor(q):
        ll, lh = log_bounds(p)
        lo += ll // (p-1)
        hi += ceil_div(lh, p-1)
        m = q // power
        f = order_mod(p, m)
        if f >= 128:  # p^(f/2)-1 >= 2^64-1
            euler_hi += ceil_div(phi(m) * lh, 2**64 - 1)
        else:
            root = isqrt(p**f * SCALE**2)
            euler_lo += (phi(m) * ll * SCALE) // (root+1-SCALE)
            euler_hi += ceil_div(phi(m) * lh * SCALE, root-SCALE)
    return phi(q)*lo//2 + euler_lo, ceil_div(phi(q)*hi, 2) + euler_hi


if __name__ == "__main__":
    lower = upper = 0
    for q in range(3, 10000):
        lo, hi = coefficient(q)
        lower += lo
        upper += hi
        if q < 139:
            assert lower > 0, q
        else:
            assert upper < 0, q
        if q in (3, 138, 139, 9999):
            print(f"Q={q}: {lower}/{SCALE} <= B(Q) <= {upper}/{SCALE}")
    print("Cumulative sign certified for every integer 3 <= Q <= 9999.")
