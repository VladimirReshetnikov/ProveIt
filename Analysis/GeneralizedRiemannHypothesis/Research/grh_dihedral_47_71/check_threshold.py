"""Certify Lambda_1(1/2)/Lambda_2(1/2) at level 47. Python 3.8+."""
from fractions import Fraction as Q
from math import isqrt
import json


GRID = 10**18
CUTOFF = 28
TAYLOR_DEGREE = 122  # even, so its partial sum bounds exp(-x) above


def down(x):
    return Q(x.numerator * GRID // x.denominator, GRID)


def up(x):
    return -down(-x)


def root(x):
    k = isqrt(x.numerator * GRID**2 // x.denominator)
    return Q(k, GRID), Q(k + 1, GRID)


def atan_inv(n):
    # Alternating Taylor bounds for arctan(1/n), n >= 5.
    terms = [Q((-1)**k, (2*k+1)*n**(2*k+1)) for k in range(32)]
    return sum(terms), sum(terms[:-1])


def pi_bounds():
    a, b = atan_inv(5)
    c, d = atan_inv(239)
    # Machin's identity.
    return down(16*a - 4*d), up(16*b - 4*c)


def scaled_product(x, y):
    products = [a*b for a in x for b in y]
    return min(products), max(products)


def gaussian_integral(a, pi):
    """Outward bounds on the integral of exp(-a*v^2) for v >= 1."""
    term = Q(1)
    series = term
    for k in range(1, TAYLOR_DEGREE + 1):
        term *= -a/k
        series += term/(2*k+1)
    k = TAYLOR_DEGREE + 1
    next_term = -term*a/(k*(2*k+1))
    complete_lo = root(pi[0]/a)[0]/2
    complete_hi = root(pi[1]/a)[1]/2
    return down(complete_lo-series), up(complete_hi-series-next_term)


def theta(a, c):
    # Q(x,y) = a*x^2 + x*y + c*y^2.
    # 4a Q = (2a*x+y)^2+47*y^2, proving the enumeration bounds.
    count = [0]*(CUTOFF+1)
    y_bound = isqrt(4*a*CUTOFF//47)
    for y in range(-y_bound, y_bound+1):
        t = isqrt(4*a*CUTOFF-47*y*y)
        lo = -((t+y)//(2*a))
        hi = (t-y)//(2*a)
        for x in range(lo, hi+1):
            count[a*x*x + x*y + c*y*y] += 1
    return count


def certify():
    pi = pi_bounds()
    d_lo, d_hi = root(Q(47))
    c_lo, c_hi = down(2*pi[0]/d_hi), up(2*pi[1]/d_lo)
    # exp(-c)<41/100 via four positive Taylor terms beyond the constant.
    exp_lower, term = Q(1), Q(1)
    for k in range(1, 5):
        term *= c_lo/k
        exp_lower += term
    r = Q(41, 100)
    assert exp_lower*r > 1
    # n*G(c*n) <= r^n/(2*c) from v^2 >= 1+2(v-1).
    tail = r**(CUTOFF+1)/(2*c_lo*(1-r))
    lower = [-tail, -tail]
    upper = [tail, tail]
    b1, b2, b3 = theta(1,12), theta(2,6), theta(3,4)
    sqrt5 = root(Q(5))
    for n in range(1, CUTOFF+1):
        # Coefficients of the two normalized eigenforms as (A +/- B*sqrt(5))/4.
        A, B = 2*b1[n]-b2[n]-b3[n], b2[n]-b3[n]
        G = gaussian_integral(n*c_hi, pi)[0], gaussian_integral(n*c_lo, pi)[1]
        assert 0 < G[0] <= G[1]
        for j, sign in enumerate((1, -1)):
            coef = sorted((A+sign*B*v)/4 for v in sqrt5)
            lo, hi = scaled_product(coef, G)
            lower[j] += lo
            upper[j] += hi
    lower = [4*x for x in lower]
    upper = [4*x for x in upper]
    assert lower[1] > 0
    C = lower[0]/upper[1], upper[0]/lower[1]
    assert Q(145202449, 10**8) < C[0] <= C[1] < Q(145202450, 10**8)
    return (lower[0], upper[0]), (lower[1], upper[1]), C


def decimal_interval(interval, digits=10):
    scale = 10**digits
    out = []
    for k, v in enumerate(interval):
        a = v.numerator*scale
        z = a//v.denominator if k == 0 else -((-a)//v.denominator)
        out.append(f"{z//scale}.{z%scale:0{digits}d}")
    return out


if __name__ == "__main__":
    first, second, ratio = certify()
    print(json.dumps({"method": "rational interval arithmetic", "cutoff": CUTOFF,
        "taylor_degree": TAYLOR_DEGREE, "Lambda1": decimal_interval(first),
        "Lambda2": decimal_interval(second), "ratio": decimal_interval(ratio)}, indent=2))
