"""Exact enclosures for the two endpoint signs in the logarithmic-integral theorem."""
from fractions import Fraction as Q
from math import factorial

PRECISION = 120
SCALE = 1 << PRECISION


def down(x):
    return Q((x * SCALE).__floor__(), SCALE)


def up(x):
    return Q((x * SCALE).__ceil__(), SCALE)


def unit_log(x):
    """For rational 1 <= x <= 2, use 50 terms in the atanh expansion."""
    assert 1 <= x <= 2
    u = (x - 1) / (x + 1)
    partial = 2 * sum(u ** (2*j+1) / (2*j+1) for j in range(50))
    tail = 2 * u**101 / (101 * (1-u*u))
    return down(partial), up(partial + tail)


LOG2 = unit_log(Q(2))


def log_interval(x):
    x = Q(x)
    assert x > 0
    exponent = x.numerator.bit_length() - x.denominator.bit_length()
    y = x / Q(2)**exponent
    if y < 1:
        exponent -= 1
        y *= 2
    lo, hi = unit_log(y)
    increments = [exponent * v for v in LOG2]
    return lo + min(increments), hi + max(increments)


def series(x, length):
    term = Q(1)
    total = Q(0)
    for j in range(1, length + 1):
        term *= x / j
        total += term / j
    return total


B, K = 32, 256
NEG_SERIES = series(Q(-B), K)
# Both truncations of sum x^j/(j j!) have tail <= 2*B^(K+1)/(K+1)!.
SERIES_ERROR = 4 * Q(B**(K+1), factorial(K+1))
# Integral from -infinity to -B has magnitude <= exp(-B)/B < 2^(-B)/B.
LEFT_ERROR = Q(1, B * 2**B)


def ei_at(t):
    assert 0 < t <= 34
    error = SERIES_ERROR if t <= B else 4 * Q(34**(K+1), factorial(K+1))
    lo, hi = log_interval(t/B)
    # Outward-rounded t^j/j! recurrence. Each term is positive here.
    left_term, right_term = Q(1), Q(1)
    p, q = Q(0), Q(0)
    for j in range(1, K + 1):
        left_term = down(t * left_term / j)
        right_term = up(t * right_term / j)
        p += down(left_term / j)
        q += up(right_term / j)
    return (lo + p - NEG_SERIES - error - LEFT_ERROR,
            hi + q - NEG_SERIES + error)


def endpoint(n):
    lo, hi = log_interval(n)
    # Ei increases on the positive axis.
    f = ei_at(lo)[0], ei_at(hi)[1]
    g = ei_at(lo-1)[0], ei_at(hi-1)[1]
    assert f[0] > 0 and g[0] > 0
    exp1 = sum(Q(1, factorial(j)) for j in range(51))
    return (n*exp1*g[0] - hi*f[1]**2,
            n*(exp1 + Q(2, factorial(51)))*g[1] - lo*f[0]**2)


if __name__ == "__main__":
    # Exact open rational intervals for e*n*Ei(log(n)-1)-log(n)*Ei(log(n))^2.
    for n, lower, upper in [(2417, Q(-437,1000), Q(-435,1000)),
                            (2418, Q(40,1000), Q(42,1000))]:
        low, high = endpoint(n)
        assert lower < low <= high < upper
        print(f"{n}: sign expression in ({lower}, {upper})")
    a, b = log_interval(3)
    assert a > Q(17,16) and -10 < ei_at(a)[0] <= ei_at(b)[1] < 10
    print("Auxiliary bounds log(3) > 17/16 and |li(3)| < 10 verified.")

    a, b = log_interval(2)
    assert -4 < ei_at(a)[0] <= ei_at(b)[1] < 4
    print("Auxiliary bound |li(2)| < 4 verified.")
