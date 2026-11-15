"""Exact rational direction construction, independent of FTA.

The result w satisfies |w| <= 1 and |w**k - c/|c|| <= eps.
See FTA_iPRA.pdf, Section 3, for the finite proof and bounds. This deliberately
uses very generous constants and is a reference implementation, not an efficient
numerical root finder.  No floating point is used by the construction.
"""
from fractions import Fraction as F


def add(z, w):
    return z[0] + w[0], z[1] + w[1]


def mul(z, w):
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def scale(a, z):
    return a * z[0], a * z[1]


def power(z, n):
    # Bounded recursion on n, as in the iPRA definition.
    result = F(1), F(0)
    for _ in range(n):
        result = mul(result, z)
    return result


def norm2(z):
    return z[0] * z[0] + z[1] * z[1]


def dyadic_sqrt_lower(r, t, lower=0, upper=1):
    """t rational bisections, lower <= sqrt(r) <= upper."""
    r, lo, hi = F(r), F(lower), F(upper)
    assert 0 <= lo <= hi and lo * lo <= r <= hi * hi
    for _ in range(t):
        mid = (lo + hi) / 2
        if mid * mid <= r:
            lo = mid
        else:
            hi = mid
    return lo


def direction(c, k, eps=F(1, 16)):
    """Return exact Gaussian rational with certified direction accuracy."""
    x, y = F(c[0]), F(c[1])
    eps = F(eps)
    assert k >= 1 and 0 < eps <= F(1, 16) and (x != 0 or y != 0)
    eta = eps / (k + 1)
    required = F(k + 1) / eps
    ceiling = (required.numerator + required.denominator - 1) // required.denominator
    precision = 12 + ceiling.bit_length()
    t = 8 * precision + 16
    mag = max(abs(x), abs(y))
    X, Y = x / mag, y / mag
    S = dyadic_sqrt_lower(X * X + Y * Y, t, 1, 2)
    A = X / S
    S1 = dyadic_sqrt_lower((1 + A) / 2, t)
    S2 = dyadic_sqrt_lower((1 + S1) / 2, t)
    S3 = dyadic_sqrt_lower((1 + S2) / 2, t)
    T3 = dyadic_sqrt_lower((1 - S2) / 2, t)
    q = S3, (-T3 if y < 0 else T3)
    z = q[0] - 1, q[1]

    count = 8 * k + 4 * precision
    coefficients = [F(1)]
    for j in range(count):
        coefficients.append(coefficients[-1] * (F(1, k) - j) / (j + 1))
    result = F(0), F(0)
    for coefficient in reversed(coefficients):
        result = add(mul(result, z), (coefficient, F(0)))
    u = power(result, 8)
    return scale(1 / (1 + eta), u)


def verify_rational_unit_target(c, absolute_value, k):
    """Exact verification for test inputs whose complex absolute value is rational."""
    c = F(c[0]), F(c[1])
    absolute_value = F(absolute_value)
    assert absolute_value > 0 and norm2(c) == absolute_value ** 2
    eps = F(1, 16)
    w = direction(c, k, eps)
    target = scale(1 / absolute_value, c)
    error = add(power(w, k), scale(F(-1), target))
    assert norm2(w) <= 1
    assert norm2(error) <= eps * eps
    return {"k": k, "c": tuple(map(str, c)), "norm_bound": True,
            "direction_bound": True}


def check_direction(c, k, w, eps=F(1, 16)):
    """An exact rational certificate; no square roots, real numbers, or floats.

    If A=|c|^2, b=|w^k|^2+1-eps^2, d=2 Re(w^k conjugate(c)),
    the desired error bound is equivalent to b sqrt(A) <= d.
    The sufficient conditions below check that inequality by squaring only
    after both sides are known to have nonnegative sign.
    """
    c = F(c[0]), F(c[1])
    w = F(w[0]), F(w[1])
    eps = F(eps)
    assert k >= 1 and eps > 0
    A = norm2(c)
    if A == 0 or norm2(w) > 1:
        return False
    wk = power(w, k)
    b = norm2(wk) + 1 - eps * eps
    d = 2 * (wk[0] * c[0] + wk[1] * c[1])
    return d >= 0 and (b <= 0 or d * d >= b * b * A)


if __name__ == "__main__":
    import json
    tests = [(1, 0, 1, 1), (-1, 0, 1, 1), (3, 4, 5, 2), (3, -4, 5, 3)]
    for x, y, absolute_value, k in tests:
        print(json.dumps(verify_rational_unit_target((x, y), absolute_value, k)), flush=True)
