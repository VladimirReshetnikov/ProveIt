"""Exact finite calculus for Report216; Python standard library only.

E counts M=kL+b and T counts M>=kL+b; the empty partition is excluded.
A is a formal indeterminate. All coefficients are exact rational Laurent
polynomials in A. Fixed-order expansions are asymptotic, not convergent sums.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial


def natural(value, name, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum} (bool excluded)")
    return value


def parameters(kind, k, b, order):
    if type(kind) is not str or kind not in ("E", "T"):
        raise ValueError("kind must be E or T")
    natural(k, "k", 2); natural(b, "b"); natural(order, "order")
    return k if kind == "E" else k - 1


class Laurent:
    """Finite sum of rational multiples of A**exponent; no float coercion."""
    __slots__ = ("terms",)

    def __init__(self, value=0):
        if isinstance(value, Laurent):
            self.terms = value.terms
            return
        if type(value) is int or isinstance(value, F):
            value = {0: F(value)}
        if type(value) is not dict:
            raise ValueError("Laurent input must be an exact rational or exponent dictionary")
        clean = []
        for exponent, coefficient in value.items():
            if type(exponent) is not int:
                raise ValueError("Laurent exponents must be integers")
            if type(coefficient) is not int and not isinstance(coefficient, F):
                raise ValueError("Laurent coefficients must be exact rationals")
            if coefficient:
                clean.append((exponent, F(coefficient)))
        self.terms = tuple(sorted(clean))

    def __add__(self, other):
        other = Laurent(other); result = dict(self.terms)
        for e, c in other.terms:
            result[e] = result.get(e, F(0)) + c
        return Laurent(result)

    __radd__ = __add__

    def __neg__(self):
        return Laurent({e: -c for e, c in self.terms})

    def __sub__(self, other):
        return self + (-Laurent(other))

    def __rsub__(self, other):
        return Laurent(other) + (-self)

    def __mul__(self, other):
        other = Laurent(other); result = {}
        for e, c in self.terms:
            for f, d in other.terms:
                result[e + f] = result.get(e + f, F(0)) + c * d
        return Laurent(result)

    __rmul__ = __mul__

    def __truediv__(self, other):
        if (type(other) is not int and not isinstance(other, F)) or not other:
            raise ValueError("Laurent division requires a nonzero exact rational")
        return Laurent({e: c / other for e, c in self.terms})

    def __pow__(self, exponent):
        natural(exponent, "power")
        result = Laurent(1); base = self
        while exponent:
            if exponent % 2:
                result = result * base
            base = base * base; exponent //= 2
        return result

    def __bool__(self):
        return bool(self.terms)

    def __eq__(self, other):
        return isinstance(other, Laurent) and self.terms == other.terms

    def record(self):
        return {str(e): str(c) for e, c in self.terms}


A = Laurent({1: 1})
ZERO = Laurent(0)
ONE = Laurent(1)


def multiply(a, b, degree):
    """Truncated product, for Fraction or Laurent coefficient lists."""
    result = [0] * (degree + 1)
    for i, x in enumerate(a[:degree + 1]):
        if x:
            for j, y in enumerate(b[:degree + 1 - i]):
                if y:
                    result[i + j] += x * y
    return result


def radial_coefficients(kind, k, b, degree):
    parameters(kind, k, b, degree)
    result = [F(0)] * (degree + 1)
    j = 1
    while (k - 1) * j + (kind == "E") <= degree:
        D = ((2 * k + 1) * j * j + (2 * b - 1) * j) // 2
        poly = [F((-D) ** ell, factorial(ell)) for ell in range(degree + 1)]
        for r in range(j if kind == "E" else j + 1, k * j + 1):
            factor = [F(0)] + [F(-(-r) ** ell, factorial(ell)) for ell in range(1, degree + 1)]
            poly = multiply(poly, factor, degree)
        sign = 1 if j % 2 else -1
        result = [x + sign * y for x, y in zip(result, poly)]
        j += 1
    return result


def q_polynomial(ell):
    """Q_ell: entry h multiplies t**h A**(-h)."""
    natural(ell, "ell")
    return [F((-1) ** h * factorial(ell + h + 1),
              factorial(ell + 1 - h) * factorial(h) * 4 ** h)
            for h in range(ell + 2)]


def forward_coefficients(kind, k, b, order):
    s = parameters(kind, k, b, order)
    g = radial_coefficients(kind, k, b, s + order)
    result = [ZERO] * (order + 1)
    for ell in range(s, s + order + 1):
        for h, q in enumerate(q_polynomial(ell)):
            m = ell + h - s
            if m <= order:
                result[m] += Laurent({-h: g[ell] * q / factorial(k)})
    return result


def normalized_series(coefficients, order):
    natural(order, "order")
    if type(coefficients) not in (list, tuple) or len(coefficients) != order + 1:
        raise ValueError("coefficient vector must have exactly order+1 entries")
    c = [Laurent(value) for value in coefficients]
    if c[0] != ONE:
        raise ValueError("constant coefficient must equal one")
    return c


def series_log(series, order):
    """log(1+x) by finite powers; assumes constant term one."""
    series = normalized_series(series, order)
    x = series[:]; x[0] = ZERO
    result = [ZERO] * (order + 1)
    power = [ONE] + [ZERO] * order
    for j in range(1, order + 1):
        power = multiply(power, x, order)
        for i in range(order + 1):
            result[i] += Laurent(power[i]) * F((-1) ** (j - 1), j)
    return result


def series_reciprocal(series, order):
    series = normalized_series(series, order)
    result = [ONE] + [ZERO] * order
    for i in range(1, order + 1):
        result[i] = -sum((series[j] * result[i - j] for j in range(1, i + 1)), ZERO)
    return result


def inverse_residual(c, d, u, order):
    """delta-d log(1+z delta)+log H(2Az/(1+z delta))."""
    c = normalized_series(c, order); natural(d, "d", 1)
    if type(u) not in (list, tuple) or len(u) != order + 1:
        raise ValueError("inverse coefficient vector must have order+1 entries")
    u = [Laurent(v) for v in u]
    if u[0]:
        raise ValueError("delta must have zero constant coefficient")
    denominator = [ONE, ZERO] + u[1:order]
    denominator = denominator[:order + 1]
    reciprocal = series_reciprocal(denominator, order)
    v = [ZERO] + [2 * A * x for x in reciprocal[:order]]
    H = [ONE] + [ZERO] * order
    power = H[:]
    for j in range(1, order + 1):
        power = multiply(power, v, order)
        H = [x + c[j] * Laurent(y) for x, y in zip(H, power)]
    log_den = series_log(denominator, order)
    log_H = series_log(H, order)
    return [u[i] - d * log_den[i] + log_H[i] for i in range(order + 1)]


def revert_coefficients(coefficients, d):
    """Triangular formal reversion; u[0]=0, u[j] multiplies w0**(-j)."""
    if type(coefficients) not in (list, tuple) or not coefficients:
        raise ValueError("nonempty coefficient vector required")
    order = len(coefficients) - 1
    c = normalized_series(coefficients, order); natural(d, "d", 1)
    u = [ZERO] * (order + 1)
    for j in range(1, order + 1):
        residual = inverse_residual(c[:j + 1], d, u[:j + 1], j)
        u[j] = -residual[j]
    return u


def inverse_coefficients(kind, k, b, order):
    s = parameters(kind, k, b, order)
    return revert_coefficients(forward_coefficients(kind, k, b, order), s + 2)


@lru_cache(maxsize=4)
def partition_numbers(N):
    """Euler's pentagonal recurrence, returned as an immutable tuple."""
    natural(N, "N")
    p = [1] + [0] * N
    for n in range(1, N + 1):
        j = 1
        while j * (3 * j - 1) // 2 <= n:
            a = j * (3 * j - 1) // 2; b = j * (3 * j + 1) // 2
            sign = 1 if j % 2 else -1
            p[n] += sign * p[n - a]
            if b <= n:
                p[n] += sign * p[n - b]
            j += 1
    return tuple(p)


def exact_counts(kind, k, b, N):
    """Return X(0)..X(N) from the finite q-sieve (exact integers)."""
    parameters(kind, k, b, N)
    p = partition_numbers(N); result = [0] * (N + 1)
    j = 1
    while True:
        D = ((2 * k + 1) * j * j + (2 * b - 1) * j) // 2
        if D > N:
            break
        term = list(p[:N - D + 1])
        for r in range(j if kind == "E" else j + 1, k * j + 1):
            for n in range(len(term) - 1, r - 1, -1):
                term[n] -= term[n - r]
        sign = 1 if j % 2 else -1
        for n, count in enumerate(term):
            result[n + D] += sign * count
        j += 1
    if result[0] != 0 or any(type(x) is not int or x < 0 for x in result):
        raise RuntimeError("invalid exact-count output")
    return result
