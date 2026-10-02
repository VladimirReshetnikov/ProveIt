"""Small truncated-series and polynomial routines (ordinary coefficients)."""
from dataclasses import dataclass


def add(a, b):
    if len(a) != len(b):
        raise ValueError("series must have the same truncation length")
    return [x + y for x, y in zip(a, b)]


def scale(a, c):
    return [c * x for x in a]


def mul(a, b):
    if len(a) != len(b):
        raise ValueError("series must have the same truncation length")
    return [sum(a[j] * b[k-j] for j in range(k+1)) for k in range(len(a))]


def logpoly(v):
    """log(v), truncated to len(v), for v[0] = 1."""
    if v[0] != 1:
        raise ValueError("formal logarithm requires constant coefficient 1")
    h = v.copy()
    h[0] = h[0] - 1
    power = [1] + [0] * (len(v)-1)
    ans = [0] * len(v)
    for k in range(1, len(v)):
        power = mul(power, h)
        # Avoid binary floating-point constants in exact/mp arithmetic.
        ans = add(ans, [((-1)**(k+1) * x) / k for x in power])
    return ans


def invpoly(v):
    """1/v, truncated to len(v), for v[0] = 1."""
    if v[0] != 1:
        raise ValueError("formal reciprocal requires constant coefficient 1")
    h = v.copy()
    h[0] = h[0] - 1
    power = [1] + [0] * (len(v)-1)
    ans = power.copy()
    for k in range(1, len(v)):
        power = mul(power, h)
        ans = add(ans, scale(power, (-1)**k))
    return ans


@dataclass
class Polynomial:
    """Polynomial in h, coefficients in ascending degree; no CAS dependency."""
    coefficients: list

    def __post_init__(self):
        while len(self.coefficients) > 1 and self.coefficients[-1] == 0:
            self.coefficients.pop()

    @staticmethod
    def of(value):
        return value if isinstance(value, Polynomial) else Polynomial([value])

    def __add__(self, other):
        a, b = self.coefficients, self.of(other).coefficients
        return Polynomial([(a[k] if k < len(a) else 0) +
                           (b[k] if k < len(b) else 0)
                           for k in range(max(len(a), len(b)))])

    __radd__ = __add__

    def __neg__(self):
        return Polynomial([-x for x in self.coefficients])

    def __sub__(self, other):
        return self + (-self.of(other))

    def __rsub__(self, other):
        return self.of(other) + (-self)

    def __mul__(self, other):
        a, b = self.coefficients, self.of(other).coefficients
        c = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x == 0:
                continue
            for j, y in enumerate(b):
                c[i+j] += x*y
        return Polynomial(c)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return Polynomial([x / scalar for x in self.coefficients])

    def __eq__(self, other):
        c = (self - other).coefficients
        return all(x == 0 for x in c)

    def evaluate(self, h):
        value = 0
        for c in reversed(self.coefficients):
            value = value*h + c
        return value
