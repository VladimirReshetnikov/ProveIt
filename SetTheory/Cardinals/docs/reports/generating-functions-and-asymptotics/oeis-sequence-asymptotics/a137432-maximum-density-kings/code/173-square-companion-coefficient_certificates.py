"""Exact c1,c2,c3 certificates using only Fraction and finite algebra.

A sparse polynomial encodes boundary run lengths and k. Rational generating
functions have only the poles q=1 and q=1/2, so elementary polynomial arithmetic
suffices; no floating-point sample and no sequence term is used in this proof.
"""
from fractions import Fraction as Q
from functools import lru_cache


def trim(p):
    p = list(map(Q, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p or [Q(0)])


def padd(p, q):
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                 for i in range(max(len(p), len(q)))])


def pmul(p, q):
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(out)


def ppow(p, exponent):
    out = (Q(1),)
    for _ in range(exponent):
        out = pmul(out, p)
    return out


def pdivide_linear(p, slope):
    """Divide by 1-slope*q if exact; return None otherwise."""
    if len(p) == 1:
        return None
    out = [p[0]]
    for i in range(1, len(p) - 1):
        out.append(p[i] + slope * out[-1])
    if p[-1] != -slope * out[-1]:
        return None
    return trim(out)


class Rational:
    """N(q) / ((1-q)**a * (1-2q)**b), with Fraction coefficients."""
    def __init__(self, numerator=(0,), a=0, b=0):
        if a < 0 or b < 0:
            raise ValueError("Denominator exponents must be nonnegative")
        p = trim(numerator)
        if p == (Q(0),):
            a = b = 0
        for slope, count in ((1, a), (2, b)):
            for _ in range(count):
                divided = pdivide_linear(p, slope)
                if divided is None:
                    break
                p = divided
                if slope == 1:
                    a -= 1
                else:
                    b -= 1
        self.p, self.a, self.b = p, a, b

    @staticmethod
    def wrap(value):
        return value if isinstance(value, Rational) else Rational((Q(value),))

    def __add__(self, other):
        other = self.wrap(other)
        a, b = max(self.a, other.a), max(self.b, other.b)
        def raised(value):
            return pmul(value.p, pmul(ppow((1, -1), a - value.a), ppow((1, -2), b - value.b)))
        return Rational(padd(raised(self), raised(other)), a, b)

    __radd__ = __add__

    def __neg__(self):
        return Rational([-c for c in self.p], self.a, self.b)

    def __sub__(self, other):
        return self + -self.wrap(other)

    def __mul__(self, other):
        other = self.wrap(other)
        return Rational(pmul(self.p, other.p), self.a + other.a, self.b + other.b)

    __rmul__ = __mul__

    def D(self):
        """Euler derivative q*d/dq, kept entirely exact."""
        deriv = tuple(i * self.p[i] for i in range(1, len(self.p))) or (Q(0),)
        first = pmul(deriv, pmul((1, -1), (1, -2)))
        second = pmul(self.p, (self.a + 2 * self.b, -2 * self.a - 2 * self.b))
        return Rational((Q(0),) + padd(first, second), self.a + 1, self.b + 1)

    def certificate(self):
        return {"numerator_ascending": [str(c) for c in self.p],
                "denominator_power_1_minus_q": self.a,
                "denominator_power_1_minus_2q": self.b}


NVARS = 7  # k, left first/second/third runs, right first/second/third runs
ZERO = (0,) * NVARS


class Polynomial:
    def __init__(self, terms=None):
        self.terms = {key: Q(value) for key, value in (terms or {}).items() if value}

    @staticmethod
    def wrap(value):
        return value if isinstance(value, Polynomial) else Polynomial({ZERO: Q(value)})

    @staticmethod
    def variable(index):
        exps = list(ZERO)
        exps[index] = 1
        return Polynomial({tuple(exps): 1})

    def __add__(self, other):
        out = dict(self.terms)
        for key, value in self.wrap(other).terms.items():
            out[key] = out.get(key, 0) + value
        return Polynomial(out)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + -self.wrap(other)

    def __rsub__(self, other):
        return self.wrap(other) + -self

    def __mul__(self, other):
        out = {}
        for key, value in self.terms.items():
            for key2, value2 in self.wrap(other).terms.items():
                combined = tuple(a + b for a, b in zip(key, key2))
                out[combined] = out.get(combined, 0) + value * value2
        return Polynomial(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if exponent < 0:
            raise ValueError("Polynomial exponent must be nonnegative")
        out = self.wrap(1)
        for _ in range(exponent):
            out = out * self
        return out


def correction_polynomials():
    k, sl, tl, ul, sr, tr, ur = [Polynomial.variable(i) for i in range(NVARS)]
    d = 1 - k
    b1 = sl + sr
    b2 = sl**2 + tl + sr**2 + tr
    b3 = sl**3 + 2*sl*tl + tl**2 + ul + sr**3 + 2*sr*tr + tr**2 + ur
    e1 = b1 - Q(1, 2)*d**2
    e2 = b2 - 2*d*b1 + Q(1, 3)*d**3
    e3 = b3 - 3*d*b2 + 3*d**2*b1 - Q(3, 2)*b1**2 - Q(1, 4)*d**4
    return [Polynomial.wrap(1), e1, e2 + Q(1, 2)*e1**2,
            e3 + e1*e2 + Q(1, 6)*e1**3]


F = Rational((1, -1), 0, 1)


@lru_cache(None)
def h(order):
    return Rational((0, 1), 1, 0) if order == 0 else h(order - 1).D()


@lru_cache(None)
def side_moment(exponents):
    last = max([i + 1 for i, exponent in enumerate(exponents) if exponent] + [0])
    out = F
    for exponent in exponents[:last]:
        out = out * h(exponent)
    return out


@lru_cache(None)
def moment(exponents):
    out = side_moment(exponents[1:4]) * side_moment(exponents[4:7])
    for _ in range(exponents[0]):
        out = out.D()
    return out


# Displayed coefficients after q = 1/e, in ascending powers of q.
CLAIMED = [Rational((1,)),
           Rational(tuple(-Q(x, 2) for x in (1, -12, 45, -40, 4)), 2, 2),
           Rational(tuple(Q(x, 24) for x in (11, -82, 694, -4902, 19179, -34836, 28984, -9200, 176)), 4, 4),
           Rational(tuple(-Q(x, 48) for x in (21, -484, -17, 37848, -268609, 850396, -1209231, 86272, 2100764, -2882112, 1642864, -358912, 1344)), 6, 6)]


def check_coefficients():
    certificates = []
    inverse_w = Rational((1, -4, 4), 2, 0)
    for order, polynomial in enumerate(correction_polynomials()):
        summed = sum((coefficient * moment(exponents)
                      for exponents, coefficient in polynomial.terms.items()), Rational())
        derived = summed * inverse_w
        difference = derived - CLAIMED[order]
        if difference.p != (Q(0),):
            raise RuntimeError(f"Exact coefficient c{order} differs from the displayed expression")
        certificates.append({"order": order, "boundary_polynomial_monomials": len(polynomial.terms),
                             "derived": derived.certificate(), "difference_numerator": ["0"]})
    return certificates


if __name__ == "__main__":
    import json
    print(json.dumps(check_coefficients(), sort_keys=True, indent=2))
