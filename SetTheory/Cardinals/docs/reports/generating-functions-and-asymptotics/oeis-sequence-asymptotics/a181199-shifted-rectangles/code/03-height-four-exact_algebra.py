"""Small exact algebra for the certificate: Q[n,u,v] and Q(n).

This is deliberately independent of any computer algebra package. Polynomial
coefficients are fractions.Fraction. Rational-function equality means that the
cross-multiplied polynomial residual has every coefficient equal to zero.
"""
from fractions import Fraction as F


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


class Poly:
    """Sparse polynomial in the fixed variable order (n,u,v)."""
    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.terms = dict(value.terms)
        elif isinstance(value, dict):
            self.terms = {tuple(k): F(v) for k, v in value.items() if v}
            require(all(len(k) == 3 and all(isinstance(e, int) and e >= 0 for e in k)
                        for k in self.terms), "invalid polynomial exponent")
        else:
            self.terms = {(0, 0, 0): F(value)} if value else {}

    def __add__(self, other):
        other = Poly(other)
        result = dict(self.terms)
        for exponent, coefficient in other.terms.items():
            result[exponent] = result.get(exponent, F(0)) + coefficient
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        other = Poly(other)
        result = {}
        for x, a in self.terms.items():
            for y, b in other.terms.items():
                exponent = tuple(i+j for i, j in zip(x, y))
                result[exponent] = result.get(exponent, F(0)) + a*b
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, power):
        require(isinstance(power, int) and power >= 0, "invalid polynomial power")
        result, base = Poly(1), self
        while power:
            if power & 1:
                result = result * base
            base = base * base
            power //= 2
        return result

    def __eq__(self, other):
        return self.terms == Poly(other).terms

    def __bool__(self):
        return bool(self.terms)

    def derivative(self, variable):
        require(variable in (0, 1, 2), "unknown polynomial variable")
        result = {}
        for exponent, coefficient in self.terms.items():
            if exponent[variable]:
                changed = list(exponent)
                changed[variable] -= 1
                result[tuple(changed)] = coefficient * exponent[variable]
        return Poly(result)

    def substitute(self, replacements):
        """Simultaneous polynomial substitution; keys are variable indices."""
        variables = [N, U, V]
        for index, value in replacements.items():
            require(index in (0, 1, 2), "unknown substitution variable")
            variables[index] = Poly(value)
        result = Poly()
        for exponent, coefficient in self.terms.items():
            term = Poly(coefficient)
            for variable, power in zip(variables, exponent):
                term = term * variable**power
            result = result + term
        return result

    def value(self, n=0, u=0, v=0):
        values = (F(n), F(u), F(v))
        return sum((coefficient * values[0]**e[0] * values[1]**e[1] * values[2]**e[2]
                    for e, coefficient in self.terms.items()), F(0))

    def univariate(self):
        return all(e[1:] == (0, 0) for e in self.terms)

    def degree(self):
        require(self.univariate(), "univariate operation on a multivariate polynomial")
        return max((e[0] for e in self.terms), default=-1)

    def coefficient(self, power):
        return self.terms.get((power, 0, 0), F(0))


N = Poly({(1, 0, 0): 1})
U = Poly({(0, 1, 0): 1})
V = Poly({(0, 0, 1): 1})


def quotient_remainder(a, b):
    a, b = Poly(a), Poly(b)
    require(a.univariate() and b.univariate() and b,
            "polynomial division needs univariate inputs and a nonzero divisor")
    quotient, remainder = Poly(), a
    while remainder and remainder.degree() >= b.degree():
        degree = remainder.degree() - b.degree()
        coefficient = remainder.coefficient(remainder.degree()) / b.coefficient(b.degree())
        term = Poly({(degree, 0, 0): coefficient})
        quotient = quotient + term
        remainder = remainder - term*b
    return quotient, remainder


def exact_quotient(a, b):
    quotient, remainder = quotient_remainder(a, b)
    require(not remainder, "expected an exact polynomial division")
    return quotient


def polynomial_gcd(a, b):
    a, b = Poly(a), Poly(b)
    while b:
        a, b = b, quotient_remainder(a, b)[1]
    return a * (1 / a.coefficient(a.degree())) if a else Poly()


class Rat:
    """Reduced rational function in n only, backed by Poly and Fraction."""
    def __init__(self, numerator=0, denominator=1):
        if isinstance(numerator, Rat):
            require(Poly(denominator) == 1, "nested rational denominator")
            self.num, self.den = numerator.num, numerator.den
            return
        numerator, denominator = Poly(numerator), Poly(denominator)
        require(numerator.univariate() and denominator.univariate() and denominator,
                "invalid rational function")
        gcd = polynomial_gcd(numerator, denominator)
        numerator = exact_quotient(numerator, gcd)
        denominator = exact_quotient(denominator, gcd)
        leading = denominator.coefficient(denominator.degree())
        self.num, self.den = numerator * (1/leading), denominator * (1/leading)

    def __add__(self, other):
        other = Rat(other)
        return Rat(self.num*other.den + other.num*self.den, self.den*other.den)

    __radd__ = __add__

    def __neg__(self):
        return Rat(-self.num, self.den)

    def __sub__(self, other):
        return self + -Rat(other)

    def __rsub__(self, other):
        return Rat(other) + -self

    def __mul__(self, other):
        other = Rat(other)
        return Rat(self.num*other.num, self.den*other.den)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Rat(other)
        require(bool(other.num), "division by the zero rational function")
        return Rat(self.num*other.den, self.den*other.num)

    def __rtruediv__(self, other):
        return Rat(other) / self

    def __pow__(self, power):
        require(isinstance(power, int) and power >= 0, "invalid rational power")
        return Rat(self.num**power, self.den**power)

    def __eq__(self, other):
        other = Rat(other)
        return self.num*other.den == other.num*self.den

    def shift(self, amount=1):
        return Rat(self.num.substitute({0: N+amount}), self.den.substitute({0: N+amount}))

    def value(self, n):
        denominator = self.den.value(n=n)
        require(denominator != 0, "rational evaluation at a pole")
        return self.num.value(n=n) / denominator


def self_test():
    require((N+U+V)**2 == N*N+U*U+V*V+2*N*U+2*N*V+2*U*V,
            "polynomial expansion self-test failed")
    require((N*U**2*V).derivative(1) == 2*N*U*V,
            "polynomial derivative self-test failed")
    require((U-V).substitute({1: V, 2: U}) == V-U,
            "simultaneous substitution self-test failed")
    require(exact_quotient(N**4-1, N-1) == N**3+N**2+N+1,
            "polynomial quotient self-test failed")
    require(Rat(N**2-1, N-1) == Rat(N+1), "rational cancellation self-test failed")
    require(Rat(1, N).shift().value(2) == F(1, 3), "rational shift self-test failed")
