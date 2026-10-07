"""Independent finite certificate using sparse polynomial powers and division.

No import from inverse_series. Solve exp(delta)*Q=1 degree by degree using
finite factorial sums; obtain R from polynomial long division by Q^2.
This deliberately avoids the logarithm and exponential coefficient recurrences
used by the main generator.
"""
from fractions import Fraction
from math import factorial


def require(condition, message):
    if not condition:
        raise ValueError(message)


def product(left, right, degree):
    out = {}
    for i, a in left.items():
        for j, b in right.items():
            if i + j <= degree:
                out[i+j] = out.get(i+j, Fraction(0)) + a*b
    return {i: a for i, a in out.items() if a}


def combination(*terms):
    out = {}
    for factor, polynomial in terms:
        for i, a in polynomial.items():
            out[i] = out.get(i, Fraction(0)) + factor*a
    return {i: a for i, a in out.items() if a}


def exp_by_powers(delta, degree):
    require(not delta.get(0, 0), 'sparse exponential requires zero constant')
    value, power = {0: Fraction(1)}, {0: Fraction(1)}
    for k in range(1, degree + 1):
        power = product(power, delta, degree)
        value = combination((1, value), (Fraction(1, factorial(k)), power))
    return value


def derive(degree):
    require(type(degree) is int and 1 <= degree <= 40, 'degree must be an integer in 1..40')
    one, u, u2 = {0: Fraction(1)}, {1: Fraction(1)}, {2: Fraction(1)}
    d = {}

    def quantities(n):
        z = combination((1, one), (1, product(u, d, n)))
        q = combination((1, product(z, z, n)), (-1, product(u, z, n)), (1, u2))
        return z, {i: a for i, a in q.items() if i <= n}

    for n in range(1, degree + 1):
        _, q = quantities(n)
        trial = product(exp_by_powers(d, n), q, n)
        d[n] = -trial.get(n, Fraction(0))
    z, q = quantities(degree)
    require(product(exp_by_powers(d, degree), q, degree) == one, 'independent exponential identity')
    numerator, denominator = product(z, z, degree), product(q, q, degree)
    quotient = {}
    require(denominator[0] == 1, 'independent division unit denominator')
    for n in range(degree + 1):
        coefficient = numerator.get(n, Fraction(0)) - sum(
            (a * quotient.get(n-i, Fraction(0)) for i, a in denominator.items() if 1 <= i <= n), Fraction(0))
        if coefficient:
            quotient[n] = coefficient
    require(product(quotient, denominator, degree) == numerator, 'independent rational factor identity')
    return ([d.get(i, Fraction(0)) for i in range(degree + 1)],
            [quotient.get(i, Fraction(0)) for i in range(degree + 1)])
