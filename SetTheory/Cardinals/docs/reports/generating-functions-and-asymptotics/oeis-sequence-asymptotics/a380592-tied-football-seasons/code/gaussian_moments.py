"""Exact Gaussian moment algebra for the local football-score integral.

The covariance is a I + b J, with a = 9/(28n-2) and
b = (9/(2(n-1)) - a)/n. Formal moments retain the constant and 1/n
coefficients. All arithmetic in the moment computation is exact.
"""

from collections import Counter
from fractions import Fraction
from functools import lru_cache

import sympy as S

n, x, y = S.symbols("n x y")
P = S.symbols("P0:7")
mean = S.Rational(4, 3) * (x + y)
values = [3 * x - mean, x + y - mean, 3 * y - mean]
moments = {0: S.Integer(1), 1: S.Integer(0)}
cumulants = {1: S.Integer(0)}
for degree in range(2, 7):
    moments[degree] = S.expand(sum(value**degree / 3 for value in values))
    cumulants[degree] = S.expand(
        moments[degree]
        - sum(
            S.binomial(degree - 1, j - 1) * cumulants[j] * moments[degree - j]
            for j in range(1, degree)
        )
    )

# Two distinguished matches per unordered pair cancel the factor 1/2 in
# the power-sum aggregation of a symmetric bivariate polynomial.
L = {}
for degree in range(3, 7):
    coefficients = [
        cumulants[degree].coeff(x, j).coeff(y, degree - j)
        for j in range(degree + 1)
    ]
    L[degree] = S.expand(
        S.I**degree / S.factorial(degree)
        * (
            sum(coefficients[j] * P[j] * P[degree - j] for j in range(degree + 1))
            - sum(coefficients) * P[degree]
        )
    ).subs(P[0], n).expand()


@lru_cache(None)
def grouped_partitions(degrees):
    """Count set partitions grouped by sorted sums of degrees in blocks."""
    states = {(): 1}
    for degree in degrees:
        following = Counter()
        for blocks, count in states.items():
            following[tuple(sorted(blocks + (degree,)))] += count
            for old, multiplicity in Counter(blocks).items():
                updated = list(blocks)
                updated.remove(old)
                updated.append(old + degree)
                following[tuple(sorted(updated))] += count * multiplicity
        states = following
    return tuple(states.items())


def double_factorial(k):
    """Include the convention (-1)!! = 1."""
    return 1 if k <= 0 else int(S.factorial2(k))


@lru_cache(None)
def distinct_moment(degrees):
    """Return coefficients of a**K b**B for distinct vertex indices."""
    total = sum(degrees)
    if total % 2:
        return ()
    coefficients = {0: 1}
    for degree in degrees:
        following = Counter()
        for power, coefficient in coefficients.items():
            for pairs in range(degree // 2 + 1):
                following[power + pairs] += (
                    coefficient * int(S.binomial(degree, 2 * pairs))
                    * double_factorial(2 * pairs - 1)
                )
        coefficients = following
    return tuple(
        ((power, total // 2 - power), coefficient * double_factorial(total - 2 * power - 1))
        for power, coefficient in coefficients.items()
    )


@lru_cache(None)
def moment(degrees, power_of_n):
    """Expand E[n**u product(P_d)] through order n**(-1)."""
    answer = Counter()
    for blocks, multiplicity in grouped_partitions(degrees):
        length = len(blocks)
        for (power_a, power_b), coefficient in distinct_moment(blocks):
            exponent = power_of_n + length - power_a - 2 * power_b
            if exponent < -1:
                continue
            leading = (
                Fraction(multiplicity * coefficient)
                * Fraction(9, 28)**power_a * Fraction(117, 28)**power_b
            )
            answer[exponent] += leading
            if exponent >= 0:
                answer[exponent - 1] += leading * (
                    -Fraction(length * (length - 1), 2)
                    + Fraction(power_a, 14) + Fraction(15 * power_b, 14)
                )
            if exponent > 0:
                raise ValueError("More Laurent terms required for this monomial")
    return tuple(answer.items())


def expectation(poly):
    """Return the exact constant and 1/n coefficients of a polynomial mean."""
    answer = Counter()
    for powers, coefficient in S.Poly(S.expand(poly), n, *P[1:]).terms():
        degrees = tuple(
            degree for degree, count in enumerate(powers[1:], 1)
            for _ in range(count)
        )
        for exponent, value in moment(degrees, powers[0]):
            answer[exponent] += coefficient * S.Rational(value.numerator, value.denominator)
    return tuple(S.simplify(answer.get(exponent, 0)) for exponent in (0, -1))


def add(*values):
    return tuple(S.simplify(sum(value[j] for value in values)) for j in (0, 1))


def multiply(first, second):
    return (first[0] * second[0], first[0] * second[1] + first[1] * second[0])


def scale(value, coefficient):
    return tuple(S.simplify(item * coefficient) for item in value)
