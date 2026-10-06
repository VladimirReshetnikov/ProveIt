"""Exact integer/rational implementation of the formulas in Report 134.

This module has no command-line side effects and writes no files.
Dimensions use hook lengths; strips use interlacing inequalities.
"""
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial


def require(condition, message):
    """A check that remains active under python -O."""
    if not condition:
        raise ValueError(message)


def partitions3(n):
    for c in range(n // 3 + 1):
        for b in range(c, (n - c) // 2 + 1):
            yield (n - b - c, b, c)


@lru_cache(maxsize=None)
def dimension(shape):
    a, b, c = shape
    require(a >= b >= c >= 0, "invalid partition")
    numerator = factorial(a+b+c) * (a-b+1) * (a-c+2) * (b-c+1)
    denominator = factorial(a+2) * factorial(b+1) * factorial(c)
    quotient, remainder = divmod(numerator, denominator)
    require(remainder == 0, "nonintegral hook dimension")
    return quotient


@lru_cache(maxsize=None)
def boundary(n):
    require(n >= 0, "negative size")
    result = [[0] * (n+1) for _ in range(n+1)]
    for a, b, c in partitions3(n):
        values = [0] * (n+1)
        for u in range(b, a+1):
            for v in range(c, b+1):
                for w in range(c+1):
                    values[n-u-v-w] += dimension((u, v, w))
        require(values[0] == dimension((a,b,c)), "empty strip mismatch")
        require(all(0 <= x <= values[0] for x in values), "strip dimension bound")
        for p, x in enumerate(values):
            for q, y in enumerate(values):
                result[p][q] += x*y
    return result


def halves_from_boundary(t, outer, inner):
    """Also check the zero extension, rather than silently discard negatives."""
    values = {}
    for i in range(t+2):
        for j in range(t+2):
            h = outer[i+1][j+1] - inner[i][j]
            require(h >= 0, "negative half coefficient")
            require(i+j <= t or h == 0, "half support violation")
            if i+j <= t:
                values[i,j] = h
    return values


@lru_cache(maxsize=None)
def halves(t):
    return halves_from_boundary(t, boundary(t+2), boundary(t+1))


def exact_count(n, half_layers=None):
    if n < 4:
        return 0
    total = 0
    for s in range(n-3):
        t = n-4-s
        left = halves(s) if half_layers is None else half_layers[s]
        right = halves(t) if half_layers is None else half_layers[t]
        for (i,j), a in left.items():
            for (k,l), b in right.items():
                total += a*b*comb(i+k,i)*comb(j+l,j)
    return total


def d(i):
    return Fraction(comb(i+2,2), 3**i)


def finite_certificate(half_layers, cutoff):
    """Product-of-sums implementation; all arithmetic is exact."""
    size = len(half_layers)
    S = [sum((comb(i+k,i)*d(i) for i in range(cutoff+1)), Fraction())
         for k in range(size)]
    P = [sum((comb(i+k,i)*d(i+1) for i in range(cutoff+1)), Fraction())
         for k in range(size)]
    result = Fraction()
    partials = []
    for t, layer in enumerate(half_layers):
        term = sum(h*(81*P[k]*P[l]-9*S[k]*S[l])
                   for (k,l), h in layer.items())
        require(term > 0, "nonpositive finite-certificate layer")
        result += Fraction(2, 9**(t+4))*term
        partials.append(result)
    return result, partials


def positive_series(half_layers):
    """A partial sum, NOT a certified approximation to the infinite series."""
    result = Fraction()
    terms = []
    for t, layer in enumerate(half_layers):
        term = Fraction()
        for (k,l), h in layer.items():
            pk, pl = k*k+15*k+38, l*l+15*l+38
            qk, ql = k*k+11*k+18, l*l+11*l+18
            weight = Fraction(1, 10368*9**t)*Fraction(3,2)**(k+l)*(pk*pl-qk*ql)
            require(weight > 0 and h >= 0, "positive-series sign failure")
            term += h*weight
        require(term > 0, "zero positive-series layer")
        terms.append(term)
        result += term
    return result, terms
