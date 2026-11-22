"""Realizable signs of rational univariate polynomials, using exact arithmetic.

Coefficients are listed in ascending powers of T. The empty tuple denotes 0.
Uses the signed-remainder Tarski query and derivative samples from the report.
"""

from fractions import Fraction
from functools import lru_cache
from itertools import product


def polynomial(coefficients):
    values = list(map(Fraction, coefficients))
    while values and values[-1] == 0:
        values.pop()
    return tuple(values)


ONE = polynomial([1])


def multiply(f, g):
    if not f or not g:
        return ()
    coeffs = [Fraction(0)] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            coeffs[i + j] += a * b
    return polynomial(coeffs)


def derivative(f):
    return polynomial(i * f[i] for i in range(1, len(f)))


def divide(f, g):
    if not g:
        raise ZeroDivisionError("polynomial division by zero")
    q = [Fraction(0)] * max(0, len(f) - len(g) + 1)
    rem = list(f)
    while len(rem) >= len(g):
        offset = len(rem) - len(g)
        c = rem[-1] / g[-1]
        q[offset] = c
        for j, b in enumerate(g):
            rem[offset + j] -= c * b
        while rem and not rem[-1]:
            rem.pop()
    return polynomial(q), tuple(rem)


def exact_quotient(f, g):
    q, rem = divide(f, g)
    assert not rem
    return q


def gcd(f, g):
    while g:
        f, g = g, divide(f, g)[1]
    return tuple(c / f[-1] for c in f)


def squarefree(f):
    if not f:
        return ()
    return exact_quotient(f, gcd(f, derivative(f)))


def sign(x):
    return int(x > 0) - int(x < 0)


def tail_sign(f, right):
    if not f:
        return 0
    parity = 1 if right or len(f) % 2 == 1 else -1
    return parity * sign(f[-1])


def variations(seq, right):
    signs = [tail_sign(f, right) for f in seq]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def tarski_query(d, w):
    """Sum sign(w) over distinct real roots of squarefree d."""
    if len(d) < 2:
        return 0
    b = divide(multiply(derivative(d), w), d)[1]
    if not b:
        return 0
    common = gcd(d, b)
    a, b = exact_quotient(d, common), exact_quotient(b, common)
    chain = [a, b]
    while True:
        rem = divide(chain[-2], chain[-1])[1]
        if not rem:
            break
        chain.append(tuple(-c for c in rem))
    return variations(chain, False) - variations(chain, True)


# (exponent, coefficient) for the report's twice-indicator polynomials.
INDICATOR = {
    -1: ((2, 1), (1, -1)),
    0: ((0, 2), (2, -2)),
    1: ((2, 1), (1, 1)),
}


def signs_at_roots(d, polys):
    """Dictionary from a sign condition to its nonzero root count."""
    if len(d) < 2:
        return {}
    powers = [(ONE, f, multiply(f, f)) for f in polys]

    @lru_cache(maxsize=None)
    def query(exponents):
        w = ONE
        for row, e in zip(powers, exponents):
            w = multiply(w, row[e])
        return tarski_query(d, w)

    counts = {}
    divisor = 2 ** len(polys)
    for signs in product((-1, 0, 1), repeat=len(polys)):
        total = 0
        for factors in product(*(INDICATOR[s] for s in signs)):
            exps = tuple(e for e, _ in factors)
            c = 1
            for _, weight in factors:
                c *= weight
            total += c * query(exps)
        count, rem = divmod(total, divisor)
        assert rem == 0 and count >= 0
        if count:
            counts[signs] = count
    return counts


def attainable_signs(coefficient_lists):
    """All sign vectors realized on the real line, including point cells."""
    polys = [polynomial(f) for f in coefficient_lists]
    p = ONE
    for f in polys:
        if len(f) >= 2:
            p = multiply(p, f)
    d = squarefree(p)
    patterns = {tuple(tail_sign(f, side) for f in polys)
                for side in (False, True)}
    patterns.update(signs_at_roots(d, polys))
    patterns.update(signs_at_roots(squarefree(derivative(d)), polys))
    return patterns


if __name__ == "__main__":
    # Unit circle cuts a horizontal line of height 3/5 at x = ±4/5.
    eq = [Fraction(-16, 25), 0, 1]
    print("Signs of (x²-16/25, x):", sorted(attainable_signs([eq, [0, 1]])))
