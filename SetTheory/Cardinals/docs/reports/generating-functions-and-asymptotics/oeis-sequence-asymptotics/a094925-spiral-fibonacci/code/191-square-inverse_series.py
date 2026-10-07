"""Rational coefficient generation for the analytic inverse germ in Report191.

Triangular solution of delta + log(Q)=0, Q=(1+u*delta)^2-u*(1+u*delta)+u^2.
Only finite formal identities are checked here. Analytic existence is proved
in the article and cannot be established by a finite coefficient calculation.
"""
from fractions import Fraction as F


def need(condition, message):
    if not condition:
        raise ValueError(message)


def order(value):
    need(type(value) is int and 1 <= value <= 40, 'order must be an integer in 1..40')
    return value


def polynomial(a, n):
    order(n)
    need(type(a) is list and len(a) == n + 1, 'polynomial length mismatch')
    need(all(type(x) in (int, F) for x in a), 'coefficients must be integers or Fraction')
    return [F(x) for x in a]


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def scale(a, c):
    return [c * x for x in a]


def multiply(a, b, n):
    return [sum((a[j] * b[i-j] for j in range(i + 1)), F(0)) for i in range(n + 1)]


def shift(a, k, n):
    return [F(0)] * k + a[:n + 1 - k] if k <= n else [F(0)] * (n + 1)


def exponential(a, n):
    a = polynomial(a, n)
    need(a[0] == 0, 'exponential input must have zero constant')
    b = [F(1)] + [F(0)] * n
    for i in range(1, n + 1):
        b[i] = sum((F(k) * a[k] * b[i-k] for k in range(1, i+1)), F(0)) / i
    return b


def logarithm(a, n):
    a = polynomial(a, n)
    need(a[0] == 1, 'logarithm input must have unit constant')
    b = [F(0)] * (n + 1)
    for i in range(1, n + 1):
        b[i] = a[i] - sum((F(k) * b[k] * a[i-k] for k in range(1, i)), F(0)) / i
    return b


def derive(n):
    order(n)
    one = [F(1)] + [F(0)] * n
    delta = [F(0)] * (n + 1)

    def quantities():
        z = add(one, shift(delta, 1, n))
        q = add(add(multiply(z, z, n), scale(shift(z, 1, n), F(-1))), shift(one, 2, n))
        return z, q

    for k in range(1, n + 1):
        _, q = quantities()
        delta[k] = -logarithm(q, n)[k]
    z, q = quantities()
    need(add(delta, logarithm(q, n)) == [F(0)] * (n + 1), 'implicit logarithmic identity')
    need(multiply(exponential(delta, n), q, n) == one, 'implicit exponential identity')
    inverse = multiply(multiply(z, z, n), exponential(scale(delta, F(2)), n), n)
    need(multiply(inverse, multiply(q, q, n), n) == multiply(z, z, n), 'inverse factor identity')
    return delta, inverse
