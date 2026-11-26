"""Exact cubic certificates for V(x)=x^4-14x^3+100x^2+x, epsilon=10^-12."""
from fractions import Fraction
from math import prod


def multiply_polys(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def gamma_average(poly, n):
    p = Fraction(2 * n + 1, 2)
    return sum(a * prod(p + i for i in range(k)) for k, a in enumerate(poly))


def add(*intervals):
    return tuple(map(sum, zip(*intervals)))


def multiply(a, b):
    ends = [x * y for x in a for y in b]
    return min(ends), max(ends)


def term(k, *intervals):
    result = (k, k)
    for interval in intervals:
        result = multiply(result, interval)
    return result


def certificate(n, eps):
    potential = [0, 1, 100, -14, 1]
    squared = multiply_polys(potential, potential)
    c = []
    for i in range(n, n + 4):
        lower = 1 - eps * gamma_average(potential, i)
        c.append((lower, lower + eps**2 * gamma_average(squared, i) / 2))
    # Evaluate the discriminant after translating the multiple Gaussian root to zero.
    a = c[3]
    b = add(term(3, c[2]), term(-3, c[3]))
    d1 = add(term(3, c[1]), term(-6, c[2]), term(3, c[3]))
    d0 = add(c[0], term(-3, c[1]), term(3, c[2]), term(-1, c[3]))
    return add(term(18, a, b, d1, d0), term(-4, b, b, b, d0),
               term(1, b, b, d1, d1), term(-4, a, d1, d1, d1),
               term(-27, a, a, d0, d0))


if __name__ == "__main__":
    eps = Fraction(1, 10**12)
    for n, power, left, right in [(0, 3, 92590000, 92600000),
                                   (1, 2, -15553, -15551)]:
        low, high = certificate(n, eps)
        assert left * eps**power < low <= high < right * eps**power
        print(f"shift {n}: {left} < disc/epsilon^{power} < {right}")
