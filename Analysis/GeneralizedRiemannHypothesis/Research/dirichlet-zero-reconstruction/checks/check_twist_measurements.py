"""Check the fixed-list theorem on finite samples with exact arithmetic.

Run with Python 3.10 or newer. Fourier products are integer polynomials
reduced modulo the cyclotomic polynomial Phi_E. No external dependencies.
"""
from functools import lru_cache
from itertools import combinations
from math import gcd


def reduce_mod(coefficients, divisor):
    """Remainder modulo a monic integer polynomial; low-degree term first."""
    a = list(coefficients)
    d = len(divisor) - 1
    for i in range(len(a) - 1, d - 1, -1):
        if a[i]:
            factor = a[i]
            for j, coefficient in enumerate(divisor):
                a[i - d + j] -= factor * coefficient
    return tuple((a + [0] * d)[:d])


@lru_cache(maxsize=None)
def cyclotomic(n):
    polynomial = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d:
            continue
        divisor = cyclotomic(d)
        shift = len(divisor) - 1
        quotient = [0] * (len(polynomial) - shift)
        for i in reversed(range(len(quotient))):
            quotient[i] = polynomial[i + shift]
            for j, coeff in enumerate(divisor):
                polynomial[i + j] -= quotient[i] * coeff
        assert all(v == 0 for v in polynomial)
        polynomial = quotient
    return tuple(polynomial)


def fixed_queries(n):
    divisors = [d for d in range(2, n + 1) if n % d == 0]
    queries = []
    for d in divisors:
        k = n // d
        queries.append([k] * (d - 1) + [-(d - 1) * k])
    for d, e in combinations(divisors, 2):
        g = gcd(d, e)
        if g > 1:
            queries.append([n // d] * (d // g) + [-(n // e)] * (e // g))
    assert all(sum(q) == 0 and all(q) for q in queries)
    return queries


def histograms(n, mass):
    if n == 1:
        yield (mass,)
        return
    for k in range(mass + 1):
        for t in histograms(n - 1, mass - k):
            yield (k,) + t


def rotation_class(f):
    return min(f[k:] + f[:k] for k in range(len(f)))


def check(n, mass=4):
    phi = cyclotomic(n)
    d = len(phi) - 1
    queries = fixed_queries(n)

    @lru_cache(maxsize=8192)
    def multiply(a, b):
        tmp = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    tmp[i + j] += x * y
        return reduce_mod(tmp, phi)

    def signature(f):
        fourier = {}
        for k in {t % n for q in queries for t in q}:
            terms = [0] * n
            for j, z in enumerate(f):
                terms[(j * k) % n] += z
            fourier[k] = reduce_mod(terms, phi)
        products = []
        for q in queries:
            value = (1,) + (0,) * (d - 1)
            for t in q:
                value = multiply(value, fourier[t % n])
            products.append(value)
        return tuple(products)

    signatures, classes = {}, {}
    total = 0
    for f in histograms(n, mass):
        total += 1
        sig, orbit = signature(f), rotation_class(f)
        assert signatures.setdefault(sig, orbit) == orbit
        assert classes.setdefault(orbit, sig) == sig
    print(f"E={n:2}  mass={mass}  queries={len(queries):2}  "
          f"histograms={total:4}  rotation classes={len(classes):3}  OK")


if __name__ == "__main__":
    for exponent in (2, 3, 4, 6, 8, 9, 12):
        check(exponent)

