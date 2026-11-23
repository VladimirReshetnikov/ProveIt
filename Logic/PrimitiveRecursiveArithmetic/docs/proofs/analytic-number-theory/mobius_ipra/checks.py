#!/usr/bin/env python3
"""Exact finite checks for the Möbius function report. Python 3, standard library."""
from functools import lru_cache
from math import isqrt


@lru_cache(maxsize=None)
def factors(n):
    """All prime factors, with multiplicity, by trial division."""
    assert n >= 1
    remaining = n
    result = []
    for d in range(2, isqrt(n) + 1):
        while remaining % d == 0:
            result.append(d)
            remaining //= d
    if remaining > 1:
        result.append(remaining)
    return tuple(result)


def mu(n):
    f = factors(n)
    return (-1) ** len(f) if len(set(f)) == len(f) else 0


@lru_cache(maxsize=None)
def divisors(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)


def source_list(label, actual, expected):
    if actual != expected:
        raise AssertionError((label, actual, expected))
    print(f"{label}:")
    print("  " + ", ".join(map(str, actual)))


def check_source_tables():
    rows = [
        [1, -1, -1, 0, -1, 1, -1, 0, 0, 1],
        [-1, 0, -1, 1, 1, 0, -1, 0, -1, 0],
        [1, 1, -1, 0, 0, 1, 0, 0, -1, -1],
        [-1, 0, 1, 1, 1, 0, -1, 1, 1, 0],
        [-1, -1, -1, 0, 0, 1, -1, 0, 0, 0],
        [1, 0, -1, 0, 1, 0, 1, 1, -1, 0],
    ]
    for index, expected in enumerate(rows):
        start = 10 * index + 1
        source_list(f"mu for n={start}..{start + 9}",
                    [mu(n) for n in range(start, start + 10)], expected)

    source_list("|mu| for n=1..12", [abs(mu(n)) for n in range(1, 13)],
                [1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0])
    for label, sign, expected in [
        ("MathWorld negative prefix", -1,
         [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 30]),
        ("MathWorld zero prefix", 0, [4, 8, 9, 12, 16, 18, 20, 24, 25, 27, 28]),
        ("MathWorld positive prefix", 1, [1, 6, 10, 14, 15, 21, 22, 26]),
        ("Wikipedia square-divisible prefix", 0,
         [4, 8, 9, 12, 16, 18, 20, 24, 25, 27, 28, 32, 36, 40, 44, 45, 48,
          49, 50, 52, 54, 56, 60, 63]),
    ]:
        source_list(label, [n for n in range(1, expected[-1] + 1) if mu(n) == sign],
                    expected)
    for k, expected in [
        (3, [30, 42, 66, 70, 78, 102, 105, 110, 114, 130, 138, 154, 165, 170,
             174, 182, 186, 190, 195, 222]),
        (5, [2310, 2730, 3570, 3990, 4290, 4830, 5610, 6006, 6090, 6270, 6510,
             6630, 7410, 7590, 7770, 7854, 8610, 8778, 8970, 9030, 9282, 9570,
             9690]),
    ]:
        actual = [n for n in range(1, expected[-1] + 1)
                  if len(factors(n)) == k and len(set(factors(n))) == k]
        source_list(f"Squarefree products of {k} primes through {expected[-1]}",
                    actual, expected)


def check_identities():
    for n in range(1, 257):
        ds = divisors(n)
        assert sum(mu(d) for d in ds) == int(n == 1)
        assert sum(abs(mu(d)) for d in ds) == 2 ** len(set(factors(n)))
        assert sum(mu(d) * len(divisors(n // d)) for d in ds) == 1
        assert sum(mu(d) * (n // d) for d in range(1, n + 1)) == 1
        for p in (2, 3, 5, 7, 11):
            is_power = all(factor == p for factor in factors(n))
            assert -sum(mu(p * d) for d in ds) == int(is_power)
    print("Divisor, floor-sum and Lambert coefficient identities hold through 256")
    print("Prime-shifted Lambert coefficients hold through 256 for p=2,3,5,7,11")

    primes = [p for p in range(2, 252) if factors(p) == (p,)]
    for p in primes:
        # Distinct residues among powers certify exact order p-1.
        generators = [a for a in range(1, p)
                      if len({pow(a, k, p) for k in range(p - 1)}) == p - 1]
        assert generators and (sum(generators) - mu(p - 1)) % p == 0
    print(f"Gauss primitive-root congruence holds for all {len(primes)} primes through 251")


def monic_coefficients(code, degree, p):
    """Decode a monic polynomial by its coefficients from constant to leading."""
    coeff = []
    for _ in range(degree):
        code, digit = divmod(code, p)
        coeff.append(digit)
    return coeff + [1]


def is_multiple(f, g, p):
    """Polynomial long division by a monic polynomial g over F_p."""
    rem = f.copy()
    for shift in range(len(f) - len(g), -1, -1):
        scalar = rem[shift + len(g) - 1]
        for i, digit in enumerate(g):
            rem[shift + i] = (rem[shift + i] - scalar * digit) % p
    return all(digit == 0 for digit in rem)


def check_irreducibles():
    for p, limit in ((2, 9), (3, 6)):
        counts = []
        for n in range(1, limit + 1):
            candidates = [monic_coefficients(code, d, p)
                          for d in range(1, n // 2 + 1) for code in range(p ** d)]
            count = 0
            for code in range(p ** n):
                f = monic_coefficients(code, n, p)
                if not any(is_multiple(f, g, p) for g in candidates):
                    count += 1
            assert n * count == sum(mu(d) * p ** (n // d) for d in divisors(n))
            counts.append(count)
        print(f"Monic irreducibles over F_{p} for degrees 1..{limit}: {counts}")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O to enable all assertions")
    check_source_tables()
    check_identities()
    check_irreducibles()
    print("All exact finite checks passed.")
