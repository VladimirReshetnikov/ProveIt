"""Check inverse pole orders with integer polynomial arithmetic.

These examples use the multiplicative formal group over Z_p, so [a](X)
equals (1+X)^a - 1. No truncated series inversion is needed.
"""
from itertools import combinations
from math import comb


def product(f, g, modulus):
    result = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            result[i + j] += a * b
    return [a % modulus for a in result]


def valuation(a, prime):
    assert a != 0
    exponent = 0
    while a % prime == 0:
        a //= prime
        exponent += 1
    return exponent


def pole_order(polynomial, p, r):
    modulus = p**r
    omega = next(j for j, a in enumerate(polynomial) if a % p)
    # D = high + low with high = X^omega * unit and low divisible by p.
    # The numerator of 1/D over high^r is the finite geometric sum.
    high = [0] * omega + polynomial[omega:]
    minus_low = [-a for a in polynomial[:omega]]
    numerator = [1]
    low_power = [1]
    for _ in range(1, r):
        numerator = product(numerator, high, modulus)
        low_power = product(low_power, minus_low, modulus)
        for j, a in enumerate(low_power):
            numerator[j] = (numerator[j] + a) % modulus
    first = next(j for j, a in enumerate(numerator) if a % modulus)
    return r * omega - first


def check_case(B, b, p, r):
    modulus = p**r
    delta = [1]
    heights = []
    for c in B:
        if c == b:
            continue
        heights.append(valuation(abs(b - c), p))
        f = [comb(b, i) - comb(c, i) for i in range(max(b, c) + 1)]
        delta = product(delta, f, modulus)
    h = max(heights)
    omega = sum(p**j for j in heights)
    t = pole_order(delta, p, r)
    bound = omega + (r - 1) * (p**h - 1)
    assert t <= bound
    if r == 1 or h == 0:
        assert t == bound
    elif h > 1:
        assert t < bound
    else:
        count = heights.count(1)
        largest = max(j for j in range(r)
                      if j + valuation(comb(count + j - 1, j), p) < r)
        assert t == omega + (p - 1) * largest
        assert (t == bound) == (comb(count + r - 2, r - 1) % p != 0)
    if r == 2:
        surviving = [a for a in set(heights) if a and heights.count(a) % p]
        shift = (p - 1) * p**(max(surviving) - 1) if surviving else 0
        assert t == omega + shift
    return t


if __name__ == "__main__":
    count = 0
    for p in (2, 3, 5):
        for r in (1, 2, 3, 4):
            for size in (2, 3):
                for B in combinations(range(1 + 2*p), size):
                    for b in B:
                        check_case(B, b, p, r)
                        count += 1
    assert check_case((0, 2, 6), 0, 2, 2) == 4
    assert check_case((0, 4), 0, 2, 2) == 6
    print(f"Verified {count} branch choices and both manuscript examples.")
