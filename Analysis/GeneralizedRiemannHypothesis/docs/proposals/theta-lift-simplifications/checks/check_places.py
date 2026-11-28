#!/usr/bin/env python3
"""Exact finite checks of the explicit digit construction for sparse places."""
from itertools import product
from math import gcd, isqrt


def require(condition, description):
    if not condition:
        raise AssertionError(description)


def code(u, base):
    low = sum(digit * base**i for i, digit in enumerate(u))
    return low + base**len(u) * sum(digit**2 for digit in u)


def read_code(value, n, height, limit):
    base = height * limit
    digits = []
    quotient = value
    for _ in range(n - 2):
        quotient, digit = divmod(quotient, base)
        if digit >= height:
            return None
        digits.append(digit)
    return tuple(digits) if quotient == sum(digit**2 for digit in digits) else None


def enumerate_codes(n, height, limit):
    k = n - 2
    require(n >= 3 and 1 <= k <= limit and height >= 1 and limit >= 2, "parameters")
    base = height * limit
    words = list(product(range(height), repeat=k))
    codes = [code(word, base) for word in words]
    require(len(set(codes)) == height**k, "injectivity")
    require(all(read_code(e, n, height, limit) == w for w, e in zip(words, codes)), "inverse")
    return codes


def check_finite():
    cases = relations = 0
    for n, height, limit in [(3, 1, 2), (3, 7, 3), (4, 4, 2), (5, 3, 3), (6, 2, 4)]:
        codes = enumerate_codes(n, height, limit)
        capacity = (height * limit)**n
        for modulus in [capacity, capacity + 1, 1 << (capacity - 1).bit_length()]:
            for a in range(1, limit):
                for b in range(1, limit - a + 1):
                    targets = {(a + b) * v % modulus: v for v in codes}
                    require(len(targets) == len(codes), "no overflow or target alias")
                    for u, w in product(codes, repeat=2):
                        v = targets.get((a * u + b * w) % modulus)
                        require(v is None or u == v == w, "weighted modular progression")
                        relations += 1
            cases += 1
    return cases, relations


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def check_places(s, n, height, prime_limit):
    # These small test families use the exact modulus shape of the proof.
    q0 = 18480
    power = 1
    while 3 * power <= s:
        power *= 3
    ell0 = 81 * power
    modulus = q0 * 3 * ell0 * 2**s
    g = 1 + 3 * ell0 * q0
    require((2 * ell0 * height)**n <= 2**s, "room")
    require(2 * ell0 * (prime_limit + 1) < 2**s, "prime bound")
    require(gcd(g, modulus) == 1, "unit")
    exponents = enumerate_codes(n, height, 2 * ell0)
    places = {(-pow(g, e, modulus)) % modulus for e in exponents}
    require(len(places) == len(exponents) and all(p % q0 == q0 - 1 for p in places), "fibre")
    anchors = 0
    for p in filter(is_prime, range(2, prime_limit + 1)):
        prime_to_p = modulus
        while prime_to_p % p == 0:
            prime_to_p //= p
        reduced = {point % prime_to_p for point in places}
        for anchor in places:
            hits = 0
            point = anchor % prime_to_p
            for _ in range(1, ell0):
                point = point * p % prime_to_p
                if point in reduced or (-point) % prime_to_p in reduced:
                    hits += 1
            require(hits < 2, "forbidden signed Frobenius orbit")
            anchors += 1
    return len(places), anchors


if __name__ == "__main__":
    cases, relations = check_finite()
    print(f"Finite exponent checks: {cases} modulus cases, {relations} ordered pair/weight tests.")
    for params in [(64, 4, 3, 19), (90, 5, 2, 23)]:
        size, anchors = check_places(*params)
        print(f"s={params[0]}, n={params[1]}, H={params[2]}: {size} distinct places, "
              f"{anchors} anchor/prime pairs through p={params[3]}.")
