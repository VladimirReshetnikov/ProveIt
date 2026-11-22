#!/usr/bin/env python3
"""Exact power-divisor transforms and inversion on reduced residue classes."""
from functools import lru_cache
from math import gcd, prod

from check_equivalences import mobius


def exponents(n):
    divisor = 2
    while divisor * divisor <= n:
        exponent = 0
        while n % divisor == 0:
            n //= divisor
            exponent += 1
        if exponent:
            yield exponent
        divisor += 1
    if n > 1:
        yield 1


def run():
    limit = 64
    mu = [0] + [mobius(n) for n in range(1, limit + 1)]
    checked = 0
    for h in range(2, 7):
        local = [0] + [
            prod({0: 1, 1: -1}.get(e % h, 0) for e in exponents(n))
            for n in range(1, limit + 1)
        ]
        for n in range(1, limit + 1):
            divisors = [d**h for d in range(1, n + 1) if n % d**h == 0]
            assert local[n] == sum(mu[n // power] for power in divisors)
            if h == 2:
                assert local[n] == (-1)**sum(exponents(n))

        @lru_cache(None)
        def prefix(use_local, q, a, n):
            values = local if use_local else mu
            return sum(values[i] for i in range(1, n + 1) if i % q == a)

        for q in range(1, 10):
            for a in range(q):
                if gcd(a, q) != 1:
                    continue
                for n in range(limit + 1):
                    forward = inverse = 0
                    for d in range(1, n + 1):
                        power = d**h
                        if power > n:
                            break
                        if gcd(d, q) == 1:
                            preimage = (a * pow(power, -1, q)) % q
                            forward += prefix(False, q, preimage, n // power)
                            inverse += mu[d] * prefix(True, q, preimage, n // power)
                    assert forward == prefix(True, q, a, n)
                    assert inverse == prefix(False, q, a, n)
                    checked += 1
        if h == 2:
            example = [prefix(True, q, a, 10) for q, a in [(1, 0), (3, 1), (3, 2)]]
            assert example == [0, 2, -3]
            print("Liouville prefixes through 10 (all, 1 mod 3, 2 mod 3):", example)
    print(f"{checked} exact forward and inverse prefix comparisons, including the empty cutoff.")


if __name__ == "__main__":
    run()
