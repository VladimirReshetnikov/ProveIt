#!/usr/bin/env python3
"""Finite checks of the prime predicate and the centered dyadic statistic."""
from bisect import bisect_right
from decimal import Decimal, getcontext
from math import isqrt

getcontext().prec = 35


def primes_through(bound):
    sieve = bytearray([1]) * (bound + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(bound) + 1):
        if sieve[p]:
            count = (bound - p*p) // p + 1
            sieve[p*p::p] = bytes(count)
    return [p for p in range(2, bound + 1) if sieve[p]]


def irreducible_binomial(p, ell):
    return p % ell == 1 and pow(2, (p - 1) // ell, p) != 1


def independent_check(p, ell):
    # Frobenius^j sends X to X^(p^j) in F_p[X]/(X^ell-2).
    # Degree ell is prime. Rabin's test also excludes a linear factor.
    quotient, remainder = divmod(p**ell, ell)
    fixed_after_ell = remainder == 1 and pow(2, quotient, p) == 1
    has_root = any(pow(x, ell, p) == 2 % p for x in range(p))
    return fixed_after_ell and not has_root


def experiment(ell, primes):
    for p in primes[:bisect_right(primes, 1000)]:
        if p not in (2, ell):
            assert irreducible_binomial(p, ell) == independent_check(p, ell)
    selected = [p for p in primes if p not in (2, ell) and irreducible_binomial(p, ell)]
    print(f"ell={ell}; irreducibility tests agree up to p=1000")
    print("first 12 primes:", selected[:12])
    print("x       count<=x    sqrt(x)*(dyadic increment - log(2)/ell)")
    logs = {p: Decimal(p).ln() for p in selected}
    for n in [100, 1000, 10000, 100000]:
        x = Decimal(n)
        value = sum(logs[p] for p in selected if p <= n) / (2*x)
        value += sum(logs[p] * (1/Decimal(p) - 1/(2*x))
                     for p in selected if n < p <= 2*n)
        centered = x.sqrt() * (value - Decimal(2).ln()/ell)
        print(f"{n:6}  {bisect_right(selected, n):9}    {centered: .8f}")


if __name__ == "__main__":
    primes = primes_through(200000)
    for ell in [3, 5]:
        experiment(ell, primes)
