"""Compare eta-product and Frobenius coefficients, then print Riesz sums.

Run with Python 3.10+, using only its standard library. The integer coefficient
check is exact. Riesz sums use double-precision logarithms and math.fsum.
"""
import argparse
from math import fsum, isqrt, log, sqrt


def primes_up_to(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit - p*p)//p + 1)
    return (p for p in range(2, limit + 1) if sieve[p])


def pentagonal_terms(limit):
    yield (0, 1)
    k = 1
    while k*(3*k-1)//2 <= limit:
        for exponent in (k*(3*k-1)//2, k*(3*k+1)//2):
            if exponent <= limit:
                yield exponent, (-1)**k
        k += 1


def eta_coefficients(limit):
    # eta(z) eta(23z)=q E(q) E(q^23). Euler's pentagonal theorem.
    coef = [0] * (limit + 1)
    terms = list(pentagonal_terms(limit - 1))
    for j, sign in pentagonal_terms((limit - 1)//23):
        shift = 1 + 23*j
        for i, sign2 in terms:
            if shift + i > limit:
                break
            coef[shift+i] += sign*sign2
    return coef


def split_completely(p):
    # Test X^p = X in F_p[X]/(X^3-X-1).
    def mul(u, v):
        a,b,c = u
        d,e,f = v
        c3 = b*f + c*e
        c4 = c*f
        return ((a*d+c3) % p, (a*e+b*d+c3+c4) % p,
                (a*f+b*e+c*d+c4) % p)
    result = (1,0,0)
    base = (0,1,0)
    exponent = p
    while exponent:
        if exponent % 2:
            result = mul(result, base)
        base = mul(base, base)
        exponent //= 2
    return result == (0,1,0)


def run(limit):
    coef = eta_coefficients(limit)
    weights = []
    counts = {-1: 0, 0: 0, 2: 0}
    for p in primes_up_to(limit):
        if p == 23:
            assert coef[p] == 1
            continue
        # The sign character is (-23/p)=(p/23), also at p=2.
        if pow(p % 23, 11, 23) == 22:
            trace = 0
        else:
            trace = 2 if split_completely(p) else -1
        if coef[p] != trace:
            raise ValueError((p, trace, coef[p]))
        counts[trace] += 1
        weights.append((p, trace*log(p)))
    print(f"Unramified prime comparisons through {limit}: {sum(counts.values())}")
    print("Frobenius trace counts:", counts)
    print("Threshold, prime Riesz sum, sum divided by sqrt(threshold)")
    for x in sorted({10**k for k in range(1, len(str(limit))) if 10**k <= limit} | {limit}):
        total = fsum(w * (1 - p / x) for p,w in weights if p <= x)
        print(f"{x}, {total:.9f}, {total/sqrt(x):.9f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", nargs="?", type=int, default=1_000_000)
    limit = parser.parse_args().limit
    if limit < 2:
        parser.error("limit must be at least 2")
    run(limit)
