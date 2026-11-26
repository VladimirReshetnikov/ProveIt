#!/usr/bin/env python3
"""Evaluate the uncentered fourth-power statistic for y^2+y=x^3-x (d=2).

Uses only Python's standard library. The table includes the first difference
of S(x)-4 log(x), which removes the unknown additive constant. This finite
calculation does not test an eventual power bound. For small ranges.
"""
import argparse
import math


def primes_up_to(bound):
    sieve = bytearray(b"\x01") * (bound + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(bound) + 1):
        if sieve[p]:
            start = p * p
            sieve[start::p] = bytes((bound - start) // p + 1)
    return [p for p in range(2, bound + 1) if sieve[p]]


def frobenius_trace(p):
    """Count affine points on the reduced curve via value multiplicities."""
    counts = [0] * p
    for y in range(p):
        counts[(y * y + y) % p] += 1
    affine_points = sum(counts[(x * x * x - x) % p] for x in range(p))
    return p - affine_points


def weights(limit):
    terms = []
    for p in primes_up_to(limit):
        if p == 37:
            continue
        a = frobenius_trace(p)
        trace_prev, trace = 2, a
        q = p
        while q <= limit:
            assert trace * trace <= 4 * q
            z = trace / math.sqrt(q)
            f = (z * z + math.sqrt(2) * z) ** 2
            terms.append((q, math.log(p) * f))
            trace_prev, trace = trace, a * trace - p * trace_prev
            q *= p
    return sorted(terms)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=10)
    args = parser.parse_args()
    if args.max_n < 2:
        parser.error("--max-n must be at least 2")
    # Independent values for E at the first three good primes.
    assert [frobenius_trace(p) for p in (2, 3, 5)] == [-2, -3, -2]
    terms = weights(args.max_n ** 4)
    print("n,x,S_f(x),S_f(x)-4log(x),change_from_previous_row")
    previous = None
    for n in range(1, args.max_n + 1):
        x = n ** 4
        value = math.fsum(w * (1 / q - 1 / x) for q, w in terms if q <= x)
        centered = value - 4 * math.log(x)
        change = "" if previous is None else f"{centered - previous:.12f}"
        print(f"{n},{x},{value:.12f},{centered:.12f},{change}")
        previous = centered


if __name__ == "__main__":
    main()
