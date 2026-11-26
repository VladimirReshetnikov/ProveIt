#!/usr/bin/env python3
"""Independent arbitrary-precision proof of the finite paired-norm lemma."""
import sys
from collections import Counter
from functools import lru_cache
from math import isqrt
from multiprocessing import Pool

LOWER = 31 * 10**19
CUTOFF = 5500
WITNESS_LIMIT = 2000


def sieve(bound):
    table = [True] * (bound + 1)
    table[:2] = [False, False]
    for n in range(2, isqrt(bound) + 1):
        if table[n]:
            table[n*n::n] = [False] * ((bound - n*n) // n + 1)
    return [n for n, is_prime in enumerate(table) if is_prime]


PRIMES = sieve(2 * CUTOFF)  # exceeds sqrt of every factor of size <= 3*CUTOFF^2
PROBES = [(r, {v*v % r for v in range(1, r)})
          for r in PRIMES if 2 < r <= WITNESS_LIMIT]
ELIGIBLE = [p for p in PRIMES if p <= CUTOFF and 4*p**6 > LOWER]


@lru_cache(maxsize=8000)
def factor(n):
    factors = []
    for prime in PRIMES:
        if prime * prime > n:
            break
        while n % prime == 0:
            factors.append(prime)
            n //= prime
    if n > 1:
        factors.append(n)
    return factors


def check_first_prime(p):
    counts = [0, 0, 0, 0]
    for q in ELIGIBLE:
        if q <= p:
            continue
        counts[0] += 1
        pc, qc = p**3, q**3
        product = qc*qc - pc*pc
        ceiling = isqrt(product)
        multiplicities = Counter()
        for part in (q-p, q+p, q*q+p*q+p*p, q*q-p*q+p*p):
            multiplicities.update(factor(part))
        divisors = [1]
        for prime, exponent in multiplicities.items():
            added = []
            for k in range(1, exponent + 1):
                power = prime**k
                added.extend(d*power for d in divisors if d*power <= ceiling)
            divisors.extend(added)
        for u in divisors:
            if u <= qc-pc:
                continue
            counts[1] += 1
            coefficient = product // u - u
            norm_value = 4*pc*pc - coefficient*coefficient
            if norm_value <= LOWER:
                continue
            counts[2] += 1
            if not any((-norm_value) % r in squares for r, squares in PROBES):
                counts[3] += 1
                print("Survivor", p, q, u, norm_value, flush=True)
    return counts


def main():
    totals = [0] * 4
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    with Pool(workers) as pool:
        for counts in pool.imap_unordered(check_first_prime, ELIGIBLE):
            totals = [a+b for a,b in zip(totals, counts)]
    print(f"Upper prime {CUTOFF}, eligible primes {len(ELIGIBLE)}.")
    labels = ("Prime pairs", "Divisors in the open/closed interval",
              "Candidates above the lower bound", "Survivors")
    for label, count in zip(labels, totals):
        print(f"{label}: {count}")
    if totals != [85491, 10144433, 9393302, 0]:
        raise ArithmeticError("Counts disagree with the finite lemma.")


if __name__ == "__main__":
    main()
