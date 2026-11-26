"""Riesz means of the two nonidentity Hilbert classes modulo inversion for D=-47.

Run `python sample_primes.py` to recreate prime_sample.csv next to this script.
Class membership, sieve, and comparisons of splitting are exact integers.
The final logarithmic sums are evaluated in double precision.
"""
import csv
from math import fsum, isqrt, log, sqrt
from pathlib import Path


CUTOFFS = (100, 1_000, 10_000, 100_000, 1_000_000)
# Reduced quadratic forms. The sign reversal of b gives the same represented
# integers by (x,y) -> (-x,y), so one member of each inverse pair suffices.
FORMS = ((1, 1, 12), (2, 1, 6), (3, 1, 4))


def prime_sieve(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p::p] = b"\x00" * ((limit - p*p) // p + 1)
    return flags


def represented_primes(form, prime):
    a, b, c = form
    assert 4*a*c - b*b == 47
    limit = len(prime) - 1
    seen = set()
    # 4aQ = (2ax+by)^2+47y^2. Simultaneous negation allows y>=0.
    for y in range(isqrt(4*a*limit // 47) + 1):
        radius = isqrt(4*a*limit - 47*y*y)
        xmin = -((radius + b*y) // (2*a))
        xmax = (radius - b*y) // (2*a)
        for x in range(xmin, xmax + 1):
            n = a*x*x + b*x*y + c*y*y
            if n != 47 and prime[n]:
                seen.add(n)
    return seen


def build():
    limit = max(CUTOFFS)
    prime = prime_sieve(limit)
    classes = [represented_primes(form, prime) for form in FORMS]
    principal, first, second = classes
    assert sum(map(len, classes)) == len(principal | first | second)
    # For positive primes p != 47, (-47/p)=(p/47), also valid for p=2.
    split = {p for p in range(2, limit+1) if prime[p] and pow(p, 23, 47) == 1}
    assert split == principal | first | second
    assert sum(prime) == 78_498
    print(f"{sum(prime):,} primes checked up to {limit:,}, including ramified prime 47.")
    print(f"{len(split):,} split primes; counts for the three forms: "
          + ", ".join(f"{len(c):,}" for c in classes) + ".")
    with Path(__file__).with_name("prime_sample.csv").open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("x", "n_principal", "n_class1", "n_class2", "S1", "S2",
                         "centered_S1_over_sqrt_x", "centered_S2_over_sqrt_x"))
        for x in CUTOFFS:
            counts = [sum(p <= x for p in c) for c in classes]
            means = [fsum(log(p)*((x-p)/x) for p in sorted(c) if p <= x)
                     for c in (first, second)]
            normalized = [(s-x/10)/sqrt(x) for s in means]
            writer.writerow((x, *counts, *(f"{s:.9f}" for s in (*means, *normalized))))
            print(f"x={x:7}:  normalized values {normalized[0]: .8f}, {normalized[1]: .8f}")


if __name__ == "__main__":
    build()
